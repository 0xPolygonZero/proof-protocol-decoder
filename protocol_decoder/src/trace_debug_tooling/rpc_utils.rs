use std::{
    collections::HashMap,
    fmt::{self, Display, LowerHex},
    marker::PhantomData,
    ops::Deref,
    time::Duration,
};

use ethereum_types::{Address, H256, U256};
use plonky2_evm::generation::mpt::AccountRlp;
use rand::Rng;
use reqwest::{RequestBuilder, Url};
use serde::{
    de::{self, DeserializeOwned, IntoDeserializer, Visitor},
    Deserialize, Deserializer,
};
use serde_json::json;
use serde_with::{serde_as, DefaultOnError};
use thiserror::Error;
use tokio::time::timeout;

use crate::types::{BlockHeight, CodeHash, StorageAddr, StorageVal, TrieRootHash};

pub type VerifierRpcResult<T> = Result<T, VerifierRpcError>;

const RPC_TIMEOUT: Duration = Duration::from_millis(500);

const RPC_BACKOFF_MIN: Duration = Duration::from_millis(250);
const RPC_BACKOFF_MAX: Duration = Duration::from_millis(1000);

#[derive(Debug, Error)]
pub enum VerifierRpcError {
    #[error(transparent)]
    Reqwest(#[from] reqwest::Error),

    #[error(transparent)]
    Deserialize(#[from] serde_json::Error),
}

#[derive(Clone, Debug)]
pub(super) struct RpcRequest<'a> {
    endpoint: Url,
    method: &'static str,
    params: &'a [serde_json::Value],
}

pub(super) async fn rpc_request<T>(req: RpcRequest<'_>) -> VerifierRpcResult<T>
where
    T: DeserializeOwned,
{
    let client = reqwest::Client::new();

    let req_fut = || {
        let req = &req;
        client
            .post(req.endpoint.clone())
            .json(&json_req_payload(req.method, req.params))
    };

    retry_req_until_we_get_resp_with_backoff(req_fut).await
}

async fn retry_req_until_we_get_resp_with_backoff<
    T: DeserializeOwned,
    F: Fn() -> RequestBuilder,
>(
    req_fn: F,
) -> VerifierRpcResult<T> {
    loop {
        let req_fut = req_fn().send();
        let resp_res = timeout(RPC_TIMEOUT, req_fut).await;

        match resp_res {
            Err(_) | Ok(Err(_)) => {
                tokio::time::sleep(gen_random_backoff()).await;
                continue;
            }
            Ok(Ok(resp)) => {
                let bytes = resp.bytes().await?;
                let s = String::from_utf8(bytes.to_vec()).unwrap();

                println!("RPC RESP: for request: {}", s);

                return serde_json::from_slice(&bytes).map_err(|err| err.into());
            }
        }
    }
}

fn gen_random_backoff() -> Duration {
    let mut rng = rand::thread_rng();
    rng.gen_range(RPC_BACKOFF_MIN..RPC_BACKOFF_MAX)
}

fn json_req_payload(method: &str, params: &[serde_json::Value]) -> serde_json::Value {
    json!({
        "jsonrpc": "2.0",
        "method": method,
        "params": params,
        "id": 1,
    })
}

#[derive(Debug, Deserialize)]
pub(super) struct GetBlockByNumberResponse {
    pub(super) result: GetBlockByNumberResult,
}

impl GetBlockByNumberResponse {
    pub(super) async fn fetch(
        endpoint: &Url,
        b_height: BlockHeight,
    ) -> VerifierRpcResult<GetBlockByNumberResult> {
        let req = RpcRequest {
            endpoint: endpoint.clone(),
            method: "eth_getBlockByNumber",
            params: &[format!("0x{:x}", b_height).into(), false.into()],
        };

        let res = rpc_request::<Self>(req)
            .await
            .map(|resp| {
                println!("{:?}", resp);
                resp.result
            })
            .unwrap_or_else(|err| panic!("{}", err));

        Ok(res)
    }
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct GetBlockByNumberResult {
    pub(super) state_root: TrieRootHash,
    pub(super) receipts_root: TrieRootHash,

    #[serde(rename = "transactionsRoot")]
    pub(super) txns_root: TrieRootHash,

    #[serde(rename = "transactions")]
    pub(super) txn_hashes: Vec<H256>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct EthGetProofResponse {
    pub(super) result: EthGetProofResult,
}

impl EthGetProofResponse {
    pub(super) async fn fetch(
        endpoint: &Url,
        address: Address,
        b_height: BlockHeight,
    ) -> VerifierRpcResult<EthGetProofResult> {
        let req = RpcRequest {
            endpoint: endpoint.clone(),
            method: "eth_getProof",
            params: &[
                format!("0x{:x}", address).into(),
                json!([]),
                format!("0x{:x}", b_height).into(),
            ],
        };

        let resp = rpc_request::<Self>(req.clone()).await;

        println!("Resp: {:?}", resp);

        let res = resp
            .map(|resp| resp.result)
            .unwrap_or_else(|err| panic!("{}, req: {:?}", err, req));

        Ok(res)
    }
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct EthGetProofResult {
    pub(super) balance: U256,
    pub(super) nonce: U256,
    pub(super) code_hash: CodeHash,
    pub(super) storage_hash: TrieRootHash,
}

impl From<EthGetProofResult> for AccountRlp {
    fn from(v: EthGetProofResult) -> Self {
        Self {
            nonce: v.nonce,
            balance: v.balance,
            storage_root: v.storage_hash,
            code_hash: v.code_hash,
        }
    }
}

#[derive(Debug, Deserialize)]
pub(super) struct TraceReplayTransactionResponse {
    pub(super) result: TraceReplayTransactionResult,
}

impl TraceReplayTransactionResponse {
    pub(super) async fn fetch(
        endpoint: &Url,
        txn_hash: &H256,
    ) -> VerifierRpcResult<TraceReplayTransactionResult> {
        let req = RpcRequest {
            endpoint: endpoint.clone(),
            method: "trace_replayTransaction",
            params: &[
                format!("0x{:x}", txn_hash).into(),
                serde_json::Value::Array(vec!["stateDiff".into()]),
            ],
        };

        rpc_request::<Self>(req).await.map(|resp| resp.result)
    }
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct TraceReplayTransactionResult {
    pub(super) state_diff: HashMap<Address, ChangedStateFields>,
}

// impl<'de> Deserialize<'de> for TraceReplayTransactionResult {
//     fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
//     where
//         D: serde::Deserializer<'de> {
//         deserializer.deserialize_map(StateDiffVisitor).map(|x| Self(x))
//     }
// }

struct StateDiffVisitor;

impl<'de> Visitor<'de> for StateDiffVisitor {
    type Value = HashMap<Address, ChangedStateFields>;

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        let mut h_map = HashMap::with_capacity(map.size_hint().unwrap_or(1));

        while let Some((k, v)) = map.next_entry::<Address, serde_json::Value>()? {
            let v = ChangedStateFields::deserialize(v.into_deserializer()).unwrap();
            h_map.insert(k, v);
        }

        Ok(h_map)
    }

    fn expecting(&self, _formatter: &mut fmt::Formatter) -> fmt::Result {
        todo!()
    }
}

#[derive(Clone, Debug, Deserialize)]
pub(super) struct FromToEntry<T> {
    from: T,
    to: T,
}

// #[derive(Clone, Debug)]
// struct CodeHashWithProperDeser(CodeHash);

// impl<'de> Deserialize<'de> for CodeHashWithProperDeser {
//     fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
//     where
//         D: Deserializer<'de> {

//     }
// }

// struct CodeHashWithProperDeserVisitor

// impl Deref for CodeHashWithProperDeser {
//     type Target = CodeHash;

//     fn deref(&self) -> &Self::Target {
//         &self.0
//     }
// }

#[serde_as]
#[derive(Clone, Debug, Deserialize)]
pub(super) struct ChangedStateFields {
    balance: DiffValueOpt<U256>,
    nonce: DiffValueOpt<U256>,
    #[serde_as(deserialize_as = "DefaultOnError")]
    code: DiffValueOpt<CodeHash>,
    storage: HashMap<StorageAddr, DiffValueOpt<StorageVal>>,
}

#[derive(Debug)]
pub(super) struct AccountRlpWithStorageTrie {
    pub(super) balance: U256,
    pub(super) nonce: U256,
    pub(super) code_hash: CodeHash,
    pub(super) storage_trie_delta: HashMap<StorageAddr, StorageVal>,
}

impl ChangedStateFields {
    pub(super) fn create_diff_from_actual_data(
        &self,
        old_data: &AccountRlpWithStorageTrie,
    ) -> AccountStateEntryDiff {
        let storage: HashMap<_, _> = self
            .storage
            .iter()
            .map(|(slot, new_val)| {
                (
                    slot,
                    new_val.clone().unwrap_or_default(),
                    old_data
                        .storage_trie_delta
                        .get(slot)
                        .cloned()
                        .unwrap_or_default(),
                )
            })
            .filter(|(_, new_val, old_val)| old_val != new_val)
            .map(|(slot, new_val, old_val)| {
                (
                    *slot,
                    DiffValue {
                        old: old_val,
                        new: new_val,
                    },
                )
            })
            .collect();

        AccountStateEntryDiff {
            balance: DiffValue::get_new_value_if_value_changed(&old_data.balance, &self.balance),
            nonce: DiffValue::get_new_value_if_value_changed(&old_data.nonce, &self.nonce),
            code_hash: DiffValue::get_new_value_if_value_changed(&old_data.code_hash, &self.code),
            storage: (!storage.is_empty()).then_some(storage),
        }
    }

    pub(super) fn get_storage_addrs_changed(&self) -> Option<Vec<StorageAddr>> {
        (!self.storage.is_empty()).then(|| self.storage.keys().cloned().collect())
    }
}

#[derive(Clone, Debug, Default)]
struct DiffValueOpt<T>(Option<T>);

impl<'de, T: DeserializeOwned> Deserialize<'de> for DiffValueOpt<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self(
            deserializer.deserialize_any(DiffFieldVisitor(PhantomData::<T>))?,
        ))
    }
}

impl<T> Deref for DiffValueOpt<T> {
    type Target = Option<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug)]
struct DiffValue<T> {
    old: T,
    new: T,
}

impl<T: Display> Display for DiffValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Local: {}, Upstream: {}", self.old, self.new)
    }
}

impl<T: LowerHex> LowerHex for DiffValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Local: {:x}, Upstream: {:x}", self.old, self.new)
    }
}

impl<T: Clone + PartialEq> DiffValue<T> {
    fn get_new_value_if_value_changed(old_v: &T, changed_v: &Option<T>) -> Option<DiffValue<T>> {
        match changed_v {
            Some(new_v) if new_v != old_v => Some(Self {
                old: new_v.clone(),
                new: new_v.clone(),
            }),
            _ => None,
        }
    }
}

struct DiffFieldVisitor<T>(PhantomData<T>);

impl<'de, T: DeserializeOwned> Visitor<'de> for DiffFieldVisitor<T> {
    type Value = Option<T>;

    fn visit_str<E>(self, _v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(None)
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        Ok(match map.next_entry::<String, serde_json::Value>() {
            Ok(Some((op_type, entry_raw))) => match op_type.as_str() {
                "*" => Some(
                    FromToEntry::deserialize(entry_raw.into_deserializer())
                        .map_err(de::Error::custom)?
                        .to,
                ),
                "+" => {
                    Some(T::deserialize(entry_raw.into_deserializer()).map_err(de::Error::custom)?)
                }
                _ => {
                    return Err(de::Error::custom(format!(
                        "Unsupported op type {}!",
                        op_type
                    )))
                }
            },
            _ => None,
        })
        // .unwrap()
        // .unwrap();

        // match op_type.as_str() {

        //     "*" | "+" => {
        //         FromToEntry::deserialize(from_to_entry.into_deserializer())

        //         Ok(Some(from_to_entry.to))
        //     },
        //     _ => Err(de::Error::invalid_value(
        //         Unexpected::Str(&op_type),
        //         &"+ | *",
        //     )),
        // }
    }

    fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "An operator followed by a to & from entry.")
    }
}

// #[derive(Debug, Deserialize)]
// struct AccountStateEntryDiffRaw {
//     balance: DiffValueOpt<U256>,
//     nonce: DiffValueOpt<U256>,
//     code_hash: DiffValueOpt<CodeHash>,
//     storage_root: DiffValueOpt<TrieRootHash>,
// }

// impl Deserialize for AccountStateEntryDiffRaw {
//     fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
//     where
//         D: serde::Deserializer<'de> {
//         Ok(Self {
//             balance: deserializer.,
//             nonce: todo!(),
//             code_hash: todo!(),
//             storage_root: todo!(),
//         })
//     }
// }

#[derive(Clone, Debug)]
pub(super) struct AccountStateEntryDiff {
    balance: Option<DiffValue<U256>>,
    nonce: Option<DiffValue<U256>>,
    code_hash: Option<DiffValue<CodeHash>>,
    storage: Option<HashMap<StorageAddr, DiffValue<StorageVal>>>,
}

impl Display for AccountStateEntryDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.values_have_changed() {
            false => write!(f, "None")?,
            true => {
                Self::print_field_if_different_hex_and_return_if_diff_detected(f, &self.balance)?;
                Self::print_field_if_different_hex_and_return_if_diff_detected(f, &self.nonce)?;
                Self::print_field_if_different_hex_and_return_if_diff_detected(f, &self.code_hash)?;

                if let Some(v) = &self.storage {
                    write!(f, "Storage slots changed:")?;
                    write!(f, "{:#?}", v)?
                }
            }
        }

        Ok(())
    }
}

impl AccountStateEntryDiff {
    pub(super) fn values_have_changed(&self) -> bool {
        self.balance.is_some()
            || self.nonce.is_some()
            || self.code_hash.is_some()
            || self.storage.is_some()
    }

    fn print_field_if_different_hex_and_return_if_diff_detected<T: LowerHex>(
        f: &mut fmt::Formatter,
        field: &Option<DiffValue<T>>,
    ) -> fmt::Result {
        if let Some(v) = field {
            write!(f, "{:x}", v)?;
        }

        Ok(())
    }
}
