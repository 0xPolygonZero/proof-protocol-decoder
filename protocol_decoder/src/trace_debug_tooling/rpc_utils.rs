use std::{
    collections::HashMap,
    fmt::{self, Display, LowerHex, Pointer},
    marker::PhantomData,
    str::FromStr,
};

use ethereum_types::{Address, H256, U256};
use plonky2_evm::generation::mpt::AccountRlp;
use reqwest::Url;
use serde::{
    de::{self, DeserializeOwned, Unexpected, Visitor},
    Deserialize,
};
use serde_json::json;
use thiserror::Error;

use crate::types::{BlockHeight, CodeHash, TrieRootHash};

pub type VerifierRpcResult<T> = Result<T, VerifierRpcError>;

#[derive(Debug, Error)]
pub enum VerifierRpcError {
    #[error(transparent)]
    Reqwest(#[from] reqwest::Error),

    #[error(transparent)]
    Deserialize(#[from] serde_json::Error),
}

pub(super) struct RpcRequest<'a> {
    endpoint: Url,
    method: &'static str,
    params: &'a [String],
}

pub(super) async fn rpc_request<T>(req: RpcRequest<'_>) -> VerifierRpcResult<T>
where
    T: DeserializeOwned,
{
    let client = reqwest::Client::new();

    let resp = client
        .post(req.endpoint)
        .json(&json_req_payload(req.method, req.params))
        .send()
        .await?;

    let bytes = resp.bytes().await?;
    let res = serde_json::from_slice(&bytes)?;

    Ok(res)
}

fn json_req_payload(method: &str, params: &[String]) -> serde_json::Value {
    json!({
        "jsonrpc": "2.0",
        "method": method,
        "params": params,
        "id": 1,
    })
}

#[derive(Debug, Deserialize)]
pub(super) struct GetBlockByNumberResponse {
    pub(super) state_root: TrieRootHash,
    pub(super) receipts_root: TrieRootHash,
    pub(super) txn_root: TrieRootHash,
    pub(super) txn_hashes: Vec<H256>,
}

impl GetBlockByNumberResponse {
    pub(super) async fn fetch(endpoint: &Url, b_height: BlockHeight) -> VerifierRpcResult<Self> {
        let req = RpcRequest {
            endpoint: endpoint.clone(),
            method: "eth_getBlockByNumber",
            params: &[b_height.to_string(), "false".into()],
        };

        rpc_request(req).await
    }
}

// #[derive(Debug, Deserialize)]
// pub(super) struct EthGetAccountResponse {
//     pub(super) balance: U256,
//     pub(super) nonce: U256,
//     pub(super) code_root: CodeHash,
//     pub(super) storage_root: TrieRootHash,
// }

// impl From<EthGetAccountResponse> for AccountRlp {
//     fn from(v: EthGetAccountResponse) -> Self {
//         Self {
//             nonce: v.nonce,
//             balance: v.balance,
//             storage_root: v.storage_root,
//             code_hash: v.code_root,
//         }
//     }
// }

// impl EthGetAccountResponse {
//     pub(super) async fn fetch(
//         endpoint: &Url,
//         address: Address,
//         b_height: BlockHeight,
//     ) -> VerifierRpcResult<Self> {
//         let req = RpcRequest {
//             endpoint: endpoint.clone(),
//             method: "eth_getAccount",
//             params: &[address.to_string(), b_height.to_string()],
//         };

//         rpc_request(req).await
//     }
// }

#[derive(Debug, Deserialize)]
pub(super) struct EthGetProofResponse {
    pub(super) balance: U256,
    pub(super) nonce: U256,
    pub(super) code_hash: CodeHash,
    pub(super) storage_hash: TrieRootHash,
}

impl From<EthGetProofResponse> for AccountRlp {
    fn from(v: EthGetProofResponse) -> Self {
        Self {
            nonce: v.nonce,
            balance: v.balance,
            storage_root: v.storage_hash,
            code_hash: v.code_hash,
        }
    }
}

impl EthGetProofResponse {
    pub(super) async fn fetch(
        endpoint: &Url,
        address: Address,
        b_height: BlockHeight,
    ) -> VerifierRpcResult<Self> {
        let req = RpcRequest {
            endpoint: endpoint.clone(),
            method: "eth_getProof",
            params: &[address.to_string(), b_height.to_string()],
        };

        rpc_request(req).await
    }
}

#[derive(Debug, Deserialize)]
pub(super) struct TraceReplayTransactionResponse {
    pub(super) result: TraceReplayTransactionResult,
}

impl TraceReplayTransactionResponse {
    pub(super) async fn fetch(endpoint: &Url, txn_hash: &H256) -> VerifierRpcResult<Self> {
        let req = RpcRequest {
            endpoint: endpoint.clone(),
            method: "trace_replayTransaction",
            params: &[txn_hash.to_string(), "stateDiff".into()],
        };

        rpc_request(req).await
    }
}

#[derive(Debug, Deserialize)]
pub(super) struct TraceReplayTransactionResult {
    pub(super) state_diff: HashMap<Address, ChangedStateFields>,
}

struct DiffFieldVisitor<T: FromStr>(PhantomData<T>);

impl<'de, T: FromStr + DeserializeOwned> Visitor<'de> for DiffFieldVisitor<T> {
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
        let (op_type, from_to_entry): (String, FromToEntry<T>) = map.next_entry().unwrap().unwrap();

        match op_type.as_str() {
            "*" | "+" => Ok(Some(from_to_entry.to)),
            _ => Err(de::Error::invalid_value(
                Unexpected::Str(&op_type),
                &"+ | *",
            )),
        }
    }

    fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "An operator followed by a to & from entry.")
    }
}

#[derive(Clone, Debug, Deserialize)]
pub(super) struct FromToEntry<T> {
    from: T,
    to: T,
}

#[derive(Clone, Debug, Deserialize)]
pub(super) struct ChangedStateFields {
    balance: Option<U256>,
    nonce: Option<U256>,
    code: Option<CodeHash>,
    storage: Option<TrieRootHash>,
}

impl ChangedStateFields {
    pub(super) fn create_diff_from_actual_data(
        &self,
        old_data: &AccountRlp,
    ) -> AccountStateEntryDiff {
        AccountStateEntryDiff {
            balance: DiffValue::get_new_value_if_value_changed(&old_data.balance, &self.balance),
            nonce: DiffValue::get_new_value_if_value_changed(&old_data.nonce, &self.nonce),
            code_hash: DiffValue::get_new_value_if_value_changed(&old_data.code_hash, &self.code),
            storage_root: DiffValue::get_new_value_if_value_changed(
                &old_data.storage_root,
                &self.storage,
            ),
        }
    }
}

#[derive(Clone, Debug)]
struct DiffValue<T> {
    old: T,
    new: T,
}

impl<T: Display> Display for DiffValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Prev: {}, New: {}", self.old, self.new)
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

#[derive(Clone, Debug)]
pub(super) struct AccountStateEntryDiff {
    balance: Option<DiffValue<U256>>,
    nonce: Option<DiffValue<U256>>,
    code_hash: Option<DiffValue<CodeHash>>,
    storage_root: Option<DiffValue<TrieRootHash>>,
}

impl Display for AccountStateEntryDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Self::print_field_if_different(f, &self.balance)?;
        Self::print_field_if_different(f, &self.nonce)?;
        Self::print_field_if_different(f, &self.code_hash)?;
        Self::print_field_if_different(f, &self.storage_root)?;

        Ok(())
    }
}

impl AccountStateEntryDiff {
    pub(super) fn values_have_changed(&self) -> bool {
        self.balance.is_some()
            || self.nonce.is_some()
            || self.code_hash.is_some()
            || self.storage_root.is_some()
    }

    fn print_field_if_different<T: LowerHex>(
        f: &mut fmt::Formatter,
        field: &Option<DiffValue<T>>,
    ) -> fmt::Result {
        if let Some(_v) = field {
            field.fmt(f)?;
        }

        Ok(())
    }
}
