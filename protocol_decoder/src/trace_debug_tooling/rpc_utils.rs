use ethereum_types::{Address, H256, U256};
use plonky2_evm::generation::mpt::AccountRlp;
use reqwest::Url;
use serde::{de::DeserializeOwned, Deserialize};
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

#[derive(Debug, Deserialize)]
pub(super) struct EthGetAccountResponse {
    pub(super) balance: U256,
    pub(super) nonce: U256,
    pub(super) code_root: CodeHash,
    pub(super) storage_root: TrieRootHash,
}

impl From<EthGetAccountResponse> for AccountRlp {
    fn from(v: EthGetAccountResponse) -> Self {
        Self {
            nonce: v.nonce,
            balance: v.balance,
            storage_root: v.storage_root,
            code_hash: v.code_root,
        }
    }
}

impl EthGetAccountResponse {
    pub(super) async fn fetch(
        endpoint: &Url,
        address: Address,
        b_height: BlockHeight,
    ) -> VerifierRpcResult<Self> {
        let req = RpcRequest {
            endpoint: endpoint.clone(),
            method: "eth_getAccount",
            params: &[address.to_string(), b_height.to_string()],
        };

        rpc_request(req).await
    }
}
