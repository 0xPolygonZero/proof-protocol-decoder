use reqwest::IntoUrl;
use serde::{de::DeserializeOwned, Deserialize};
use serde_json::json;
use thiserror::Error;

use crate::types::{BlockHeight, TrieRootHash};

pub type VerifierRpcResult<T> = Result<T, VerifierRpcError>;

#[derive(Debug, Error)]
pub enum VerifierRpcError {
    #[error(transparent)]
    Reqwest(#[from] reqwest::Error),

    #[error(transparent)]
    Deserialize(#[from] serde_json::Error),
}

pub(super) struct RpcRequest<'a, U: IntoUrl> {
    endpoint: U,
    method: &'static str,
    params: &'a [String],
}

pub(super) async fn rpc_request<'a, T, U>(req: RpcRequest<'a, U>) -> VerifierRpcResult<T>
where
    T: DeserializeOwned,
    U: IntoUrl,
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
    pub(super) async fn fetch<U: IntoUrl>(
        endpoint: U,
        b_height: BlockHeight,
    ) -> VerifierRpcResult<Self> {
        let req = RpcRequest {
            endpoint,
            method: "eth_getBlockByNumber",
            params: &[b_height.to_string(), "false".into()],
        };

        rpc_request(req).await
    }
}
