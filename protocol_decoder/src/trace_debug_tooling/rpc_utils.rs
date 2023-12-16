use reqwest::Url;
use serde::de::DeserializeOwned;
use serde_json::json;
use thiserror::Error;

pub type VerifierRpcResult<T> = Result<T, VerifierRpcError>;

#[derive(Debug, Error)]
pub enum VerifierRpcError {
    #[error(transparent)]
    Reqwest(#[from] reqwest::Error),

    #[error(transparent)]
    Deserialize(#[from] serde_json::Error),
}

pub(super) struct RpcRequest {
    endpoint: Url,
    method: &'static str,
    params: Vec<String>,
}

pub(super) async fn rpc_request<T: DeserializeOwned>(req: &RpcRequest) -> VerifierRpcResult<T> {
    let client = reqwest::Client::new();

    let resp = client
        .post(req.endpoint.clone())
        .json(&json_req_payload(req.method, &req.params))
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
