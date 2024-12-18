pub mod error;
pub mod request;
pub mod response;

use self::{
    error::{LlmError, LlmResult},
    request::IsLlmRequest,
    response::IsLlmResponse,
};
use attach::Attach;
use disk_cache::{error::LlmCacheError, DiskCache};
use request::{chat_completion::LlmChatCompletionRequest, LlmRequest};
use response::{chat_completion::LlmChatCompletionResponse, LlmResponse};
use serde::{Deserialize, Serialize};

#[sealed::sealed]
pub trait IsLlm: IsLlmImpl {
    fn chat_completion(&self, prompt: &str) -> Result<Self::ChatCompletionResponse, Self::Error>;
    // TODO: what's the difference between chat_completion_with_caching and chat_completion_without_caching?
    fn chat_completion_without_caching(
        &self,
        prompt: &str,
    ) -> LlmResult<Self::ChatCompletionResponse>;
}

pub trait IsLlmImpl {
    type Db: Attach;
    type Error: From<LlmCacheError> + From<LlmError> + Into<LlmError>;
    type Request: IsLlmRequest + From<LlmRequest>;
    type Response: IsLlmResponse + Into<LlmResponse>;
    type ChatCompletionRequest: TryFrom<Self::Request>
        + From<LlmChatCompletionRequest>
        + Into<Self::Request>;
    type ChatCompletionResponse: TryFrom<Self::Response>
        + From<LlmChatCompletionResponse>
        + Into<Self::Response>;

    fn cache(&self) -> &DiskCache<Self::Db, Self::Request, Self::Response>;
    fn chat_completion_impl(
        &self,
        request: Self::ChatCompletionRequest,
    ) -> Result<Self::Response, Self::Error>;
}

#[sealed::sealed]
impl<T: IsLlmImpl> IsLlm for T {
    fn chat_completion(&self, prompt: &str) -> Result<Self::ChatCompletionResponse, Self::Error> {
        let request: Self::ChatCompletionRequest = LlmChatCompletionRequest {
            prompt: prompt.to_string(),
        }
        .into();
        self.cache()
            .get_or_call(request.into(), |request| match request.clone().try_into() {
                Ok(request) => self.chat_completion_impl(request),
                Err(_) => unreachable!(),
            })
            .map(|response| match response.try_into() {
                Ok(response) => response,
                Err(_) => unreachable!(),
            })
    }

    fn chat_completion_without_caching(
        &self,
        prompt: &str,
    ) -> LlmResult<Self::ChatCompletionResponse> {
        todo!()
    }
}

#[sealed::sealed]
pub trait IsLlmDyn {}
