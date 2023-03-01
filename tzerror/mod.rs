
//! 
//! 错误码
//! 
//! 目标实现多种描述符
//! 并且携带错误信息
//! 讨论是否可以分成中文和英文两种调试信息
//! 
//! 最基本的处理方式:
//! 1. 抛出异常与信息
//! 2. 将异常返回到上级
//! 
//! by iTheds
//! 
//! 考虑到其他组件也会使用错误码,例如 os_base 层次,或者同级 utilities 层次.
//! 错误码可进行兼容性追加.
//! 追加方式:
//! 1. 直接新建错误码并追加.添加错误码之后应该建立描述符;
//! 2. 兼容性追加: 在 TZError 中添加一个错误码, 以 Link 方式,并且在描述符中添加该错误码描述
//! 
//! 

///
/// 错误码 
/// 
#[derive(Debug)]
pub enum TZError {
    TZDB_CODE_RPC_NETWORK_UNAVAIL,  // 所有名称按此编写, 每添加一个名称就应该多一个描述
    MapSizeZero,
    NoLinkOrOsId,
    FlinkInvalidOsId,
    LinkCreateFailed(std::io::Error),
    LinkWriteFailed(std::io::Error),
    LinkExists,
    LinkOpenFailed(std::io::Error),
    LinkReadFailed(std::io::Error),
    LinkDoesNotExist,
    MappingIdExists,
    MapCreateFailed(u32),
    MapOpenFailed(u32),
    UnknownOsError(u32),
}

/// 重写显示
impl std::fmt::Display for TZError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TZError::TZDB_CODE_RPC_NETWORK_UNAVAIL => f.write_str("You cannot create a shared memory mapping of 0 size"),
            TZError::MapSizeZero => f.write_str("You cannot create a shared memory mapping of 0 size"),
            TZError::NoLinkOrOsId => f.write_str("Tried to open mapping without flink path or os_id"),
            TZError::FlinkInvalidOsId => f.write_str("Tried to open mapping from both flink and os_id but the flink did not point to the same os_id"),
            TZError::LinkCreateFailed(err) => write!(f, "Creating the link file failed, {err}"),
            TZError::LinkWriteFailed(err) => write!(f, "Writing the link file failed, {err}"),
            TZError::LinkExists => f.write_str("Shared memory link already exists"),
            TZError::LinkOpenFailed(err) => write!(f, "Opening the link file failed, {err}"),
            TZError::LinkReadFailed(err) => write!(f, "Reading the link file failed, {err}"),
            TZError::LinkDoesNotExist => f.write_str("Requested link file does not exist"),
            TZError::MappingIdExists => f.write_str("Shared memory OS specific ID already exists"),
            TZError::MapCreateFailed(err) => write!(f, "Creating the shared memory failed, os error {err}"),
            TZError::MapOpenFailed(err) => write!(f, "Opening the shared memory failed, os error {err}"),
            TZError::UnknownOsError(err) => write!(f, "An unexpected OS error occurred, os error {err}"),
        }
    }
}

///重载,该处猜测是链接到其他的错误码中,有一段描述符,嵌套另一套描述符
impl std::error::Error for TZError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            TZError::LinkCreateFailed(err) => Some(err),
            TZError::LinkWriteFailed(err) => Some(err),
            TZError::LinkOpenFailed(err) => Some(err),
            TZError::LinkReadFailed(err) => Some(err),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::TZError;

    struct Food{}

    /// 手动抛出异常
    fn call_error() -> Result<Food, TZError>{
        Err(TZError::FlinkInvalidOsId)
    }
    /// unwarp 抛出
    
    /// 捕获其他异常并且分析,主要是因为其他的组件可能有自我的错误处理

    /// 人存在于社会,不应该只追求自己值多少,更应该询问自己愿意为谁而服务
    #[test]
    fn test_error(){

    }
}

