use crate::*;

pub trait ParseFromWithRollback<SP>: TryParseOptionFromStream<SP>
where
    SP: IsStreamParser + ?Sized,
{
    type Error;

    fn try_parse_from_stream_with_rollback_when_no_error<'a>(
        stream: &mut SP,
    ) -> Result<Option<Self>, <Self as ParseFromWithRollback<SP>>::Error>;

    fn try_parse_option_from_with_rollback_ignoring_error<'a>(stream: &mut SP) -> Option<Self>;
}

impl<Context, P> ParseFromWithRollback<Context> for P
where
    Context: IsStreamParser + ?Sized,
    P: TryParseOptionFromStream<Context>,
{
    type Error = <P as TryParseOptionFromStream<Context>>::Error;
    fn try_parse_from_stream_with_rollback_when_no_error<'a>(
        stream: &mut Context,
    ) -> Result<Option<Self>, <P as TryParseOptionFromStream<Context>>::Error> {
        let state = stream.state();
        let result = Self::try_parse_option_from_stream_without_guaranteed_rollback(stream);
        match result {
            // rollback for no pattern
            Ok(None) => stream.rollback(state),
            _ => (),
        }
        result
    }

    fn try_parse_option_from_with_rollback_ignoring_error<'a>(
        stream: &mut Context,
    ) -> Option<Self> {
        let state = stream.state();
        let result = Self::try_parse_option_from_stream_without_guaranteed_rollback(stream);
        match result {
            Ok(Some(patt)) => Some(patt),
            Ok(None) | Err(_) => {
                stream.rollback(state);
                None
            }
        }
    }
}

pub trait ParseFromWithContextAndRollback<SP>: TryParseOptionFromStreamWithContext<SP>
where
    SP: IsStreamParser + ?Sized,
{
    type Error;

    fn parse_from_with_rollback_when_no_error<'a>(
        stream: &mut SP,
        ctx: Self::Context,
    ) -> Result<Option<Self>, <Self as ParseFromWithContextAndRollback<SP>>::Error>;

    fn try_parse_from_with_rollback<'a>(stream: &mut SP, ctx: Self::Context) -> Option<Self>;
}

impl<SP, P> ParseFromWithContextAndRollback<SP> for P
where
    SP: IsStreamParser + ?Sized,
    P: TryParseOptionFromStreamWithContext<SP>,
{
    type Error = <P as TryParseOptionFromStreamWithContext<SP>>::Error;
    fn parse_from_with_rollback_when_no_error<'a>(
        stream: &mut SP,
        ctx: Self::Context,
    ) -> Result<Option<Self>, <P as TryParseOptionFromStreamWithContext<SP>>::Error> {
        let state = stream.state();
        let result = Self::try_parse_option_from_stream_without_guaranteed_rollback(stream, ctx);
        match result {
            // rollback for no pattern
            Ok(None) => stream.rollback(state),
            _ => (),
        }
        result
    }

    fn try_parse_from_with_rollback<'a>(stream: &mut SP, ctx: Self::Context) -> Option<Self> {
        let state = stream.state();
        let result = Self::try_parse_option_from_stream_without_guaranteed_rollback(stream, ctx);
        match result {
            Ok(Some(patt)) => Some(patt),
            Ok(None) | Err(_) => {
                stream.rollback(state);
                None
            }
        }
    }
}
