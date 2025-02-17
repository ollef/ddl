// This file is automatically @generated by ddl 0.1.0
// It is not intended for manual editing.

pub struct Pair {
    pub first: ddl_rt::InvalidDataDescription,
    pub second: ddl_rt::InvalidDataDescription,
}

impl ddl_rt::Binary for Pair {
    type Host = Pair;
}

impl<'data> ddl_rt::ReadBinary<'data> for Pair {
    fn read(ctxt: &mut ddl_rt::ReadCtxt<'data>) -> Result<Pair, ddl_rt::ReadError> {
        let first = ctxt.read::<ddl_rt::InvalidDataDescription>()?;
        let second = ctxt.read::<ddl_rt::InvalidDataDescription>()?;

        Ok(Pair {
            first,
            second,
        })
    }
}
