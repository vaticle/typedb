/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::fmt;

use storage::durability_client::WALClient;

pub enum ActiveTransaction {
    Read(database::transaction::TransactionRead<WALClient>),
    Write(database::transaction::TransactionWrite<WALClient>),
    Schema(database::transaction::TransactionSchema<WALClient>),
}

impl fmt::Debug for ActiveTransaction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ActiveTransaction::Read(_) => "Read",
            ActiveTransaction::Write(_) => "Write",
            ActiveTransaction::Schema(_) => "Schema",
        })
    }
}

macro_rules! with_read_tx {
    ($context:ident, |$tx:ident| $expr:expr) => {
        match $context.active_transaction.as_ref().unwrap() {
            $crate::transaction_context::ActiveTransaction::Read($tx) => $expr, // TODO: Add more panics here?
            $crate::transaction_context::ActiveTransaction::Write($tx) => $expr,
            $crate::transaction_context::ActiveTransaction::Schema($tx) => $expr,
        }
    };
}
pub(crate) use with_read_tx;

macro_rules! with_write_tx {
    ($context:ident, |$tx:ident| $expr:expr) => {
        match $context.active_transaction.as_mut().unwrap() {
            $crate::transaction_context::ActiveTransaction::Read(_) => panic!("Using Read transaction as Write"),
            $crate::transaction_context::ActiveTransaction::Write($tx) => $expr,
            $crate::transaction_context::ActiveTransaction::Schema($tx) => $expr,
        }
    };
}
pub(crate) use with_write_tx;

macro_rules! with_schema_tx {
    ($context:ident, |$tx:ident| $expr:expr) => {
        match $context.active_transaction.as_mut().unwrap() {
            $crate::transaction_context::ActiveTransaction::Read(_) => panic!("Using Read transaction as Schema"),
            $crate::transaction_context::ActiveTransaction::Write(_) => panic!("Using Write transaction as Schema"),
            $crate::transaction_context::ActiveTransaction::Schema($tx) => $expr,
        }
    };
}
pub(crate) use with_schema_tx;
