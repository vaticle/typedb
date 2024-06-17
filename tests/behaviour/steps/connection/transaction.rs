/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use database::transaction::{TransactionRead, TransactionSchema, TransactionWrite};
use macro_rules_attribute::apply;

use crate::{
    assert::assert_matches,
    generic_step,
    params::{check_boolean, Boolean, MayError},
    ActiveTransaction, Context,
};

#[apply(generic_step)]
#[step(expr = "connection open {word} transaction for database: {word}")]
pub async fn connection_open_transaction(context: &mut Context, tx_type: String, db_name: String) {
    let db = context.databases().get(&db_name).unwrap();
    let tx = match tx_type.as_str() {
        "read" => ActiveTransaction::Read(TransactionRead::open(db.clone())),
        "write" => ActiveTransaction::Write(TransactionWrite::open(db.clone())),
        "schema" => ActiveTransaction::Schema(TransactionSchema::open(db.clone())),
        _ => unreachable!("Unrecognised transaction type"),
    };
    context.set_transaction(tx);
}

#[apply(generic_step)]
#[step(expr = "transaction is open: {boolean}")]
pub async fn transaction_is_open(context: &mut Context, is_open: Boolean) {
    check_boolean!(is_open, context.transaction().is_some());
}

#[apply(generic_step)]
#[step(expr = "transaction has type: {word}")]
pub async fn transaction_has_type(context: &mut Context, tx_type: String) {
    match tx_type.as_str() {
        "read" => assert_matches!(context.transaction().unwrap(), ActiveTransaction::Read(_)),
        "write" => assert_matches!(context.transaction().unwrap(), ActiveTransaction::Write(_)),
        "schema" => assert_matches!(context.transaction().unwrap(), ActiveTransaction::Schema(_)),
        _ => unreachable!("Unrecognised transaction type"),
    };
}

#[apply(generic_step)]
#[step(expr = "transaction commits{may_error}")]
pub async fn transaction_commits(context: &mut Context, may_error: MayError) {
    match context.take_transaction().unwrap() {
        ActiveTransaction::Read(_) => {}
        ActiveTransaction::Write(tx) => may_error.check(&tx.commit()),
        ActiveTransaction::Schema(tx) => may_error.check(&tx.commit()),
    }
}

#[apply(generic_step)]
#[step(expr = "transaction closes")]
pub async fn transaction_closes(context: &mut Context) {
    match context.take_transaction().unwrap() {
        ActiveTransaction::Read(tx) => tx.close(),
        ActiveTransaction::Write(tx) => tx.close(),
        ActiveTransaction::Schema(tx) => tx.close(),
    }
}

#[apply(generic_step)]
#[step(expr = "open transactions in parallel of type:")]
pub async fn open_transactions_in_parallel(context: &mut Context) {
    todo!()
}

#[apply(generic_step)]
#[step(expr = "transactions in parallel are null: {boolean}")]
pub async fn transations_in_parallel_are_null(context: &mut Context, are_null: Boolean) {
    todo!()
}

#[apply(generic_step)]
#[step(expr = "transactions in parallel are open: {boolean}")]
pub async fn transactions_in_parallel_are_open(context: &mut Context, are_open: Boolean) {
    todo!()
}

#[apply(generic_step)]
#[step(expr = "transactions in parallel have type:")]
pub async fn transactions_in_parallel_have_type(context: &mut Context) {
    todo!()
}
