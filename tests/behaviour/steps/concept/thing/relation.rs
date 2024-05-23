/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::slice;

use concept::{
    thing::object::{Object, ObjectAPI},
    type_::TypeAPI,
};
use cucumber::gherkin::Step;
use itertools::Itertools;
use macro_rules_attribute::apply;

use crate::{
    generic_step, params,
    transaction_context::{with_read_tx, with_write_tx},
    Context,
};

#[apply(generic_step)]
#[step(expr = r"relation {var} add player for role\({type_label}\): {var}")]
async fn relation_add_player_for_role(
    context: &mut Context,
    relation_var: params::Var,
    role_label: params::Label,
    player_var: params::Var,
) {
    let relation = context.objects.get(&relation_var.name).unwrap().as_ref().unwrap().object.clone().unwrap_relation();
    let player = context.objects.get(&player_var.name).unwrap().as_ref().unwrap().object.clone();
    with_write_tx!(context, |tx| {
        let role_type = relation
            .type_()
            .get_relates_role(&tx.snapshot, &tx.type_manager, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        relation.add_player(&mut tx.snapshot, &tx.thing_manager, role_type, player).unwrap();
    });
}

#[apply(generic_step)]
#[step(expr = r"relation {var} get players {contains_or_doesnt}: {var}")]
async fn relation_get_players_contains(
    context: &mut Context,
    relation_var: params::Var,
    contains_or_doesnt: params::ContainsOrDoesnt,
    player_var: params::Var,
) {
    let relation = context.objects.get(&relation_var.name).unwrap().as_ref().unwrap().object.clone().unwrap_relation();
    let players = with_read_tx!(context, |tx| {
        relation
            .get_players(&tx.snapshot, &tx.thing_manager)
            .collect_cloned_vec(|(rp, _count)| rp.player().into_owned())
            .unwrap()
    });
    let player = &context.objects.get(&player_var.name).unwrap().as_ref().unwrap().object;
    contains_or_doesnt.check(slice::from_ref(player), &players);
}

#[apply(generic_step)]
#[step(expr = r"relation {var} get players {contains_or_doesnt}:")]
async fn relation_get_players_contains_table(
    context: &mut Context,
    step: &Step,
    relation_var: params::Var,
    contains_or_doesnt: params::ContainsOrDoesnt,
) {
    let relation = context.objects.get(&relation_var.name).unwrap().as_ref().unwrap().object.clone().unwrap_relation();
    let players = with_read_tx!(context, |tx| {
        relation
            .get_players(&tx.snapshot, &tx.thing_manager)
            .collect_cloned_vec(|(rp, _count)| {
                (
                    rp.role_type().get_label(&tx.snapshot, &tx.type_manager).unwrap().name().as_str().to_owned(),
                    rp.player().into_owned(),
                )
            })
            .unwrap()
    });
    let expected = step
        .table()
        .unwrap()
        .rows
        .iter()
        .map(|row| {
            let [role_label, var_name] = &row[..] else {
                panic!("Expected exactly two columns: role type and variable name, received: {row:?}")
            };
            (role_label.to_owned(), context.objects.get(var_name.as_str()).unwrap().as_ref().unwrap().object.clone())
        })
        .collect_vec();
    contains_or_doesnt.check(&expected, &players);
}

/*
#[apply(generic_step)]
#[step(expr = r"relation {var} get players for role\({type_label}\) {contains_or_doesnt}: {var}")]
async fn relation_get_players_for_role_contains(
    context: &mut Context,
    relation_var: params::Var,
    role_label: params::Label,
    contains_or_doesnt: params::ContainsOrDoesnt,
    player_var: params::Var,
) {
    let relation = context.objects.get(&relation_var.name).unwrap().as_ref().unwrap().object.clone().unwrap_relation();
    let players = with_read_tx!(context, |tx| {
        let role_type = relation
            .type_()
            .get_relates_role(&tx.snapshot, &tx.type_manager, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        relation
            .get_players_role_type(&tx.snapshot, &tx.thing_manager, role_type)
            .collect_cloned_vec(|r| r.into_owned())
            .unwrap()
    });
    let player = &context.objects.get(&player_var.name).unwrap().as_ref().unwrap().object;
    contains_or_doesnt.check(slice::from_ref(player), &players);
}

#[apply(generic_step)]
#[step(expr = r"{object_root_label} {var} get relations {contains_or_doesnt}: {var}")]
async fn object_get_relations_contain(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    player_var: params::Var,
    contains_or_doesnt: params::ContainsOrDoesnt,
    relation_var: params::Var,
) {
    let player = &context.objects.get(&player_var.name).unwrap().as_ref().unwrap().object;
    object_root.assert(&player.type_());
    let relations = with_read_tx!(context, |tx| {
        player
            .get_relations(&tx.snapshot, &tx.thing_manager)
            .unwrap()
            .collect_cloned_vec(|(rel, _, _)| rel.into_owned())
            .unwrap()
    });
    let Object::Relation(relation) = &context.objects.get(&relation_var.name).unwrap().as_ref().unwrap().object else {
        panic!()
    };
    contains_or_doesnt.check(slice::from_ref(relation), &relations);
}

#[apply(generic_step)]
#[step(
    expr = r"{object_root_label} {var} get relations\({type_label}\) with role\({type_label}\) {contains_or_doesnt}: {var}"
)]
async fn object_get_relations_of_type_with_role_contain(
    context: &mut Context,
    object_root: params::ObjectRootLabel,
    player_var: params::Var,
    relation_type_label: params::Label,
    role_label: params::Label,
    contains_or_doesnt: params::ContainsOrDoesnt,
    relation_var: params::Var,
) {
    let player = &context.objects.get(&player_var.name).unwrap().as_ref().unwrap().object;
    object_root.assert(&player.type_());
    let relations = with_read_tx!(context, |tx| {
        let relation_type =
            tx.type_manager.get_relation_type(&tx.snapshot, &relation_type_label.to_typedb()).unwrap().unwrap();
        let role_type = relation_type
            .get_relates_role(&tx.snapshot, &tx.type_manager, role_label.to_typedb().name().as_str())
            .unwrap()
            .unwrap()
            .role();
        player
            .get_relations_role_type(&tx.snapshot, &tx.thing_manager, role_type)
            .unwrap()
            .collect_cloned_vec(|rel| rel)
            .unwrap()
    });
    let Object::Relation(relation) = &context.objects.get(&relation_var.name).unwrap().as_ref().unwrap().object else {
        panic!()
    };
    contains_or_doesnt.check(slice::from_ref(relation), &relations);
}
*/
