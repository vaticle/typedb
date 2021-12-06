/*
 * Copyright (C) 2021 Vaticle
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *
 */

package com.vaticle.typedb.core.reasoner.reactive;

import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.logic.resolvable.Resolvable;

import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

public interface Reactive<INPUT, OUTPUT> extends Publisher<OUTPUT>, Subscriber<INPUT> {

    Reactive<INPUT, INPUT> findFirstSubscribe();

    <UPS_INPUT> Reactive<UPS_INPUT, INPUT> mapSubscribe(Function<UPS_INPUT, INPUT> function);

    <UPS_INPUT> Reactive<UPS_INPUT, INPUT> flatMapOrRetrySubscribe(Function<UPS_INPUT, FunctionalIterator<INPUT>> function);

}
