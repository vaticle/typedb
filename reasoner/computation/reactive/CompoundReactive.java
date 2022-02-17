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

package com.vaticle.typedb.core.reasoner.computation.reactive;


import com.vaticle.typedb.core.reasoner.computation.actor.Processor.Monitoring;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;

public class CompoundReactive<PLAN_ID, PACKET> extends AbstractUnaryReactiveStream<PACKET, PACKET> {

    private final Publisher<PACKET> leadingPublisher;
    private final List<PLAN_ID> remainingPlan;
    private final BiFunction<PACKET, PACKET, PACKET> compoundPacketsFunc;
    private final BiFunction<PLAN_ID, PACKET, Publisher<PACKET>> spawnLeaderFunc;
    private final Map<Provider<PACKET>, PACKET> publisherPackets;
    private final PACKET initialPacket;
    private final MultiProviderRegistry<PACKET> providerManager;

    public CompoundReactive(List<PLAN_ID> plan, BiFunction<PLAN_ID, PACKET, Publisher<PACKET>> spawnLeaderFunc,
                            BiFunction<PACKET, PACKET, PACKET> compoundPacketsFunc, PACKET initialPacket,
                            Monitoring monitor, String groupName) {
        super(monitor, groupName);
        assert plan.size() > 0;
        this.providerManager = new MultiProviderRegistry<>(this, null);
        this.initialPacket = initialPacket;
        this.remainingPlan = new ArrayList<>(plan);
        this.leadingPublisher = spawnLeaderFunc.apply(this.remainingPlan.remove(0), initialPacket);
        this.compoundPacketsFunc = compoundPacketsFunc;
        this.spawnLeaderFunc = spawnLeaderFunc;
        this.publisherPackets = new HashMap<>();
        this.leadingPublisher.publishTo(this);
    }

    @Override
    protected ProviderRegistry<PACKET> providerRegistry() {
        return providerManager;
    }

    @Override
    public void receive(Provider<PACKET> provider, PACKET packet) {
        super.receive(provider, packet);
        PACKET mergedPacket = compoundPacketsFunc.apply(initialPacket, packet);
        if (leadingPublisher.equals(provider)) {
            if (remainingPlan.size() == 0) {  // For a single item plan
                receiverRegistry().finishPulling();
                receiverRegistry().receiver().receive(this, mergedPacket);
            } else {
                Publisher<PACKET> follower;
                if (remainingPlan.size() == 1) {
                    follower = spawnLeaderFunc.apply(remainingPlan.get(0), mergedPacket);
                } else {
                    follower = new CompoundReactive<>(remainingPlan, spawnLeaderFunc, compoundPacketsFunc, mergedPacket, monitor(), groupName()).buffer();
                }
                publisherPackets.put(follower, mergedPacket);
                monitor().onPathFork(1, this);
                monitor().onAnswerDestroy(this);
                follower.publishTo(this);
                providerRegistry().pull(leadingPublisher);  // Pull again on the leader in case the follower never produces an answer
                providerRegistry().pull(follower);
            }
        } else {
            receiverRegistry().finishPulling();
            PACKET compoundedPacket = compoundPacketsFunc.apply(mergedPacket, publisherPackets.get(provider));
            receiverRegistry().receiver().receive(this, compoundedPacket);
        }
    }
}
