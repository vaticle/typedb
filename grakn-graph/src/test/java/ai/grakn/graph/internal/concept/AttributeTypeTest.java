/*
 * Grakn - A Distributed Semantic Database
 * Copyright (C) 2016  Grakn Labs Limited
 *
 * Grakn is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Grakn is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Grakn. If not, see <http://www.gnu.org/licenses/gpl.txt>.
 */

package ai.grakn.graph.internal.concept;

import ai.grakn.Grakn;
import ai.grakn.GraknTx;
import ai.grakn.GraknSession;
import ai.grakn.GraknTxType;
import ai.grakn.concept.Attribute;
import ai.grakn.concept.AttributeType;
import ai.grakn.exception.GraphOperationException;
import ai.grakn.graph.internal.GraphTestBase;
import org.hamcrest.CoreMatchers;
import org.junit.Before;
import org.junit.Test;

import java.time.LocalDateTime;
import java.util.TimeZone;
import java.util.regex.PatternSyntaxException;

import static junit.framework.TestCase.assertNull;
import static org.hamcrest.CoreMatchers.containsString;
import static org.junit.Assert.assertEquals;

public class AttributeTypeTest extends GraphTestBase {
    private AttributeType<String> attributeType;


    @Before
    public void buildGraph() {
        attributeType = graknGraph.putResourceType("Attribute Type", AttributeType.DataType.STRING);
    }

    @Test
    public void whenCreatingResourceTypeOfTypeString_DataTypeIsString() throws Exception {
        assertEquals(AttributeType.DataType.STRING, attributeType.getDataType());
    }

    @Test
    public void whenCreatingStringResourceTypeWithValidRegex_EnsureNoErrorsThrown(){
        assertNull(attributeType.getRegex());
        attributeType.setRegex("[abc]");
        assertEquals(attributeType.getRegex(), "[abc]");
    }

    @Test
    public void whenCreatingStringResourceTypeWithInvalidRegex_Throw(){
        assertNull(attributeType.getRegex());
        expectedException.expect(PatternSyntaxException.class);
        attributeType.setRegex("[");
    }

    @Test
    public void whenSettingRegexOnNonStringResourceType_Throw(){
        AttributeType<Long> thing = graknGraph.putResourceType("Random ID", AttributeType.DataType.LONG);
        expectedException.expect(GraphOperationException.class);
        expectedException.expectMessage(GraphOperationException.cannotSetRegex(thing).getMessage());
        thing.setRegex("blab");
    }

    @Test
    public void whenAddingResourceWhichDoesNotMatchRegex_Throw(){
        attributeType.setRegex("[abc]");
        attributeType.putResource("a");
        expectedException.expect(GraphOperationException.class);
        expectedException.expectMessage(CoreMatchers.allOf(containsString("[abc]"), containsString("1"), containsString(attributeType.getLabel().getValue())));
        attributeType.putResource("1");
    }

    @Test
    public void whenSettingRegexOnResourceTypeWithResourceNotMatchingRegex_Throw(){
        attributeType.putResource("1");
        expectedException.expect(GraphOperationException.class);
        expectedException.expectMessage(GraphOperationException.regexFailure(attributeType, "1", "[abc]").getMessage());
        attributeType.setRegex("[abc]");
    }

    @Test
    public void whenGettingTheResourceFromAResourceType_ReturnTheResource(){
        AttributeType<String> t1 = graknGraph.putResourceType("t1", AttributeType.DataType.STRING);
        AttributeType<String> t2 = graknGraph.putResourceType("t2", AttributeType.DataType.STRING);

        Attribute c1 = t1.putResource("1");
        Attribute c2 = t2.putResource("2");

        assertEquals(c1, t1.getResource("1"));
        assertNull(t1.getResource("2"));

        assertEquals(c2, t2.getResource("2"));
        assertNull(t2.getResource("1"));
    }

    @Test
    public void whenCreatingMultipleResourceTypesWithDifferentRegexes_EnsureAllRegexesAreChecked(){
        AttributeType<String> t1 = graknGraph.putResourceType("t1", AttributeType.DataType.STRING).setRegex("[b]");
        AttributeType<String> t2 = graknGraph.putResourceType("t2", AttributeType.DataType.STRING).setRegex("[abc]").sup(t1);

        //Valid Attribute
        Attribute<String> attribute = t2.putResource("b");

        //Invalid Attribute
        expectedException.expect(GraphOperationException.class);
        expectedException.expectMessage(CoreMatchers.allOf(containsString("[b]"), containsString("b"), containsString(attribute.type().getLabel().getValue())));
        t2.putResource("a");
    }

    @Test
    public void whenSettingTheSuperTypeOfAStringResourceType_EnsureAllRegexesAreAppliedToResources(){
        AttributeType<String> t1 = graknGraph.putResourceType("t1", AttributeType.DataType.STRING).setRegex("[b]");
        AttributeType<String> t2 = graknGraph.putResourceType("t2", AttributeType.DataType.STRING).setRegex("[abc]");

        //Future Invalid
        Attribute<String> attribute = t2.putResource("a");

        expectedException.expect(GraphOperationException.class);
        expectedException.expectMessage(GraphOperationException.regexFailure(t2, "a", "[b]").getMessage());
        t2.sup(t1);
    }

    @Test
    public void whenSettingRegexOfSuperType_EnsureAllRegexesAreApplied(){
        AttributeType<String> t1 = graknGraph.putResourceType("t1", AttributeType.DataType.STRING);
        AttributeType<String> t2 = graknGraph.putResourceType("t2", AttributeType.DataType.STRING).setRegex("[abc]").sup(t1);
        Attribute<String> attribute = t2.putResource("a");

        expectedException.expect(GraphOperationException.class);
        expectedException.expectMessage(GraphOperationException.regexFailure(t1, "a", "[b]").getMessage());
        t1.setRegex("[b]");
    }

    @Test
    public void whenCreatingAResourceTypeOfTypeDate_EnsureTheTimeZoneIsSetTOADefaultAndDoesNotAffectRetreival() {

        // offset the time to GMT-8
        TimeZone.setDefault(TimeZone.getTimeZone("GMT-8"));
        // get the local time (without timezone)
        LocalDateTime rightNow = LocalDateTime.now();
        // now add the timezone to the graph
        try (GraknSession session = Grakn.session(Grakn.IN_MEMORY, "somethingmorerandom")) {
            try (GraknTx graph = session.open(GraknTxType.WRITE)) {
                AttributeType<LocalDateTime> aTime = graph.putResourceType("aTime", AttributeType.DataType.DATE);
                aTime.putResource(rightNow);
                graph.commit();
            }
        }

        // offset the time to GMT where the colleague is working
        TimeZone.setDefault(TimeZone.getTimeZone("GMT"));
        // the colleague extracts the LocalTime which should be the same
        try (GraknSession session = Grakn.session(Grakn.IN_MEMORY, "somethingmorerandom")) {
            try (GraknTx graph = session.open(GraknTxType.WRITE)) {
                AttributeType aTime = graph.getResourceType("aTime");
                LocalDateTime databaseTime = (LocalDateTime) ((Attribute) aTime.instances().iterator().next()).getValue();

                // localTime should not have changed as it should not be sensitive to timezone
                assertEquals(rightNow, databaseTime);
            }
        }
    }
}