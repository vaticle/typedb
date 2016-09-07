package io.mindmaps.migration.sql;

import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.Logger;
import io.mindmaps.MindmapsTransaction;
import io.mindmaps.engine.controller.CommitLogController;
import io.mindmaps.engine.controller.GraphFactoryController;
import io.mindmaps.engine.controller.TransactionController;
import io.mindmaps.core.Data;
import io.mindmaps.core.MindmapsGraph;
import io.mindmaps.core.implementation.exception.MindmapsValidationException;
import io.mindmaps.core.model.RelationType;
import io.mindmaps.core.model.ResourceType;
import io.mindmaps.core.model.RoleType;
import io.mindmaps.core.model.Type;
import io.mindmaps.factory.GraphFactory;
import io.mindmaps.engine.loader.BlockingLoader;
import io.mindmaps.engine.util.ConfigProperties;
import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import java.sql.Connection;
import java.sql.SQLException;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class SQLSchemaMigratorTest {

    private static final String GRAPH_NAME = "test";

    private MindmapsGraph graph;
    private MindmapsTransaction transaction;
    private BlockingLoader loader;

    private Namer namer = new Namer() {};
    private static SQLSchemaMigrator migrator;

    @BeforeClass
    public static void start(){
        Logger logger = (Logger) org.slf4j.LoggerFactory.getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME);
        logger.setLevel(Level.INFO);

        System.setProperty(ConfigProperties.CONFIG_FILE_SYSTEM_PROPERTY,ConfigProperties.TEST_CONFIG_FILE);
        System.setProperty(ConfigProperties.CURRENT_DIR_SYSTEM_PROPERTY, System.getProperty("user.dir")+"/../");

        new TransactionController();
        new CommitLogController();
        new GraphFactoryController();

        migrator = new SQLSchemaMigrator();
    }

    @Before
    public void setup() throws MindmapsValidationException {
        graph = GraphFactory.getInstance().getGraphBatchLoading(GRAPH_NAME);
        transaction = graph.getTransaction();
        loader = new BlockingLoader(GRAPH_NAME);
    }

    @After
    public void shutdown() throws SQLException {
        graph.clear();
        graph.close();
        migrator.close();
    }

    @Test
    public void usersTest() throws SQLException {
        Connection connection = Util.setupExample("simple");
        migrator.configure(connection).migrate(loader);

        Type type = transaction.getEntityType("USERS");
        assertNotNull(type);

        assertResourceRelationExists("ID", Data.LONG, type);
        assertResourceRelationExists("NAME", Data.STRING, type);
        assertResourceRelationExists("EMAIL", Data.STRING, type);
    }

    @Test
    public void alterTableTest() throws SQLException {
        Connection connection = Util.setupExample("alter-table");
        migrator.configure(connection).migrate(loader);
        transaction.refresh();

        Type cart = transaction.getEntityType("CART");
        assertNotNull(cart);

        assertResourceRelationExists("ID", Data.LONG, cart);
        assertResourceRelationExists("NAME", Data.STRING, cart);

        Type cartItem = transaction.getEntityType("CART_ITEM");

        assertResourceRelationExists("ITEM_QTY", Data.LONG, cartItem);
        assertResourceRelationExists("LAST_UPDATED", Data.STRING, cartItem);

        Type category = transaction.getEntityType("CATEGORY");
        assertResourceRelationExists("ID", Data.LONG, category);
        assertResourceRelationExists("DESCRIPTION", Data.STRING, category);
        assertResourceRelationExists("NAME", Data.STRING, category);

        Type customer = transaction.getEntityType("CUSTOMER");
        assertResourceRelationExists("ID", Data.LONG, customer);
        assertResourceRelationExists("NAME", Data.STRING, customer);
        assertResourceRelationExists("PASSWORD", Data.STRING, customer);
        assertResourceRelationExists("LAST_UPDATED", Data.STRING, customer);
        assertResourceRelationExists("REGISTRATION_DATE", Data.STRING, customer);

        Type product = transaction.getEntityType("PRODUCT");

        assertRelationExists(cart, customer, "CUSTOMER_ID");
        assertRelationExists(cartItem, cart, "CART_ID");
        assertRelationExists(cartItem, product, "PRODUCT_ID");
        assertRelationExists(product, category, "CATEGORY_ID");
    }

    @Test
    public void emptyTest() throws SQLException {
        Connection connection = Util.setupExample("empty");
        migrator.configure(connection).migrate(loader);
        transaction.refresh();

        System.out.println(transaction.getMetaType().instances());
        assertTrue(transaction.getMetaType().instances().size() == 8);
        assertTrue(transaction.getMetaEntityType().instances().size() == 0);
        assertTrue(transaction.getMetaRelationType().instances().size() == 0);
        assertTrue(transaction.getMetaResourceType().instances().size() == 0);
        assertTrue(transaction.getMetaRoleType().instances().size() == 0);
        assertTrue(transaction.getMetaRuleType().instances().size() == 2);
    }

    @Test
    public void datavaultSchemaTest() throws SQLException {
        Connection connection = Util.setupExample("datavault");
        migrator.configure(connection).migrate(loader);
        transaction.refresh();

        Type entity = transaction.getEntityType("AZ_BAKUAPPEALCOURT_CASES");
        assertNotNull(entity);
        assertResourceRelationExists("ID", Data.LONG, entity);
        assertResourceRelationExists("DATE", Data.STRING, entity);
        assertResourceRelationExists("CASE_ID", Data.STRING, entity);
        assertResourceRelationExists("DETAILS", Data.STRING, entity);
        assertResourceRelationExists("SOURCE_URL", Data.STRING, entity);
    }

    @Test
    public void postgresSchemaTest() throws SQLException, ClassNotFoundException {
        Connection connection = Util.setupExample("postgresql-example");
        migrator.configure(connection).migrate(loader);
        transaction.refresh();

        Type city = transaction.getEntityType("CITY");
        assertNotNull(city);

        assertResourceRelationExists("ID", Data.LONG, city);
        assertResourceRelationExists("NAME", Data.STRING, city);
        assertResourceRelationExists("COUNTRYCODE", Data.STRING, city);
        assertResourceRelationExists("DISTRICT", Data.STRING, city);
        assertResourceRelationExists("POPULATION", Data.LONG, city);

        Type country = transaction.getEntityType("COUNTRY");
        assertNotNull(country);

        Type language = transaction.getEntityType("COUNTRYLANGUAGE");
        assertNotNull(language);

        assertRelationExists(country, city, "CAPITAL");
        assertRelationExists(language, country, "COUNTRYCODE");

        RoleType countryCodeChild = transaction.getRoleType("COUNTRYCODE-child");
        assertTrue(country.playsRoles().contains(countryCodeChild));
    }

    @Test
    public void mysqlSchemaTest() throws SQLException {
        Connection connection = Util.setupExample("mysql-example");
        migrator.configure(connection).migrate(loader);
        transaction.refresh();

        System.out.println(transaction.getMetaEntityType().instances());
        Type pet = transaction.getEntityType("PET");
        Type event = transaction.getEntityType("EVENT");
        assertNotNull(pet);
        assertNotNull(event);

        assertResourceRelationExists("NAME", Data.STRING, pet);
        assertResourceRelationExists("OWNER", Data.STRING, pet);
        assertResourceRelationExists("SPECIES", Data.STRING, pet);
        assertResourceRelationExists("SEX", Data.STRING, pet);
        assertResourceRelationExists("BIRTH", Data.STRING, pet);
        assertResourceRelationExists("DEATH", Data.STRING, pet);

        assertResourceRelationExists("NAME", Data.STRING, event);
        assertResourceRelationExists("DATE", Data.STRING, event);
        assertResourceRelationExists("EVENTTYPE", Data.STRING, event);
        assertResourceRelationExists("REMARK", Data.STRING, event);
    }

    @Test
    public void combinedKeyTest() throws SQLException {
        Connection connection = Util.setupExample("combined-key");
        migrator.configure(connection).migrate(loader);
        transaction.refresh();

        Type type = transaction.getEntityType("USERS");
        assertNotNull(type);

        assertResourceRelationExists("FIRSTNAME", Data.STRING, type);
        assertResourceRelationExists("LASTNAME", Data.STRING, type);
        assertResourceRelationExists("EMAIL", Data.STRING, type);
    }

    private ResourceType assertResourceExists(String name, Data datatype) {
        ResourceType resourceType = transaction.getResourceType(name);
        assertNotNull(resourceType);
        assertEquals(datatype.getName(), resourceType.getDataType().getName());
        return resourceType;
    }

    private void assertResourceRelationExists(String name, Data datatype, Type owner){
        String resourceName = namer.resourceName(owner.getId(), name);
        ResourceType resource = assertResourceExists(resourceName, datatype);

        RelationType relationType = transaction.getRelationType("has-" + resourceName);
        RoleType roleOwner = transaction.getRoleType("has-" + resourceName + "-owner");
        RoleType roleOther = transaction.getRoleType("has-" + resourceName + "-value");

        assertNotNull(relationType);
        assertNotNull(roleOwner);
        assertNotNull(roleOther);

        assertEquals(relationType, roleOwner.relationType());
        assertEquals(relationType, roleOther.relationType());

        assertTrue(owner.playsRoles().contains(roleOwner));
        assertTrue(resource.playsRoles().contains(roleOther));
    }

    private void assertRelationExists(Type owner, Type other, String relation) {

        RelationType relationType = transaction.getRelationType(relation + "-relation");
        RoleType roleOwner = transaction.getRoleType(relation + "-parent");
        RoleType roleOther = transaction.getRoleType(relation + "-child");

        assertNotNull(relationType);
        assertNotNull(roleOwner);
        assertNotNull(roleOther);

        assertEquals(relationType, roleOwner.relationType());
        assertEquals(relationType, roleOther.relationType());

        assertTrue(owner.playsRoles().contains(roleOwner));
        assertTrue(other.playsRoles().contains(roleOther));
    }
}
