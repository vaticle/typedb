package ai.grakn.engine.controller;

import ai.grakn.engine.GraknEngineTestBase;
import ai.grakn.engine.user.UsersHandler;
import ai.grakn.engine.util.JWTHandler;

import com.jayway.restassured.response.Response;
import mjson.Json;
import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.Field;

import static com.jayway.restassured.RestAssured.given;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class AuthControllerTest extends GraknEngineTestBase {

    @Test
    public void newSessionWithNonExistingUser() {
        Json body = Json.object("username", "navarro", "password", "ciaone");

        Response dataResponse = given().
                contentType("application/json").
                body(body.toString()).when().
                post("/auth/session/");

        dataResponse.then().assertThat().statusCode(401);
    }

    @Test
    public void newSessionWithWrongPassword() {
        UsersHandler.getInstance().addUser(Json.object(UsersHandler.USER_NAME, "marco", 
        											   UsersHandler.USER_PASSWORD, "ciao", 
        											   UsersHandler.USER_IS_ADMIN, true));

        Json body = Json.object("username", "marco", "password", "hello");

        Response dataResponse = given().
                contentType("application/json").
                body(body.toString()).when().
                post("/auth/session/");
        dataResponse.then().assertThat().statusCode(401);
    }

    @Test
    public void newSessionWithWrongUsername() {
        UsersHandler.getInstance().addUser(Json.object(UsersHandler.USER_NAME, "marco", 
				   UsersHandler.USER_PASSWORD, "ciao", 
				   UsersHandler.USER_IS_ADMIN, true));

        Json body = Json.object("username", "genoveffo", "password", "ciao");

        Response dataResponse = given().
                contentType("application/json").
                body(body.toString()).when().
                post("/auth/session/");
        dataResponse.then().assertThat().statusCode(401);
    }

    @Test
    public void newSessionWithExistingUser() {
        //Add a user
        UsersHandler.getInstance().addUser(Json.object(UsersHandler.USER_NAME, "giulio", 
				   UsersHandler.USER_PASSWORD, "ciao", 
				   UsersHandler.USER_IS_ADMIN, true));

        Json body = Json.object("username", "giulio", "password", "ciao");

        //Ask for a new Token
        Response dataResponse = given().
                        contentType("application/json").
                        body(body.toString()).when().
                        post("/auth/session/");

        dataResponse.then().assertThat().statusCode(200);
        String token = dataResponse.asString();
        assertTrue(JWTHandler.verifyJWT(token));
        assertEquals("giulio", JWTHandler.extractUserFromJWT(dataResponse.asString()));

        //Try to execute query WRONG token in request
        Response dataResponseNonAuthenticated = given().
                header("Authorization", "Bearer aaaaaaaaaa.bbbbbbbbbbb.cccccccccccc").
                contentType("application/json").
                body(body.toString()).when().
                get("/graph/ontology");
        dataResponseNonAuthenticated.then().assertThat().statusCode(401);

        //Try to execute query with token in request
        Response dataResponseAuthenticated = given().
                header("Authorization", "Bearer " + token).
                contentType("application/json").
                body(body.toString()).when().
                get("/graph/ontology");
        dataResponseAuthenticated.then().assertThat().statusCode(200);

    }

    @Test
    public void requestWithoutToken(){
        //find a way to change password.protected config in config file

        Json body = Json.object("username", "giulio", "password", "ciao");


        //Try to execute query without token in request, malformed request
        Response dataResponseMalformed = given().
                contentType("application/json").
                body(body.toString()).when().
                get("/graph/ontology");
        dataResponseMalformed.then().assertThat().statusCode(400);
    }

}