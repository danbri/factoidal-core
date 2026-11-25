package io.github.andreawesterinen.wikidata.rewriter;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import org.apache.jena.atlas.json.JSON;
import org.apache.jena.atlas.json.JsonObject;
import org.apache.jena.query.QueryFactory;
import org.apache.jena.query.Syntax;

/** Parse one SPARQL 1.1 query per JSONL {id, query} record, then serialise it. */
public final class NormalizeJena {
    public static void main(String[] args) throws Exception {
        try (BufferedReader input = new BufferedReader(
                new InputStreamReader(System.in, StandardCharsets.UTF_8))) {
            String line;
            while ((line = input.readLine()) != null) {
                JsonObject request = JSON.parse(line);
                JsonObject answer = new JsonObject();
                answer.put("id", request.get("id"));
                try {
                    String text = request.get("query").getAsString().value();
                    // An explicit opt-in supports the same defaults as the original WDQS input.
                    if (request.hasKey("wdqs_defaults")) {
                        text = WdqsPrefixes.addMissingUsed(text);
                    }
                    var query = QueryFactory.create(text, Syntax.syntaxSPARQL_11);
                    query.getPrefixMapping().clearNsPrefixMap();
                    answer.put("text", query.serialize(Syntax.syntaxSPARQL_11));
                } catch (RuntimeException error) {
                    answer.put("error", String.valueOf(error.getMessage()));
                }
                System.out.println(answer.toString().replace("\r", "").replace("\n", ""));
            }
        }
    }
}
