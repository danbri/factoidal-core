// Apache Jena side of the cross-backend SPARQL differential gate
// (tests/stack/backend_diff.sh). One JVM answers every case, so the gate does
// not pay a JVM start per test.
//
// Input on stdin, one case per line, tab separated:
//   CASE-ID  DATA-NQ  QUERY-FILE  OUT-DIR
// For each case it writes OUT-DIR/jena-tdb2.json and OUT-DIR/jena-mem.json:
// SPARQL 1.1 Query Results JSON for SELECT and ASK, or {"error": "..."}.
//
//   jena-tdb2: a fresh TDB2 database (DatabaseMgr.connectDatasetGraph on a new
//              directory), loaded inside a write transaction, queried inside
//              a read transaction. Storage, node table and value inlining are
//              TDB2's own.
//   jena-mem:  the transactional in-memory dataset (ARQ reference engine).
//
// The data file is N-Quads written by the Lean engine, so Jena, the Lean
// reference evaluator and the Lean store all read the same bytes.
// The query is read with QueryFactory.read, so its base IRI is the query
// file's own URL, as the Lean CLI does with `--query FILE`.
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.Comparator;
import org.apache.jena.query.*;
import org.apache.jena.riot.*;
import org.apache.jena.sparql.core.DatasetGraph;
import org.apache.jena.sparql.core.DatasetGraphFactory;
import org.apache.jena.system.Txn;
import org.apache.jena.tdb2.DatabaseMgr;
import org.apache.jena.dboe.base.file.Location;

public class JenaRunner {
    static void write(Path out, String text) throws IOException {
        Files.writeString(out, text, StandardCharsets.UTF_8);
    }

    static String jsonString(String s) {
        StringBuilder b = new StringBuilder("\"");
        for (char c : s.toCharArray()) {
            if (c == '"' || c == '\\') b.append('\\').append(c);
            else if (c < 0x20) b.append(String.format("\\u%04x", (int) c));
            else b.append(c);
        }
        return b.append('"').toString();
    }

    static String answer(DatasetGraph dsg, String queryFile) {
        try {
            Query q = QueryFactory.read(queryFile, Syntax.syntaxSPARQL_11);
            try (QueryExecution qe = QueryExecutionFactory.create(q, DatasetFactory.wrap(dsg))) {
                ByteArrayOutputStream bytes = new ByteArrayOutputStream();
                if (q.isSelectType()) {
                    ResultSetFormatter.outputAsJSON(bytes, qe.execSelect());
                } else if (q.isAskType()) {
                    ResultSetFormatter.outputAsJSON(bytes, qe.execAsk());
                } else {
                    return "{\"error\":\"not SELECT or ASK\"}";
                }
                return bytes.toString(StandardCharsets.UTF_8);
            }
        } catch (Throwable t) {
            return "{\"error\":" + jsonString(t.getClass().getSimpleName() + ": " + t.getMessage()) + "}";
        }
    }

    static void deleteTree(Path p) throws IOException {
        if (!Files.exists(p)) return;
        try (var walk = Files.walk(p)) {
            walk.sorted(Comparator.reverseOrder()).forEach(f -> f.toFile().delete());
        }
    }

    public static void main(String[] args) throws Exception {
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
        String line;
        while ((line = in.readLine()) != null) {
            String[] f = line.split("\t");
            if (f.length < 4) continue;
            String data = f[1], query = f[2];
            Path outDir = Paths.get(f[3]);
            // In-memory reference.
            String mem;
            try {
                DatasetGraph m = DatasetGraphFactory.createTxnMem();
                Txn.executeWrite(m, () -> RDFDataMgr.read(m, data, Lang.NQUADS));
                mem = Txn.calculateRead(m, () -> answer(m, query));
            } catch (Throwable t) {
                mem = "{\"error\":" + jsonString("load: " + t.getMessage()) + "}";
            }
            write(outDir.resolve("jena-mem.json"), mem);
            // TDB2 on disk.
            Path loc = outDir.resolve("tdb2");
            deleteTree(loc);
            String tdb;
            try {
                DatasetGraph t = DatabaseMgr.connectDatasetGraph(Location.create(loc.toString()));
                Txn.executeWrite(t, () -> RDFDataMgr.read(t, data, Lang.NQUADS));
                tdb = Txn.calculateRead(t, () -> answer(t, query));
                org.apache.jena.tdb2.sys.TDBInternal.expel(t);
            } catch (Throwable e) {
                tdb = "{\"error\":" + jsonString("load: " + e.getMessage()) + "}";
            }
            write(outDir.resolve("jena-tdb2.json"), tdb);
            deleteTree(loc);
            System.out.println("done\t" + f[0]);
            System.out.flush();
        }
    }
}
