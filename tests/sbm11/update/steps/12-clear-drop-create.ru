PREFIX ex: <http://ex.org/>
# CLEAR and DROP of one graph, the SILENT forms on a graph that does not exist, CREATE of a new graph,
# CREATE SILENT of a graph that exists, LOAD SILENT
CLEAR GRAPH ex:g6 ;
DROP GRAPH ex:g5 ;
CLEAR SILENT GRAPH ex:nonexistent ;
DROP SILENT GRAPH ex:nonexistent ;
CREATE SILENT GRAPH ex:g1 ;
CREATE GRAPH ex:g9 ;
LOAD SILENT <http://ex.org/doc>
