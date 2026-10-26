PREFIX ex: <http://ex.org/>
# COPY, ADD and MOVE between named graphs and the default graph; the later operations read the earlier results
COPY ex:g1 TO ex:g4 ;
ADD ex:g2 TO ex:g4 ;
MOVE ex:g4 TO ex:g5 ;
ADD DEFAULT TO ex:g6 ;
COPY DEFAULT TO ex:g7 ;
MOVE ex:g7 TO ex:g8
