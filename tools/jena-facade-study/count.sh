#!/bin/bash
# usage: count.sh <jena root> <module>
J=$1; m=$2
main=$(find $J/$m -path '*/src/main/java/*' -name '*.java' 2>/dev/null)
nf=$(echo "$main" | grep -c .)
pubtypes=$(echo "$main" | xargs grep -hE '^public (final |abstract |sealed )*(class|interface|enum|record) ' 2>/dev/null | wc -l)
pubmeth=$(echo "$main" | xargs grep -hE '^\s+public [^=(]*\(' 2>/dev/null | grep -vE '\b(class|interface|enum)\b' | wc -l)
test=$(find $J/$m -path '*/src/test/java/*' -name '*.java' 2>/dev/null)
ntf=$(echo "$test" | grep -c .)
tclasses=$(echo "$test" | xargs grep -lE '@Test\b|extends (TestCase|AbstractTestPackage)|public void test[A-Z_0-9]' 2>/dev/null | wc -l)
tann=$(echo "$test" | xargs grep -hE '^\s*@(Test|ParameterizedTest|RepeatedTest|TestFactory)\b' 2>/dev/null | wc -l)
tj3=$(echo "$test" | xargs grep -hE '^\s*public void test[A-Za-z0-9_]*\s*\(' 2>/dev/null | wc -l)
echo "$m mainfiles=$nf pubtypes=$pubtypes pubmethods=$pubmeth testfiles=$ntf testclasses=$tclasses @Test=$tann testXxxMethods=$tj3"
