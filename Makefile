jacopjar=solvers/jacop/target/jacop-1.0.0-jar-with-dependencies.jar

all: classes/jacop.jar tests doc

clean:
	rm -f classes/jacop.jar
	rm -f ${jacopjar}
	rm -f foreignfd.html

classes/jacop.jar: ${jacopjar}
	mkdir -p classes
	cp ${jacopjar} classes/jacop.jar

${jacopjar}: solvers/jacop/src/main/java/foreignfd/*.java
	cd solvers/jacop; mvn compile assembly:single

tests: foreignfd.pl foreignfd.plt
	CLASSPATH="classes/*" swipl -g \
	  "call_cleanup((['foreignfd.plt'], run_tests, halt(0)), halt(1))"

doc: foreignfd.html

foreignfd.html: foreignfd.pl
	swipl -g "call_cleanup((['foreignfd.pl'], doc_save(foreignfd, []), halt(0)), halt(1))"
