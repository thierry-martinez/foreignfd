jacopjar=solvers/jacop/target/jacop-1.0.0-jar-with-dependencies.jar

all: classes/jacop.jar tests doc

clean:
	rm -f classes/jacop.jar
	- rmdir classes
	rm -f ${jacopjar}
	rm -f doc/foreignfd.html doc/h1-bg.png doc/h2-bg.png doc/multi-bg.png doc/pldoc.css doc/priv-bg.png doc/pub-bg.png
	- rmdir doc
	rm -rf solvers/jacop/target

classes/jacop.jar: ${jacopjar}
	mkdir -p classes
	cp ${jacopjar} classes/jacop.jar

${jacopjar}: solvers/jacop/src/main/java/foreignfd/*.java
	cd solvers/jacop; mvn compile assembly:single

tests: foreignfd.pl foreignfd.plt
	CLASSPATH="classes/*" swipl -g \
	  "call_cleanup((['foreignfd.plt'], run_tests, halt(0)), halt(1))"

doc: doc/foreignfd.html

doc/foreignfd.html: foreignfd.pl
	mkdir -p doc
	swipl -g "call_cleanup(([foreignfd], doc_save(foreignfd, [doc_root(doc)]), halt(0)), halt(1))"
