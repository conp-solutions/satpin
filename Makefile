PHONY: cd crs
d:
	cd core; make d; cp minisat_debug ../satpin

rs:
	cd core; make rs; cp minisat_static ../satpin

clean:
	cd core; make clean; cd ..
	rm -f satpin
