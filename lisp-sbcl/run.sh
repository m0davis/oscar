sbcl --noinform --load monolithic-oscar.lisp --eval "(run-all-tests)" --non-interactive 2>&1 | tee run.log > /dev/null
