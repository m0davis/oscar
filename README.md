Herein you may find the OSCAR project, originally developed by John L. Pollock (John), and cared for by yours truly (YT).

The directory structure includes

- [archive](archive), a collection of previous attempts at bringing Oscar to life. Of particular note are the subdirectories:
  - [lisp-originalish](archive/lisp-originalish), a pretty-close-to-original version of John's lisp-coded version of OSCAR.
  - [lisp-revised](archive/lisp-revised), a development of `lisp-originalish` that fixes some bugs and works (such as it does) in the SBCL interpreter. See especially, the latest and greatest version of the [OSCAR lisp code](archive/lisp-revised/monolithic-oscar.lisp).
- [docs/john-l-pollock](docs/john-l-pollock), a collection of works by John that informs my thinking about this project's development.

As a git repository, versions of the project up through 0.3.0.2 are tagged with descriptions in [the archived change-cum-planning-log](archive/docs/HISTORY-and-TODO). More tags of interest are:

- `hasV3.31`, probably tagged to note that it contains John's original (or close to original) lisp code.
- `agdabug-with-433`, probably something about a possible bug in Agda having to do with the `with` functionality, and something about the number 433.

In addition to `master` branch, active development will proceed in `develop`. These other extant branches may be considered not actively developed and may someday be dispensed with:

- bugfind--$-required-for-instance-resolution--version-2
- bugfind--interactive-checked-error-1
- bugfind--interactive-checked-error-2
- develop--add-all-arguments-to-transitivity
- develop--remove-transitivity-function-instances

Much of the lisp code (especially in [lisp-originalish](archive/lisp-originalish)) was derived from [John's website](http://johnpollock.us/ftp/OSCAR-web-page/oscar.html). As noted on the linked page:

> Permission is granted to use this software for educational and research purposes. For use in a commercial product, a license must be obtained from Lilian Jacques [support@johnpollock.us].
