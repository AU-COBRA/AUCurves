# Various Scripts for Making Pretty Timing Tables

These scripts assume that your development has a `Makefile` in its root,
and that if you `make TIMED=1`, you get timing data a la the output of
a `coq_makefile`-made `Makefile`.

Each top-level script has documentation in a comment at the top of the script.

## [make-pretty-timed.sh](./make-pretty-timed.sh)
Record the compilation performance of the current state of the
library

This script creates a file with the duration of
compilation of each file that is compiled by `make`, as well as the
total duration.

This script is most useful after you have already committed your
changes, or when you do not care about comparing the current state
with a previous state.

## [make-pretty-timed-diff.sh](./make-pretty-timed-diff.sh)
Record the compilation performance of the current state of the
library and the previous state, and compare them.

This script creates a file with the
duration of compilation of each file that is compiled by `make`, as
well as the total duration, of both the current state of the library
and the most recent commit.  These results are tabulated, and a difference
column is added.

This script uses `git stash` to save the current state of the
repository.  This script is most useful after you have run `git add`
on all of the files, and are preparing to make a commit, but have
not yet committed (you have staged your changes, but not commited
them).

## [make-pretty-timed-diff-tip.sh](./make-pretty-timed-diff-tip.sh)
Record the compilation performance of the current tip of the
library and the previous commit, and compare them.

This script creates a file with the
duration of compilation of each file that is compiled by `make`, as
well as the total duration, of both the current state of the library
and the most recent commit.  These results are tabulated, and a difference
column is added.

This script uses `git checkout` to change states; this script will
exit if you have staged but uncomitted changes.

## [make-pretty-timed-only-diff.sh](./make-pretty-timed-only-diff.sh)
Record the compilation performance of the current state of the
library and the previous state, and compare them, only on the files that
changed.

This script creates a file with the
duration of compilation of each file that is compiled by `make`, as
well as the total duration, of both the current state of the library
and the most recent commit.  These results are tabulated, and a difference
column is added.

This script uses `git stash` to save the current state of the
repository.  This script is most useful after you have run `git add`
on all of the files, and are preparing to make a commit, but have
not yet committed (you have staged your changes, but not commited
them).

## [make-pretty-timed-only-diff-tip.sh](./make-pretty-timed-only-diff-tip.sh)
Record the compilation performance of the current tip of the library
and the previous commit, and compare them, only on the files that
changed.

This script creates a file with the
duration of compilation of each file that is compiled by `make`, as
well as the total duration, of both the current state of the library
and the most recent commit.  These results are tabulated, and a difference
column is added.

This script uses `git checkout` to change states; this script will
exit if you have staged but uncomitted changes.

