# Working on the Isabelle theories

Isabelle is not on `PATH`. Use `/Applications/Isabelle2025-2.app/bin/isabelle`.
Run every command from this directory (the repo is a Git worktree, so editing in place is safe).
Don't copy the theories to a scratch directory. `ROOT` defines the session `Zen_With_Terms`, and
`process_theories -d .` finds it from here.

## Naming conventions

- **Names follow the Java.** A model type, function or field carries the Java
  concept's name in Isabelle's `snake_case` (or `Camel_Case` for theories and
  types) to the extent possible.
- **New concepts** introduced as proof aids which have no equivalent in Java
  should be named descriptively, with explanatory documentation alongside
  their definitions.
- **No single-character variables.** Name variables after their types, or use
  some other descriptive name as appropriate.

## Iterating on a theory: `process_theories` with a timeout

Some proof methods (notably `blast`, and `auto` on a large definition) can loop for minutes. A plain
`isabelle build` then looks hung and tells you nothing about where it is. For experiments use
`process_theories`, single-threaded, with a per-command timeout:

```sh
/Applications/Isabelle2025-2.app/bin/isabelle process_theories \
  -d . -l HOL-Library \
  -o threads=1 -o timeout=5 -o parallel_proofs=0 \
  Zen_With_Terms.Abstract_Model
```

- The theory is named with its session prefix, for example `Zen_With_Terms.Refinement`.
- `-o timeout=5` stops any single command after 5 seconds, so a looping step fails with
  `*** Timeout` instead of blocking. A step that needs more than 5 seconds is slow enough to be
  worth rewriting (split it up, or give it more explicit facts) rather than giving it a longer timeout.
- `-o threads=1 -o parallel_proofs=0` makes the output unambiguous, with errors in source order.
- The output usually ends with `At command "by" (line N of ".../Foo.thy")`. Line N is the failing
  step. If a timeout has no location, bisect by splitting the suspect step into smaller ones.
- Filter the output: `... 2>&1 | grep -v "^$" | grep -B2 -A22 "At command\|Timeout\|rror\|Finished" | head -60`.
- `-O` prints all messages from every theory, including imports. It is far too noisy, so leave it off.
- Don't run it with `| head` while it is still going if you also want the log, and don't start a
  second copy while one is running.

Only theories that the named theory imports are rechecked, so name the theory you are working on.

## Before finishing: reformat, then build

```sh
python3 -I format_isabelle.py
/Applications/Isabelle2025-2.app/bin/isabelle build \
  -o threads=1 -o timeout=60 -o quick_and_dirty=false -D .
```

The build must finish with no errors. Never pass `-o quick_and_dirty` or `-o skip_proofs`.

## Proof tips learned the hard way

- `blast` and `auto` can loop on a conjunction with many conjuncts or a large unfolded definition
  such as `messages_ok` or `transient_link`. Extract the needed conjunct into its own lemma
  (see `messages_won_positive`), or split a link proof into `persisted_link` and `transient_link`
  and prove the pieces with `simp` using explicit facts.
- `term` is an Isabelle keyword. Don't use it as a bound variable outside quotes (`for node term`).
- When adding an item to `node_linkD`, append it at the end. Existing proofs use positional
  references such as `node_linkD(10)`.
- Don't leave stale Isabelle processes behind. Kill only your own: `pgrep -fl poly`, then `kill <pid>`.
  Other `poly` processes may belong to other work.
