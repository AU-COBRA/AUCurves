# Slow proofs: patterns to avoid

Each pattern below cost minutes or gigabytes in a real file. Timings are from `dune build -j2` on Rocq 9.2 with
4 cores and 16 GB. `scripts/check_slow_patterns.sh` counts the first four patterns and fails if a count rises; for `Axiom` it sees
only statements on one line. CI runs it on every push and pull request.

A file over 5 minutes or 4 GB is a bug to investigate. `dune` prints per-sentence times for theories that set
`-time`; start from the slowest sentence, not from the file.

## `inversion` on a hypothesis about a large unfolded program

`inversion` generalizes over the whole term at every step, so its cost grows with the program that remains.

    inversion Hexec; subst; clear Hexec.      (* rust_exec_ed over the unfolded program *)

Prove an inversion lemma once for arbitrary commands, and use it with `destruct` or `apply`:

    Lemma rexec_seq_inv : forall cp cpn ft c1 c2 rs1 rs3,
      rust_exec_ed cp cpn ft (REdSeq c1 c2) rs1 rs3 ->
      exists rs2, rust_exec_ed cp cpn ft c1 rs1 rs2 /\ rust_exec_ed cp cpn ft c2 rs2 rs3.
    Proof. intros * H; inversion H; subst; eauto. Qed.

`Sign_Strong_Correctness.v`: 381 s and 9.3 GB became 37 s and 1.3 GB, with the main `Qed` going from 62 s to 7 s.

`rexec_seq_inv`, `rexec_call_inv`, `rexec_let_zero_inv` and `rexec_let_u64_inv` are in `Sign_Strong_Correctness.v`, which
`StrongCorrectnessTactics.v` and every strong-correctness proof import; `peel_all_let_zero` and `peel_let_u64_step` use them.
`Sign_Strong_Correctness_VerifiedClamp.v`: 418 s and 9.6 GB became 38 s and 1.3 GB; `Verify_Strong_Correctness.v`: 191 s and
4.5 GB became 21 s and 0.8 GB; `Schnorr/Strong_Correctness.v`: 206 s and 4.5 GB became 24 s and 0.8 GB.

## `rewrite H at n` in a large goal or separation hypothesis

`at n` goes through setoid rewriting, and its typeclass search can dominate the file. When the term occurs once,
a plain `rewrite` gives the same result; check with `pattern x at 2`, which then fails. Otherwise use
`pattern x at n` before a plain `rewrite`.

`Cmov5Felems_64.v`: one such rewrite took 1,006 s; the file went from 1,065 s to 16 s.

## `destruct_head'` with `cbv in *` and `tauto` for a sig obligation

These walk the whole context. When the goal is a conjunct of the sig proof up to conversion, say so:

    abstract (destruct c as [[[a b] d] p]; exact (proj1 p)).

`EdwardsXYZT64.v`: 467 s and 73 s became 0.02 s and 0.05 s.

## `Axiom` whose statement contains a large computation

Declaring the axiom reduces its statement. `Axiom E_mul_l_B_zero : E.eq (Escalar (Z.pos l_pos) E.B) E.zero`
passed 11 GB, whereas `Check`, `Definition` and `Lemma ... Admitted` of the same statement peak at 469 MB.
`Strategy opaque` does not help, and neither does wrapping the statement in a `Definition`. Use `Lemma ... Admitted`, or seal
the large value in a `Module Type`. Both remain visible to `Print Assumptions`.

Do not assume the cost is in a proof or in native compilation until the sentence is identified: the output of
`-time` is buffered, so the last line printed before a stop may not be the sentence at fault.

## `f_equal` on a goal with concrete field constants

`f_equal` tries to close its goals by reduction. On an `F.opp` goal with the curve constant `E.d` it took 486 s.
Apply the congruence directly and leave the rest to `ring`:

    apply (f_equal (@F.opp _)). ring.

`Ristretto255_Inj.v`: 530 s became 40 s. This pattern is not counted by the script, because plain `f_equal` is
usually harmless.

## Pipeline runs that consumers do not need

`make_computed_op` over many limbs is the most expensive step in a field file, and many importers use only the
field parameters. Keep the parameters and the synthesized operations in separate files.
`bw6_761_prime.v` takes about 5 s since its operations moved to `bw6_761_prime_ops.v`.
