(** Diagnostic file: time each Require Import individually
    to find which dep's load is slow in MontgomeryCurveSpecs chain. *)

From Stdlib Require Import ZArith.

(* Standalone Stdlib imports (baseline) *)
Time Require Import Coq.ZArith.ZArith.
Time Require Import Coq.Classes.Morphisms.
Time Require Import Coq.micromega.Lia.

(* The suspects *)
Time Require Import Crypto.Algebra.Ring.
Time Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Time Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Time Require Import Crypto.Arithmetic.WordByWordMontgomery.

(* Rewriter *)
Time Require Import Rewriter.Util.Bool.

(* Theory imports that MontgomeryCurveSpecs uses *)
Time Require Import Theory.Fields.QuadraticFieldExtensions.
Time Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.
Time Require Import Theory.WordByWordMontgomery.wbw_morphisms.
Time Require Import Theory.Fields.ReflectiveZmod.
Time Require Import Theory.Fields.ReflectiveZmodTac.

(* Also the Partition / UniformWeight used by MontgomeryCurveSpecs *)
Time Require Import Crypto.Arithmetic.Partition.
Time Require Import Crypto.Arithmetic.UniformWeight.
