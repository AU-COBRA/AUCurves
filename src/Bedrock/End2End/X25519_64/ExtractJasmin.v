(** Extract the Jasmin module string and the C module string for X25519-64. *)

From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlString.
Require Import Bedrock.End2End.X25519_64.MontgomeryLadder64.

Extraction "x25519_64_extracted" x25519_jasmin_module x25519_c_module.
