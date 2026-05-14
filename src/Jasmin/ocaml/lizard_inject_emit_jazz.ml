(** Lizard-inject .jazz emitter.
 *
 *  Companion of [lizard_inject_main.ml].  Where the main driver feeds
 *  the extracted [jasmin_func] list directly into jasminc's OCaml API
 *  (verified AST path), this small driver instead invokes the
 *  pretty-printer [pp_module] (Bedrock/Jasmin/Core.v lines 1986+) to
 *  emit human-readable Jasmin source text, suitable for vendoring as
 *  a [.jazz] file (e.g. as a replacement for hand-written stubs in
 *  SSProve-lean's bench/jasmin/gen/lizard_encode.jazz).
 *
 *  Trust posture: the .jazz output is via the unverified pretty-printer
 *  (DEPRECATED for compile-time use per Bedrock/Jasmin/Core.v).  The
 *  *.s output via the AST path (lizard_inject_main.ml) is verified.
 *  This emitter is purely for human inspection and for vendoring as
 *  a self-contained Jasmin-source mirror of the verified IR.
 *
 *  Usage:
 *    lizard_inject_emit_jazz <output.jazz>
 *)

let char_list_to_string (cl : char list) : string =
  let buf = Buffer.create 256 in
  List.iter (Buffer.add_char buf) cl;
  Buffer.contents buf

let () =
  let outfile = match Array.to_list Sys.argv with
    | _ :: f :: _ -> f
    | _ -> "/tmp/lizard_inject_emitted.jazz" in
  (* Concatenate the verified body with the stubs so the .jazz is
     self-contained.  Each stub function emits as
       export fn name(...) { }
     since the body is [JCskip].  The verified lizard_inject body
     then references them as calls. *)
  let body : Lizard_inject_jasmin_extracted.jasmin_func list =
    Lizard_inject_jasmin_extracted.lizard_inject_all_jasmin in
  let stubs : Lizard_inject_jasmin_extracted.jasmin_func list =
    Obj.magic Lizard_stubs_jasmin_extracted.lizard_inject_stubs in
  let all = body @ stubs in
  let text = char_list_to_string
    (Lizard_inject_jasmin_extracted.pp_module all) in
  let oc = open_out outfile in
  output_string oc
    "// Auto-emitted from AUCurves Rocq -> Jasmin Bridge.\n\
     // Source: BLS/AUCurves/src/Bedrock/End2End/Lizard/Inject_RustCmd.v\n\
     //   lizard_inject_rs : rust_cmd_ed (Qed-verified borrow_ok + wf preservation)\n\
     // Pipeline: rust_cmd_ed -> inline_callfn_n -> rust_cmd_ed_to_jasmin\n\
     //   -> polish_func_hoist -> pp_module (this file).\n\
     // Stubs (JCskip bodies, link-time resolved):\n\
     //   lizard_pack, elligator2_to_edwards, ristretto_encode\n\n";
  output_string oc text;
  close_out oc;
  Printf.eprintf "[lizard_inject_emit_jazz] wrote %d bytes to %s\n%!"
    (String.length text) outfile
