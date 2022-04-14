open MLast
open Pcaml
open Pretty
open Prtools
open Pa_ppx_base
open Ppxutil
open Pa_ppx_runtime_fat
open Print_gram
open Comp_llk
open Primtypes

module Process = struct

let process verbose input_file output_file = 
  let txt = match input_file with
        "<stdin>" -> really_input_string stdin (in_channel_length stdin)
      | _ -> RT.read_file input_file
  in
  let code = txt |> Top.codegen Ploc.dummy ~bootstrap:true in
  let oc = match output_file with
        "<stdout>" -> stdout
      | _ -> open_out output_file
  in
  output_string oc (Eprinter.apply pr_str_item Pprintf.empty_pc code) ;
  output_string oc "\n" ;
  flush oc

open Cmdliner

let verbose =
  let doc = "Print file names as they are copied." in
  Arg.(value & flag & info ["v"; "verbose"] ~doc)

let src =
  let doc = "Source file to process." in
  Arg.(value & pos 0 string "<stdin>" & info [] ~docv:"SOURCE" ~doc)

let dst =
  let doc = "Destination file." in
  Arg.(value & pos 1 string "<stdout>" & info [] ~docv:"DESTINATION" ~doc)

let cmd =
  let doc = "process command" in
  let man = [
    `S Manpage.s_description;
    `P "Process a file"]
  in
  let info = Cmd.info "process" ~doc ~man in
  Cmd.v info Term.(const process $ verbose $ src $ dst)
end

module Firstk = struct
open ATN
open GraphDFA
open GraphFirstk

let firstk depth input_file entryname = 
  let txt = match input_file with
        "<stdin>" -> really_input_string stdin (in_channel_length stdin)
      | _ -> RT.read_file input_file
  in
  let entryname = match entryname with
      Some s -> Name.mk s
    | None -> Fmt.(failwithf "Must specify entryname")
  in
  let cg = txt |> Top.atn Ploc.dummy ~bootstrap:true in
  let e = CG.gram_entry cg entryname in
  let memo = ATN.GraphDFA.Memo.mk() in
  ignore (compute_firstk ~depth:6 (cg,memo) e)

open Cmdliner

let depth =
  let doc = "depth for computing firstk" in
  Arg.(value & opt int 6 & info ["d"; "depth"] ~doc)

let src =
  let doc = "Source file to process." in
  Arg.(value & pos 0 string "<stdin>" & info [] ~docv:"SOURCE" ~doc)

let entryname =
  let doc = "entryname" in
  Arg.(value & pos 1 (some string) None & info [] ~docv:"DESTINATION" ~doc)

let cmd =
  let doc = "firstk command" in
  let man = [
    `S Manpage.s_description;
    `P "firstk"]
  in
  let info = Cmd.info "firstk" ~doc ~man in
  Cmd.v info Term.(const firstk $ depth $ src $ entryname)
end

open Cmdliner

let main_cmd =
  let doc = "LLK cmdline" in
  let info = Cmd.info "standalone" ~version:"%%VERSION%%" ~doc in
  let default = Term.(ret (const (`Help (`Pager, None)))) in
  Cmd.group info ~default [Process.cmd; Firstk.cmd]

if not !Sys.interactive then begin
    Printexc.record_backtrace true ;
    exit (Cmd.eval main_cmd)
end
;
