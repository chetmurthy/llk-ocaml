open MLast ;
open Pcaml ;
open Pretty;
open Prtools;
open Print_gram ;
open Comp_llk ;
open Pa_ppx_runtime_fat ;

value _main ~{verbose} ~{input_file} ~{output_file} = 
  let txt = match input_file with [
        "<stdin>" -> really_input_string stdin (in_channel_length stdin)
      | _ -> RT.read_file input_file
      ] in
  let code = txt |> Top.codegen Ploc.dummy ~{bootstrap=True} in
  let oc = match output_file with [
        "<stdout>" -> stdout
      | _ -> open_out output_file
      ] in do {
    output_string oc (Eprinter.apply pr_str_item Pprintf.empty_pc code) ;
    output_string oc "\n" ;
    flush oc
  }
;

value usage_msg = "usage" ;
value verbose = ref False ;
value input_file = ref "<stdin>" ;
value output_file = ref "<stdout>" ;
value anon_fun filename =
  input_file.val := filename ;

value speclist =
  [("-verbose", Arg.Set verbose, "Output debug information");
   ("-o", Arg.Set_string output_file, "Set output file name")]
;

value main () =
  try
    _main ~{verbose=verbose.val} ~{input_file=input_file.val} ~{output_file=output_file.val}
  with [
      e ->
      let open Printexc in
      let loc = match e with [
            Ploc.Exc loc _ -> loc
          | _ -> Ploc.dummy
          ] in
      Fmt.(pf stderr "%sException raised:%a@;%s"
             (Ploc.string_of_location loc)
             Exceptions.pp e
             (get_backtrace()))
    ]
;

if not Sys.interactive.val then do {
    Arg.parse speclist anon_fun usage_msg;
    Printexc.record_backtrace True ;
    main ()
} else ()
;
