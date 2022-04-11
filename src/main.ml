open! Lplib

let spec =
  Arg.align
  [
    ("--signature", Arg.Set_string Deskolem.signature_name,
     "Set the name of the signtaure file");
    ("--package", Arg.Set_string Deskolem.package_name,
     "Set the name of the lambdapi package")
  ]

let _ =
  let usage =
    Printf.sprintf "Usage: %s --signature [NAME] --package [NAME] [FILES]"
      Sys.argv.(0)
  in
  let files = ref [] in
  Arg.parse spec (fun s -> files := s :: !files) usage;
  Common.Library.set_lib_root None;
  files := List.rev !files;
  let process_file s =
    Deskolem.main s (Handle.Compile.compile_file ~force:true s) in
  List.iter process_file !files
