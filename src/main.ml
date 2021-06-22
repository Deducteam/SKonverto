open! Lplib

let spec =
  Arg.align []

let _ =
  let usage = Printf.sprintf "Usage: %s [OPTIONS] [FILES]" Sys.argv.(0) in
  let files = ref [] in
  Arg.parse spec (fun s -> files := s :: !files) usage;
  Common.Library.set_lib_root None;
  files := List.rev !files;
  let process_file s = s |> Handle.Compile.compile_file |> Deskolem.main in
  List.iter process_file !files