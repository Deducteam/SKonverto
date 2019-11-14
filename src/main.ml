open Core
open Extra

(** [sig_of_file f] returns the signature of the file path [f]. *)
let sig_of_file : string -> Sign.t = fun fname ->
  let mp = Files.module_path fname in
  begin try Compile.compile true mp
    with
        Console.Fatal(None, msg) -> Console.exit_with "%s" msg
      | Console.Fatal(Some(p), msg) -> Console.exit_with "[%a] %s" Pos.print p msg end;
  Files.PathMap.find mp Sign.(Timed.(!loaded))

let spec =
  Arg.align []

let _ =
  let usage = Printf.sprintf "Usage: %s [OPTIONS] [FILES]" Sys.argv.(0) in
  let files = ref [] in
  Arg.parse spec (fun s -> files := s :: !files) usage;
  files := List.rev !files;
  let process_file _ = () in
  List.iter process_file !files