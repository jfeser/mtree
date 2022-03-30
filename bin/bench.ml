open Core
open Core_bench

let dist x x' = Float.abs (x -. x')

let () =
  Command.run
  @@ Bench.(
       make_command
         [
           Test.create ~name:"insert" (fun () ->
               let tree = M_tree.create dist in
               for _ = 0 to 1000 do
                 M_tree.insert tree (Random.float 1.0)
               done);
           (let tree = M_tree.create dist in
            for _ = 0 to 1000 do
              M_tree.insert tree (Random.float 1.0)
            done;
            Test.create ~name:"range" (fun () ->
                M_tree.range tree (Random.float 1.) ~radius:(Random.float 1.)
                  ignore));
         ])
