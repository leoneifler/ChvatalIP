Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.
Require Import Coq.Strings.Ascii.

Set Implicit Arguments.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.all_ssreflect.

Require Import SparseMatrix.
Require Import SeqSet.
Require Import ParsingTools.
Require Import LineParser.
Require Import GenChvatalMatrix.
Require Import GenChvatalMatrixRevised.
Require Import ZArith.Znat.
Set Warnings "-extraction-reserved-identifier".
Import LString.
Import ListNotations.
Import C.Notations.

Local Open Scope char_scope.

(** Return if string (line) is relevant. Currently relevant lines are constraints (C) or bounds (B) *)
Definition is_relevant (str : LString.t) :  bool :=
 if str is h :: t then (h == "C") || (h == "B") else false.

(** Check if input has the correct format *)
Definition check_input (input : seq LString.t) : bool :=
  all is_relevant input.

(** Extracts the varsec from an LString. This starts with a line beginning with "VAR" and ends with a line beginning with "OBJ" *)
Definition getVarSec (input : list LString.t) (b : bool ) : list LString.t :=
  let start := find (subseq ["V";"A";"R"]) input in
  let sseq := drop start.+1 input in
  let ending := find (subseq ["O";"B";"J"]) sseq in
  take ending sseq .

(** Extracts the constraint sections from an LString. This starts with a line beginning with "CON" and ends with a line beginning with "RTP" *)
Definition getConsSec (input : list LString.t)(b : bool) : list LString.t :=
  let start := find (subseq ["C";"O";"N"]) input in
  let startseq := drop start.+1 input in
  let ending := find (subseq ["R";"T";"P"]) startseq in
  let theseq := take ending startseq in
  [seq x <- theseq | false == ( ["0"] ==  (nth [" "] (tokenize  x) 3))].

(** Create sparse matrix from vipr-input *)
Definition create_matrix (input : list LString.t) (vartable : list nat) : smat :=
  [seq ordervec (parseline vartable  h) | h <- input].


Definition a := [["t";"_";"x";"$";"y";"#";"1"];["t";"_";"x";"$";"x";"#";"6"];["t";"_";"x";"$";"y";"#";"3"];["t";"_";"x";"$";"x";"#";"4"]].

(** Create a vartable (convert between zimpl-numbering of sets in powerset and canonical ordering) *)
Definition create_vartable (input : list LString.t) (card : nat) : list nat :=
  let s := [seq drop 3 s | s <- input] in
  let f := (fun (x : LString.t) => if "y" \in x then extractNumber (drop 3 x) + pow2_min1 card
                                else if "z" \in x then (2 * pow2_min1 card)
                                else extractNumber (drop 3 x)) in
  [seq f x | x <- s].

(** parse the content of an LString into a sparse matrix. Create the correct chvatal-matrix and check if they are the same. Print some logging information *)
  Definition parse_content (content : LString.t) (card : nat) : C.t System.effect unit :=
    (* extract variable section and print it to shell *)
    let varsec := getVarSec (LString.split content (Char.n)) true in
    do! System.log (LString.s "Variable section:") in
        do! System.log (LString.join ([Char.n]) varsec) in
        (* extract problem description and print it to shell *)
        let inplist := getConsSec (LString.split content (Char.n)) true in
        do! System.log (LString.s "Relevant input:") in
            do! System.log ( LString.join ([Char.n])  inplist ) in
            (*create ordered input matrix*)
            let vartable := (create_vartable varsec card) in 
            let matrix := order (create_matrix inplist vartable) in 
            do! System.log (LString.s "Ordered input:") in
                do! System.log (toString (matrix)) in
                do! System.log (LString.s "coq-created matrix:") in
                (*create check-matrix*)
                let ch_matrix := order(create_mat card) in
                do! System.log (toString (ch_matrix) ) in
                (*Check if both matrices are the same*)
                if  (matrix == ch_matrix)
                then System.log (LString.s "The matrices are the same.")
                else  do! System.log (LString.s "The matrices are not the same, first different vectors:.") in
                      System.log (toString (diffvec matrix ch_matrix))
                .

(** Read vipr file and parse the content. *)
Definition read_file (argv : list LString.t) : C.t System.effect unit :=
  do! System.log (LString.s "Enter file-name of VIPR certificate to be checked:") in
    let! file_name := System.read_line in
    match file_name with
    | None => ret tt
    | Some name => 
    let! content := System.read_file name in
    do! System.log (LString.s "What is [n]?") in
        let! n := System.read_line in
        match n with
        | None => ret tt
        | Some number =>
          match content with
          | None => System.log (LString.s "Cannot read the file")
          | Some content => parse_content content (extractNumber  number)
          end
        end
    end.
        
(** Extract into compilable Ocaml code *)
Definition main := Extraction.launch read_file.
Extraction "bin/checkvipr" main.

Close Scope char_scope.