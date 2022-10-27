open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-2;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
let rec simplifie l clauses =
  match clauses with
  | [] -> []
  (* Si clauses est vide, on retourne l'ensemble vide *)
  | c :: clauses -> if mem l c then simplifie l clauses else
    (* Si c contient l, on appelle 'simplifie' récursivement *)
    let s = rev (filter_map (fun x -> if x = -l then None else Some x) c)
    (* Sinon, on filtre la clause c à l'aide de filter_map *)
    (* Le filtre supprime la négation du littéral l, si elle existe *)
    in s :: simplifie l clauses
    (* Finalement, on concatène la clause filtrée à l'appel récursif de 'simplifie' *)
  
(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* une clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split [[1;-2;-3];[-2;3];[-2]] []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let rec unitaire clauses =
  match clauses with
  | [] -> raise (Failure "Not_found")
  (* Si clauses est vide, il n'y a pas de clause unitaire *)
  | c :: clauses -> match c with
    (* Sinon, on vérifie si c en est une *)
    | x :: [] -> x
    (* c est une clause unitaire puisqu'elle est de la forme x concaténé à la liste vide, donc on retourne x *)
    | _ -> unitaire clauses;;
    (* Default : c n'est pas une clause unitaire, on appelle alors 'unitaire' récursivement *)
    
(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses =
  let l = flatten clauses
  (* On utilise flatten pour avoir une liste simple *)
  in let m = map (fun x -> if mem (-x) l then x :: [-x] else [x]) l
  (* Pour chaque éléments de l, on regarde si l contient sa négation.
    Si c'est le cas, on crée un tuple [x;-x] *)
  in try unitaire m with
    e -> raise (Failure "Pas de litteral pur");;
    (* Finalement, si il existe un élément de m qui n'est pas un tuple, c'est qu'il est pur *)

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  if clauses = [] then Some interpretation else
    (* L'ensmble vide de clauses est satisfiable *)
  if mem [] clauses then None else
    (* Une clause vide n'est pas satisfiable *)
  try solveur_dpll_rec (simplifie (unitaire clauses) clauses) ((unitaire clauses)::interpretation) with
    (* On essaie d'abord de simplifier un littéral unitaire s'il existe puis d'appeler la récursion *)
    e -> try solveur_dpll_rec (simplifie (pur clauses) clauses) ((pur clauses)::interpretation) with
      (* On essaie ensuite de simplifier un littéral pur s'il existe puis d'appeler la récursion *)
      e -> let branche = solveur_dpll_rec (simplifie (hd (hd clauses)) clauses) ((hd (hd clauses))::interpretation)
      (* Il n'y a plus de clause unitaire/littéral pur, on simplifie par le premier terme *)
  in match branche with
  | None -> solveur_dpll_rec (simplifie (-(hd (hd clauses))) clauses) ((-(hd (hd clauses))) :: interpretation)
  (* Si l ne donne pas d'interprétation satisfaisant clauses, on essaie sa négation *)
  | _ -> branche;;

(* tests *)
(* let () = print_modele (solveur_dpll_rec [[1;-2;-3];[-2;3];[-2]] []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
