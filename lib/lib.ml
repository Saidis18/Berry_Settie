type 'a exprat =
  | Epsilon
  | Const of 'a
  | Sum of 'a exprat * 'a exprat
  | Concat of 'a exprat * 'a exprat
  | Kleene of 'a exprat

let rec contient_vide = function
  | Epsilon -> true
  | Const _ -> false
  | Sum (l1, l2) -> contient_vide l1 || contient_vide l2
  | Concat (l1, l2) -> contient_vide l1 && contient_vide l2
  | Kleene _ -> true

let rec union l = function
  | [] -> l
  | h :: t when List.mem h l -> union l t
  | h :: t -> union (h :: l) t

let rec lettres = function
  | Epsilon -> []
  | Const a -> [ a ]
  | Sum (l1, l2) -> union (lettres l1) (lettres l2)
  | Concat (l1, l2) -> union (lettres l1) (lettres l2)
  | Kleene l -> lettres l

let rec prefixes = function
  | Epsilon -> []
  | Const a -> [ a ]
  | Sum (l1, l2) -> union (prefixes l1) (prefixes l2)
  | Concat (l1, l2) when contient_vide l1 -> union (prefixes l1) (prefixes l2)
  | Concat (l, _) -> prefixes l
  | Kleene l -> prefixes l

let rec suffixes = function
  | Epsilon -> []
  | Const a -> [ a ]
  | Sum (l1, l2) -> union (suffixes l1) (suffixes l2)
  | Concat (l1, l2) when contient_vide l2 -> union (suffixes l1) (suffixes l2)
  | Concat (_, l) -> suffixes l
  | Kleene l -> suffixes l

let rec produit l1 l2 =
  match (l1, l2) with
  | [], _ | _, [] -> []
  | h1 :: t1, h2 :: t2 -> ((h1, h2) :: produit t1 [ h2 ]) @ produit l1 t2

let rec facteurs2 = function
  | Epsilon -> []
  | Const _ -> []
  | Sum (l1, l2) -> union (facteurs2 l1) (facteurs2 l2)
  | Concat (l1, l2) ->
      let f1 = facteurs2 l1 and f2 = facteurs2 l2 in
      let s1 = suffixes l1 and p2 = prefixes l2 in
      let s1p2 = produit s1 p2 in
      union (union f1 f2) s1p2
  | Kleene l -> facteurs2 (Concat (l, l))

let linearisation l =
  let n = ref 0 in
  let rec aux = function
    | Epsilon -> Epsilon
    | Const a ->
        incr n;
        Const (a, !n)
    | Sum (l1, l2) -> Sum (aux l1, aux l2)
    | Concat (l1, l2) -> Concat (aux l1, aux l2)
    | Kleene l -> Kleene (aux l)
  in
  aux l

type ('a, 'b) automate = {
  etats : 'b list;
  init : 'b list;
  finaux : 'b list;
  trans : ('b * 'a * 'b) list;
}

let identite n =
  let rec aux l = function -1 -> l | k -> aux (k :: l) (k - 1) in
  aux [] n

let glushkov e =
  let e_bis = linearisation e in
  let p = prefixes e_bis in
  let f = facteurs2 e_bis in
  let s = suffixes e_bis in
  let l = lettres e_bis in
  let n = List.length l in

  let etats = identite n in
  let init = [ 0 ] in
  let finaux =
    if contient_vide e_bis then 0 :: List.map snd s else List.map snd s
  in

  let rec aux1 l = function
    (* Transitions depuis 0 *)
    | [] -> l
    | h :: t -> aux1 ((0, fst h, snd h) :: l) t
  in

  let rec aux2 l = function
    (* Transitions entre deux lettres appartenant � un facteurs de longueur 2 *)
    | [] -> l
    | (x, y) :: t -> aux2 ((snd x, fst y, snd y) :: l) t
  in

  let trans = aux2 (aux1 [] p) f in

  { etats; init; finaux; trans }

let rec extrp s =
  (* Extraire parenth�ses *)
  if s = "" then []
  else
    let n = String.length s in
    let count = ref 0 in
    let test = ref true in
    let debut = ref 0 in
    let fin = ref 0 in

    let i = ref 0 in
    let break = ref false in

    while !i < n && not !break do
      if s.[!i] = '(' then
        if !test then (
          test := false;
          debut := !i)
        else incr count;
      if s.[!i] = ')' then
        if !count = 0 then (
          fin := !i;
          break := true)
        else decr count;

      incr i
    done;

    if !debut = 0 && !fin = 0 then [ s ]
    else
      let s1 = String.sub s 0 !debut in
      let s2 = String.sub s !debut (!fin - !debut + 1) in
      let s3 = String.sub s (!fin + 1) (n - !fin - 1) in

      let l = s1 :: s2 :: extrp s3 in
      let f a = not (a = "") in
      List.filter f l





type inter = S of string | P of string | Plus | Etoile

open String


let rec extract_signs = function
  | [] -> []
  | h :: t when h.[0] = '(' -> P (sub h 1 (length h - 2)) :: extract_signs t
  | "" :: t -> extract_signs t
  (* *+...*+ *)
  | h :: t
    when length h >= 4
         && h.[0] = '*'
         && h.[1] = '+'
         && h.[length h - 2] = '*'
         && h.[length h - 1] = '+' ->
      Etoile :: Plus
      :: S (sub h 2 (length h - 4))
      :: Etoile :: Plus :: extract_signs t
  (* *+...* *)
  | h :: t
    when length h >= 3 && h.[0] = '*' && h.[1] = '+' && h.[length h - 1] = '*'
    ->
      Etoile :: Plus :: S (sub h 2 (length h - 3)) :: Etoile :: extract_signs t
  (* *+...+ *)
  | h :: t
    when length h >= 3 && h.[0] = '*' && h.[1] = '+' && h.[length h - 1] = '+'
    ->
      Etoile :: Plus :: S (sub h 2 (length h - 3)) :: Plus :: extract_signs t
  (* *+... *)
  | h :: t when length h >= 2 && h.[0] = '*' && h.[1] = '+' ->
      Etoile :: Plus :: S (sub h 2 (length h - 2)) :: extract_signs t
  (* *...* *)
  | h :: t when length h >= 2 && h.[0] = '*' && h.[length h - 1] = '*' ->
      Etoile :: S (sub h 1 (length h - 2)) :: Etoile :: extract_signs t
  (* *...+ *)
  | h :: t when length h >= 2 && h.[0] = '*' && h.[length h - 1] = '+' ->
      Etoile :: S (sub h 1 (length h - 2)) :: Plus :: extract_signs t
  (* *...*+ *)
  | h :: t
    when length h >= 3
         && h.[0] = '*'
         && h.[length h - 2] = '*'
         && h.[length h - 1] = '+' ->
      Etoile :: S (sub h 2 (length h - 3)) :: Etoile :: Plus :: extract_signs t
  (* *... *)
  | h :: t when h.[0] = '*' ->
      Etoile :: S (sub h 1 (length h - 1)) :: extract_signs t
  (* ...* *)
  | h :: t when h.[length h - 1] = '*' ->
      S (sub h 0 (length h - 1)) :: Etoile :: extract_signs t
  (* +...*+ *)
  | h :: t
    when length h >= 3
         && h.[0] = '+'
         && h.[length h - 2] = '*'
         && h.[length h - 1] = '+' ->
      Plus :: S (sub h 1 (length h - 3)) :: Etoile :: Plus :: extract_signs t
  (* +...* *)
  | h :: t when length h >= 2 && h.[0] = '+' && h.[length h - 1] = '*' ->
      Plus :: S (sub h 1 (length h - 2)) :: Etoile :: extract_signs t
  (* +...+ *)
  | h :: t when length h >= 2 && h.[0] = '+' && h.[length h - 1] = '+' ->
      Plus :: S (sub h 1 (length h - 2)) :: Plus :: extract_signs t
  (* +... *)
  | h :: t when h.[0] = '+' ->
      Plus :: S (sub h 1 (length h - 1)) :: extract_signs t
  (* ...+ *)
  | h :: t when h.[length h - 1] = '+' ->
      S (sub h 0 (length h - 1)) :: Plus :: extract_signs t
  | h :: t -> S h :: extract_signs t



type 'a arbre = Nil | F of 'a | N of 'a arbre * 'a arbre

let div_list l =
  let n = List.length l in
  let rec aux l1 l2 = function
    | 0 -> (List.rev l1, l2)
    | k -> aux (List.hd l2 :: l1) (List.tl l2) (k - 1)
  in
  if l = [] then ([], []) else aux [] l (n / 2)

let rec construire_arbre = function
  | [] -> Nil
  | [ h ] -> F h
  | l ->
      let l1, l2 = div_list l in
      N (construire_arbre l1, construire_arbre l2)

let string_to_list s =
  let n = length s in
  let l = ref [] in
  for i = n - 1 downto 0 do
    l := s.[i] :: !l
  done;
  !l

let simple_string_to_exprat s =
  let rec aux = function
    | Nil -> Epsilon
    | F h -> Const h
    | N (a, b) -> Concat (aux a, aux b)
  in
  aux (construire_arbre @@ string_to_list s)


	let rec simplifier = function
  | Epsilon -> Epsilon
  | Const a -> Const a
  | Sum (a, b) -> Sum (simplifier a, simplifier b)
  | Concat (a, Epsilon) | Concat (Epsilon, a) -> simplifier a
  | Concat (a, b) -> Concat (simplifier a, simplifier b)
  | Kleene Epsilon -> Epsilon
  | Kleene a -> Kleene (simplifier a)

	(*
let rec transform s =
  let rec aux e = function
    | [] -> e
    | [ S a ] when not (contains a '+' || contains a '*' || contains a '(') ->
        Concat (e, simple_string_to_exprat a)
    | [ P a ] when not (contains a '+' || contains a '*' || contains a '(') ->
        Concat (e, simple_string_to_exprat a)
    | Plus :: P a :: Etoile :: t -> Sum (e, aux (Kleene (transform a)) t)
    | Plus :: S a :: Etoile :: t when length a >= 3 ->
        let n = length a in
        if a.[n - 2] = '+' then begin
          let x = sub a 0 (n - 2) in
          let y = a.[n - 1] in
          Sum (Sum (e, transform x), aux (Kleene (Const y)) t)
				end
        else begin
          let x = sub a 0 (n - 1) in
          let y = a.[n - 1] in
          Concat (Sum (e, transform x), aux (Kleene (Const y)) t)
				end
    | Plus :: P a :: t -> Sum (e, aux (transform a) t)
    | Plus :: S a :: t when length a >= 3 ->
        let n = length a in
        if a.[n - 2] = '+' then begin
          let x = sub a 0 (n - 2) in
          let y = a.[n - 1] in
          Sum (Sum (e, transform x), aux (Const y) t)
				end
        else begin
          let x = sub a 0 (n - 1) in
          let y = a.[n - 1] in
          Concat (Sum (e, transform x), aux (Const y) t)
				end
		| Plus :: S a :: Etoile :: t when length a = 2 -> Sum (e, aux (Concat (Const a.[0], (Kleene (Const a.[1])))) t)
    | Plus :: S a :: Etoile :: t -> Sum (e, aux (Kleene (Const a.[0])) t)
    | Plus :: S a :: t -> Sum (e, aux (transform a) t)
    | P a :: Etoile :: t -> aux (Concat (e, Kleene (transform a))) t
    | P a :: t -> aux (Concat (e, transform a)) t
    | S a :: Etoile :: t when length a >= 3 ->
        let n = length a in
        if a.[n - 2] = '+' then begin
          let x = sub a 0 (n - 2) in
          let y = a.[n - 1] in
          Sum (Concat (e, transform x), aux (Kleene (Const y)) t)
				end
        else begin
          let x = sub a 0 (n - 1) in
          let y = a.[n - 1] in
          Concat (Concat (e, transform x), aux (Kleene (Const y)) t)
				end
    | S a :: Etoile :: t -> aux (Concat (e, Kleene (transform a))) t
    | S a :: t when length a >= 3 ->
        let n = length a in
        if a.[n - 2] = '+' then begin
          let x = sub a 0 (n - 2) in
          let y = a.[n - 1] in
          Sum (Concat (e, transform x), aux (Const y) t)
				end
        else begin
          let x = sub a 0 (n - 1) in
          let y = a.[n - 1] in
          Concat (Concat (e, transform x), aux (Const y) t)
				end
    | S a :: t -> aux (Concat (e, transform a)) t
    | _ -> failwith "erreur"
  in
  aux Epsilon (extract_signs @@ extrp s)
*)



let extract_plus s =
	let r = ref [] in
	let n = length s in
	let i = ref 0 in
	let j = ref 0 in
	while !j < n do
		if s.[!j] = '+' then begin
			r := (sub s !i (!j - !i))::!r;
			incr j;
			i := !j;
		end else
			incr j
	done;
	r := (sub s !i (!j - !i))::!r;
	List.rev !r;;

let rec last = function
	|[] -> failwith "liste vide"
	|[a] -> a
	|_::t -> last t


let rec transform s =
  let rec aux e = function
		(* Cas de base *)
    | [] -> e
    | [ S a ] when not (contains a '+' || contains a '*' || contains a '(') ->
        Concat (e, simple_string_to_exprat a)
    | [ P a ] when not (contains a '+' || contains a '*' || contains a '(') ->
        Concat (e, simple_string_to_exprat a)
		(**)
    | Plus :: P a :: Etoile :: t -> Sum (e, aux (Kleene (transform a)) t)
    | Plus :: P a :: t -> Sum (e, aux (transform a) t)
		(**)
    | Plus :: S a :: Etoile :: t when length a >= 3 ->
        let n = length a in
        if a.[n - 2] = '+' then begin
          let x = sub a 0 (n - 2) in
          let y = a.[n - 1] in
          Sum (Sum (e, transform x), aux (Kleene (Const y)) t)
				end
        else begin
          let x = sub a 0 (n - 1) in
          let y = a.[n - 1] in
          Sum(e, aux (transform x) t)
				end
		| Plus :: S a :: Etoile :: t when length a = 2 -> Sum (e, aux (Concat (Const a.[0], (Kleene (Const a.[1])))) t)
    | Plus :: S a :: Etoile :: t -> Sum (e, aux (Kleene (Const a.[0])) t)
		(**)



		| Plus :: S a :: t -> Sum (e, aux (transform a) t)
		

		(**)
    | P a :: Etoile :: t -> aux (Concat (e, Kleene (transform a))) t
    | P a :: t -> aux (Concat (e, transform a)) t
		(**)
    | S a :: Etoile :: t ->
			(match extract_plus a with
				|h1::h2::h3::t_bis ->
					let h4 = last (h3::t_bis) in
					
					let f x y = Sum(x, transform y) in
					let x = List.fold_left f (transform h2) t_bis in
					aux (Sum (Sum (Concat(e, transform h1), x), Kleene (Const h4.[length h4 - 1]))) t
				|[h1;h2] ->

					aux (Sum(Sum(e, transform h1), transform h2_bis))
				|_ -> failwith "erreur")
				(*
        let n = length a in
        if a.[n - 2] = '+' then begin
          let x = sub a 0 (n - 2) in
          let y = a.[n - 1] in
          Sum (Concat (e, transform x), aux (Kleene (Const y)) t)
				end
        else begin
          let x = sub a 0 (n - 1) in
          let y = a.[n - 1] in
          Concat (Concat (e, transform x), aux (Kleene (Const y)) t)
				end
				*)
    | S a :: Etoile :: t -> aux (Concat (e, Kleene (transform a))) t
		(**)
    | (*(*???????????????????*)*) S a :: t when length a >= 3 ->
        let n = length a in
        if a.[n - 2] = '+' then begin
          let x = sub a 0 (n - 2) in
          let y = a.[n - 1] in
          Sum (Concat (e, transform x), aux (Const y) t)
				end
        else begin
          let x = sub a 0 (n - 1) in
          let y = a.[n - 1] in
          Concat (Concat (e, transform x), aux (Const y) t)
				end
    | (*(*???????????????????*)*) S a :: t -> aux (Concat (e, transform a)) t
    | _ -> failwith "erreur"
  in
  simplifier @@ aux Epsilon (extract_signs @@ extrp s)









(*
	let rec transform s =
		let rec aux e = function
			| [] -> e
			| [ S a ] when not (contains a '+' || contains a '*' || contains a '(') ->
					Concat (e, simple_string_to_exprat a)
			| [ P a ] when not (contains a '+' || contains a '*' || contains a '(') ->
					Concat (e, simple_string_to_exprat a)
			| Plus :: P a :: Etoile :: t -> Sum (e, aux (Kleene (transform a)) t)
			| Plus :: S a :: Etoile :: t when length a >= 3 ->
					let n = length a in
					if a.[n - 2] = '+' then
						let x = sub a 0 (n - 2) in
						let y = a.[n - 1] in
						Sum (Sum (e, transform x), aux (Kleene (Const y)) t)
					else
						let x = sub a 0 (n - 1) in
						let y = a.[n - 1] in
						Concat (Sum (e, transform x), aux (Kleene (Const y)) t)
			| Plus :: P a :: t -> Sum (e, aux (transform a) t)
			| Plus :: S a :: t when length a >= 3 ->
					let n = length a in
					if a.[n - 2] = '+' then
						let x = sub a 0 (n - 2) in
						let y = a.[n - 1] in
						Sum (Sum (e, transform x), aux (Const y) t)
					else
						let x = sub a 0 (n - 1) in
						let y = a.[n - 1] in
						Concat (Sum (e, transform x), aux (Const y) t)
			| Plus :: S a :: Etoile :: t -> Sum (e, aux (Kleene (transform a)) t)
			| Plus :: S a :: t -> Sum (e, aux (transform a) t)
			| P a :: Etoile :: t -> aux (Concat (e, Kleene (transform a))) t
			| P a :: t -> aux (Concat (e, transform a)) t
			| S a :: Etoile :: t when length a >= 3 ->
					let n = length a in
					if a.[n - 2] = '+' then
						let x = sub a 0 (n - 2) in
						let y = a.[n - 1] in
						Sum (Concat (e, transform x), aux (Kleene (Const y)) t)
					else
						let x = sub a 0 (n - 1) in
						let y = a.[n - 1] in
						Concat (Concat (e, transform x), aux (Kleene (Const y)) t)
			| S a :: Etoile :: t when length a = 2 -> aux (Concat (e, Concat(Const a.[0], Kleene (Const a.[1])))) t
			| S a :: Etoile :: t when length a = 1 -> aux (Concat (e,  Kleene (Const a.[0]))) t
			| S a :: t -> Concat(transform a, aux Epsilon t)
			| _ -> failwith "erreur"
		in
		simplifier @@ aux Epsilon (extract_signs @@ extrp s)
	*)
