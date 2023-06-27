type 'a exprat =
	| Epsilon
	| Const of 'a
	| Sum of 'a exprat * 'a exprat
	| Concat of 'a exprat * 'a exprat
	| Kleene of 'a exprat


let rec contient_vide = function
	| Epsilon -> true
	| Const(_) -> false
	| Sum(l1, l2) -> contient_vide l1 || contient_vide l2
	| Concat(l1, l2) -> contient_vide l1 && contient_vide l2
	| Kleene(_) -> true


let rec union l = function
	|[] -> l
	|h::t when List.mem h l -> union l t
	|h::t -> union (h::l) t


let rec lettres = function
	| Epsilon -> []
	| Const(a) -> [a]
	| Sum(l1, l2) -> union (lettres l1) (lettres l2)
	| Concat(l1, l2) -> union (lettres l1) (lettres l2)
	| Kleene(l) -> lettres l


let rec prefixes = function
	| Epsilon -> []
	| Const(a) -> [a]
	| Sum(l1, l2) -> union (prefixes l1) (prefixes l2)
	| Concat(l1, l2) when contient_vide l1 -> union (prefixes l1) (prefixes l2)
	| Concat(l, _) -> prefixes l
	| Kleene(l) -> prefixes l


let rec suffixes = function
	| Epsilon -> []
	| Const(a) -> [a]
	| Sum(l1, l2) -> union (suffixes l1) (suffixes l2)
	| Concat(l1, l2) when contient_vide l2 -> union (suffixes l1) (suffixes l2)
	| Concat(_, l) -> suffixes l
	| Kleene(l) -> suffixes l


let rec produit l1 l2 = match l1, l2 with
	|[], _ |_, [] -> []
	|h1::t1 , h2::t2 -> (h1,h2)::(produit t1 [h2]) @ produit l1 t2 


let rec facteurs2 = function
	| Epsilon -> []
	| Const(_) -> []
	| Sum(l1, l2) -> union (facteurs2 l1) (facteurs2 l2)
	| Concat(l1, l2) ->
		let f1 = facteurs2 l1 and f2 = facteurs2 l2 in
		let s1 = suffixes l1 and p2 = prefixes l2 in
		let s1p2 = produit s1 p2 in
		union (union f1 f2) s1p2
	| Kleene(l) -> facteurs2 (Concat(l,l))


let linearisation l =
	let n = ref 0 in
	let rec aux = function
		| Epsilon -> Epsilon
		| Const(a) -> incr n; Const(a, !n)
		| Sum(l1, l2) -> Sum(aux l1, aux l2)
		| Concat(l1, l2) -> Concat(aux l1, aux l2)
		| Kleene(l) -> Kleene(aux l)
	in aux l



type ('a, 'b) automate = {
	etats : 'b list;
	init : 'b list;
	finaux: 'b list;
	trans: ('b * 'a * 'b) list
}

let identite n =
	let rec aux l = function
		| -1 -> l
		| k -> aux (k::l) (k-1) in
	aux [] n


let glushkov e =
	let e_bis = linearisation e in
	let p = prefixes e_bis in
	let f = facteurs2 e_bis in
	let s = suffixes e_bis in
	let l = lettres e_bis in
	let n = List.length l in
	
	let etats = identite n in
	let init = [0] in
	let finaux = if contient_vide e_bis then 0::(List.map snd s) else (List.map snd s) in
	
	let rec aux1 l = function (* Transitions depuis 0 *)
		|[] -> l
		|h::t -> aux1 ((0,fst h,snd h)::l) t in
		
	let rec aux2 l = function
	(* Transitions entre deux lettres appartenant � un facteurs de longueur 2 *)
		|[] -> l
		|(x,y)::t -> aux2 ((snd x,fst y,snd y)::l) t in
	
	let trans = aux2 (aux1 [] p) f in
	
	{etats = etats; init = init; finaux = finaux; trans = trans}


let rec extrp s = (* Extraire parenth�ses *)
	if s = "" then [] else begin
	
	let n = String.length s in
	let count = ref 0 in
	let test = ref true in
	let debut = ref 0 in
	let fin = ref 0 in
	
	let i = ref 0 in
	let break = ref false in
	
	while !i < n && not !break do
		if s.[!i] = '(' then begin
			if !test then begin
				test := false;
				debut := !i;
			end
			else
				incr count;
		end;
		if s.[!i] = ')' then begin
			if !count = 0 then begin
				fin := !i;
				break := true;
			end
			else
				decr count
		end;
		
		incr i
	done;
	
	if !debut = 0 && !fin = 0 then
		[s]
	else begin
		let s1 = String.sub s 0 !debut in
		let s2 = String.sub s !debut (!fin - !debut + 1) in
		let s3 = String.sub s (!fin + 1) (n - !fin - 1) in
	
		let l = s1::s2::extrp s3 in
		let f a = not (a = "") in
		List.filter f l
		end
	end


type inter =
	|S of string
	|P of string
	|Plus
	|Etoile

open String

let rec extract_signs = function
	|[] -> []
	|h::t when h.[0] = '(' -> (P (sub h 1 (length h - 2)))::extract_signs t
	|""::t -> extract_signs t

	(* *+...*+ *)
	|h::t when (length h >= 4) && h.[0] = '*' && h.[1] = '+' && h.[length h - 2] = '*' && h.[length h - 1] = '+' ->
		Etoile::Plus::(S (sub h 2 (length h - 4)))::Etoile::Plus::extract_signs t
	(* *+...* *)
	|h::t when (length h >= 3) && h.[0] = '*' && h.[1] = '+' && h.[length h - 1] = '*' ->
		Etoile::Plus::(S (sub h 2 (length h - 3)))::Etoile::extract_signs t
	(* *+...+ *)
	|h::t when (length h >= 3) &&  h.[0] = '*' && h.[1] = '+' && h.[length h - 1] = '+' ->
		Etoile::Plus::(S (sub h 2 (length h - 3)))::Plus::extract_signs t
	(* *+... *)
	|h::t when (length h >= 2) && h.[0] = '*' && h.[1] = '+' ->
		Etoile::Plus::(S (sub h 2 (length h - 2)))::extract_signs t
	(* *...* *)
	|h::t when (length h >= 2) && h.[0] = '*' && h.[length h - 1] = '*' ->
		Etoile::(S (sub h 1 (length h - 2)))::Etoile::extract_signs t
	(* *...+ *)
	|h::t when (length h >= 2) && h.[0] = '*' && h.[length h - 1] = '+' ->
		Etoile::(S (sub h 1 (length h - 2)))::Plus::extract_signs t
	(* *...*+ *)
	|h::t when (length h >= 3) && h.[0] = '*' && h.[length h - 2] = '*' && h.[length h - 1] = '+' ->
		Etoile::(S (sub h 2 (length h - 3)))::Etoile::Plus::extract_signs t
	(* *... *)
	|h::t when h.[0] = '*' ->
		Etoile::(S (sub h 1 (length h - 1)))::extract_signs t
	(* ...* *)
	|h::t when h.[length h - 1] = '*' ->
		(S (sub h 0 (length h - 1)))::Etoile::extract_signs t

	(* +...*+ *)
	|h::t when (length h >= 3) && h.[0] = '+' && h.[length h - 2] = '*' && h.[length h - 1] = '+' ->
		Plus::(S (sub h 1 (length h - 3)))::Etoile::Plus::extract_signs t
	(* +...* *)
	|h::t when (length h >= 2) && h.[0] = '+' && h.[length h - 1] = '*' ->
		Plus::(S (sub h 1 (length h - 2)))::Etoile::extract_signs t
	(* +...+ *)
	|h::t when (length h >= 2) && h.[0] = '+' && h.[length h - 1] = '+' ->
		Plus::(S (sub h 1 (length h - 2)))::Plus::extract_signs t
	(* +... *)
	|h::t when h.[0] = '+' ->
		Plus::(S (sub h 1 (length h - 1)))::extract_signs t
	(* ...+ *)
	|h::t when h.[length h - 1] = '+' ->
		(S (sub h 0 (length h - 1)))::Plus::extract_signs t
	
	|h::t -> (S h)::extract_signs t

let extract_plus a =
	let rec aux s = function
		|[] -> s
		|Plus::t -> aux ([]::s) t
		|h::t when s = [] -> aux [[h]] t
		|h::t -> aux ((h::List.hd s)::List.tl s) t
in List.rev (List.map List.rev (aux [] a))



type 'a arbre =
	|Nil
	|F of 'a
	|N of 'a arbre * 'a arbre

let div_list l =
	let n = List.length l in
	let rec aux l1 l2 = function
			|0 -> (List.rev l1), l2
			|k -> aux ((List.hd l2)::l1) (List.tl l2) (k-1)
	in
	if l = [] then
		[], []
	else
		aux [] l (n/2)

let rec construire_arbre = function
	|[] -> Nil
	|[h] -> F h
	|l -> let l1, l2 = div_list l in N (construire_arbre l1, construire_arbre l2)

let string_to_list s =
	let n = length s in
	let l = ref [] in
	for i = n-1 downto 0 do
		l := s.[i]::(!l)
	done;
	!l

let simple_string_to_exprat s =
	let rec aux = function
		|Nil -> Epsilon
		|F h -> Const h
		|N(a,b) -> Concat(aux a, aux b)
in aux (construire_arbre @@ string_to_list s)







let rec aux1 = function
	|Nil -> Epsilon
	|F h -> aux2 h
	|N(a,b) -> Sum(aux1 a, aux1 b)

and aux2 = function
	|[] -> Epsilon
	|[S a] when not( contains a '+' || contains a '*' || contains a '(' ) -> simple_string_to_exprat a
	|[P a] when not( contains a '+' || contains a '*' || contains a '(' ) -> simple_string_to_exprat a
	|[S a] |[P a] -> transform a
	|(P a)::Etoile::t -> Concat(Kleene (transform a), aux2 t)
	|(S a)::Etoile::t -> Concat(Concat(transform (sub a 0 (length a - 1)),Kleene (Const (a.[length a - 1]))), aux2 t)
	|l when not (List.mem Etoile l) ->
		let l1, l2 = div_list l in Concat(aux2 l1, aux2 l2)
	|_ -> failwith "Erreur"

and transform s = aux1 @@ construire_arbre @@ extract_plus @@ extract_signs @@ extrp s
