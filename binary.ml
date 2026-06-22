let rec fib n = if n <= 1 then 1 else fib (n-1)+fib (n-2);; (* suite de fibonacci *)

(** type entier unaire*)
type nat = O | S : nat -> nat;; 

(*  l'addition en unaire 
    plus : nat -> (nat -> nat)
*) 
let rec plus a b =
  match a with
  | O    -> b
  | S a' -> S (plus a' b);; 
  
(* traduction
   i2n : int -> nat  
*)  
let rec i2n i =
  if i = 0 then O else S (i2n (i-1));;
  
(* traduction inverse 
  n2i : nat -> int
*)  
let rec n2i a =
  match a with
  | O    -> 0
  | S a' -> 1+(n2i a');; 
  
(* la multiplication en unaire 
   mult : nat -> nat -> nat
*)  
let rec mult a b =
  match a with
  | O    -> O
  | S a' -> plus b (mult a' b);; 
  
(* l'exponentielle en unaire 
   exp : nat -> nat (la puissance) -> nat 
*)
let rec exp b a =
  match a with
  | O    -> S O
  | S a' -> mult b (exp b a');;
  
  
(* test de l'exponentielle -> 2**10=1024 *)  
n2i(exp (i2n 2) (i2n 10));;  

(** nouveau type les bit :
  0 ou 1 
*)
type bit = Zero | One;; 

(** nouveau type les eniters binaires positifs : 
   XH -> 1
   XC(XH, Zero/One) -> 2q + 0/1 
   Ex : 1011 -> XC(XC(XC(XH,Zero),One),One)
*)
type pos = XH : pos | XC : pos * bit -> pos;; 


(*  traduction des bit vers les nat :
    b2n : bit -> nat
*)
let b2n b =
  match b with
  | Zero  -> O
  | One  -> S O;;
     
(*  traduction des positifs vers les nat -> manque 0 pas inclu dans les pos 
    p2n : pos -> nat
*)  
let rec p2n p=
  match p with
  | XH  -> S O
  | XC (q,b) -> plus (b2n b) (mult (S (S O))  (p2n q)) ;;
   
(* test de trad -> 3 *)     
p2n (XC(XH,One));; 

(* la division par 2 
   div2 : nat -> nat * bit
*)
let rec div2 a=
  match a with
  | O -> (O,Zero)
  | S O -> (O,One)				 
  | S(S n)  -> let (q, r) = div2 n in (S q, r);;
  
(* traduction des nat vers les positifs en excluant 0 -> produit une exception si appeler en 0
   n2p : nat -> pos
 *)    
let rec n2p n=
  let (q, r) = div2 n 
  in match q with
     | O -> (match r with One -> XH)
     | S h -> XC (n2p q, r);; 
     
(* traduction des plus utiles des int vers les positifs
   i2p : int -> pos
*)
let i2p n=
  n2p (i2n n);; 
  
(* et inversement ...
   p2i : pos -> int
 *)  
let p2i _n=
   n2i (p2n _n);; 
   
(* test avec le quotient en int
   t : int -> int * bit
 *)
let t n=
  let (q, r) = div2 (i2n n) in (n2i q, r);; 
  
(** nouveau type les bin, 
   BZ -> 0 et BP -> un bin positif (prend un pos en parametre)
*)
type bin = BZ | BP : pos -> bin;; 

(* trd. des nat vers les bin 
   n2b : nat -> bin
*)
let n2b n=
  match n with 
  | O -> BZ
  | S _ -> BP (n2p n);; 
  
(* et inversement...
   b2n : bin -> nat
*)
let b2n b=
  match b with
  | BZ -> O
  | BP p -> p2n p;; 

(* addition de 2 bits (a et b) et d'une potentielle retenue c 
   addb : bit -> bit -> bit -> bit * bit 
*)
let addb a b c= 
  match (a, b, c) with
  | Zero,Zero,Zero -> (Zero, Zero)
  | Zero, Zero, One -> (Zero, One)
  | Zero, One, Zero -> (Zero, One)
  | Zero, One, One -> (One, Zero)
  | One, Zero, Zero -> (Zero, One)
  | One, Zero, One -> (One, Zero)
  | One, One, Zero -> (One, Zero)
  | One, One, One -> (One, One);; 
  
(* test 1 + 1 + 1 = 3 soit One One *)  
addb One One One;; 

(* le successeur d'un positif 
   succp : pos -> pos 
*)
let rec succp p=
  match p with
   |XC(q,Zero) -> XC(q, One)
   |XC(q, One) -> XC(succp q, Zero)
   |XH -> XC (XH, Zero);; 
   
(* additionner 0 ou 1 à un pos grâce au successeur pour les retenues
   addpb : pos -> bit -> pos 
*)
let addpb p b=
  match b with 
  | Zero -> p
  | One -> succp p ;;

(* addition de 2 pos et une retenue en bit 
   addp : pos -> pos -> bit -> pos
*)
let rec addp x y c=
  match (x,y) with
  |XC (p, a), XC (q, b)
    -> let (r,s)= addb a b c in
       let pqr= addp p q r
       in XC (pqr, s)
  |XH, XH
    -> let (_,s)= addb One One c
       in XC(XH,s) 
  |XC (p, a), XH
    -> let (r,s)= addb a One c in
       let pqr= addpb p r 
       in XC (pqr, s)
  |XH, XC(q, b)
    -> let (r,s)= addb One b c in 
       let pqr= addpb q r
       in XC (pqr, s);; 

(* trd. des bits vers les bin 
   b2b : bit -> bin
*)
let b2b x=
  match x with
  | Zero -> BZ
  | One -> BP(XH);; 

(* addition de 2 bin et une retenue en bit 
   addbin : bin -> bin -> bit -> bin
*)
let addbin x y c =
  match (x,y) with
  | BZ, BZ -> b2b c 
  | BZ, BP b -> BP (addpb b c)
  | BP a, BZ -> BP (addpb a c) 
  | BP a, BP b -> BP (addp a b c) ;; 
  
(* test addp 
   t : int -> int -> int 
*)
 let t n m =
    (n2i (p2n (addp (n2p (i2n n)) (n2p (i2n m)) Zero)));;

(* test en pos -> 8 + 4 = 12 *)
addp (XC(XC (XC (XH, Zero), Zero), Zero)) (XC(XC(XH, Zero), Zero)) Zero ;;
(* test en pos -> 7 + 10 = 17 *)
addp (XC(XC(XH, One), One)) (XC(XC(XC(XH, Zero),One),Zero)) Zero;;
(* test en pos -> 8 + 3 = 11 *)
addp (XC(XC (XC (XH, Zero), Zero), Zero)) (XC (XH, One)) Zero ;;

(* multiplication de bit -> 4 cas 0*1, 1*0, 0*0 et 1*1
   multb : bit -> bit -> bit
*)
let multb a b=
  match a with
  | Zero -> Zero
  | One -> b ;; 
  
(* multiplication de 2 pos grâce à l'addition et aux appelles récursifs 
   multp pos -> pos -> pos
*)  
let rec multp x y=
  match x with
  | XC(p,Zero) -> XC ( multp p y, Zero)
  | XC(p, One) -> (addp y (XC(multp p y,Zero)) Zero) 
  | XH -> y ;; 

(* multiplication de 2 bin
  multbin : bin -> bin -> bin
*)
let multbin x y=
  match (x,y) with 
  | _,BZ -> BZ
  | BZ,_ -> BZ
  | BP(m),BP(n) -> BP (multp m n) ;; 

(* test multp en int 
   test : int -> int -> int 
*)
let test x y=
  p2i (multp (i2p x) (i2p y));; 
  
(** Nouveau type les diff, permettent de comparer/soustraire 2 pos  
    Neg -> a < b | Eq -> a = b | Pos -> a > b
*) 
type diff = Neg : pos -> diff | Eq | Pos : pos -> diff 

(* trd. des diff vers les int 
   d2i : diff -> int 
*)
let d2i x= 
  match x with 
  | Neg d -> - (p2i d) (* < *)
  | Eq -> 0  (* = *)
  | Pos d -> p2i d ;; (* > *) 
  
(* predecesseur d'un pos incluant 0 (None) mais passant au type Some pos *)
(*
let rec predp x=
  match x with
  | XH -> None
  | XC(d, One) -> Some (XC(d, Zero))
  | XC(d, Zero) -> 
    match predp d with
    | None   -> Some XH
    | Some p -> Some (XC (p,One));;
    *) 
    
let rec predp x=
  match x with
  | XC(d, One)   -> XC(d, Zero)
  | XC(XH, Zero) -> XH
  | XC(d,Zero)   -> XC (predp d,One);; (* predecesseur sans 0 mais qu'avec les pos *)

let t x = p2i (predp (i2p x));; (* test pred *)

let diffb a b =
  match (a, b) with
  | One, Zero -> Pos XH
  | Zero, One -> Neg XH
  | _, _ -> Eq;; (* différence/comparaison de 2 bit *)

let rec diffp x y=
  match (x,y) with
  | XH, XH -> Eq
  | _, XH  -> Pos (predp x)
  |XH, _   -> Neg (predp y)
  | XC(p, a), XC(q, b) ->
    match diffp p q with
    | Neg d -> Neg (match diffb b a with
      | Neg _ -> predp (XC (d,Zero))
      | Eq    -> XC (d,Zero)
      | Pos _ -> XC (d,One)) 
    | Eq    -> diffb a b;
    | Pos d -> Pos (match diffb a b with
      | Neg _ -> predp (XC (d,Zero))
      | Eq    -> XC (d,Zero)
      | Pos _ -> XC (d,One));;  (* différence/comparaison 2 pos *)

let diffbin x y= 
  match (x,y) with 
  | BZ, BZ -> Eq
  | BZ, BP a -> Neg a
  | BP a, BZ -> Pos a
  | BP a, BP b -> diffp a b ;;
  

let t x y= diffp (i2p x) (i2p y);;

t 3 4;;

let mult2b b = 
  match b with
  | BZ -> BZ
  | BP p -> BP (XC (p,Zero));; 

let rec div x d=
  match x with
  |XH -> (match d with 
         | XH -> (BP XH, BZ)
         | _  -> (BZ, BP XH))
  |XC(p, Zero) ->
         let (q,r) = div p d in
         let r'= mult2b r
         in (match diffbin r' (BP d) with
            | Neg _ -> (mult2b q, r') 
            | Eq    -> (addbin (mult2b q) BZ One, BZ)
            | Pos k   -> (addbin (mult2b q) BZ One, BP k))
  |XC(p, One) ->
         let (q,r) = div p d in
         let r'= addbin (mult2b r) BZ One
         in match diffbin r' (BP d) with
            | Neg _   -> (mult2b q, r') 
            | Eq      -> (addbin (mult2b q) BZ One, BZ)
            | Pos k   -> (addbin (mult2b q) BZ One, BP k) ;;

let t x d = div (i2p x) (i2p d) ;;

let b2p x=
  match x with
  | BP a -> a ;;

let rec base x b = 
  let (q,r) = div x b in
  match q with
  | BZ -> [r] 
  | _ -> let l = base (b2p q) b in l@[r] ;;

let bl2i x=
  match x with
  | [ BZ] -> [0]
  | [BP a] -> [p2i a] 
  | [ BP a ; BZ] -> [p2i a ; 0]
  | [ BP a ; BP b] -> [p2i a ; p2i b]
  | [ BP a ; BZ; BZ] -> [p2i a ; 0; 0]
  | [ BP a ; BZ; BP c] -> [p2i a ; 0; p2i c]
  | [ BP a ; BP b; BZ] -> [p2i a ; p2i b; 0]
  | [ BP a ; BP b; BP c] -> [p2i a ; p2i b; p2i c];; 

let t x b= base (i2p x) (i2p b);;

let t2 x b= bl2i (base (i2p x) (i2p b));;

base (XC(XC(XH,Zero),One)) (XC(XH,One)) ;;










