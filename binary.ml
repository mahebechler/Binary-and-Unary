let rec fib n = if n <= 1 then 1 else fib (n-1)+fib (n-2);;

type nat = O | S : nat -> nat;;

let rec plus a b =
  match a with
  | O    -> b
  | S a' -> S (plus a' b);;
  
let rec i2n i =
  if i = 0 then O else S (i2n (i-1));;
  
let rec n2i a =
  match a with
  | O    -> 0
  | S a' -> 1+(n2i a');;
  
let rec mult a b =
  match a with
  | O    -> O
  | S a' -> plus b (mult a' b);;

let rec exp b a =
  match a with
  | O    -> S O
  | S a' -> mult b (exp b a');;
  
n2i(exp (i2n 2) (i2n 10));;

type bit = Zero | One;;
type pos = XH : pos | XC : pos * bit -> pos;;

let b2n b =
  match b with
  | Zero  -> O
  | One  -> S O;;
  
let rec p2n p=
  match p with
  | XH  -> S O
  | XC (q,b) -> plus (b2n b) (mult (S (S O))  (p2n q)) ;;

p2n (XC(XH,One));;

let rec div2 a=
  match a with
  | O -> (O,Zero)
  | S O -> (O,One)
  | S(S n)  -> let (q, r) = div2 n in (S q, r);;

let t n=
  let (q, r) = div2 (i2n n) in (n2i q, r);;

let rec n2p n=
  let (q, r) = div2 n 
  in match q with
     | O -> (match r with One -> XH)
     | S h -> XC (n2p q, r);;
     
let t n=
  n2p (i2n n);;
  
t 1023;;

type bin = BZ | BP : pos -> bin;;

let n2b n=
  match n with 
  | O -> BZ
  | S _ -> BP (n2p n);;

let b2n b=
  match b with
  | BZ -> O
  | BP p -> p2n p;; 

n2b (i2n 3)







