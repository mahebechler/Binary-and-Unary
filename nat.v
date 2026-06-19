Inductive nat := O : nat | S : nat -> nat.
Check nat.

Fixpoint plusn x y :=
  match x with 
  | O    => y
  | S x' => S (plusn x' y)
  end. 

Check plusn (S O) O.
Eval compute in (plusn (S O) (S O)).

Fact plusn_Ol z : plusn O z = z.
Proof.
  simpl.
  trivial.
Qed.

Fact plusn_Or z : plusn z O = z.
Proof.
  induction z as [ | n IH ].
  + simpl.
    trivial.
  + simpl.
    rewrite IH.
    trivial.
Qed.

Fact plusn_comm_S x y : plusn x (S y) = S (plusn x y).
Proof. 
  induction x as [ | x IH ].
  + simpl; trivial.
  + simpl.
    rewrite IH.
    trivial.
Qed.  

Fact plusn_comm x y : plusn x y = plusn y x.
Proof.
  induction x as [ | x IH ].
  + simpl.
    rewrite plusn_Or.
    trivial.
  + simpl.
    rewrite plusn_comm_S, IH.
    trivial.
Qed.

Fact plusn_assoc x y z : plusn (plusn x y) z = plusn x (plusn y z).
Proof.
  induction x as [ | x IH ].
  + simpl.
    trivial.
  + simpl. rewrite IH.
    trivial.
Qed.

Fixpoint multn x y :=
  match x with 
  | O    => O
  | S x' => plusn y (multn x' y)
  end.

Fact absorb_element_Ol m : multn O m = O.
Proof.
  simpl.
  trivial.
Qed.

Fact absorb_element_Or m : multn m O = O.
Proof.
  induction m as [ | m IH ].
  + simpl.
  trivial.
  + simpl. rewrite IH.
  trivial.
Qed.

Fact neutral_element_Sr m : multn m (S O) = m.
Proof.
  induction m as [ | m IH ].
  + simpl.
  trivial.
  + simpl. rewrite IH.
  trivial.
Qed.

Fact neutral_element_Sl m : multn (S O) m = m.
Proof.
  simpl. 
  rewrite plusn_Or.
  trivial.
Qed.

Fact multn_comm_S x y : multn x (S y) = plusn x (multn x y).
Proof. 
  induction x as [ | x IH ].
  + simpl.
  trivial.
  + simpl.
    rewrite IH, <- !plusn_assoc. 
    rewrite (plusn_comm x).
    trivial.
Qed.

Fact multn_comm x y : multn x y = multn y x.
Proof.
  induction x as [ | x IH ].
  + simpl. 
  rewrite absorb_element_Or.
  trivial.
  + simpl.
  rewrite multn_comm_S.
  rewrite IH.
  trivial.
Qed.

Fact multn_distrib x y z : multn x (plusn y z) = plusn (multn x y) (multn x z).
Proof.
  induction x as [ | x IH ].
  + simpl.
  trivial.
  + simpl.
  rewrite IH.
  rewrite <- !plusn_assoc.
  rewrite (plusn_comm y (multn x y)).
  rewrite (plusn_assoc (multn x y) y z ).
  rewrite (plusn_comm (multn x y) (plusn y z)).
  trivial.
Qed.


Fact multn_assoc x y z : multn (multn x y) z = multn x (multn y z).
Proof.
  induction x as [ | x IH ].
  + simpl.
  trivial.
  + simpl.
  rewrite multn_comm. 
  rewrite multn_distrib.
  rewrite multn_comm.
  rewrite (multn_comm z).
  rewrite IH.
  trivial.
Qed.

Section nat_ind2.

  Variables (P : nat -> Prop)
            (P0 : P O)
            (P1 : P (S O))
            (P2 : forall n, P n -> P (S (S n))).
            
  Fixpoint nat_ind2 n : P n.
  Proof.
    destruct n as [ | [ | n ] ].
    + apply P0.
    + apply P1.
    + apply P2, nat_ind2.
  Qed.

End nat_ind2.

Inductive bit := Zero | One.

Fixpoint div2 x :=
  match x with 
  | O    => (O, Zero)
  | S O => (O, One)
  | S(S n) => let (q, r) := div2 n in (S q, r)
  end.
  
Definition b2n b :=
  match b with
  | Zero => O
  | One => S O
  end.

Fact div2_spec x : let (q,r) := div2 x in plusn ( b2n r) (multn (S (S O)) q) = x.
Proof.
  induction x as [ | | n IH ] using nat_ind2.
  + simpl.
      trivial.
  + simpl.
    trivial.
  + simpl.
    destruct (div2 n) as (q,r).
    simpl.
    simpl in IH.
    rewrite !plusn_comm_S, IH.
    split; trivial.
Qed.

Inductive pos := XH | XC : pos -> bit -> pos.

Inductive bin := BZ | BP : pos -> bin.

Definition addb a b c := 
  match (a, b, c) with
  | (Zero, Zero, Zero) => (Zero, Zero)
  | (Zero, Zero, One) => (Zero, One)
  | (Zero, One, Zero) => (Zero, One)
  | (Zero, One, One) => (One, Zero)
  | (One, Zero, Zero) => (Zero, One)
  | (One, Zero, One) => (One, Zero)
  | (One, One, Zero) => (One, Zero)
  | (One, One, One) => (One, One)
  end.

Fixpoint succp p :=
  match p with 
  |XC q Zero => XC q  One
  |XC q One  => XC (succp q)  Zero
  |XH        => XC XH Zero
  end.
  
Fixpoint p2n p :=
  match p with
  | XH => S O
  | XC q b => plusn (b2n b) (multn (S( S O)) (p2n q))
  end.

Fact succp_spec p : p2n (succp p) = S (p2n p).
Proof.
  induction p as [ | p IHp b ].
  +simpl.
  trivial.
  + simpl.
    destruct b.
    * simpl; trivial.
    * simpl.
      rewrite IHp. 
      rewrite !plusn_Or, !plusn_comm_S.
      simpl.
      trivial.
Qed.

Fixpoint n2p n :=
  let (q, r) := div2 n 
  in match q with
     | O => match r with 
        | Zero => None
        | One => Some XH end
     | S h => Some XC (Some(n2p  q)) r
     end. 


Definition addpb p b :=
  match b with 
  | Zero => p
  | One  => succp p
  end.


Fixpoint addp x y c :=
  match (x,y) with
  |(XC p a, XC q b)
    => let (r,s) := addb a b c in
       let pqr := addp p q r
       in XC pqr  s
  |(XH, XH)
    => let (_,s) := addb One One c
       in XC XH s 
  |(XC p a, XH)
    => let (r,s) := addb a One c in
       let pqr := addpb p r 
       in XC pqr s
  |(XH, XC q b)
    => let (r,s) := addb One b c in 
       let pqr := addpb q r
       in XC pqr s
       end. 

Definition b2b x :=
  match x with
  | Zero => BZ
  | One  => BP XH
  end.

Definition addbin x y c :=
  match (x,y) with
  | (BZ, BZ)     => b2b c 
  | (BZ, BP b)   => BP (addpb b c)
  | (BP a, BZ)   => BP (addpb a c) 
  | (BP a, BP b) => BP (addp a b c)
  end.
  
Fact 







