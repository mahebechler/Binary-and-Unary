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

    rewrite IH.
  simpl.
  trivial.
Qed.