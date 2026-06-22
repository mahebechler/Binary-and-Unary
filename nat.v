(* Inductive nat := O : nat | S : nat -> nat. *)
Check nat.

(*
Fixpoint plusn x y :=
  match x with 
  | O    => y
  | S x' => S (plusn x' y)
  end. 
  *)
  
Print Nat.add.

Abbreviation plusn := Nat.add.

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

(*
Fixpoint multn x y :=
  match x with 
  | O    => O
  | S x' => plusn y (multn x' y)
  end.
*)

Abbreviation multn := Nat.mul.

Print multn.

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

Fact lien_mult_add_2 n : plusn n n = multn n 2.
  induction n as [ | n IH ].
   + trivial.
   + simpl. rewrite plusn_comm_S, IH.
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
  | XH  => S O
  | XC q b => plus (b2n b) (mult (S (S O))  (p2n q)) 
  end.

Fact p2n_n n :
p2n n = match n with
  | XH  => S O
  | XC q b => plus (b2n b) (mult (S (S O))  (p2n q)) 
  end.
Proof. 



Fact p2n_not_O p :
  match p2n p with
  | O => False
  | S _ => True
  end.
Proof.
  induction p as [ | q IH b ].
  + now simpl.
  + simpl.
    destruct b.
    * simpl.
      destruct (p2n q).
      - easy.
      - simpl. easy.
   * simpl. easy.
Qed.

 Definition Sp2n p :=
  match p with
  | None => O
  | Some x => p2n x
  end.

Fact Sp2n_n n :
Sp2n n = match n with
  | None => O
  | Some x => p2n x
  end.
Proof.
unfold Sp2n at 1.
easy.
Qed.

(* Fixpoint p2n p :=
  match p with
  | None => O
  | Some XH => S O
  | Some (XC q b) => match p2n (Some (XC q b)) with
     | O => O
     | x => plusn (b2n b) (multn (S( S O)) x)
     end
  end. *)

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

Require Import Arith.

Check lt_wf.

Fixpoint n2p_fuel n c :=
  match c with
  | O    => None
  | S c' => let (q, r) := div2 n in
     match q with
     | O =>
        match r with 
        | Zero => None
        | One => Some XH
        end
     | S _ => match n2p_fuel q c' with
              | None   => None
              | Some p => Some (XC p r)
              end
     end
   end.

Definition n2p n := n2p_fuel n (S n).

Fact div2_lt n : let (q,r) := div2 n in q = 0 \/ q < n.
Proof.
  induction n as [ | | n IHn ] using nat_ind2; simpl.
  + now left.
  + now left.
  + destruct (div2 n) as (q,r).
    destruct IHn as [ IHn | IHn ].
    * subst.
      right.
      red.
      do 2 apply le_n_S.
      apply le_0_n.
    * right.
      apply le_n_S.
      apply Nat.le_trans with (1 := IHn).
      apply Nat.le_succ_diag_r.
Qed.

Fact n2p_O : n2p O = None.
Proof.
  unfold n2p; simpl.
  trivial.
Qed.

Fact n2p_SO : n2p (S O) = Some XH.
Proof. trivial. Qed.

Require Import Lia.

Fact n2p_fuel_S_Some n c :
  S n < c ->
  match n2p_fuel (S n) c with
  | Some _ => True
  | None => False
  end.
Proof.
  induction c as [ | c IHc ] in n |- *.
  + lia.
  + intros Hnc.
    unfold n2p_fuel; fold n2p_fuel.
    generalize (div2_spec (S n)).
    intros Hn.
    destruct (div2 (S n)) as (q,r).
    destruct q as [ | q ].
    * destruct r.
      - simpl in Hn.
        discriminate.
      - trivial.
    * specialize (IHc q).
      destruct (n2p_fuel (S q) c).
      - trivial.
      - apply IHc.
        apply le_S_n.
        apply Nat.le_trans with (2 := Hnc).
        apply le_n_S.
        rewrite <- Hn.
        lia.
Qed.

Fact n2p_Some n c d : 
  match n2p_fuel n c, n2p_fuel n d with 
  | Some r1, Some r2 => r1 = r2
  | _, _ => True
  end.
Proof.
  induction c as [ | c IHc ] in n, d |- *.
  + simpl; trivial.
  + destruct d as [ | d ].
    * simpl n2p_fuel at 2.
      destruct (n2p_fuel n (S c)); trivial.
    * simpl.
      destruct (div2 n) as (q,r).
      destruct q as [ | q ].
      - destruct r; trivial.
      - specialize (IHc (S q) d).
        destruct (n2p_fuel (S q) c); trivial.
        destruct (n2p_fuel (S q) d); trivial.
        now subst.
Qed.

Fact n2p_n n :
  n2p n = let (q,r) := div2 n in
  match q with
  | O =>
    match r with 
    | Zero => None
    | One => Some XH
    end
  | S _ =>
    match n2p q with
    | None   => None
    | Some p => Some (XC p r)
    end
  end.
Proof.
  unfold n2p at 1.
  simpl.
  generalize (div2_lt n).
  intros Hn.
  destruct (div2 n) as (q,r).
  destruct q as [ | q ].
  + trivial.
  + unfold n2p.
    destruct Hn as [ Hn | Hn ].
    * discriminate.
    * generalize (n2p_Some (S q) n (S (S q)))
                 (n2p_fuel_S_Some q n Hn)
                 (n2p_fuel_S_Some q (S (S q))).
      intros H1 H2 H3.
      destruct (n2p_fuel (S q) n);
      destruct (n2p_fuel (S q) (S (S q))).
      - intros; subst; auto.
      - exfalso.
        lia.
      - destruct H2.
      - destruct H2.
Qed. 

Check n2p_O.
Check n2p_SO.
Check n2p_n.

Opaque n2p.

Fact div2_invert_injective r s p q : plusn (b2n r) (multn 2 p) = plusn (b2n s) (multn 2 q) -> r = s /\ p = q.
Admitted.

Fact div2_invert q r : (q,r) = div2 (plusn (b2n r) (multn 2 q)).
Proof.
  induction q as [ | q IH ] in r |- *.
  + destruct r; simpl; auto.
  + assert (plusn (b2n r) (multn 2 (S q)) = S (S (plusn (b2n r) (multn 2 q)))) as E.
    * simpl. rewrite !plusn_comm_S. trivial. 
    * rewrite E; unfold div2; fold div2.
      now rewrite <- IH.
Qed.


Fact inverse_n2p_p2n x : n2p (Sp2n x) = x.
Proof.
  destruct x as [ p | ].
  - induction p as [ | x' IH q].
    + simpl. apply n2p_SO.
    + simpl. rewrite n2p_n.
    rewrite plusn_Or.
    rewrite lien_mult_add_2.
    rewrite multn_comm.
    rewrite <- div2_invert. simpl in IH. rewrite IH. generalize (p2n_not_O x'). destruct (p2n x').
      * easy.
      * trivial.
  - simpl. apply n2p_O.
Qed.

Fact inverse_p2n_n2p x : Sp2n (n2p x) = x.
Proof.
  destruct x.
  + easy.
  + induction x as [ | x' IH ].
    * easy.
    * rewrite Sp2n_n. rewrite Sp2n_n in IH. 



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








