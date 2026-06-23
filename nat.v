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
  
Definition bit2n b :=
  match b with
  | Zero => O
  | One => S O
  end.

Fact div2_spec x : let (q,r) := div2 x in plusn (bit2n r) (multn (S (S O)) q) = x.
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

Require Import Arith Lia.

Fact plusn_multn_S a q : plusn a (multn 2 (S q)) = S (S (plusn a (multn 2 q))).
Proof. simpl; rewrite !plusn_comm_S; trivial. Qed.

Fact div2_invert q r : (q,r) = div2 (plusn (bit2n r) (multn 2 q)).
Proof.
  induction q as [ | q IH ] in r |- *.
  + destruct r; simpl; auto.
  + assert (plusn (bit2n r) (multn 2 (S q)) = S (S (plusn (bit2n r) (multn 2 q)))) as E.
    * lia.
    * rewrite E; unfold div2; fold div2.
      now rewrite <- IH.
Qed.

Fact div2_inv_inj r p s q : plusn (bit2n r) (multn 2 p) = plusn (bit2n s) (multn 2 q) -> r = s /\ p = q.
Proof.
  generalize (div2_invert p r) (div2_invert q s).
  intros E1 E2 H.
  rewrite H in E1.
  rewrite <- E2 in E1.
  now inversion E1.
Qed.

Inductive pos := XH | XC : pos -> bit -> pos.

Inductive bin := BZ | BP : pos -> bin.

Definition addbit a b c := 
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
  | XC q b => plusn (bit2n b) (multn (S( S O)) (p2n q))
  end.
  
Fact p2n_fix q b : p2n (XC q b) = plusn (bit2n b) (multn (S (S O)) (p2n q)).
Proof. trivial. Qed.

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

Require Import Arith Lia.

Inductive n2p_graph : nat -> pos -> Prop :=
  | n2p_g0 n : (O,One) = div2 n -> n2p_graph n XH  
  | n2p_g1 n q r o : (S q,r) = div2 n -> n2p_graph (S q) o -> n2p_graph n (XC o r).
  
Fact n2p_fun n m o1 o2 : n2p_graph n o1 -> n2p_graph m o2 -> n = m -> o1 = o2.
Proof.
  induction 1 as [ n Hn | n p r1 o1 E1 H1 IH1 ] in m, o2 |- *;
    destruct 1 as [ m Hm | m q r2 o2 E2 H2 ]; intros E; auto.
  + subst; now rewrite <- E2 in Hn.
  + subst; now rewrite <- E1 in Hm.
  + subst.
    rewrite <- E2 in E1.
    inversion E1; subst; f_equal.
    apply IH1 with (2 := eq_refl); auto.
Qed.

Definition not_O n := match n with O => False | S _ => True end.

Definition n2p_pwc n : not_O n -> { o | n2p_graph n o }.
Proof.
  induction n as [ n IHn ] using (well_founded_induction lt_wf).
  generalize (div2_spec n).
  case_eq (div2 n); intros q r E H1 H2.
  case_eq q.
  + intros ->; destruct r; simpl in H1; subst.
    * easy.
    * exists XH; now constructor.
  + intros q' Hq'.
    refine (let (o,ho) := IHn q _ _ in exist _ (XC o r) _); subst.
    * lia.
    * exact I.
    * constructor 2 with q'; auto.
Defined.

Require Import Extraction.

Definition n2p n hn := proj1_sig (n2p_pwc n hn).

Fact n2p_spec n hn : n2p_graph n (n2p n hn).
Proof. apply (proj2_sig _). Qed.

Fact n2p_fix_1 h : n2p 1 h = XH.
Proof.
  apply n2p_fun with (1 := n2p_spec _ _) (3 := eq_refl).
  constructor 1; auto.
Qed.

Fact n2p_fix_2 n hn q hq r : (q,r) = div2 n -> n2p n hn = XC (n2p q hq) r.
Proof.
  intros E.
  apply n2p_fun with (1 := n2p_spec _ _) (3 := eq_refl).
  destruct q as [ | q ].
  + destruct hq.
  + constructor 2 with q; auto.
    apply n2p_spec.
Qed.

Fact p2n_not_O p : not_O (p2n p).
Proof.
  induction p as [ | p IHq [] ]; simpl; trivial.
  destruct (p2n p); simpl in *; trivial.
Qed.

Fact p2n_n2p n hn : p2n (n2p n hn) = n.
Proof.
  generalize (n2p n hn) (n2p_spec n hn).
  induction 1 as [ n E | n q r o E H IH ].
  + generalize (div2_spec n).
    rewrite <- E; simpl; auto.
  + generalize (div2_spec n).
    rewrite <- E.
    simpl in IH.
    simpl p2n.
    rewrite IH; trivial.
Qed.

Fact n2p_p2n p hp : n2p (p2n p) hp = p.
Proof.
  induction p as [ | p IH r ].
  + simpl.
    apply n2p_fix_1.
  + revert hp; rewrite p2n_fix; intros hp.
    rewrite n2p_fix_2 with (q := p2n p) (hq := p2n_not_O _) (r := r).
    * f_equal; auto.
    * generalize (p2n p); intros n.
      apply div2_invert.
Qed.

Definition b2n b :=
  match b with
  | BZ   => 0
  | BP p => p2n p
  end.

Definition n2b n :=
  match n with
  | O   => BZ
  | S q => BP (n2p (S q) I)
  end.

Fact b2n_n2b n : b2n (n2b n) = n.
Proof.
  destruct n; simpl; auto.
  apply p2n_n2p.
Qed.

Fact n2b_b2n b : n2b (b2n b) = b.
Proof.
  destruct b; simpl; auto.
  unfold n2b.
  generalize (p2n_not_O p) (n2p_p2n p (p2n_not_O _)).
  destruct (p2n p); simpl.
  + intros [].
  + intros [] <-; trivial.
Qed.

Extraction Inline n2p_pwc.
Recursive Extraction n2b b2n.

(*

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

*)

Definition addpb p b :=
  match b with 
  | Zero => p
  | One  => succp p
  end.

Check addpb.

Fact succp_p2n p : p2n (succp p) = S (p2n p).
Proof.
  induction p as [ | p IH [] ]; simpl; auto.
  now rewrite IH, !plusn_Or, plusn_comm_S; simpl.
Qed.

Fact addpb_p2n p b : p2n (addpb p b) = bit2n b + p2n p.
Proof.
  destruct b; simpl; trivial.
  apply succp_p2n.
Qed.

Fixpoint addp x y c :=
  match (x,y) with
  |(XC p a, XC q b)
    => let (r,s) := addbit a b c in
       let pqr := addp p q r
       in XC pqr  s
  |(XH, XH)
    => let (_,s) := addbit One One c
       in XC XH s 
  |(XC p a, XH)
    => let (r,s) := addbit a One c in
       let pqr := addpb p r 
       in XC pqr s
  |(XH, XC q b)
    => let (r,s) := addbit One b c in 
       let pqr := addpb q r
       in XC pqr s
       end.
       
Fact addp_p2n x y c : p2n (addp x y c) = bit2n c + p2n x + p2n y.
Proof.
  induction x as [ | p IHp a ] in y, c |- *; destruct y as [ | q b ]; simpl.
  + destruct c; simpl; auto.
  + destruct b; destruct c; simpl; auto;
      rewrite !plusn_Or, !succp_p2n, !plusn_comm_S; auto.
  + destruct a; destruct c; simpl; auto;
      rewrite !plusn_Or, (plusn_comm _ 1).
    * easy.
    * rewrite !succp_p2n, !plusn_comm_S; auto.
    * rewrite !succp_p2n, !plusn_comm_S; auto.
    * rewrite !succp_p2n, !plusn_comm_S; auto.
  + case_eq (addbit a b c); intros r s E.
    specialize (IHp q r).
    simpl; rewrite IHp.
    destruct a; destruct b; destruct c; cbv in E; simpl; inversion E; subst; simpl;
      rewrite !plusn_Or; auto.
    all: lia.
Qed.

Definition bit2b x :=
  match x with
  | Zero => BZ
  | One  => BP XH
  end.

Definition addbin x y c :=
  match (x,y) with
  | (BZ, BZ)     => bit2b c 
  | (BZ, BP b)   => BP (addpb b c)
  | (BP a, BZ)   => BP (addpb a c) 
  | (BP a, BP b) => BP (addp a b c)
  end.

Fact addbin_b2n x y c : b2n (addbin x y c) = bit2n c + b2n x + b2n y.
Proof.
  revert x y; intros [ | a ] [ | b ]; simpl.
  + unfold addbin; destruct c; simpl; auto.
  + now rewrite addpb_p2n, plusn_Or.
  + now rewrite addpb_p2n, plusn_Or.
  + now rewrite addp_p2n.
Qed.

Definition addb x y := addbin x y Zero.

Fact addb_b2n x y : b2n (addb x y) = b2n x + b2n y.
Proof. apply (addbin_b2n _ _ Zero). Qed.

Fact b2n_inj x y : b2n x = b2n y -> x = y.
Proof. intros H; now rewrite <- (n2b_b2n x), H, n2b_b2n. Qed.

Fact plusn_n2b n m : n2b (n+m) = addb (n2b n) (n2b m).
Proof.
  apply b2n_inj.
  now rewrite addb_b2n, !b2n_n2b.
Qed.

Definition multbit a b :=
  match a with
  | Zero => Zero
  | One => b 
  end. 

Fixpoint multp x y :=
  match x with
  | XC p Zero => XC (multp p y) Zero
  | XC p One  => addp y (XC (multp p y) Zero) Zero
  | XH        => y
  end.
  
Fact multp_p2n x y : p2n (multp x y) = p2n x * p2n y.
Proof.
  induction x as [ | p IH [] ]; simpl.
  + now rewrite plusn_Or.
  + now rewrite !plusn_Or, IH, !(multn_comm _ (p2n y)), multn_distrib.
  + rewrite addp_p2n; simpl. 
    now rewrite !plusn_Or, IH, !(multn_comm _ (p2n y)), multn_distrib.
Qed.

Definition multb x y :=
  match x, y with 
  |  _ ,  BZ   => BZ
  | BZ ,   _   => BZ
  | BP x ,BP y => BP (multp x y)
  end.
  
Fact multb_b2n x y : b2n (multb x y) = b2n x * b2n y.
Proof.
  revert x y; intros [ | x ] [ | y ]; simpl; auto.
  apply multp_p2n.
Qed.


  
  
  
Eval compute in n2b 1.  

(* test multp en int 
   test : int -> int -> int 
*)
let test x y=
  p2i (multp (i2p x) (i2p y));; 
   











