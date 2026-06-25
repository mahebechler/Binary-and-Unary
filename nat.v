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

(* Abbreviation plusn := Nat.add. *)

(*
Check plusn (S O) O.
Eval compute in (plusn (S O) (S O)).
*)

Fact plusn_Ol z : O + z = z.
Proof.
  simpl.
  trivial.
Qed.

Fact plusn_Or z : z + O = z.
Proof.
  induction z as [ | n IH ].
  + simpl.
    trivial.
  + simpl.
    rewrite IH.
    trivial.
Qed.

Fact plusn_comm_S x y : x + (S y) = S (x + y).
Proof. 
  induction x as [ | x IH ].
  + simpl; trivial.
  + simpl.
    rewrite IH.
    trivial.
Qed.  

Fact plusn_comm x y : x + y = y + x.
Proof.
  induction x as [ | x IH ].
  + simpl.
    rewrite plusn_Or.
    trivial.
  + simpl.
    rewrite plusn_comm_S, IH.
    trivial.
Qed.

Fact plusn_assoc x y z : (x + y) + z = x + (y + z).
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
(*
Abbreviation multn := Nat.mul.

Print multn.
*)

Fact absorb_element_Ol m : O*m = O.
Proof.
  simpl.
  trivial.
Qed.

Fact absorb_element_Or m : m*O = O.
Proof.
  induction m as [ | m IH ].
  + simpl.
  trivial.
  + simpl. rewrite IH.
  trivial.
Qed.

Fact neutral_element_Sr m : m*(S O) = m.
Proof.
  induction m as [ | m IH ].
  + simpl.
  trivial.
  + simpl. rewrite IH.
  trivial.
Qed.

Fact neutral_element_Sl m : (S O)*m = m.
Proof.
  simpl. 
  rewrite plusn_Or.
  trivial.
Qed.

Fact multn_comm_S x y : x*(S y) = x+(x*y).
Proof. 
  induction x as [ | x IH ].
  + simpl.
  trivial.
  + simpl.
    rewrite IH, <- !plusn_assoc. 
    rewrite (plusn_comm x).
    trivial.
Qed.

Fact multn_comm x y : x*y = y*x.
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

Fact multn_distrib x y z : x*(y+z) = x*y+x*z.
Proof.
  induction x as [ | x IH ].
  + simpl.
  trivial.
  + simpl.
  rewrite IH.
  rewrite <- !plusn_assoc.
  rewrite (plusn_comm y (x*y)).
  rewrite (plusn_assoc (x*y) y z ).
  rewrite (plusn_comm (x*y) (y+z)).
  trivial.
Qed.

Fact multn_assoc x y z : (x*y)*z = x*(y*z).
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

Fact div2_spec x : let (q,r) := div2 x in (bit2n r)+2*q = x.
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

Fact plusn_multn_S a q : a+2*(S q) = S (S (a+2*q)).
Proof. simpl; rewrite !plusn_comm_S; trivial. Qed.

Fact div2_invert q r : (q,r) = div2 (bit2n r + 2*q).
Proof.
  induction q as [ | q IH ] in r |- *.
  + destruct r; simpl; auto.
  + assert (bit2n r+2*(S q) = S (S (bit2n r+2*q))) as E.
    * lia.
    * rewrite E; unfold div2; fold div2.
      now rewrite <- IH.
Qed.

Fact div2_inv_inj r p s q : bit2n r+2*p = bit2n s+2*q -> r = s /\ p = q.
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
  | XH => 1
  | XC q b => bit2n b+2*(p2n q)
  end.
  
Fact p2n_fix q b : p2n (XC q b) = bit2n b+2*(p2n q).
Proof. trivial. Qed.

Fact p2n_gt_0 p : 0 < p2n p.
Proof. induction p; simpl; lia. Qed.

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

Inductive diff :=
  | Neg : pos -> diff
  | Eq : diff
  | Pos : pos -> diff.

Definition diffbit a b :=
  match a, b with
  | One, Zero => Pos XH
  | Zero, One => Neg XH
  | _, _      => Eq
  end.
  
Fact diffbit_bit2n a b :
  match diffbit a b with
  | Neg d => S (bit2n a) = bit2n b /\ d = XH
  | Eq    => a = b
  | Pos d => bit2n a = S (bit2n b) /\ d = XH
  end.
Proof.
  revert a b; intros [] []; now simpl.
Qed.

Definition not_XH p :=
  match p with
  | XH => False
  | _ => True
  end.

Fixpoint predp p : not_XH p -> pos.
Proof.
  refine (match p return not_XH p -> pos with
  | XH => fun C => match C with end
  | XC d Zero => fun _ =>
    match d as d' return d = d' -> pos with
    | XH     => fun _ => XH
    | XC e b => fun E => XC (predp d _) One
    end eq_refl
  | XC d One  => fun _ => XC d Zero
  end).
  now subst.
Defined.

Fact predp_fix_0 h : predp (XC XH Zero) h = XH.
Proof. reflexivity. Qed.

Fact predp_fix_1 p h : predp (XC p One) h = XC p Zero.
Proof. reflexivity. Qed.

Fact True_pirr (A B : True) : A = B.
Proof. revert A B; now intros [] []. Qed.

Fact predp_fix_2 p h hp : predp (XC p Zero) h = XC (predp p hp) One.
Proof.
  simpl.
  destruct p.
  * easy.
  * do 2 f_equal.
    apply True_pirr.
Qed. 

Fact predp_p2n p hp : S (p2n (predp p hp)) = p2n p.
Proof.
  induction p as [ | d IH [] ].
  + easy.
  + destruct d as [ | d b ]. 
    * rewrite predp_fix_0; now simpl.
    * rewrite predp_fix_2 with (p := XC _ _) (hp := I), p2n_fix.
      simpl bit2n; unfold plus.
      rewrite p2n_fix, <- (IH I); simpl; lia.
  + rewrite predp_fix_1; simpl; auto.
Qed.

Opaque predp.

(*

Inductive predp_graph : pos -> pos -> Prop :=
| predpg_0 : predp_graph (XC XH Zero) XH
| predpg_1 d : predp_graph (XC d One) (XC d Zero)
| predpg_2 d o : not_XH d -> predp_graph d o -> predp_graph (XC d Zero) (XC o One).

Fact predp_fun p r q s : predp_graph p r -> predp_graph q s -> p = q -> r = s.
Proof.
  induction 1 as [ | p | p r Hp H1 IH1 ] in q, s |- *;
    destruct 1 as [ | q | q s Hq H2 ]; auto; try discriminate.
  + inversion 1; now subst.
  + now inversion 1.
  + inversion 1; now subst.
  + inversion 1; f_equal; eauto.
Qed.

Definition predp_pwc p : not_XH p -> { o | predp_graph p o }.
Proof.
  induction p as [ | p IH [] ].
  + intros [].
  + intros _.
    destruct p as [ | p b ].
    * exists XH; constructor.
    * destruct IH as (o & Ho); simpl; auto.
      exists (XC o One); constructor; simpl; auto.
  + intros _; exists (XC p Zero); constructor.
Qed.

Definition predp p hp := proj1_sig (predp_pwc p hp).

Fact predp_spec p hp : predp_graph p (predp p hp).
Proof. apply (proj2_sig _). Qed.

Fact predp_fix_0 h : predp (XC XH Zero) h = XH.
Proof. apply predp_fun with (1 := predp_spec _ _) (3 := eq_refl); constructor. Qed.

Fact predp_fix_1 p h : predp (XC p One) h = XC p Zero.
Proof. apply predp_fun with (1 := predp_spec _ _) (3 := eq_refl); constructor. Qed.

Fact predp_fix_2 p h hp : predp (XC p Zero) h = XC (predp p hp) One.
Proof.
  apply predp_fun with (1 := predp_spec _ _) (3 := eq_refl).
  constructor; simpl; auto; apply predp_spec.
Qed.

Fact predp_p2n p hp : S (p2n (predp p hp)) = p2n p.
Proof.
  generalize (predp p hp) (predp_spec p hp).
  induction 1 as [ | | d o Hd H IH ].
  + now simpl.
  + now simpl.
  + simpl.
    rewrite <- IH, <- !plusn_comm_S; auto.
    rewrite plusn_Or, (plusn_comm _ 2); simpl.
    now rewrite plusn_comm_S.
Qed.

*)

Fixpoint diffp p q :=
  match p, q with
  | XH, XH => Eq
  | _ as p', XH  => Pos (predp p' I)
  | XH, _  as q' => Neg (predp q' I)
  | XC p a, XC q b =>
    match diffp p q with
    | Neg d => Neg (match diffbit b a with
               | Neg _ => predp (XC d Zero) I
               | Eq    => XC d Zero
               | Pos _ => XC d One
               end)
    | Eq => diffbit a b
    | Pos d => Pos (match diffbit a b with
               | Neg _ => predp (XC d Zero) I
               | Eq    => XC d Zero
               | Pos _ => XC d One
               end)
    end
  end.

Fact diffp_p2n p q :
  match diffp p q with
  | Neg d => p2n d + p2n p = p2n q
  | Eq    => p = q
  | Pos d => p2n p = p2n d + p2n q
  end.
Proof.
  induction p as [ | p IH a ] in q |- *; destruct q as [ | q b ]; auto.
  + now simpl.
  + rewrite p2n_fix; simpl diffp; cbv iota.
    simpl p2n.
    rewrite (plusn_comm _ 1); simpl plus at 1.
    rewrite predp_p2n; auto.
  + rewrite p2n_fix; simpl diffp; cbv iota. 
    simpl p2n.
    rewrite (plusn_comm _ 1); simpl.
    rewrite predp_p2n; simpl; auto.
  + specialize (IH q).
    rewrite p2n_fix; simpl diffp; cbv iota.
    destruct (diffp p q) as [ d1 | | d1 ].
    * generalize (diffbit_bit2n b a); intros E.
      destruct (diffbit b a).
      - apply Nat.succ_inj.
        rewrite  <- Nat.add_succ_l, predp_p2n.
        rewrite !p2n_fix.
        simpl bit2n; lia.
      - subst.
        rewrite !p2n_fix; simpl; lia.
      - rewrite !p2n_fix; simpl; lia.
    * subst q.
      rewrite p2n_fix.
      generalize (diffbit_bit2n a b); intros E.
      destruct (diffbit a b) as [ d | | d ]; subst; auto.
      - destruct E; subst; simpl; lia.
      - destruct E; subst; simpl; lia.
    * generalize (diffbit_bit2n a b); intros E.
      destruct (diffbit a b).
      - apply Nat.succ_inj.
        rewrite  <- (Nat.add_succ_l (p2n _)), predp_p2n.
        rewrite !p2n_fix.
        simpl bit2n; lia.
      - subst.
        rewrite !p2n_fix; simpl; lia.
      - rewrite !p2n_fix; simpl; lia.
Qed.

Definition diffb x y :=
  match x, y with
  | BZ, BZ     => Eq
  | BZ, BP q   => Neg q
  | BP p, BZ   => Pos p
  | BP p, BP q => diffp p q
  end.

Fact diffb_b2n x y :
  match diffb x y with
  | Neg d => p2n d + b2n x = b2n y
  | Eq    => x = y
  | Pos d => b2n x = p2n d + b2n y
  end.
Proof.
  revert x y; intros [ | p ] [ | q ]; simpl; auto.
  generalize (diffp_p2n p q); destruct (diffp p q); intros; subst; auto.
Qed.

Definition doubleb x :=
  match x with
  | BZ   => BZ
  | BP p => BP (XC p Zero)
  end.
  
Fact doubleb_b2n x : b2n (doubleb x) = 2*b2n x.
Proof. now destruct x. Qed.

Fixpoint divp x d :=
  match x with
  | XH => match d with
          | XH => (BP XH, BZ)
          | _  => (BZ, BP XH)
          end
  | XC p Zero =>
          let (q,r) := divp p d in
          let r' := doubleb r in
          let q' := doubleb q in
          match diffb r' (BP d) with
          | Neg _ => (q', r')
          | Eq    => (addb q' (BP XH),BZ)
          | Pos k => (addb q' (BP XH),BP k)
          end
  | XC p One =>
          let (q,r) := divp p d in
          let r' := addb (BP XH) (doubleb r) in
          let q' := doubleb q in
          match diffb r' (BP d) with
          | Neg _ => (q', r')
          | Eq    => (addb q' (BP XH),BZ)
          | Pos k => (addb q' (BP XH),BP k)
          end
  end.

Fact divp_spec x d : let (q,r) := divp x d in p2n x = b2n q*p2n d + b2n r /\ b2n r < p2n d.
Proof.
  induction x as [ | p IH [] ]; simpl.
  + destruct d; split; simpl; auto.
    generalize (p2n_gt_0 d); lia. 
  + destruct (divp p d) as (q,r).
    generalize (diffb_b2n (doubleb r) (BP d)).
    destruct IH as [ IH1 IH2 ].
    destruct (diffb (doubleb r) (BP d)) as [ k | | k ]; intros E; split.
    * rewrite plusn_Or, !doubleb_b2n.
      rewrite multn_assoc, <- multn_distrib, <- IH1.
      simpl; now rewrite plusn_Or.
    * rewrite doubleb_b2n in E |- *; simpl b2n in E.
      generalize (p2n_gt_0 k); lia.
    * rewrite plusn_Or, addb_b2n, doubleb_b2n.
      apply f_equal with (f := b2n) in E.
      rewrite doubleb_b2n in E.
      simpl b2n at 2 in E.
      rewrite (multn_comm _ (p2n _)), multn_distrib.
      rewrite !(multn_comm (p2n _)). 
      rewrite <- E at 2.
      simpl.
      rewrite !plusn_Or.
      rewrite IH1; lia.
    * apply p2n_gt_0.
    * rewrite plusn_Or, addb_b2n, doubleb_b2n.
      rewrite doubleb_b2n in E; simpl in E.
      simpl b2n.
      lia.
    * rewrite doubleb_b2n in E; simpl b2n in E |- *; lia.
  + destruct (divp p d) as (q,r).
    generalize (diffb_b2n (addb (BP XH) (doubleb r)) (BP d)).
    destruct IH as [ IH1 IH2 ].
    destruct (diffb (addb (BP XH) (doubleb r)) (BP d)) as [ k | | k ]; intros E; split.
    * rewrite plusn_Or, !doubleb_b2n.
      rewrite addb_b2n in E |- *.
      simpl b2n in E |- *.
      rewrite doubleb_b2n; lia.
    * rewrite addb_b2n, doubleb_b2n in E |- *; simpl b2n in E |- *.
      generalize (p2n_gt_0 k); lia.
    * rewrite plusn_Or, addb_b2n, doubleb_b2n.
      apply f_equal with (f := b2n) in E.
      rewrite addb_b2n, doubleb_b2n in E.
      simpl b2n in E |- *.
      lia.
    * apply p2n_gt_0.
    * rewrite plusn_Or, addb_b2n, doubleb_b2n.
      rewrite addb_b2n, doubleb_b2n in E.
      simpl b2n in E |- *.
      lia.
    * rewrite addb_b2n, doubleb_b2n in E; simpl b2n in E |- *; lia.
Qed.

Definition divb x d :=
  match x with
  | BZ   => (BZ,BZ)
  | BP x => divp x d
  end.
  
Fact divb_spec x d : let (q,r) := divb x d in b2n x = b2n q*p2n d + b2n r /\ b2n r < p2n d.
Proof.
  destruct x as [ | x ]; simpl.
  + split; auto; apply p2n_gt_0.
  + apply divp_spec.
Qed.

Recursive Extraction divb.

(* test multp en int 
   test : int -> int -> int 
*)
let test x y=
  p2i (multp (i2p x) (i2p y));; 
   











