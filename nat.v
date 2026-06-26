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

Fact plusn_succ n : S n = plus n 1.
Proof.
  induction n as [ |  n IH ].
  + trivial.
  + rewrite plusn_comm_S, plusn_Or.
  trivial.
Qed.

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
Proof.
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

Fact div2_Sn_not_O n :
match div2 (S n) with
  | (0,Zero) => False
  | (_,_) => True
  end.
Proof.
simpl.
  induction n as [ | n IH ].
  + easy.
  + destruct div2. easy.
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

Fact p2n_n n :
p2n n = match n with
  | XH  => S O
  | XC q b => plus (b2n b) (mult (S (S O))  (p2n q)) 
  end.
Proof.
 destruct n.
  + trivial.
  + simpl.
  trivial.
Qed.

Fact Sp2n_n p :
Sp2n p = match p with
  | None => O
  | Some XH  => S O
  | Some (XC q b) => plus (b2n b) (mult (S (S O))  (p2n q)) 
  end.
Proof.
destruct p.
  +  induction p as [ | q IH b ].
     * trivial.
     * trivial.
  + trivial.
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

Section div2_ind.

  Variables (P : nat -> Prop)
            (HP0 : P 0)
            (HP1 : P 1)
            (HPn : forall n, (let (q,r) := div2 n in P q) -> P n).
            
  Fact div2_ind n : P n.
  Proof.
    induction n as [ n IH ] using (well_founded_induction lt_wf).
    generalize (div2_lt n) (div2_spec n).
    case_eq (div2 n).
    intros q r E [ H1 | H1 ] H2.
    + destruct r.
      * subst; simpl in *; apply HP0.
      * subst; simpl in *; apply HP1.
    + apply HPn.
      rewrite E.
      now apply IH.
  Qed.
  
End div2_ind.

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

From Stdlib Require Import Arith Lia.

Fact n2p_NO n : n2p n = None -> n = O.
Proof.
  induction n as [ | | n IH ] using div2_ind; rewrite n2p_n.
  + now simpl.
  + discriminate.
  + generalize (div2_spec n).
    destruct (div2 n) as (q,r).
    case_eq q.
    * intros H1 H2.
      destruct r.
      - simpl in H2; now subst.
      - discriminate.
    * intros q' Hq.
      rewrite <- Hq.
      destruct (n2p q).
      - discriminate.
      - rewrite IH in Hq; trivial.
        discriminate.
Qed.

Fact n2p_Sn_not_O n :
match n2p (S n) with 
  | None => False
  | Some n => True
  end.
Proof.
  generalize (n2p_NO (S n)).
  destruct (n2p (S n)).
  + trivial.
  + intros C.
    assert (S n = O) as D.
    * apply C.
      trivial.
    * discriminate.
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
  induction x as [ | | x IH ] using div2_ind; rewrite n2p_n.
  + now simpl.
  + now simpl.
  + generalize (div2_spec x).
    destruct (div2 x) as (q,r).
    intros H2.
    case_eq q.
    * intros Hq.
      destruct r; subst; simpl in *; trivial.
    * intros q' Hq.
      rewrite <- Hq.
      destruct (n2p q).
      - simpl in *; lia.
      - subst; simpl in *; discriminate.
Qed.

Definition addpb p b :=
  match b with 
  | Zero => p
  | One  => succp p
  end.

Fact addbp_p2n p b : p2n (addpb p b) = p2n p + b2n b.
Proof.
induction p as [ | p IH q].
  + destruct b.
    * now simpl.
    * now simpl.
  + destruct b.
    * simpl. lia.
    * simpl. generalize (succp_spec p). destruct (succp p).
      - intros H1. destruct q.
        ++ simpl. lia.
        ++ simpl. simpl in H1. lia.
      - intros H1. destruct q.
        ++ simpl. lia.
        ++ simpl. simpl in H1. lia.
Qed.

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

Fact addp_p2n x y c : p2n ( addp x y c ) = p2n x + p2n y + b2n c.
Proof.
    induction x as [ | x IHx ] in y, c |- *.
    + simpl. destruct y; simpl.
      * destruct c. 
        - now simpl.
        - now simpl.
      * destruct c; destruct b; simpl; simpl; try rewrite succp_spec; lia.
    + simpl. destruct y; simpl.
      * destruct c ; destruct b; simpl; try rewrite succp_spec; lia.
      * destruct b; destruct b0 ; destruct c; simpl; rewrite IHx; simpl; lia. 
Qed.

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

Definition multb a b :=
  match a with
  | Zero => Zero
  | One => b 
  end.

Fixpoint multp x y :=
  match x with
  | XC p Zero  => XC ( multp p y )  Zero
  | XC p  One  => addp y (XC (multp p y) Zero)  Zero 
  | XH         => y 
  end. 

Fact multp_p2n x y : p2n (multp x y) = p2n x * p2n y.
Proof.
induction x as [ | x IH ] in y |- *.
  + destruct y.
    * trivial.
    * easy.
  + destruct y.
    * destruct b; simpl; try rewrite IH; simpl; lia.
    * destruct b; destruct b0.
       -  simpl; try rewrite IH. simpl. lia.
       -  simpl; try rewrite IH. simpl. lia.
       - simpl. rewrite addp_p2n. rewrite  IH. simpl. lia.
       - simpl. rewrite addp_p2n. rewrite  IH. simpl. lia.
Qed.

Inductive diff := Neg : pos -> diff | Eq | Pos : pos -> diff.

Definition diffb a b :=
  match (a, b) with
  | (One, Zero)  => Pos XH
  | (Zero, One) => Neg XH
  | (_, _)      => Eq
  end.

Definition d2n n :=
  match n with
  | Pos n => match n with
                | XH  => S O
                | XC q b => plus (b2n b) (mult (S (S O))  (p2n q))
                end
  | Neg n => match n with
                | XH  => S O
                | XC q b => plus (b2n b) (mult (S (S O))  (p2n q))
                end
  | Eq => O
  end.

Print Nat.sub.

Fixpoint subn n m :=
    match n with
  | 0 => m
  | S k => match m with
           | 0 => n
           | S l => subn k l
           end
  end.

Fact diffb'_b2n a b : d2n (diffb a b) = subn (b2n a) (b2n b).
Proof.
  destruct a.
   + destruct b.
     * now simpl.
     * now simpl.
   + destruct b.
     * now simpl.
     * now simpl.
Qed.

Fact diffb_b2n a b :
  match diffb a b with
  | Neg d => S (b2n a) = b2n b /\ d = XH
  | Eq    => a = b
  | Pos d => b2n a = S (b2n b) /\ d = XH
  end.
Proof.
  destruct a;  destruct b ;now simpl.
Qed.

Print diffb_b2n.

Definition not_XH p :=
  match p with
  | XH => False
  | _  => True
  end.

Fixpoint predp p : not_XH p -> pos.
Proof.
  case_eq p.
  + intros; simpl.
    exfalso.
    easy.
  + intros d [] Hp _.
    * case_eq d.
      - intros Hd.
        exact XH.
      - intros q b Hd.
        apply XC.
        ++ apply (predp d).
           rewrite Hd.
           simpl; trivial.
        ++ exact One.
    * exact (XC d Zero).
Defined.

Fact predp_p2n p hp : S (p2n (predp p hp)) = p2n p.
Proof.
  induction p as [ | d IH [] ]; simpl.
  + simpl in hp; easy.
  + destruct d as [ | q b ].
    * simpl; trivial.
    * rewrite p2n_n.
      specialize (IH (@eq_ind_r _ (XC _ _) (fun d => not_XH d) I _ eq_refl)).
      rewrite <- IH.
      simpl b2n; lia.
  + trivial.
Qed.

Require Import Extraction.
     

Fixpoint predp' x :=
  match x with
  | ( XC d One )  => Some ( XC d Zero )
  | ( XC XH Zero) => Some XH
  | ( XC d Zero ) => match predp' d with 
                         | Some p => Some ( XC p Zero )
                         | None => None 
                         end
  |   XH          => None
  end.
  
Recursive Extraction predp predp'.

Fixpoint diffp x y :=
  match x, y with
  | XH, XH               => Eq
  | XC _ _ as x', XH     => Pos (predp x' I)
  | XH, XC _ _ as y'     => Neg (predp y' I)
  | XC p a, XC q b =>
        match diffp p q with
        | Neg d => Neg match diffb b a with
                      | Neg _ => predp (XC d Zero) I
                      | Eq    => XC d Zero
                      | Pos _ => XC d One
                       end
        | Eq    => diffb a b
        | Pos d => Pos match diffb a b with
                      | Neg _ => predp (XC d Zero) I
                      | Eq    => XC d Zero
                      | Pos _ => XC d One
                      end
         end
  end.
  
Opaque predp.

Fact diffp_p2n x y :
  match diffp x y with
  | Neg d => p2n d + p2n x = p2n y
  | Eq => x = y
  | Pos d => p2n x = p2n d + p2n y
  end.
Proof.
  induction x as [ | x IH q ] in y |-*.
    + case_eq y.
      * easy.
      * intros p b IHy. 
        simpl.
        rewrite plusn_comm.
        simpl.
        rewrite predp_p2n.
        simpl. trivial.
    + case_eq y.
      * simpl. rewrite (plusn_comm (p2n (predp (XC x q) I)) 1).
        simpl.
        rewrite predp_p2n.
        simpl. trivial.
      * simpl. 
        intros p b IHy.
        destruct diffp.
          -   generalize (diffb_b2n b q). destruct (diffb b q).
            ++ intros [ H1 H2 ]. rewrite <- H1. simpl. rewrite plusn_comm_S. admit.
            ++ intros H1. simpl. rewrite H1. 
Admitted.







