From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism. 
From Coq Require Import Unicode.Utf8.

Inductive IdentityF2_u: Type :=
  | ValF2_u: @uPack (@uPack (Z ::UT nilUT) Z ::UT (Z ::UT nilUT)) Z → IdentityF2_u.

Fixpoint IdentityF2_wf (x : IdentityF2_u): Type :=
  match x with
  | ValF2_u lq_tmp0 => let argTps :=
                       @Pack
                       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
                       (Z ::UT nilUT)
                       ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
                       Z
                       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                          (v_x_86795196 : Z),
                        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196))
                       ::RT λ (lq_tmp0 : @Pack
                                         ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
                                         (Z ::UT nilUT)
                                         ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
                                         Z
                                         (λ (x_86795196 : ArgList ({lq_tmp1: Z | True}
                                                                   ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                                            (v_x_86795196 : Z),
                                          ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196))),
                            {lq_tmp3: Z | True} ::RT λ (lq_tmp3 : {lq_tmp3: Z | True}), nilRT in
                       let p : forall (args: ArgList argTps), _ -> Prop :=
                       λ (x_83955502 : ArgList (@Pack
                                                ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
                                                (Z ::UT nilUT)
                                                ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
                                                Z
                                                (λ (x_86795196 : ArgList ({lq_tmp1: Z | True}
                                                                          ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}),
                                                                               nilRT))
                                                   (v_x_86795196 : Z),
                                                 ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196))
                                                ::RT λ (lq_tmp0 : @Pack
                                                                  ({lq_tmp1: Z | True}
                                                                   ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
                                                                  (Z ::UT nilUT)
                                                                  ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
                                                                  Z
                                                                  (λ (x_86795196 : ArgList ({lq_tmp1: Z | True}
                                                                                            ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}),
                                                                                                 nilRT))
                                                                     (v_x_86795196 : Z),
                                                                   ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196))),
                                                     {lq_tmp3: Z | True} ::RT λ (lq_tmp3 : {lq_tmp3: Z | True}), nilRT))
                         (v_x_83955502 : Z),
                       ltac:(flattenP (λ (lq_tmp0 : @Pack
              ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
              Z
              (λ (x_86795196 : ArgList ({lq_tmp1: Z | True}
                                        ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                 (v_x_86795196 : Z),
               ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
   (lq_tmp3 : {lq_tmp3: Z | True})
   (VV : Z),
 True) x_83955502 v_x_83955502) in
                       let z: projectsArgListT argTps (@uPack (Z ::UT nilUT) Z ::UT (Z ::UT nilUT)) :=
                       ltac:(mkProjectsArgListTG (argTps) ((@uPack (Z ::UT nilUT) Z ::UT (Z ::UT nilUT)))) in
                       uPack_wf argTps z p lq_tmp0
  end.

Theorem IdentityF2_wf_ref
  [p : IdentityF2_u → Prop] (tm : sigT (fun v: IdentityF2_u => {_:IdentityF2_wf v | p v})):
  IdentityF2_wf ⌊- tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation IdentityF2 := (sigT (fun x: IdentityF2_u => IdentityF2_wf x)).

Definition ValF2_lem
  (lq_tmp0 : @Pack
             (@Pack
              ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
              Z
              (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                 (v_x_40877513 : Z),
               ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
              ::RT λ (lq_tmp0 : @Pack
                                ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                (Z ::UT nilUT)
                                ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
                                Z
                                (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                                   (v_x_40877513 : Z),
                                 ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
                   {VV: Z | True} ::RT λ (lq_tmp3 : {VV: Z | True}), nilRT)
             (@uPack (Z ::UT nilUT) Z ::UT (Z ::UT nilUT))
             ltac:(mkProjectsArgListTG (@Pack
 ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
 (Z ::UT nilUT)
 ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
 Z
 (λ (x_40877513 : ArgList ({VV: Z | True}
                           ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
    (v_x_40877513 : Z),
  ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
 ::RT λ (lq_tmp0 : @Pack
                   ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                   (Z ::UT nilUT)
                   ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
                   Z
                   (λ (x_40877513 : ArgList ({VV: Z | True}
                                             ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                      (v_x_40877513 : Z),
                    ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
      {VV: Z | True} ::RT λ (lq_tmp3 : {VV: Z | True}), nilRT) ((@uPack (Z ::UT nilUT) Z ::UT (Z ::UT nilUT))))
             Z
             (λ (x_31985188 : ArgList (@Pack
                                       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                       (Z ::UT nilUT)
                                       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
                                       Z
                                       (λ (x_40877513 : ArgList ({VV: Z | True}
                                                                 ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                                          (v_x_40877513 : Z),
                                        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
                                       ::RT λ (lq_tmp0 : @Pack
                                                         ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                                         (Z ::UT nilUT)
                                                         ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
                                                         Z
                                                         (λ (x_40877513 : ArgList ({VV: Z | True}
                                                                                   ::RT λ (lq_tmp1 : {VV: Z | True}),
                                                                                        nilRT))
                                                            (v_x_40877513 : Z),
                                                          ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
                                            {VV: Z | True} ::RT λ (lq_tmp3 : {VV: Z | True}), nilRT))
                (v_x_31985188 : Z),
              ltac:(flattenP (λ (lq_tmp0 : @Pack
              ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
              Z
              (λ (x_40877513 : ArgList ({VV: Z | True}
                                        ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                 (v_x_40877513 : Z),
               ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
   (lq_tmp3 : {VV: Z | True})
   (VV : Z),
 True) x_31985188 v_x_31985188))):
  IdentityF2_wf (ValF2_u ⌊ lq_tmp0 ⌋).
Proof.
  repeat first [split | solver].
Defined.

Definition ValF2
  (lq_tmp0 : @Pack
             (@Pack
              ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
              Z
              (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                 (v_x_40877513 : Z),
               ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
              ::RT λ (lq_tmp0 : @Pack
                                ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                (Z ::UT nilUT)
                                ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
                                Z
                                (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                                   (v_x_40877513 : Z),
                                 ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
                   {VV: Z | True} ::RT λ (lq_tmp3 : {VV: Z | True}), nilRT)
             (@uPack (Z ::UT nilUT) Z ::UT (Z ::UT nilUT))
             ltac:(mkProjectsArgListTG (@Pack
 ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
 (Z ::UT nilUT)
 ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
 Z
 (λ (x_40877513 : ArgList ({VV: Z | True}
                           ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
    (v_x_40877513 : Z),
  ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
 ::RT λ (lq_tmp0 : @Pack
                   ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                   (Z ::UT nilUT)
                   ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
                   Z
                   (λ (x_40877513 : ArgList ({VV: Z | True}
                                             ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                      (v_x_40877513 : Z),
                    ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
      {VV: Z | True} ::RT λ (lq_tmp3 : {VV: Z | True}), nilRT) ((@uPack (Z ::UT nilUT) Z ::UT (Z ::UT nilUT))))
             Z
             (λ (x_31985188 : ArgList (@Pack
                                       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                       (Z ::UT nilUT)
                                       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
                                       Z
                                       (λ (x_40877513 : ArgList ({VV: Z | True}
                                                                 ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                                          (v_x_40877513 : Z),
                                        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
                                       ::RT λ (lq_tmp0 : @Pack
                                                         ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                                         (Z ::UT nilUT)
                                                         ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
                                                         Z
                                                         (λ (x_40877513 : ArgList ({VV: Z | True}
                                                                                   ::RT λ (lq_tmp1 : {VV: Z | True}),
                                                                                        nilRT))
                                                            (v_x_40877513 : Z),
                                                          ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
                                            {VV: Z | True} ::RT λ (lq_tmp3 : {VV: Z | True}), nilRT))
                (v_x_31985188 : Z),
              ltac:(flattenP (λ (lq_tmp0 : @Pack
              ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
              Z
              (λ (x_40877513 : ArgList ({VV: Z | True}
                                        ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                 (v_x_40877513 : Z),
               ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
   (lq_tmp3 : {VV: Z | True})
   (VV : Z),
 True) x_31985188 v_x_31985188))):
  IdentityF2 :=
  existT _ (ValF2_u ⌊ lq_tmp0 ⌋) (ValF2_lem lq_tmp0).

#[global] Hint Resolve IdentityF2_wf_ref: wf_constr_db.

#[global] Hint Unfold IdentityF2_wf: wf_constr_db.

#[global] Hint Unfold ValF2: ref_constr_db.

Inductive IdentityF1_u: Type :=
  | ValF1_u: @uPack (@uPack (Z ::UT nilUT) Z ::UT nilUT) Z → IdentityF1_u.

(* Fixpoint IdentityF1_eq (x y : IdentityF1_u): bool :=
  match (x, y) with | (ValF1_u lq_tmp0, ValF1_u lq_tmp0') => true && (lq_tmp0 ==? lq_tmp0') end.

Theorem IdentityF1_eq_refl : ∀ (x : IdentityF1_u), is_true (IdentityF1_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve IdentityF1_eq_refl: eq_hint_db.

Theorem IdentityF1_eqb_eq : ∀ (s t : IdentityF1_u), is_true (IdentityF1_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve IdentityF1_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_IdentityF1: LeibnitzEqB := {
    equalB' := IdentityF1_eq;
    refl' := IdentityF1_eq_refl;
    eqb_eq' := IdentityF1_eqb_eq }. *)

Fixpoint IdentityF1_wf (x : IdentityF1_u): Type :=
  match x with
  | ValF1_u lq_tmp0 => let argTps :=
                       @Pack
                       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
                       (Z ::UT nilUT)
                       ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
                       Z
                       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                          (v_x_86795196 : Z),
                        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196))
                       ::RT λ (lq_tmp0 : @Pack
                                         ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
                                         (Z ::UT nilUT)
                                         ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
                                         Z
                                         (λ (x_86795196 : ArgList ({lq_tmp1: Z | True}
                                                                   ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                                            (v_x_86795196 : Z),
                                          ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196))),
                            nilRT in
                       let p :=
                       λ (x_24546733 : ArgList (@Pack
                                                ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
                                                (Z ::UT nilUT)
                                                ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
                                                Z
                                                (λ (x_86795196 : ArgList ({lq_tmp1: Z | True}
                                                                          ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}),
                                                                               nilRT))
                                                   (v_x_86795196 : Z),
                                                 ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196))
                                                ::RT λ (lq_tmp0 : @Pack
                                                                  ({lq_tmp1: Z | True}
                                                                   ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
                                                                  (Z ::UT nilUT)
                                                                  ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
                                                                  Z
                                                                  (λ (x_86795196 : ArgList ({lq_tmp1: Z | True}
                                                                                            ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}),
                                                                                                 nilRT))
                                                                     (v_x_86795196 : Z),
                                                                   ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196))),
                                                     nilRT))
                         (v_x_24546733 : Z),
                       ltac:(flattenP (λ (lq_tmp0 : @Pack
              ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
              Z
              (λ (x_86795196 : ArgList ({lq_tmp1: Z | True}
                                        ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                 (v_x_86795196 : Z),
               ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
   (VV : Z),
 True) x_24546733 v_x_24546733) in
                       let z: projectsArgListT argTps (@uPack (Z ::UT nilUT) Z ::UT nilUT) :=
                       ltac:(mkProjectsArgListTG (argTps) ((@uPack (Z ::UT nilUT) Z ::UT nilUT))) in
                       uPack_wf argTps z p lq_tmp0
  end.

Global Notation IdentityF1 := (sigT (fun x => IdentityF1_wf x)).

Theorem IdentityF1_wf_ref
  [p : IdentityF1_u → Prop] (tm : sigT (fun v: IdentityF1_u => {_:IdentityF1_wf v | p v})):
  IdentityF1_wf (projT1 tm).
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Definition ValF1_lem
  (lq_tmp0 : @Pack
             (@Pack
              ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                 (v_x_40877513 : Z),
               ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
              ::RT λ (lq_tmp0 : @Pack
                                ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                (Z ::UT nilUT)
                                ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                Z
                                (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                                   (v_x_40877513 : Z),
                                 ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
                   nilRT)
             (@uPack (Z ::UT nilUT) Z ::UT nilUT)
             ltac:(mkProjectsArgListTG ((@Pack
  ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Z
  (λ (x_40877513 : ArgList ({VV: Z | True}
                            ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
     (v_x_40877513 : Z),
   ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
  ::RT λ (lq_tmp0 : @Pack
                    ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                    (Z ::UT nilUT)
                    ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                    Z
                    (λ (x_40877513 : ArgList ({VV: Z | True}
                                              ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                       (v_x_40877513 : Z),
                     ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
       nilRT)) ((@uPack (Z ::UT nilUT) Z ::UT nilUT)))
             Z
             (λ (x_26007066 : ArgList (@Pack
                                       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                       (Z ::UT nilUT)
                                       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                       Z
                                       (λ (x_40877513 : ArgList ({VV: Z | True}
                                                                 ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                                          (v_x_40877513 : Z),
                                        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
                                       ::RT λ (lq_tmp0 : @Pack
                                                         ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                                         (Z ::UT nilUT)
                                                         ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                                         Z
                                                         (λ (x_40877513 : ArgList ({VV: Z | True}
                                                                                   ::RT λ (lq_tmp1 : {VV: Z | True}),
                                                                                        nilRT))
                                                            (v_x_40877513 : Z),
                                                          ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
                                            nilRT))
                (v_x_26007066 : Z),
              ltac:(flattenP (λ (lq_tmp0 : @Pack
              ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_40877513 : ArgList ({VV: Z | True}
                                        ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                 (v_x_40877513 : Z),
               ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
   (VV : Z),
 True) x_26007066 v_x_26007066))):
  IdentityF1_wf (ValF1_u ⌊ lq_tmp0 ⌋).
Proof.
  repeat first [split | solver].
Defined.

Definition ValF1
  (lq_tmp0 : @Pack
             (@Pack
              ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                 (v_x_40877513 : Z),
               ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
              ::RT λ (lq_tmp0 : @Pack
                                ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                (Z ::UT nilUT)
                                ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                Z
                                (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                                   (v_x_40877513 : Z),
                                 ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
                   nilRT)
             (@uPack (Z ::UT nilUT) Z ::UT nilUT)
             ltac:(mkProjectsArgListTG ((@Pack
  ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Z
  (λ (x_40877513 : ArgList ({VV: Z | True}
                            ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
     (v_x_40877513 : Z),
   ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
  ::RT λ (lq_tmp0 : @Pack
                    ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                    (Z ::UT nilUT)
                    ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                    Z
                    (λ (x_40877513 : ArgList ({VV: Z | True}
                                              ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                       (v_x_40877513 : Z),
                     ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
       nilRT)) ((@uPack (Z ::UT nilUT) Z ::UT nilUT)))
             Z
             (λ (x_26007066 : ArgList (@Pack
                                       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                       (Z ::UT nilUT)
                                       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                       Z
                                       (λ (x_40877513 : ArgList ({VV: Z | True}
                                                                 ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                                          (v_x_40877513 : Z),
                                        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))
                                       ::RT λ (lq_tmp0 : @Pack
                                                         ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
                                                         (Z ::UT nilUT)
                                                         ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                                         Z
                                                         (λ (x_40877513 : ArgList ({VV: Z | True}
                                                                                   ::RT λ (lq_tmp1 : {VV: Z | True}),
                                                                                        nilRT))
                                                            (v_x_40877513 : Z),
                                                          ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))),
                                            nilRT))
                (v_x_26007066 : Z),
              ltac:(flattenP (λ (lq_tmp0 : @Pack
              ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_40877513 : ArgList ({VV: Z | True}
                                        ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                 (v_x_40877513 : Z),
               ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
   (VV : Z),
 True) x_26007066 v_x_26007066))):
  IdentityF1 :=
  existT _ (ValF1_u ⌊ lq_tmp0 ⌋) (ValF1_lem lq_tmp0).

#[global] Hint Resolve IdentityF1_wf_ref: wf_constr_db.

#[global] Hint Unfold IdentityF1_wf: wf_constr_db.

#[global] Hint Unfold ValF1: ref_constr_db.

Definition pureF1_spec
  (f : @Pack
       (@Pack
        ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
        (Z ::UT nilUT)
        ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
        Z
        (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
           (v_x_10329927 : Z),
         ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
        ::RT λ (lq_tmp1 : @Pack
                          ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                          (Z ::UT nilUT)
                          ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                          Z
                          (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                             (v_x_10329927 : Z),
                           ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
             nilRT)
       (@uPack (Z ::UT nilUT) Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ((@Pack
  ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Z
  (λ (x_10329927 : ArgList ({VV: Z | True}
                            ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
     (v_x_10329927 : Z),
   ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
  ::RT λ (lq_tmp1 : @Pack
                    ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                    (Z ::UT nilUT)
                    ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                    Z
                    (λ (x_10329927 : ArgList ({VV: Z | True}
                                              ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                       (v_x_10329927 : Z),
                     ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
       nilRT)) ((@uPack (Z ::UT nilUT) Z ::UT nilUT)))
       Z
       (λ (x_54436533 : ArgList (@Pack
                                 ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                                 (Z ::UT nilUT)
                                 ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                 Z
                                 (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                                    (v_x_10329927 : Z),
                                  ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
                                 ::RT λ (lq_tmp1 : @Pack
                                                   ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                                                   (Z ::UT nilUT)
                                                   ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                                   Z
                                                   (λ (x_10329927 : ArgList ({VV: Z | True}
                                                                             ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                                                      (v_x_10329927 : Z),
                                                    ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
                                      nilRT))
          (v_x_54436533 : Z),
        ltac:(flattenP (λ (lq_tmp1 : @Pack
              ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_10329927 : ArgList ({VV: Z | True}
                                        ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                 (v_x_10329927 : Z),
               ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
   (VV : Z),
 True) x_54436533 v_x_54436533))):
  Type :=
  IdentityF1.

#[global] Hint Unfold pureF1_spec: lia_unfold.

Definition pureF1
  (f : @Pack
       (@Pack
        ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
        (Z ::UT nilUT)
        ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
        Z
        (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
           (v_x_10329927 : Z),
         ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
        ::RT λ (lq_tmp1 : @Pack
                          ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                          (Z ::UT nilUT)
                          ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                          Z
                          (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                             (v_x_10329927 : Z),
                           ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
             nilRT)
       (@uPack (Z ::UT nilUT) Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ((@Pack
  ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Z
  (λ (x_10329927 : ArgList ({VV: Z | True}
                            ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
     (v_x_10329927 : Z),
   ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
  ::RT λ (lq_tmp1 : @Pack
                    ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                    (Z ::UT nilUT)
                    ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                    Z
                    (λ (x_10329927 : ArgList ({VV: Z | True}
                                              ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                       (v_x_10329927 : Z),
                     ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
       nilRT)) ((@uPack (Z ::UT nilUT) Z ::UT nilUT)))
       Z
       (λ (x_54436533 : ArgList (@Pack
                                 ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                                 (Z ::UT nilUT)
                                 ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                 Z
                                 (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                                    (v_x_10329927 : Z),
                                  ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
                                 ::RT λ (lq_tmp1 : @Pack
                                                   ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                                                   (Z ::UT nilUT)
                                                   ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                                   Z
                                                   (λ (x_10329927 : ArgList ({VV: Z | True}
                                                                             ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                                                      (v_x_10329927 : Z),
                                                    ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
                                      nilRT))
          (v_x_54436533 : Z),
        ltac:(flattenP (λ (lq_tmp1 : @Pack
              ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_10329927 : ArgList ({VV: Z | True}
                                        ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                 (v_x_10329927 : Z),
               ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
   (VV : Z),
 True) x_54436533 v_x_54436533))):
  pureF1_spec f.
Proof.
  refine (ValF1 f).
Defined.

Inductive pureF1_rel: @uPack (@uPack (Z ::UT nilUT) Z ::UT nilUT) Z → IdentityF1_u → Prop :=
  | pureF1_Constr: ∀ (f : @uPack (@uPack (Z ::UT nilUT) Z ::UT nilUT) Z), pureF1_rel f (ValF1_u f).

#[global] Hint Constructors pureF1_rel: core_hint_db.

#[global] Instance pureF1_lookup_rel: dictionary rel pureF1 := { lookup' := pureF1_rel }.

#[global] Instance pureF1_getF: getFunc pureF1_rel := { getF' := pureF1 }.

Theorem pureF1_rel_funct [f : @uPack (@uPack (Z ::UT nilUT) Z ::UT nilUT) Z]:
  ∀ (VV VV' : IdentityF1_u), pureF1_rel f VV → (pureF1_rel f VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve pureF1_rel_funct: f_rel_funct_db.

Theorem pureF1_rel_ex
  (f : @Pack
       (@Pack
        ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
        (Z ::UT nilUT)
        ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
        Z
        (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
           (v_x_82647028 : Z),
         ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))
        ::RT λ (lq_tmp1 : @Pack
                          ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                          (Z ::UT nilUT)
                          ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                          Z
                          (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                             (v_x_82647028 : Z),
                           ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))),
             nilRT)
       (@uPack (Z ::UT nilUT) Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ((@Pack
  ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Z
  (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                            ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
     (v_x_82647028 : Z),
   ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))
  ::RT λ (lq_tmp1 : @Pack
                    ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                    (Z ::UT nilUT)
                    ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                    Z
                    (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                              ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                       (v_x_82647028 : Z),
                     ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))),
       nilRT)) ((@uPack (Z ::UT nilUT) Z ::UT nilUT)))
       Z
       (λ (x_15714024 : ArgList (@Pack
                                 ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                                 (Z ::UT nilUT)
                                 ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                 Z
                                 (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                                           ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                                    (v_x_82647028 : Z),
                                  ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))
                                 ::RT λ (lq_tmp1 : @Pack
                                                   ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                                                   (Z ::UT nilUT)
                                                   ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                                   Z
                                                   (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                                                             ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}),
                                                                                  nilRT))
                                                      (v_x_82647028 : Z),
                                                    ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))),
                                      nilRT))
          (v_x_15714024 : Z),
        ltac:(flattenP (λ (lq_tmp1 : @Pack
              ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                        ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                 (v_x_82647028 : Z),
               ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028)))
   (VV : Z),
 True) x_15714024 v_x_15714024))):
  pureF1_rel ⌊ f ⌋ ⌊- pureF1 f -⌋.
Proof.
  Opaque pureF1.
  existence_lemma_pre pureF1; fix_notations; simpl in *.
  Transparent pureF1.
  all: (existence_lemma_quicksolve pureF1; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve pureF1_rel_ex: rel_ax_db.

#[global] Opaque pureF1.

Theorem pureF1__pureF1_rel_rw
  (f : @Pack
       (@Pack
        ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
        (Z ::UT nilUT)
        ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
        Z
        (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
           (v_x_82647028 : Z),
         ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))
        ::RT λ (lq_tmp1 : @Pack
                          ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                          (Z ::UT nilUT)
                          ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                          Z
                          (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                             (v_x_82647028 : Z),
                           ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))),
             nilRT)
       (@uPack (Z ::UT nilUT) Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ((@Pack
  ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Z
  (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                            ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
     (v_x_82647028 : Z),
   ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))
  ::RT λ (lq_tmp1 : @Pack
                    ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                    (Z ::UT nilUT)
                    ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                    Z
                    (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                              ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                       (v_x_82647028 : Z),
                     ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))),
       nilRT)) ((@uPack (Z ::UT nilUT) Z ::UT nilUT)))
       Z
       (λ (x_15714024 : ArgList (@Pack
                                 ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                                 (Z ::UT nilUT)
                                 ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                 Z
                                 (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                                           ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                                    (v_x_82647028 : Z),
                                  ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))
                                 ::RT λ (lq_tmp1 : @Pack
                                                   ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                                                   (Z ::UT nilUT)
                                                   ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                                   Z
                                                   (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                                                             ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}),
                                                                                  nilRT))
                                                      (v_x_82647028 : Z),
                                                    ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))),
                                      nilRT))
          (v_x_15714024 : Z),
        ltac:(flattenP (λ (lq_tmp1 : @Pack
              ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                        ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                 (v_x_82647028 : Z),
               ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028)))
   (VV : Z),
 True) x_15714024 v_x_15714024)))
  (VV : IdentityF1_u):
  ⌊- pureF1 f -⌋ = VV ↔ pureF1_rel ⌊ f ⌋ VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite pureF1__pureF1_rel_rw: f_rel_funct_db.

#[global] Hint Resolve pureF1__pureF1_rel_rw: rel_ax_db.

#[global] Instance pureF1_lookup_rw: dictionary rwLem pureF1 := {
    lookup' := pureF1__pureF1_rel_rw }.

Theorem pureF1__pureF1_rel
  (f : @Pack
       (@Pack
        ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
        (Z ::UT nilUT)
        ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
        Z
        (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
           (v_x_10329927 : Z),
         ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
        ::RT λ (lq_tmp1 : @Pack
                          ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                          (Z ::UT nilUT)
                          ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                          Z
                          (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                             (v_x_10329927 : Z),
                           ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
             nilRT)
       (@uPack (Z ::UT nilUT) Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ((@Pack
  ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Z
  (λ (x_10329927 : ArgList ({VV: Z | True}
                            ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
     (v_x_10329927 : Z),
   ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
  ::RT λ (lq_tmp1 : @Pack
                    ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                    (Z ::UT nilUT)
                    ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                    Z
                    (λ (x_10329927 : ArgList ({VV: Z | True}
                                              ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                       (v_x_10329927 : Z),
                     ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
       nilRT)) ((@uPack (Z ::UT nilUT) Z ::UT nilUT)))
       Z
       (λ (x_54436533 : ArgList (@Pack
                                 ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                                 (Z ::UT nilUT)
                                 ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                 Z
                                 (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                                    (v_x_10329927 : Z),
                                  ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
                                 ::RT λ (lq_tmp1 : @Pack
                                                   ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                                                   (Z ::UT nilUT)
                                                   ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                                   Z
                                                   (λ (x_10329927 : ArgList ({VV: Z | True}
                                                                             ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                                                      (v_x_10329927 : Z),
                                                    ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
                                      nilRT))
          (v_x_54436533 : Z),
        ltac:(flattenP (λ (lq_tmp1 : @Pack
              ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_10329927 : ArgList ({VV: Z | True}
                                        ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                 (v_x_10329927 : Z),
               ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
   (VV : Z),
 True) x_54436533 v_x_54436533)))
  (VV : IdentityF1_u):
  ⌊- pureF1 f -⌋ = VV ↔ pureF1_rel ⌊ f ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite pureF1__pureF1_rel: f_rel_funct_db.

Theorem pureF1__pureF1_rel'
  (f_u : @uPack (@uPack (Z ::UT nilUT) Z ::UT nilUT) Z)
  (f : @Pack
       (@Pack
        ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
        (Z ::UT nilUT)
        ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
        Z
        (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
           (v_x_10329927 : Z),
         ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
        ::RT λ (lq_tmp1 : @Pack
                          ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                          (Z ::UT nilUT)
                          ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                          Z
                          (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                             (v_x_10329927 : Z),
                           ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
             nilRT)
       (@uPack (Z ::UT nilUT) Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ((@Pack
  ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Z
  (λ (x_10329927 : ArgList ({VV: Z | True}
                            ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
     (v_x_10329927 : Z),
   ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
  ::RT λ (lq_tmp1 : @Pack
                    ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                    (Z ::UT nilUT)
                    ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                    Z
                    (λ (x_10329927 : ArgList ({VV: Z | True}
                                              ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                       (v_x_10329927 : Z),
                     ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
       nilRT)) ((@uPack (Z ::UT nilUT) Z ::UT nilUT)))
       Z
       (λ (x_54436533 : ArgList (@Pack
                                 ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                                 (Z ::UT nilUT)
                                 ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                 Z
                                 (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                                    (v_x_10329927 : Z),
                                  ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))
                                 ::RT λ (lq_tmp1 : @Pack
                                                   ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
                                                   (Z ::UT nilUT)
                                                   ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                                   Z
                                                   (λ (x_10329927 : ArgList ({VV: Z | True}
                                                                             ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                                                      (v_x_10329927 : Z),
                                                    ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927))),
                                      nilRT))
          (v_x_54436533 : Z),
        ltac:(flattenP (λ (lq_tmp1 : @Pack
              ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_10329927 : ArgList ({VV: Z | True}
                                        ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                 (v_x_10329927 : Z),
               ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
   (VV : Z),
 True) x_54436533 v_x_54436533)))
  (VV : IdentityF1_u):
  f_u = ⌊ f ⌋ → ⌊- pureF1 f -⌋ = VV ↔ pureF1_rel f_u VV.
Proof.
  intros ->. refine (pureF1__pureF1_rel f VV).
Qed.

#[global] Hint Resolve pureF1__pureF1_rel': f_rel_funct_db.

Theorem pureF1_rel_mk
  (f : @Pack
       (@Pack
        ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
        (Z ::UT nilUT)
        ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
        Z
        (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
           (v_x_82647028 : Z),
         ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))
        ::RT λ (lq_tmp1 : @Pack
                          ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                          (Z ::UT nilUT)
                          ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                          Z
                          (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                             (v_x_82647028 : Z),
                           ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))),
             nilRT)
       (@uPack (Z ::UT nilUT) Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ((@Pack
  ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Z
  (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                            ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
     (v_x_82647028 : Z),
   ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))
  ::RT λ (lq_tmp1 : @Pack
                    ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                    (Z ::UT nilUT)
                    ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                    Z
                    (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                              ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                       (v_x_82647028 : Z),
                     ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))),
       nilRT)) ((@uPack (Z ::UT nilUT) Z ::UT nilUT)))
       Z
       (λ (x_15714024 : ArgList (@Pack
                                 ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                                 (Z ::UT nilUT)
                                 ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                 Z
                                 (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                                           ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                                    (v_x_82647028 : Z),
                                  ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))
                                 ::RT λ (lq_tmp1 : @Pack
                                                   ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
                                                   (Z ::UT nilUT)
                                                   ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
                                                   Z
                                                   (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                                                             ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}),
                                                                                  nilRT))
                                                      (v_x_82647028 : Z),
                                                    ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028))),
                                      nilRT))
          (v_x_15714024 : Z),
        ltac:(flattenP (λ (lq_tmp1 : @Pack
              ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
              (Z ::UT nilUT)
              ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
              Z
              (λ (x_82647028 : ArgList ({lq_tmp2: Z | True}
                                        ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                 (v_x_82647028 : Z),
               ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028)))
   (VV : Z),
 True) x_15714024 v_x_15714024))):
  {VV: _ | pureF1_rel (packProj f) VV}.
Proof.
  intros.
  refine (exist _ ⌊- pureF1 f -⌋ _).
  rewrite <- pureF1__pureF1_rel';
  quicksolve.
Qed.

#[global] Hint Resolve pureF1_rel_mk: f_rel_funct_db.

Inductive IdentityF_u: Type :=
  | ValF_u: @uPack (Z ::UT nilUT) Z → IdentityF_u.

Fixpoint IdentityF_wf (x : IdentityF_u): Type  :=
  match x with
  | ValF_u lq_tmp0 => let argTps : ArgListT :=
                      {lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT in
                      let p :=
                      λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
                        (v_x_49697850 : Z),
                      ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (VV : Z), True) x_49697850 v_x_49697850) in
                      let z: projectsArgListT argTps (Z ::UT nilUT) :=
                      ltac:(mkProjectsArgListTG (argTps) ((Z ::UT nilUT))) in
                      uPack_wf argTps z p lq_tmp0
  end.

Theorem IdentityF_wf_ref [p : IdentityF_u → Prop] (tm : sigT (fun v: IdentityF_u => {_:IdentityF_wf v | p v})):
  IdentityF_wf ⌊- tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation IdentityF := (sigT (fun x: IdentityF_u => IdentityF_wf x)).

Definition ValF_lem
  (lq_tmp0 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             Z
             (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
                (v_x_44453395 : Z),
              ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395))):
  IdentityF_wf (ValF_u ⌊ lq_tmp0 ⌋).
Proof.
  repeat first [split | solver].
Defined.

Definition ValF
  (lq_tmp0 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             Z
             (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
                (v_x_44453395 : Z),
              ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395))):
  IdentityF :=
  existT _ (ValF_u ⌊ lq_tmp0 ⌋) (ValF_lem lq_tmp0).

#[global] Hint Resolve IdentityF_wf_ref: wf_constr_db.

#[global] Hint Unfold IdentityF_wf: wf_constr_db.

#[global] Hint Unfold ValF: ref_constr_db.

Definition pureF_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))):
  Type :=
  IdentityF.

#[global] Hint Unfold pureF_spec: lia_unfold.

Definition pureF
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513))):
  pureF_spec f.
Proof.
  refine (ValF f).
Defined.

Inductive pureF_rel: @uPack (Z ::UT nilUT) Z → IdentityF_u → Prop :=
  | pureF_Constr: ∀ (f : @uPack (Z ::UT nilUT) Z), pureF_rel f (ValF_u f).

#[global] Hint Constructors pureF_rel: core_hint_db.

#[global] Instance pureF_lookup_rel: dictionary rel pureF := { lookup' := pureF_rel }.

#[global] Instance pureF_getF: getFunc pureF_rel := { getF' := pureF }.

Theorem pureF_rel_funct [f : @uPack (Z ::UT nilUT) Z]:
  ∀ (VV VV' : IdentityF_u), pureF_rel f VV → (pureF_rel f VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve pureF_rel_funct: f_rel_funct_db.

Theorem pureF_inv_lem f pureF_inv_lem_res:
  pureF_rel f pureF_inv_lem_res ↔ pureF_inv_lem_res = ValF_u f.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite pureF_inv_lem: f_rel_back.

Theorem pureF_rel_ex
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196))):
  pureF_rel ⌊ f ⌋ ⌊- pureF f -⌋.
Proof.
  Opaque pureF.
  existence_lemma_pre pureF; fix_notations; simpl in *.
  Transparent pureF.
  all: (existence_lemma_quicksolve pureF; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve pureF_rel_ex: rel_ax_db.

#[global] Opaque pureF.

Theorem pureF__pureF_rel_rw
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (VV : IdentityF_u):
  ⌊- pureF f -⌋ = VV ↔ pureF_rel ⌊ f ⌋ VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite pureF__pureF_rel_rw: f_rel_funct_db.

#[global] Hint Resolve pureF__pureF_rel_rw: rel_ax_db.

#[global] Instance pureF_lookup_rw: dictionary rwLem pureF := { lookup' := pureF__pureF_rel_rw }.

Theorem pureF__pureF_rel
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (VV : IdentityF_u):
  ⌊- pureF f -⌋ = VV ↔ pureF_rel ⌊ f ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite pureF__pureF_rel: f_rel_funct_db.

Theorem pureF__pureF_rel'
  (f_u : @uPack (Z ::UT nilUT) Z)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (VV : IdentityF_u):
  f_u = ⌊ f ⌋ → ⌊- pureF f -⌋ = VV ↔ pureF_rel f_u VV.
Proof.
  intros ->. refine (pureF__pureF_rel f VV).
Qed.

#[global] Hint Resolve pureF__pureF_rel': f_rel_funct_db.

Theorem pureF_rel_mk
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196))):
  {VV: _ | pureF_rel (packProj f) VV}.
Proof.
  intros;
  refine (subsumptionCastT _ (λ VV, pureF_rel (packProj f) VV) (pureF f) _).
  intros;
  rewrite <- pureF__pureF_rel';
  quicksolve.
Qed.

#[global] Hint Resolve pureF_rel_mk: f_rel_funct_db.

Definition seqF1_spec (ds_daoe : IdentityF2) (ds_daof : IdentityF): Type :=
  IdentityF.

#[global] Hint Unfold seqF1_spec: lia_unfold.

Definition seqF1 (ds_daoe : IdentityF2) (ds_daof : IdentityF): seqF1_spec ds_daoe ds_daof.
Proof.
  destruct ds_daoe as [ds_daoe ds_daoe_p].
  destruct ds_daof as [ds_daof ds_daof_p].
  destruct ds_daoe as [f].
  - destruct ds_daof as [x].
    + unfold seqF1_spec. 
      (* refine (ValF (PartialApp (getPackUPack f) (getPackUPack x))).*)
      refine (ValF _). simpl.
      pose (getPackUPack f) as pack_f.
      pose (getPackUPack x) as pack_x.
      refine (PartialApp pack_f pack_x).
Defined.

Inductive seqF1_rel: IdentityF2_u → IdentityF_u → IdentityF_u → Prop :=
  | seqF1_ValF2_ValF: ∀ f x (f_res : Z),
                      getUPackRel f x f_res → seqF1_rel (ValF2_u f) (ValF_u x) (ValF_u f_res).

#[global] Hint Constructors seqF1_rel: core_hint_db.

#[global] Instance seqF1_lookup_rel: dictionary rel seqF1 := { lookup' := seqF1_rel }.

#[global] Instance seqF1_getF: getFunc seqF1_rel := { getF' := seqF1 }.

Theorem seqF1_rel_funct [ds_daoe : IdentityF2_u] [ds_daof : IdentityF_u]:
  ∀ (VV VV' : IdentityF_u), seqF1_rel ds_daoe ds_daof VV → (seqF1_rel ds_daoe ds_daof VV' → VV = VV').
Proof.
  destruct ds_daoe as [f];
  [destruct ds_daof as [x]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve seqF1_rel_funct: f_rel_funct_db.

Theorem seqF1_ValF2_ValF_lem f x seqF1_ValF2_ValF_lem_res:
  seqF1_rel (ValF2_u f) (ValF_u x) seqF1_ValF2_ValF_lem_res
  ↔ ∃ (f_res : Z), getUPackRel f x f_res ∧ seqF1_ValF2_ValF_lem_res == ValF_u f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite seqF1_ValF2_ValF_lem: f_rel_back.

Theorem seqF1_rel_ex
  (ds_daoe : IdentityF2_u)
  (ds_daoe_p : IdentityF2_wf ds_daoe ∧ True)
  (ds_daof : IdentityF_u)
  (ds_daof_p : IdentityF_wf ds_daof ∧ True):
  seqF1_rel ds_daoe ds_daof ⌊ seqF1 (exist _ ds_daoe ds_daoe_p) (exist _ ds_daof ds_daof_p) -⌋.
Proof.
  Opaque seqF1.
  existence_lemma_pre seqF1;
  destruct ds_daoe as [f];
  [destruct ds_daof as [x];
   [fix_notations]];
  simpl in *.
  Transparent seqF1.
  all: (existence_lemma_quicksolve seqF1; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve seqF1_rel_ex: rel_ax_db.

#[global] Opaque seqF1.

Theorem seqF1__seqF1_rel_rw
  (ds_daoe : IdentityF2_u)
  (ds_daoe_p : IdentityF2_wf ds_daoe ∧ True)
  (ds_daof : IdentityF_u)
  (ds_daof_p : IdentityF_wf ds_daof ∧ True)
  (VV : IdentityF_u):
  ⌊ seqF1 (exist _ ds_daoe ds_daoe_p) (exist _ ds_daof ds_daof_p) -⌋ = VV
  ↔ seqF1_rel ds_daoe ds_daof VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite seqF1__seqF1_rel_rw: f_rel_funct_db.

#[global] Hint Resolve seqF1__seqF1_rel_rw: rel_ax_db.

#[global] Instance seqF1_lookup_rw: dictionary rwLem seqF1 := { lookup' := seqF1__seqF1_rel_rw }.

Theorem seqF1__seqF1_rel (ds_daoe : IdentityF2) (ds_daof : IdentityF) (VV : IdentityF_u):
  ⌊ seqF1 ds_daoe ds_daof -⌋ = VV ↔ seqF1_rel ⌊ ds_daoe ⌋ ⌊ ds_daof ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite seqF1__seqF1_rel: f_rel_funct_db.

Theorem seqF1__seqF1_rel'
  (ds_daoe_u : IdentityF2_u)
  (ds_daof_u : IdentityF_u)
  (ds_daoe : IdentityF2)
  (ds_daof : IdentityF)
  (VV : IdentityF_u):
  ds_daoe_u = ⌊ ds_daoe ⌋
  → (ds_daof_u = ⌊ ds_daof ⌋ → ⌊ seqF1 ds_daoe ds_daof -⌋ = VV ↔ seqF1_rel ds_daoe_u ds_daof_u VV).
Proof.
  intros -> ->. refine (seqF1__seqF1_rel ds_daoe ds_daof VV).
Qed.

#[global] Hint Resolve seqF1__seqF1_rel': f_rel_funct_db.

Theorem seqF1_rel_mk
  (ds_daoe : IdentityF2_u)
  (ds_daoe_p : IdentityF2_wf ds_daoe ∧ True)
  (ds_daof : IdentityF_u)
  (ds_daof_p : IdentityF_wf ds_daof ∧ True):
  {VV: _ | seqF1_rel ds_daoe ds_daof VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, seqF1_rel ds_daoe ds_daof VV)
          (seqF1 (exist _ ds_daoe ds_daoe_p) (exist _ ds_daof ds_daof_p))
          _);
  rewrite <- seqF1__seqF1_rel';
  quicksolve.
Qed.

#[global] Hint Resolve seqF1_rel_mk: f_rel_funct_db.

#[global] Instance seqF1_pack:
  @Pack
  (IdentityF2 ::RT λ (ds_daoe : IdentityF2), IdentityF ::RT λ (ds_daof : IdentityF), nilRT)
  (IdentityF2_u ::UT (IdentityF_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((IdentityF2
  ::RT λ (ds_daoe : IdentityF2),
       IdentityF ::RT λ (ds_daof : IdentityF), nilRT)) ((IdentityF2_u ::UT (IdentityF_u ::UT nilUT))))
  IdentityF_u
  (λ (x_15168953 : ArgList (IdentityF2
                            ::RT λ (ds_daoe : IdentityF2), IdentityF ::RT λ (ds_daof : IdentityF), nilRT))
     (v_x_15168953 : IdentityF_u),
   ltac:(flattenP (λ (ds_daoe : IdentityF2) (ds_daof : IdentityF) (VV : IdentityF_u),
 IdentityF_wf VV ∧ True) x_15168953 v_x_15168953)).
Proof.
  buildPackG seqF1 seqF1_rel seqF1__seqF1_rel seqF1_rel_funct.
Defined.

#[global] Instance seqF1_upack: @uPack (IdentityF2_u ::UT (IdentityF_u ::UT nilUT)) IdentityF_u.
Proof.
  buildUPackG seqF1_rel seqF1_rel_funct.
Defined.

Definition seqF2_spec (ds_daob : IdentityF3) (ds_daoc : IdentityF): Type :=
  IdentityF2.

#[global] Hint Unfold seqF2_spec: lia_unfold.

Definition seqF2 (ds_daob : IdentityF3) (ds_daoc : IdentityF): seqF2_spec ds_daob ds_daoc.
Proof.
  destruct ds_daob as [ds_daob ds_daob_p].
  destruct ds_daoc as [ds_daoc ds_daoc_p].
  destruct ds_daob as [f].
  - destruct ds_daoc as [x].
    + refine (ValF2 (getPackF f x)).
Defined.

Inductive seqF2_rel: IdentityF3_u → IdentityF_u → IdentityF2_u → Prop :=
  | seqF2_ValF3_ValF: ∀ f x (f_res : Z),
                      getUPackRel f x f_res → seqF2_rel (ValF3_u f) (ValF_u x) (ValF2_u f_res).

#[global] Hint Constructors seqF2_rel: core_hint_db.

#[global] Instance seqF2_lookup_rel: dictionary rel seqF2 := { lookup' := seqF2_rel }.

#[global] Instance seqF2_getF: getFunc seqF2_rel := { getF' := seqF2 }.

Theorem seqF2_rel_funct [ds_daob : IdentityF3_u] [ds_daoc : IdentityF_u]:
  ∀ (VV VV' : IdentityF2_u),
  seqF2_rel ds_daob ds_daoc VV → (seqF2_rel ds_daob ds_daoc VV' → VV = VV').
Proof.
  destruct ds_daob as [f];
  [destruct ds_daoc as [x]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve seqF2_rel_funct: f_rel_funct_db.

Theorem seqF2_ValF3_ValF_lem f x seqF2_ValF3_ValF_lem_res:
  seqF2_rel (ValF3_u f) (ValF_u x) seqF2_ValF3_ValF_lem_res
  ↔ ∃ (f_res : Z), getUPackRel f x f_res ∧ seqF2_ValF3_ValF_lem_res == ValF2_u f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite seqF2_ValF3_ValF_lem: f_rel_back.

Theorem seqF2_rel_ex
  (ds_daob : IdentityF3_u)
  (ds_daob_p : IdentityF3_wf ds_daob ∧ True)
  (ds_daoc : IdentityF_u)
  (ds_daoc_p : IdentityF_wf ds_daoc ∧ True):
  seqF2_rel ds_daob ds_daoc ⌊ seqF2 (exist _ ds_daob ds_daob_p) (exist _ ds_daoc ds_daoc_p) -⌋.
Proof.
  Opaque seqF2.
  existence_lemma_pre seqF2;
  destruct ds_daob as [f];
  [destruct ds_daoc as [x];
   [fix_notations]];
  simpl in *.
  Transparent seqF2.
  all: (existence_lemma_quicksolve seqF2; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve seqF2_rel_ex: rel_ax_db.

#[global] Opaque seqF2.

Theorem seqF2__seqF2_rel_rw
  (ds_daob : IdentityF3_u)
  (ds_daob_p : IdentityF3_wf ds_daob ∧ True)
  (ds_daoc : IdentityF_u)
  (ds_daoc_p : IdentityF_wf ds_daoc ∧ True)
  (VV : IdentityF2_u):
  ⌊ seqF2 (exist _ ds_daob ds_daob_p) (exist _ ds_daoc ds_daoc_p) -⌋ = VV
  ↔ seqF2_rel ds_daob ds_daoc VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite seqF2__seqF2_rel_rw: f_rel_funct_db.

#[global] Hint Resolve seqF2__seqF2_rel_rw: rel_ax_db.

#[global] Instance seqF2_lookup_rw: dictionary rwLem seqF2 := { lookup' := seqF2__seqF2_rel_rw }.

Theorem seqF2__seqF2_rel (ds_daob : IdentityF3) (ds_daoc : IdentityF) (VV : IdentityF2_u):
  ⌊ seqF2 ds_daob ds_daoc -⌋ = VV ↔ seqF2_rel ⌊ ds_daob ⌋ ⌊ ds_daoc ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite seqF2__seqF2_rel: f_rel_funct_db.

Theorem seqF2__seqF2_rel'
  (ds_daob_u : IdentityF3_u)
  (ds_daoc_u : IdentityF_u)
  (ds_daob : IdentityF3)
  (ds_daoc : IdentityF)
  (VV : IdentityF2_u):
  ds_daob_u = ⌊ ds_daob ⌋
  → (ds_daoc_u = ⌊ ds_daoc ⌋ → ⌊ seqF2 ds_daob ds_daoc -⌋ = VV ↔ seqF2_rel ds_daob_u ds_daoc_u VV).
Proof.
  intros -> ->. refine (seqF2__seqF2_rel ds_daob ds_daoc VV).
Qed.

#[global] Hint Resolve seqF2__seqF2_rel': f_rel_funct_db.

Theorem seqF2_rel_mk
  (ds_daob : IdentityF3_u)
  (ds_daob_p : IdentityF3_wf ds_daob ∧ True)
  (ds_daoc : IdentityF_u)
  (ds_daoc_p : IdentityF_wf ds_daoc ∧ True):
  {VV: _ | seqF2_rel ds_daob ds_daoc VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, seqF2_rel ds_daob ds_daoc VV)
          (seqF2 (exist _ ds_daob ds_daob_p) (exist _ ds_daoc ds_daoc_p))
          _);
  rewrite <- seqF2__seqF2_rel';
  quicksolve.
Qed.

#[global] Hint Resolve seqF2_rel_mk: f_rel_funct_db.

#[global] Instance seqF2_pack:
  @Pack
  (IdentityF3 ::RT λ (ds_daob : IdentityF3), IdentityF ::RT λ (ds_daoc : IdentityF), nilRT)
  (IdentityF3_u ::UT (IdentityF_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((IdentityF3
  ::RT λ (ds_daob : IdentityF3),
       IdentityF ::RT λ (ds_daoc : IdentityF), nilRT)) ((IdentityF3_u ::UT (IdentityF_u ::UT nilUT))))
  IdentityF2_u
  (λ (x_38168231 : ArgList (IdentityF3
                            ::RT λ (ds_daob : IdentityF3), IdentityF ::RT λ (ds_daoc : IdentityF), nilRT))
     (v_x_38168231 : IdentityF2_u),
   ltac:(flattenP (λ (ds_daob : IdentityF3)
   (ds_daoc : IdentityF)
   (VV : IdentityF2_u),
 IdentityF2_wf VV ∧ True) x_38168231 v_x_38168231)).
Proof.
  buildPackG seqF2 seqF2_rel seqF2__seqF2_rel seqF2_rel_funct.
Defined.

#[global] Instance seqF2_upack: @uPack (IdentityF3_u ::UT (IdentityF_u ::UT nilUT)) IdentityF2_u.
Proof.
  buildUPackG seqF2_rel seqF2_rel_funct.
Defined.

Inductive Identity_u: Type :=
  | Val_u: Z → Identity_u.

Fixpoint Identity_eq (x y : Identity_u): bool :=
  match (x, y) with | (Val_u n, Val_u n') => true && (n ==? n') end.

Theorem Identity_eq_refl : ∀ (x : Identity_u), is_true (Identity_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Identity_eq_refl: eq_hint_db.

Theorem Identity_eqb_eq : ∀ (s t : Identity_u), is_true (Identity_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Identity_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Identity: LeibnitzEqB := {
    equalB' := Identity_eq;
    refl' := Identity_eq_refl;
    eqb_eq' := Identity_eqb_eq }.

Fixpoint Identity_wf (x : Identity_u): Prop :=
  match x with | Val_u n => True end.

Theorem Identity_wf_ref [p : Identity_u → Prop] (tm : {v: Identity_u | Identity_wf v ∧ p v}):
  Identity_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Identity := {x: Identity_u | Identity_wf x ∧ True}.

Definition Val_lem (n : {n: Z | True}): Identity_wf (Val_u ⌊ n ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Val (n : {n: Z | True}): Identity :=
  exist _ (Val_u ⌊ n ⌋) (Val_lem n).

#[global] Hint Resolve Identity_wf_ref: wf_constr_db.

#[global] Hint Unfold Identity_wf: wf_constr_db.

#[global] Hint Resolve Identity_eq: ref_constr_db.

#[global] Hint Unfold Val: ref_constr_db.

Definition pure_spec (x : {x: Z | True}): Type :=
  Identity.

#[global] Hint Unfold pure_spec: lia_unfold.

Definition pure (x : {x: Z | True}): pure_spec x.
Proof.
  destruct x as [x x_p]. refine (Val (# x)).
Defined.

Inductive pure_rel: Z → Identity_u → Prop :=
  | pure_Constr: ∀ x, pure_rel x (Val_u x).

#[global] Hint Constructors pure_rel: core_hint_db.

#[global] Instance pure_lookup_rel: dictionary rel pure := { lookup' := pure_rel }.

#[global] Instance pure_getF: getFunc pure_rel := { getF' := pure }.

Theorem pure_rel_funct [x : Z]:
  ∀ (VV VV' : Identity_u), pure_rel x VV → (pure_rel x VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve pure_rel_funct: f_rel_funct_db.

Theorem pure_inv_lem x pure_inv_lem_res: pure_rel x pure_inv_lem_res ↔ pure_inv_lem_res == Val_u x.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite pure_inv_lem: f_rel_back.

Theorem pure_rel_ex (x : Z) (x_p : True): pure_rel x ⌊ pure (exist _ x x_p) -⌋.
Proof.
  Opaque pure.
  existence_lemma_pre pure; fix_notations; simpl in *.
  Transparent pure.
  all: (existence_lemma_quicksolve pure; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve pure_rel_ex: rel_ax_db.

#[global] Opaque pure.

Theorem pure__pure_rel_rw (x : Z) (x_p : True) (VV : Identity_u):
  ⌊ pure (exist _ x x_p) -⌋ = VV ↔ pure_rel x VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite pure__pure_rel_rw: f_rel_funct_db.

#[global] Hint Resolve pure__pure_rel_rw: rel_ax_db.

#[global] Instance pure_lookup_rw: dictionary rwLem pure := { lookup' := pure__pure_rel_rw }.

Theorem pure__pure_rel (x : {x: Z | True}) (VV : Identity_u): ⌊ pure x -⌋ = VV ↔ pure_rel ⌊ x ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite pure__pure_rel: f_rel_funct_db.

Theorem pure__pure_rel' (x_u : Z) (x : {x: Z | True}) (VV : Identity_u):
  x_u = ⌊ x ⌋ → ⌊ pure x -⌋ = VV ↔ pure_rel x_u VV.
Proof.
  intros ->. refine (pure__pure_rel x VV).
Qed.

#[global] Hint Resolve pure__pure_rel': f_rel_funct_db.

Theorem pure_rel_mk (x : Z) (x_p : True): {VV: _ | pure_rel x VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, pure_rel x VV) (pure (exist _ x x_p)) _);
  rewrite <- pure__pure_rel';
  quicksolve.
Qed.

#[global] Hint Resolve pure_rel_mk: f_rel_funct_db.

#[global] Instance pure_pack:
  @Pack
  ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Identity_u
  (λ (x_11473763 : ArgList ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT))
     (v_x_11473763 : Identity_u),
   ltac:(flattenP (λ (x : {x: Z | True}) (VV : Identity_u), Identity_wf VV ∧ True) x_11473763 v_x_11473763)).
Proof.
  buildPackG pure pure_rel pure__pure_rel pure_rel_funct.
Defined.

#[global] Instance pure_upack: @uPack (Z ::UT nilUT) Identity_u.
Proof.
  buildUPackG pure_rel pure_rel_funct.
Defined.

Definition seq_spec (ds_daok : IdentityF) (ds_daol : Identity): Type :=
  Identity.

#[global] Hint Unfold seq_spec: lia_unfold.

Definition seq (ds_daok : IdentityF) (ds_daol : Identity): seq_spec ds_daok ds_daol.
Proof.
  destruct ds_daok as [ds_daok ds_daok_p].
  destruct ds_daol as [ds_daol ds_daol_p].
  destruct ds_daok as [f].
  - destruct ds_daol as [x].
    + refine (Val (getPackF f (# x))).
Defined.

Inductive seq_rel: IdentityF_u → Identity_u → Identity_u → Prop :=
  | seq_ValF_Val: ∀ f x (f_res : Z),
                  getUPackRel f x f_res → seq_rel (ValF_u f) (Val_u x) (Val_u f_res).

#[global] Hint Constructors seq_rel: core_hint_db.

#[global] Instance seq_lookup_rel: dictionary rel seq := { lookup' := seq_rel }.

#[global] Instance seq_getF: getFunc seq_rel := { getF' := seq }.

Theorem seq_rel_funct [ds_daok : IdentityF_u] [ds_daol : Identity_u]:
  ∀ (VV VV' : Identity_u), seq_rel ds_daok ds_daol VV → (seq_rel ds_daok ds_daol VV' → VV = VV').
Proof.
  destruct ds_daok as [f];
  [destruct ds_daol as [x]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve seq_rel_funct: f_rel_funct_db.

Theorem seq_ValF_Val_lem f x seq_ValF_Val_lem_res:
  seq_rel (ValF_u f) (Val_u x) seq_ValF_Val_lem_res
  ↔ ∃ (f_res : Z), getUPackRel f x f_res ∧ seq_ValF_Val_lem_res == Val_u f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite seq_ValF_Val_lem: f_rel_back.

Theorem seq_rel_ex
  (ds_daok : IdentityF_u)
  (ds_daok_p : IdentityF_wf ds_daok ∧ True)
  (ds_daol : Identity_u)
  (ds_daol_p : Identity_wf ds_daol ∧ True):
  seq_rel ds_daok ds_daol ⌊ seq (exist _ ds_daok ds_daok_p) (exist _ ds_daol ds_daol_p) -⌋.
Proof.
  Opaque seq.
  existence_lemma_pre seq;
  destruct ds_daok as [f];
  [destruct ds_daol as [x];
   [fix_notations]];
  simpl in *.
  Transparent seq.
  all: (existence_lemma_quicksolve seq; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve seq_rel_ex: rel_ax_db.

#[global] Opaque seq.

Theorem seq__seq_rel_rw
  (ds_daok : IdentityF_u)
  (ds_daok_p : IdentityF_wf ds_daok ∧ True)
  (ds_daol : Identity_u)
  (ds_daol_p : Identity_wf ds_daol ∧ True)
  (VV : Identity_u):
  ⌊ seq (exist _ ds_daok ds_daok_p) (exist _ ds_daol ds_daol_p) -⌋ = VV ↔ seq_rel ds_daok ds_daol VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite seq__seq_rel_rw: f_rel_funct_db.

#[global] Hint Resolve seq__seq_rel_rw: rel_ax_db.

#[global] Instance seq_lookup_rw: dictionary rwLem seq := { lookup' := seq__seq_rel_rw }.

Theorem seq__seq_rel (ds_daok : IdentityF) (ds_daol : Identity) (VV : Identity_u):
  ⌊ seq ds_daok ds_daol -⌋ = VV ↔ seq_rel ⌊ ds_daok ⌋ ⌊ ds_daol ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite seq__seq_rel: f_rel_funct_db.

Theorem seq__seq_rel'
  (ds_daok_u : IdentityF_u)
  (ds_daol_u : Identity_u)
  (ds_daok : IdentityF)
  (ds_daol : Identity)
  (VV : Identity_u):
  ds_daok_u = ⌊ ds_daok ⌋
  → (ds_daol_u = ⌊ ds_daol ⌋ → ⌊ seq ds_daok ds_daol -⌋ = VV ↔ seq_rel ds_daok_u ds_daol_u VV).
Proof.
  intros -> ->. refine (seq__seq_rel ds_daok ds_daol VV).
Qed.

#[global] Hint Resolve seq__seq_rel': f_rel_funct_db.

Theorem seq_rel_mk
  (ds_daok : IdentityF_u)
  (ds_daok_p : IdentityF_wf ds_daok ∧ True)
  (ds_daol : Identity_u)
  (ds_daol_p : Identity_wf ds_daol ∧ True):
  {VV: _ | seq_rel ds_daok ds_daol VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, seq_rel ds_daok ds_daol VV)
          (seq (exist _ ds_daok ds_daok_p) (exist _ ds_daol ds_daol_p))
          _);
  rewrite <- seq__seq_rel';
  quicksolve.
Qed.

#[global] Hint Resolve seq_rel_mk: f_rel_funct_db.

#[global] Instance seq_pack:
  @Pack
  (IdentityF ::RT λ (ds_daok : IdentityF), Identity ::RT λ (ds_daol : Identity), nilRT)
  (IdentityF_u ::UT (Identity_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((IdentityF
  ::RT λ (ds_daok : IdentityF),
       Identity ::RT λ (ds_daol : Identity), nilRT)) ((IdentityF_u ::UT (Identity_u ::UT nilUT))))
  Identity_u
  (λ (x_41047773 : ArgList (IdentityF
                            ::RT λ (ds_daok : IdentityF), Identity ::RT λ (ds_daol : Identity), nilRT))
     (v_x_41047773 : Identity_u),
   ltac:(flattenP (λ (ds_daok : IdentityF) (ds_daol : Identity) (VV : Identity_u),
 Identity_wf VV ∧ True) x_41047773 v_x_41047773)).
Proof.
  buildPackG seq seq_rel seq__seq_rel seq_rel_funct.
Defined.

#[global] Instance seq_upack: @uPack (IdentityF_u ::UT (Identity_u ::UT nilUT)) Identity_u.
Proof.
  buildUPackG seq_rel seq_rel_funct.
Defined.

Definition composition_spec (ds_dao7 ds_dao8 : IdentityF) (ds_dao9 : Identity): Type :=
  {{∃ (pureF3_res : IdentityF3_u),
    pureF3_rel compose_upack pureF3_res
    ∧ ∃ (seqF2_res : IdentityF2_u),
      seqF2_rel pureF3_res ⌊ ds_dao7 ⌋ seqF2_res
      ∧ ∃ (seqF1_res : IdentityF_u),
        seqF1_rel seqF2_res ⌊ ds_dao8 ⌋ seqF1_res
        ∧ ∃ (seq_res : Identity_u),
          seq_rel seqF1_res ⌊ ds_dao9 ⌋ seq_res
          ∧ ∃ (seq_res_2 : Identity_u),
            seq_rel ⌊ ds_dao8 ⌋ ⌊ ds_dao9 ⌋ seq_res_2
            ∧ ∃ (seq_res_3 : Identity_u), seq_rel ⌊ ds_dao7 ⌋ seq_res_2 seq_res_3 ∧ seq_res == seq_res_3}}.

#[global] Hint Unfold composition_spec: lia_unfold.

Theorem composition (ds_dao7 ds_dao8 : IdentityF) (ds_dao9 : Identity):
  composition_spec ds_dao7 ds_dao8 ds_dao9.
Proof.
  destruct ds_dao7 as [ds_dao7 ds_dao7_p].
  destruct ds_dao8 as [ds_dao8 ds_dao8_p].
  destruct ds_dao9 as [ds_dao9 ds_dao9_p].
  destruct ds_dao7 as [x].
  - destruct ds_dao8 as [y].
    + destruct ds_dao9 as [z].
      ** refine (subsumptionCast
                 Unit
                 (λ (VV : Unit),
                  ∃ (pureF3_res : IdentityF3_u),
                  pureF3_rel compose_upack pureF3_res
                  ∧ ∃ (seqF2_res : IdentityF2_u),
                    seqF2_rel pureF3_res (ValF_u x) seqF2_res
                    ∧ ∃ (seqF1_res : IdentityF_u),
                      seqF1_rel seqF2_res (ValF_u y) seqF1_res
                      ∧ ∃ (seq_res : Identity_u),
                        seq_rel seqF1_res (Val_u z) seq_res
                        ∧ ∃ (seq_res_2 : Identity_u),
                          seq_rel (ValF_u y) (Val_u z) seq_res_2
                          ∧ ∃ (seq_res_3 : Identity_u), seq_rel (ValF_u x) seq_res_2 seq_res_3 ∧ seq_res == seq_res_3)
                 (# unit)
                 ltac:(solver)).
Qed.

Definition homomorphism_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (x : {x: Z | True}):
  Type :=
  {{∃ (pure_res : Identity_u),
    pure_rel ⌊ x ⌋ pure_res
    ∧ ∃ (pureF_res : IdentityF_u),
      pureF_rel ⌊ f ⌋ pureF_res
      ∧ ∃ (seq_res : Identity_u),
        seq_rel pureF_res pure_res seq_res
        ∧ ∃ (f_res : Z),
          getPackRel f ⌊ x ⌋ f_res
          ∧ ∃ (pure_res_2 : Identity_u), pure_rel f_res pure_res_2 ∧ seq_res == pure_res_2}}.

#[global] Hint Unfold homomorphism_spec: lia_unfold.

Theorem homomorphism
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (x : {x: Z | True}):
  homomorphism_spec f x.
Proof.
  destruct x as [x x_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (pure_res : Identity_u),
           pure_rel x pure_res
           ∧ ∃ (pureF_res : IdentityF_u),
             pureF_rel ⌊ f ⌋ pureF_res
             ∧ ∃ (seq_res : Identity_u),
               seq_rel pureF_res pure_res seq_res
               ∧ ∃ (f_res : Z),
                 getPackRel f x f_res
                 ∧ ∃ (pure_res_2 : Identity_u), pure_rel f_res pure_res_2 ∧ seq_res == pure_res_2)
          (# unit)
          ltac:(solver)).
Qed.

Definition identity_spec (ds_daoa : Identity): Type :=
  {{∃ (pureF_res : IdentityF_u),
    pureF_rel id_upack pureF_res
    ∧ ∃ (seq_res : Identity_u), seq_rel pureF_res ⌊ ds_daoa ⌋ seq_res ∧ seq_res == ⌊ ds_daoa ⌋}}.

#[global] Hint Unfold identity_spec: lia_unfold.

Theorem identity (ds_daoa : Identity): identity_spec ds_daoa.
Proof.
  destruct ds_daoa as [ds_daoa ds_daoa_p].
  destruct ds_daoa as [x].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (pureF_res : IdentityF_u),
             pureF_rel id_upack pureF_res
             ∧ ∃ (seq_res : Identity_u), seq_rel pureF_res (Val_u x) seq_res ∧ seq_res == Val_u x)
            (# unit)
            ltac:(solver)).
Qed.

Definition seqF_spec (ds_daoh : IdentityF1) (ds_daoi : IdentityF): Type :=
  Identity.

#[global] Hint Unfold seqF_spec: lia_unfold.

Definition seqF (ds_daoh : IdentityF1) (ds_daoi : IdentityF): seqF_spec ds_daoh ds_daoi.
Proof.
  destruct ds_daoh as [ds_daoh ds_daoh_p].
  destruct ds_daoi as [ds_daoi ds_daoi_p].
  destruct ds_daoh as [f].
  - destruct ds_daoi as [x].
    + refine (Val (getPackF f x)).
Defined.

Inductive seqF_rel: IdentityF1_u → IdentityF_u → Identity_u → Prop :=
  | seqF_ValF1_ValF: ∀ f x (f_res : Z),
                     getUPackRel f x f_res → seqF_rel (ValF1_u f) (ValF_u x) (Val_u f_res).

#[global] Hint Constructors seqF_rel: core_hint_db.

#[global] Instance seqF_lookup_rel: dictionary rel seqF := { lookup' := seqF_rel }.

#[global] Instance seqF_getF: getFunc seqF_rel := { getF' := seqF }.

Theorem seqF_rel_funct [ds_daoh : IdentityF1_u] [ds_daoi : IdentityF_u]:
  ∀ (VV VV' : Identity_u), seqF_rel ds_daoh ds_daoi VV → (seqF_rel ds_daoh ds_daoi VV' → VV = VV').
Proof.
  destruct ds_daoh as [f];
  [destruct ds_daoi as [x]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve seqF_rel_funct: f_rel_funct_db.

Theorem seqF_ValF1_ValF_lem f x seqF_ValF1_ValF_lem_res:
  seqF_rel (ValF1_u f) (ValF_u x) seqF_ValF1_ValF_lem_res
  ↔ ∃ (f_res : Z), getUPackRel f x f_res ∧ seqF_ValF1_ValF_lem_res == Val_u f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite seqF_ValF1_ValF_lem: f_rel_back.

Theorem seqF_rel_ex
  (ds_daoh : IdentityF1_u)
  (ds_daoh_p : IdentityF1_wf ds_daoh ∧ True)
  (ds_daoi : IdentityF_u)
  (ds_daoi_p : IdentityF_wf ds_daoi ∧ True):
  seqF_rel ds_daoh ds_daoi ⌊ seqF (exist _ ds_daoh ds_daoh_p) (exist _ ds_daoi ds_daoi_p) -⌋.
Proof.
  Opaque seqF.
  existence_lemma_pre seqF;
  destruct ds_daoh as [f];
  [destruct ds_daoi as [x];
   [fix_notations]];
  simpl in *.
  Transparent seqF.
  all: (existence_lemma_quicksolve seqF; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve seqF_rel_ex: rel_ax_db.

#[global] Opaque seqF.

Theorem seqF__seqF_rel_rw
  (ds_daoh : IdentityF1_u)
  (ds_daoh_p : IdentityF1_wf ds_daoh ∧ True)
  (ds_daoi : IdentityF_u)
  (ds_daoi_p : IdentityF_wf ds_daoi ∧ True)
  (VV : Identity_u):
  ⌊ seqF (exist _ ds_daoh ds_daoh_p) (exist _ ds_daoi ds_daoi_p) -⌋ = VV
  ↔ seqF_rel ds_daoh ds_daoi VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite seqF__seqF_rel_rw: f_rel_funct_db.

#[global] Hint Resolve seqF__seqF_rel_rw: rel_ax_db.

#[global] Instance seqF_lookup_rw: dictionary rwLem seqF := { lookup' := seqF__seqF_rel_rw }.

Theorem seqF__seqF_rel (ds_daoh : IdentityF1) (ds_daoi : IdentityF) (VV : Identity_u):
  ⌊ seqF ds_daoh ds_daoi -⌋ = VV ↔ seqF_rel ⌊ ds_daoh ⌋ ⌊ ds_daoi ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite seqF__seqF_rel: f_rel_funct_db.

Theorem seqF__seqF_rel'
  (ds_daoh_u : IdentityF1_u)
  (ds_daoi_u : IdentityF_u)
  (ds_daoh : IdentityF1)
  (ds_daoi : IdentityF)
  (VV : Identity_u):
  ds_daoh_u = ⌊ ds_daoh ⌋
  → (ds_daoi_u = ⌊ ds_daoi ⌋ → ⌊ seqF ds_daoh ds_daoi -⌋ = VV ↔ seqF_rel ds_daoh_u ds_daoi_u VV).
Proof.
  intros -> ->. refine (seqF__seqF_rel ds_daoh ds_daoi VV).
Qed.

#[global] Hint Resolve seqF__seqF_rel': f_rel_funct_db.

Theorem seqF_rel_mk
  (ds_daoh : IdentityF1_u)
  (ds_daoh_p : IdentityF1_wf ds_daoh ∧ True)
  (ds_daoi : IdentityF_u)
  (ds_daoi_p : IdentityF_wf ds_daoi ∧ True):
  {VV: _ | seqF_rel ds_daoh ds_daoi VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, seqF_rel ds_daoh ds_daoi VV)
          (seqF (exist _ ds_daoh ds_daoh_p) (exist _ ds_daoi ds_daoi_p))
          _);
  rewrite <- seqF__seqF_rel';
  quicksolve.
Qed.

#[global] Hint Resolve seqF_rel_mk: f_rel_funct_db.

#[global] Instance seqF_pack:
  @Pack
  (IdentityF1 ::RT λ (ds_daoh : IdentityF1), IdentityF ::RT λ (ds_daoi : IdentityF), nilRT)
  (IdentityF1_u ::UT (IdentityF_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((IdentityF1
  ::RT λ (ds_daoh : IdentityF1),
       IdentityF ::RT λ (ds_daoi : IdentityF), nilRT)) ((IdentityF1_u ::UT (IdentityF_u ::UT nilUT))))
  Identity_u
  (λ (x_43496279 : ArgList (IdentityF1
                            ::RT λ (ds_daoh : IdentityF1), IdentityF ::RT λ (ds_daoi : IdentityF), nilRT))
     (v_x_43496279 : Identity_u),
   ltac:(flattenP (λ (ds_daoh : IdentityF1) (ds_daoi : IdentityF) (VV : Identity_u),
 Identity_wf VV ∧ True) x_43496279 v_x_43496279)).
Proof.
  buildPackG seqF seqF_rel seqF__seqF_rel seqF_rel_funct.
Defined.

#[global] Instance seqF_upack: @uPack (IdentityF1_u ::UT (IdentityF_u ::UT nilUT)) Identity_u.
Proof.
  buildUPackG seqF_rel seqF_rel_funct.
Defined.

Definition interchange_spec (ds_dao6 : IdentityF) (x : {x: Z | True}): Type :=
  {{∃ (pure_res : Identity_u),
    pure_rel ⌊ x ⌋ pure_res
    ∧ ∃ (seq_res : Identity_u),
      seq_rel ⌊ ds_dao6 ⌋ pure_res seq_res
      ∧ ∃ (idollar_res : Z),
        idollar_rel ⌊ x ⌋ idollar_res
        ∧ ∃ (pureF1_res : IdentityF1_u),
          pureF1_rel idollar_res pureF1_res
          ∧ ∃ (seqF_res : Identity_u), seqF_rel pureF1_res ⌊ ds_dao6 ⌋ seqF_res ∧ seq_res == seqF_res}}.

#[global] Hint Unfold interchange_spec: lia_unfold.

Theorem interchange (ds_dao6 : IdentityF) (x : {x: Z | True}): interchange_spec ds_dao6 x.
Proof.
  destruct ds_dao6 as [ds_dao6 ds_dao6_p].
  destruct x as [x x_p].
  destruct ds_dao6 as [f].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (pure_res : Identity_u),
             pure_rel x pure_res
             ∧ ∃ (seq_res : Identity_u),
               seq_rel (ValF_u f) pure_res seq_res
               ∧ ∃ (idollar_res : Z),
                 idollar_rel x idollar_res
                 ∧ ∃ (pureF1_res : IdentityF1_u),
                   pureF1_rel idollar_res pureF1_res
                   ∧ ∃ (seqF_res : Identity_u), seqF_rel pureF1_res (ValF_u f) seqF_res ∧ seq_res == seqF_res)
            (# unit)
            ltac:(solver)).
Qed.
