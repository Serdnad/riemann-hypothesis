module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle006
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle008
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValUniqOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL]

def blkMod (R : Type) [Field R] (v : Fin P.nV) (s : Fin (P.n' v)) :
    Submodule R (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) R) :=
  if Antitone (lamAt (P.lam0 v) s) then dualWeyl R (P.m + 1) (P.m + 1) (nuOf (lamAt (P.lam0 v) s)) else ⊥

def BlockRational (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G M : Tau → Matrix (Fin n) (Fin n) ℂ)
    (embLL : LL →+* ℂ) (lam : Tau → DomWeight n) : Prop :=
  ∀ v (s : Fin (P.n' v)) (f : MvPolynomial (Fin n × Fin n) ℤ), f ∈ delSq ℤ n (lam (pos ⟨v, s⟩)) →
    ∃ F ∈ blkMod P LL v s, ∀ y : Frames G,
      (zAt P h pos M y.1 v s).det ^ (eAt P v s) *
          eval (fun x => zAt P h pos M y.1 v s x.1 x.2) (MvPolynomial.map embLL F) =
        (y.1 (pos ⟨v, s⟩)).det ^ (lam (pos ⟨v, s⟩)).detShift *
          eval (fun x => y.1 (pos ⟨v, s⟩) x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)

variable {P}

theorem evRat_gen {h : P.m + 1 = n} {pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau} {G M : Tau → Matrix (Fin n) (Fin n) ℂ}
    {embLL : LL →+* ℂ} {lam : Tau → DomWeight n} (hb : BlockRational P h pos G M embLL lam) (r : LL)
    (f : Tau → MvPolynomial (Fin n × Fin n) ℤ) (hf : ∀ τ, f τ ∈ delSq ℤ n (lam τ)) :
    ∃ Q ∈ VtupR P LL, ∀ z : Frames G, evC P h pos G M (MvPolynomial.map embLL Q) z =
      fnOf G (shiftOf lam) 1 (embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))) z := by
  choose F hF hev using fun v s => hb v s (f (pos ⟨v, s⟩)) (hf _)
  refine ⟨r • ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb LL s (F v s)),
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun v => ∏ s, blockEmb LL s (F v s),
      fun v => Submodule.subset_span ⟨F v, hF v, rfl⟩, rfl⟩), fun z => ?_⟩
  have hmap : MvPolynomial.map embLL (r • ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb LL s (F v s))) =
      embLL r • ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (MvPolynomial.map embLL (F v s))) := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [MvPolynomial.map_rename, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    exact MvPolynomial.map_rename _ _ _
  rw [hmap, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, evC_prod]
  congr 1
  have h1 : (∏ v, ∏ s : Fin (P.n' v), ((zAt P h pos M z.1 v s).det ^ (eAt P v s) *
      eval (fun x => zAt P h pos M z.1 v s x.1 x.2) (MvPolynomial.map embLL (F v s)))) =
      ∏ τ, ((z.1 τ).det ^ (lam τ).detShift *
        eval (fun x => z.1 τ x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) (f τ))) := by
    rw [← pos.prod_comp, Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => hev v s z
  rw [h1, Finset.prod_mul_distrib]
  show _ = (∏ τ, ((1 : Tau → Matrix (Fin n) (Fin n) ℂ) τ * z.1 τ).det ^ shiftOf lam τ) *
    eval (fun x : Tau × Fin n × Fin n => ((1 : Tau → Matrix (Fin n) (Fin n) ℂ) x.1 * z.1 x.1) x.2.1 x.2.2)
      (ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)))
  simp only [Pi.one_apply, Matrix.one_mul, ten, map_prod, eval_rename, Function.comp_def, shiftOf]

theorem evRat_of_blocks {h : P.m + 1 = n} {pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau}
    {G M : Tau → Matrix (Fin n) (Fin n) ℂ} {embLL : LL →+* ℂ} {lam : Tau → DomWeight n}
    (hb : BlockRational P h pos G M embLL lam) (Pp : MvPolynomial (Tau × Fin n × Fin n) ℂ)
    (hP : Pp ∈ AddSubgroup.closure {q | ∃ (r : LL) (f : Tau → MvPolynomial (Fin n × Fin n) ℤ),
      (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
      q = embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}) :
    ∃ Q ∈ VtupR P LL, ∀ z : Frames G, evC P h pos G M (MvPolynomial.map embLL Q) z = fnOf G (shiftOf lam) 1 Pp z := by
  induction hP using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hf, rfl⟩ := hx
    exact evRat_gen hb r f hf
  | zero => exact ⟨0, Submodule.zero_mem _, fun z => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Q, hQ, e⟩ := hx
    obtain ⟨Q', hQ', e'⟩ := hy
    exact ⟨Q + Q', Submodule.add_mem _ hQ hQ', fun z => by
      rw [map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, e z, e' z]⟩
  | neg x _ hx =>
    obtain ⟨Q, hQ, e⟩ := hx
    exact ⟨-Q, Submodule.neg_mem _ hQ, fun z => by
      rw [map_neg, map_neg, map_neg, Pi.neg_apply, Pi.neg_apply, e z]⟩

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

def BlockRationalityAtPlace (X : Formalism.L2.Herm.Herm0 D) (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) : Prop :=
  BlockRational (D.gat u w hg).P (locAt X u w hg B).rk (Gt.gat_pos u w hg) (gramC (gramN D 0 (Nat.zero_le _)) (embT D))
    (crdB (embT D) (locAt X u w hg B).B) D.what₂.embLL ((D.fm u).lam 0)



theorem evRatRep_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E)
    (hb : BlockRationalityAtPlace X Gt u w hg B) :
    EvRatRep (embT D) D.what₂.embLL (D.gat u w hg) (locAt X u w hg B) (Gt.gat_pos u w hg) (embFr T u) := by
  intro x c
  obtain ⟨Pp, hPp, e⟩ := ((((T u).val0).rat _).1 ⟨x, rfl⟩).2 c
  obtain ⟨Q, hQ, hev⟩ := evRat_of_blocks hb Pp hPp
  refine ⟨Q, hQ, fun z => ?_⟩
  rw [hev z]
  show _ = (D.fm u).emb 0 x c (((T u).val0).eY.symm z)
  rw [e, Equiv.apply_symm_apply, lamT_zero]

end Formalism.L2.G
end
end

section

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix MvPolynomial
open scoped TensorProduct

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

def genericBlockMatrix (v : Fin P.nV) (s : Fin (P.n' v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (XR P ℂ) :=
  Matrix.of fun a b => X (⟨v, (s, (a, b))⟩ : Var P)

def genDet : XR P ℂ := ∏ v, ∏ s : Fin (P.n' v), (genericBlockMatrix P v s).det

theorem eval_genDet (x : Var P → ℂ) :
    eval x (genDet P) = ∏ v, ∏ s : Fin (P.n' v), (Matrix.of fun a b => x ⟨v, (s, (a, b))⟩ :
      Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det := by
  unfold genDet
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [genericBlockMatrix]

theorem genDet_ne_zero : genDet P ≠ 0 := by
  intro h
  have h1 := eval_genDet P (fun x => if x.2.2.1 = x.2.2.2 then 1 else 0)
  rw [h, map_zero] at h1
  have h2 : ∀ (v : Fin P.nV) (s : Fin (P.n' v)),
      (Matrix.of fun a b => (fun x : Var P => if x.2.2.1 = x.2.2.2 then (1 : ℂ) else 0) ⟨v, (s, (a, b))⟩ :
        Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det = 1 := by
    intro v s
    have : (Matrix.of fun a b => (fun x : Var P => if x.2.2.1 = x.2.2.2 then (1 : ℂ) else 0) ⟨v, (s, (a, b))⟩ :
        Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) = 1 := by
      ext a b
      simp [Matrix.one_apply]
    rw [this, Matrix.det_one]
  simp only [h2, Finset.prod_const_one] at h1
  exact zero_ne_one h1

theorem eq_zero_of_blocks (Q : XR P ℂ)
    (h : ∀ z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ, (∀ v s, IsUnit (z v s).det) →
      eval (fun x : Var P => z x.1 x.2.1 x.2.2.1 x.2.2.2) Q = 0) : Q = 0 := by
  have h0 : Q * genDet P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero, eval_genDet]
    by_cases hx : ∀ v (s : Fin (P.n' v)), IsUnit (Matrix.of fun a b => x ⟨v, (s, (a, b))⟩ :
        Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det
    · have h1 := h (fun v s => Matrix.of fun a b => x ⟨v, (s, (a, b))⟩) hx
      have h2 : (fun y : Var P => (fun v (s : Fin (P.n' v)) => (Matrix.of fun a b => x ⟨v, (s, (a, b))⟩ :
          Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) y.1 y.2.1 y.2.2.1 y.2.2.2) = x := by
        funext y
        rfl
      rw [h2] at h1
      rw [h1, zero_mul]
    · push Not at hx
      obtain ⟨v, s, hvs⟩ := hx
      have h3 : (Matrix.of fun a b => x ⟨v, (s, (a, b))⟩ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det = 0 := by
        by_contra hne
        exact hvs (isUnit_iff_ne_zero.2 hne)
      have h4 : (∏ v, ∏ s : Fin (P.n' v), (Matrix.of fun a b => x ⟨v, (s, (a, b))⟩ :
          Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) (Finset.prod_eq_zero (Finset.mem_univ s) h3)
      rw [h4, mul_zero]
  exact (mul_eq_zero.1 h0).resolve_right (genDet_ne_zero P)

variable {Tau : Type} [Fintype Tau] {n : ℕ}

def cRev (z : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ :=
  ((z.submatrix id Fin.rev)ᵀ)⁻¹

theorem isUnit_det_rev (z : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (hz : IsUnit z.det) :
    IsUnit ((z.submatrix id Fin.rev)ᵀ).det := by
  have h1 : (z.submatrix id Fin.rev).det = Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (P.m + 1))) * z.det :=
    Matrix.det_permute' Fin.revPerm z
  rw [Matrix.det_transpose, h1]
  refine IsUnit.mul ?_ hz
  exact (Units.isUnit (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (P.m + 1))))).map (Int.castRingHom ℂ)

theorem cRev_spec (z : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (hz : IsUnit z.det) :
    ((cRev P z)⁻¹)ᵀ.submatrix id Fin.rev = z := by
  unfold cRev
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_rev P z hz), Matrix.transpose_transpose]
  ext a b
  simp

theorem isUnit_det_cRev (z : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (hz : IsUnit z.det) : IsUnit (cRev P z).det := by
  unfold cRev
  rw [Matrix.det_nonsing_inv]
  exact (isUnit_det_rev P z hz).ringInverse

def blockPreimageMatrix (z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (x : Σ v : Fin P.nV, Fin (P.n' v)) :
    Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ :=
  if Even x.2.val then z x.1 x.2 else cRev P (z x.1 x.2)

theorem isUnit_det_block_preimage (z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)
    (hz : ∀ v s, IsUnit (z v s).det) (x : Σ v : Fin P.nV, Fin (P.n' v)) : IsUnit (blockPreimageMatrix P z x).det := by
  unfold blockPreimageMatrix
  split_ifs
  · exact hz _ _
  · exact isUnit_det_cRev P _ (hz _ _)

def frameOf (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (M : Tau → Matrix (Fin n) (Fin n) ℂ)
    (z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) : Tau → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => (M τ)⁻¹ * (blockPreimageMatrix P z (pos.symm τ)).submatrix (finCongr h).symm (finCongr h).symm

theorem isUnit_det_frameOf (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det)
    (z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (hz : ∀ v s, IsUnit (z v s).det) (τ : Tau) :
    IsUnit (frameOf P h pos M z τ).det := by
  unfold frameOf
  rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  refine IsUnit.mul ?_ (isUnit_det_block_preimage P z hz _)
  rw [Matrix.det_nonsing_inv]
  exact (hM τ).ringInverse

theorem zAt_frameOf (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det)
    (z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (hz : ∀ v s, IsUnit (z v s).det)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    zAt P h pos M (frameOf P h pos M z) v s = z v s := by
  have key : reM P h (M (pos ⟨v, s⟩) * frameOf P h pos M z (pos ⟨v, s⟩)) = blockPreimageMatrix P z ⟨v, s⟩ := by
    unfold frameOf
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hM _), Equiv.symm_apply_apply]
    ext a b
    simp [reM]
  unfold zAt
  rw [key]
  unfold blockPreimageMatrix
  by_cases hs : Even s.val
  · simp only [hs, if_true]
  · simp only [hs, if_false]
    exact cRev_spec P (z v s) (hz v s)

theorem evC_inj (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (Q : XR P ℂ) (hQ : evC P h pos G M Q = 0) : Q = 0 := by
  apply eq_zero_of_blocks P Q
  intro z hz
  have h1 := congrFun hQ (⟨frameOf P h pos M z, isUnit_det_frameOf P h pos M hM z hz⟩ : Frames G)
  have h2 : (∏ v, ∏ s : Fin (P.n' v), (zAt P h pos M (frameOf P h pos M z) v s).det ^ (eAt P v s)) *
      eval (fun x : Var P => zAt P h pos M (frameOf P h pos M z) x.1 x.2.1 x.2.2.1 x.2.2.2) Q = 0 := h1
  simp only [zAt_frameOf P h pos M hM z hz] at h2
  refine (mul_eq_zero.1 h2).resolve_left ?_
  exact Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun s _ => zpow_ne_zero _ (hz v s).ne_zero

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {Tau : Type} [Fintype Tau] {p : ℕ}

theorem isUnit_det_crdB (emb : Tau → E →+* ℂ) (B : GL (Fin n) E) (τ : Tau) : IsUnit (crdB emb B τ).det := by
  have h1 : (crdB emb B τ).det = emb τ ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det :=
    (RingHom.map_det (emb τ) _).symm
  rw [h1]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (B⁻¹ : GL (Fin n) E))).map (emb τ)

theorem evInj_pf (emb : Tau → E →+* ℂ) (G : GAtP p) (A : LocAt F E n G)
    (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau) : EvInj emb G A pos (J := J) :=
  fun Q hQ => evC_inj G.P A.rk pos (gramC J emb) (crdB emb A.B) (isUnit_det_crdB emb A.B) Q hQ

end Loc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem evInj_rec {D : D7} {X : Formalism.L2.Herm.Herm0 D} (Gt : GatTies D) (I : CmpIn D X) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    EvInj (embT D) (D.gat u w hg) (locAt X u w hg I.B) (Gt.gat_pos u w hg) (J := gramN D 0 (Nat.zero_le _)) :=
  evInj_pf (embT D) (D.gat u w hg) (locAt X u w hg I.B) (Gt.gat_pos u w hg)

end Formalism.L2.G
end
end
