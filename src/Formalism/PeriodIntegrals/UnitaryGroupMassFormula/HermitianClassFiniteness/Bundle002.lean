module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.LevelB
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField Matrix Formalism.UG PI.InHHClassFin

namespace PI.UnitaryGroupMassFormula.InHHClassFin

variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}

theorem sig_eq (I : Formalism.MainNotions.S.AutInst) : (I.cm.sig : I.E →+* I.E) = starRingEnd I.E :=
  RingHom.ext fun _ => rfl

def Frame.Jt (fr : Frame I S) : Matrix (Fin fr.m ⊕ Fin fr.k) (Fin fr.m ⊕ Fin fr.k) I.E :=
  cT (starRingEnd I.E) fr.B * I.J * fr.B

theorem Frame.J'_eq (fr : Frame I S) : fr.J' = fr.Jt.toBlocks₂₂ := rfl

theorem hform_add_left {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x x' y : n → A) : hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_left {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (c : A) (x y : n → A) : hform σ J (c • x) y = σ c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_zero_left {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (y : n → A) : hform σ J 0 y = 0 := by
  simp [hform]

theorem hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y y' : n → A) : hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (c : A) (x y : n → A) : hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_sum_right {A : Type} [CommRing A] {n ι : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x : n → A) (s : Finset ι) (y : ι → n → A) :
    hform σ J x (∑ i ∈ s, y i) = ∑ i ∈ s, hform σ J x (y i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hform]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_right, ih]

theorem hform_span_left (σ : I.E →+* I.E) (w : Fin I.n → I.E)
    (hw : ∀ s ∈ S, hform σ I.J s w = 0) :
    ∀ u ∈ Submodule.span I.E S, hform σ I.J u w = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact hw x hx
  | zero => exact hform_zero_left _ _ _
  | add x y _ _ hx hy => rw [hform_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [hform_smul_left, hx, mul_zero]

theorem hform_swap (x y : Fin I.n → I.E) :
    hform (starRingEnd I.E) I.J y x = starRingEnd I.E (hform (starRingEnd I.E) I.J x y) := by
  have hJ : ∀ i j, starRingEnd I.E (I.J i j) = I.J j i := by
    intro i j
    have h := congrFun (congrFun I.J_herm j) i
    simpa [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] using h

  simp only [hform, map_sum, map_mul, starRingEnd_self_apply, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem Frame.Jt_apply (fr : Frame I S) (p q : Fin fr.m ⊕ Fin fr.k) :
    fr.Jt p q = hform (starRingEnd I.E) I.J (fun a => fr.B a p) (fun a => fr.B a q) := by
  simp only [Frame.Jt, hform, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem Frame.Jt_12 (fr : Frame I S) : fr.Jt.toBlocks₁₂ = 0 := by
  ext p q
  show fr.Jt (Sum.inl p) (Sum.inr q) = 0
  rw [Frame.Jt_apply]
  exact hform_span_left _ _ (fun s hs => fr.orth s hs q) _ (fr.col_span p)

theorem Frame.Jt_21 (fr : Frame I S) : fr.Jt.toBlocks₂₁ = 0 := by
  ext p q
  show fr.Jt (Sum.inr p) (Sum.inl q) = 0
  rw [Frame.Jt_apply, hform_swap, hform_span_left _ _ (fun s hs => fr.orth s hs p) _ (fr.col_span q), map_zero]

theorem Frame.Jt_blocks (fr : Frame I S) : fr.Jt = Matrix.fromBlocks fr.Jt.toBlocks₁₁ 0 0 fr.J' := by
  have h := (Matrix.fromBlocks_toBlocks fr.Jt).symm
  rw [Frame.Jt_12, Frame.Jt_21, ← Frame.J'_eq] at h
  exact h

theorem cT_mul' {m p q : Type} [Fintype p] (M : Matrix m p I.E) (N : Matrix p q I.E) :
    cT (starRingEnd I.E) (M * N) = cT (starRingEnd I.E) N * cT (starRingEnd I.E) M := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem Frame.Jt_inv (fr : Frame I S) :
    fr.Jt * (fr.Bi * I.J⁻¹ * cT (starRingEnd I.E) fr.Bi) = 1 := by
  have hJ : I.J * I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr I.J_det)
  have h1 : cT (starRingEnd I.E) (1 : Matrix (Fin fr.m ⊕ Fin fr.k) (Fin fr.m ⊕ Fin fr.k) I.E) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.one_apply, h, Ne.symm h]
  have hc : cT (starRingEnd I.E) fr.B * cT (starRingEnd I.E) fr.Bi = 1 := by
    rw [← cT_mul', fr.inv_mul, h1]
  calc fr.Jt * (fr.Bi * I.J⁻¹ * cT (starRingEnd I.E) fr.Bi)
      = cT (starRingEnd I.E) fr.B * I.J * (fr.B * fr.Bi) * I.J⁻¹ * cT (starRingEnd I.E) fr.Bi := by
        simp only [Frame.Jt, Matrix.mul_assoc]
    _ = cT (starRingEnd I.E) fr.B * cT (starRingEnd I.E) fr.Bi := by
        rw [fr.mul_inv, Matrix.mul_one, Matrix.mul_assoc (cT _ fr.B), hJ, Matrix.mul_one]
    _ = 1 := hc

theorem Frame.det_blocks (fr : Frame I S) : fr.Jt.toBlocks₁₁.det ≠ 0 ∧ fr.J'.det ≠ 0 := by
  have h1 : fr.Jt.det ≠ 0 := by
    intro h
    have h2 := congrArg Matrix.det (Frame.Jt_inv fr)
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  rw [Frame.Jt_blocks, Matrix.det_fromBlocks_zero₂₁] at h1
  exact ⟨left_ne_zero_of_mul h1, right_ne_zero_of_mul h1⟩

theorem Frame.J'_herm (fr : Frame I S) : IsHerm (I.cm.sig : I.E →+* I.E) fr.J' := by
  rw [Formalism.UG.IsHerm, sig_eq]
  ext p q
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [Frame.J'_eq]
  show starRingEnd I.E (fr.Jt (Sum.inr q) (Sum.inr p)) = fr.Jt (Sum.inr p) (Sum.inr q)
  rw [Frame.Jt_apply, Frame.Jt_apply,
    hform_swap (fun a => fr.B a (Sum.inr q)) (fun a => fr.B a (Sum.inr p))]

theorem hform_eq_dot {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y : n → A) : hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_cT {p : Type} [Fintype p] (B : Matrix (Fin I.n) p I.E) (u v : p → I.E) :
    hform (starRingEnd I.E) (cT (starRingEnd I.E) B * I.J * B) u v =
      hform (starRingEnd I.E) I.J (B *ᵥ u) (B *ᵥ v) := by
  rw [hform_eq_dot, hform_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  congr 1
  funext i

  simp [Formalism.UG.cT, vecMul, mulVec, dotProduct, map_sum, mul_comm]

theorem Frame.hform_J' (fr : Frame I S) (x y : Fin fr.k → I.E) :
    hform (starRingEnd I.E) fr.J' x y =
      hform (starRingEnd I.E) I.J (fr.B *ᵥ Sum.elim 0 x) (fr.B *ᵥ Sum.elim 0 y) := by
  rw [← hform_cT]
  simp only [hform, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, zero_mul,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  rfl

theorem Frame.orth_vec (fr : Frame I S) (x : Fin fr.k → I.E) :
    ∀ s ∈ S, hform (starRingEnd I.E) I.J s (fr.B *ᵥ Sum.elim 0 x) = 0 := by
  intro s hs
  have e : fr.B *ᵥ Sum.elim 0 x = ∑ b, x b • (fun i => fr.B i (Sum.inr b)) := by
    ext i
    simp [mulVec, dotProduct, Fintype.sum_sum_type, Finset.sum_apply, mul_comm]
  rw [e, hform_sum_right]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [hform_smul_right, fr.orth s hs b, mul_zero]

theorem Frame.vec_ne_zero (fr : Frame I S) (x : Fin fr.k → I.E) (hx : x ≠ 0) :
    fr.B *ᵥ Sum.elim 0 x ≠ 0 := by
  intro h
  apply hx
  have hw : Sum.elim (0 : Fin fr.m → I.E) x = 0 := by
    have h2 := congrArg (fun v => fr.Bi *ᵥ v) h
    simpa [Matrix.mulVec_mulVec, fr.inv_mul] using h2
  funext b
  have h3 := congrFun hw (Sum.inr b)
  simpa using h3

theorem frameGram : FrameGram := by
  intro I S fr hS
  refine ⟨Frame.J'_herm fr, isUnit_iff_ne_zero.mpr (Frame.det_blocks fr).2, I.cm.totReal, fun ι => ?_⟩
  unfold Formalism.UG.IsDefiniteAt
  simp only [sig_eq]
  rcases hS ι with hpos | hneg
  · left
    intro x hx
    rw [Frame.hform_J']
    exact hpos _ (Frame.vec_ne_zero fr x hx) (Frame.orth_vec fr x)
  · right
    intro x hx
    rw [Frame.hform_J']
    exact hneg _ (Frame.vec_ne_zero fr x hx) (Frame.orth_vec fr x)

end PI.UnitaryGroupMassFormula.InHHClassFin
end
end

section

noncomputable section

open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

theorem one_mem_Kg (I : Formalism.MainNotions.S.AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · show ((1 : I.Gf) : GL (Fin I.n) _) ∈ Formalism.UG.stabGL I.Lf
    simpa using (Formalism.UG.stabGL I.Lf).one_mem
  · simp [Formalism.MainNotions.S.AutInst.fmat]

theorem kgNhd : KgNhd := by
  intro I g x hg
  letI := I.topf
  haveI := I.topf_group
  have hK : I.Kg g ∈ nhds (1 : I.Gf) := (I.topf_open g hg).mem_nhds (one_mem_Kg I g)
  have hc : Continuous fun h : I.Gf => x⁻¹ * h * x := by fun_prop
  have hT : {h : I.Gf | x⁻¹ * h * x ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    have hK' : I.Kg g ∈ nhds (x⁻¹ * 1 * x) := by simpa using hK
    exact hc.continuousAt hK'
  obtain ⟨g', hg', hsub⟩ := I.topf_basis _ hT
  exact ⟨g', hg', fun h hh => hsub hh⟩

end PI.UnitaryGroupMassFormula.InHHClassFin
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.InHHClassFin

theorem sigConj : SigConj := by
  intro I τ
  ext a
  show τ (star a) = starRingEnd ℂ (τ a)
  exact I.cm.cmUnram.2.1 τ a

end PI.UnitaryGroupMassFormula.InHHClassFin
end
end

section

noncomputable section

open NumberField Matrix IsDedekindDomain Formalism.UG Formalism.UG.P PI.InHHClassFin
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

theorem levelStep : LevelStep := by
  intro I m k B Bi hBB hBB' J' g hg
  classical
  obtain ⟨d1, hd1, h1⟩ := lvB_lat_up (F := I.F) I.L I.L_fg
  obtain ⟨d2, hd2, h2⟩ := lvB_lat_down (F := I.F) I.L I.L_span
  obtain ⟨dc, hdc, hc⟩ := lvB_denom_fam (F := I.F) (E := I.E)
    (fun p : (Fin I.n × (Fin m ⊕ Fin k)) ⊕ ((Fin m ⊕ Fin k) × Fin I.n) => match p with
      | .inl q => inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (B q.1 q.2)
      | .inr q => inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (Bi q.1 q.2))
  have hg0 : ((g : ℕ) : 𝓞 I.F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set D : 𝓞 I.F := (g : 𝓞 I.F) * d2 * dc * dc * d1 with hDdef
  have hD : D ≠ 0 := by
    simp only [hDdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hg0 hd2) hdc) hdc) hd1
  set cD : tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) :=
    ⟨levelafC I.E D, levelafC_mem D⟩ with hcD
  set Pr : Subgroup (GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :=
    princ (n := Fin k) (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F)).subtype
      (Ideal.span {cD}) with hPr
  refine ⟨stdLevel I J' ⊓ Pr.subgroupOf (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)),
    inf_le_left, ?_, ?_⟩
  ·
    rw [Subgroup.inf_relIndex_left, stdLevel, Subgroup.relIndex_subgroupOf]
    swap
    · rw [Formalism.UG.Final.LevelAfLStd I.F I.E (Fin k) I.cm.sig J']; exact inf_le_left
    have : Finite (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) ⧸
        Ideal.span {cD}) := levelaf_finite_quot D hD cD rfl
    have h0 := levelaf_princ_relIndex_ne_zero (n := Fin k)
      (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F)) (Ideal.span {cD})
    have hle : levelAfL I.cm.sig J' (stdLat (n := Fin k) (A := I.E) (𝓞 I.E)) ≤
        (bc (n := Fin k) (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E)
          (intAd I.F)).subtype).range := by
      rw [Formalism.UG.Final.LevelAfLStd I.F I.E (Fin k) I.cm.sig J', levelAf, level]
      refine inf_le_right.trans ?_
      rw [Formalism.UG.Final.StabStd _ _ (Fin k) Subtype.val_injective]
      exact le_refl _
    exact fun h => h0 (Subgroup.relIndex_eq_zero_of_le_right hle h)
  · intro y hy h hh
    have hyP : (y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) ∈ Pr :=
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hy).2
    set P : Matrix (Fin I.n) (Fin m ⊕ Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) :=
      B.map (inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F)) with hP
    set Q : Matrix (Fin m ⊕ Fin k) (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) :=
      Bi.map (inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F)) with hQ
    have hPQ : P * Q = 1 := by
      rw [hP, hQ, ← Matrix.map_mul, hBB, Matrix.map_one _ (map_zero _) (map_one _)]
    have hQP : Q * P = 1 := by
      rw [hP, hQ, ← Matrix.map_mul, hBB', Matrix.map_one _ (map_zero _) (map_one _)]
    have hPi : ∀ i j, (levelafC I.E dc • P) i j ∈
        tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) :=
      fun i j => by simpa [P, smul_eq_mul] using hc (.inl (i, j))
    have hQi : ∀ i j, (levelafC I.E dc • Q) i j ∈
        tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) :=
      fun i j => by simpa [Q, smul_eq_mul] using hc (.inr (i, j))
    have hscal : ((cD : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) =
        (g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) * levelafC I.E d2 * levelafC I.E dc *
          levelafC I.E dc * levelafC I.E d1 := by
      simp only [hcD, hDdef, levelafC_mul, lvB_C_natCast]
    have hgS : (g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) ∈
        tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) := natCast_mem _ g
    have hblk : ∀ w : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F), w ∈ Pr →
        ∃ N : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F),
          (∀ i j, N i j ∈ tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F)) ∧
          Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            (w : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) =
          1 + ((g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) * levelafC I.E d2 * levelafC I.E dc *
            levelafC I.E dc * levelafC I.E d1) • N := by
      intro w hw
      obtain ⟨N0, hN0, hw0⟩ := lvA_princ_form _ cD w hw
      refine ⟨Matrix.fromBlocks 0 0 0 N0, ?_, ?_⟩
      · intro i j
        rcases i with i | i <;> rcases j with j | j <;> simp [hN0, zero_mem]
      · rw [hw0, ← hscal]
        ext i j
        rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
    have hfm : ((h : GL (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) =
        P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
          ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q := hh
    obtain ⟨N, hN, hu⟩ := hblk _ hyP
    obtain ⟨N', hN', hu'⟩ := hblk _ (Pr.inv_mem hyP)
    have hinv : (P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
          ((((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)))⁻¹ : GL (Fin k) _) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q) *
        (P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
          ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q) = 1 := by
      have e : P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)))⁻¹ : GL (Fin k) _) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q *
          (P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q) =
          P * (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)))⁻¹ : GL (Fin k) _) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * (Q * P) *
            Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F))) * Q := by
        simp only [Matrix.mul_assoc]
      rw [e, hQP, Matrix.mul_one, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        Units.inv_mul, Matrix.fromBlocks_one, Matrix.mul_one, hPQ]
    refine ⟨?_, ?_⟩
    · show (h : GL (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) ∈ stabGL I.Lf
      intro z
      constructor
      · intro hz
        rw [hfm]
        exact lvA_maps _ I.Lf _ _ _ _ hgS h1 h2 P Q hPQ hPi hQi N hN _ hu z hz
      · intro hz
        rw [hfm] at hz
        have := lvA_maps _ I.Lf _ _ _ _ hgS h1 h2 P Q hPQ hPi hQi N' hN' _ hu' _ hz
        rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at this
    · intro z hz
      show ∃ w ∈ I.Lf, (I.fmat h - 1) *ᵥ z = (g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) • w
      rw [show I.fmat h = _ from hfm]
      exact lvA_key _ I.Lf _ _ _ _ h1 h2 P Q hPQ hPi hQi N hN _ hu z hz

end PI.UnitaryGroupMassFormula.InHHClassFin
end
end
