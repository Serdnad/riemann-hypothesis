module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

namespace USum

variable {n : ℕ} {ε : Fin n → Bool}

theorem inK_real_smul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inK ε ((t : ℂ) • X) := by
  obtain ⟨hG, hC⟩ := hX
  refine ⟨?_, ?_⟩
  · unfold inG at hG ⊢
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    rw [ht, ← smul_add, hG, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hC]

def zM (a b : Fin n) (c : ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b c - Matrix.single b a (star c)

theorem Jm_comm_zM {a b : Fin n} (hab : ε a = ε b) (c : ℂ) : Jm ε * zM a b c = zM a b c * Jm ε := by
  have hd : ∀ i j, (i = a ∧ j = b) ∨ (i = b ∧ j = a) →
      (if ε i then (1 : ℂ) else -1) = if ε j then 1 else -1 := by
    rintro i j (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hab]
  unfold Jm
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : (i = a ∧ j = b) ∨ (i = b ∧ j = a)
  · rw [hd i j hij, mul_comm]
  · have hz : zM a b c i j = 0 := by
      unfold zM
      simp only [Matrix.sub_apply, Matrix.single_apply]
      push_neg at hij
      rw [if_neg, if_neg, sub_zero]
      · exact fun h => hij.2 h.1.symm h.2.symm
      · exact fun h => hij.1 h.1.symm h.2.symm
    rw [hz, mul_zero, zero_mul]

theorem inK_zM {a b : Fin n} (hab : ε a = ε b) (c : ℂ) : inK ε (zM a b c) := by
  have hH : (zM a b c)ᴴ = -zM a b c := by
    ext i j
    have e1 : (a = j ∧ b = i) ↔ (b = i ∧ a = j) := and_comm
    have e2 : (b = j ∧ a = i) ↔ (a = i ∧ b = j) := and_comm
    simp only [zM, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply, e1, e2]
    split_ifs <;> simp
  refine ⟨?_, (Jm_comm_zM hab c).symm⟩
  unfold inG
  rw [hH, Jm_comm_zM hab c, neg_mul, neg_add_cancel]

section Act

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem actM_single (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (c : ℂ) :
    actM E (Matrix.single a b c) = c • E a b := by
  classical
  unfold actM
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [Matrix.single_apply]
  · intro j _ hj
    simp [Matrix.single_apply, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [Matrix.single_apply, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem actM_sub (E : Fin n → Fin n → Module.End ℂ M) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actM E (X - Y) = actM E X - actM E Y := by
  unfold actM
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem actM_zM (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (c : ℂ) :
    actM E (zM a b c) = c • E a b - star c • E b a := by
  unfold zM
  rw [actM_sub, actM_single, actM_single]

end Act

section Rep

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}

private theorem exp_smul_mem_Kset_of_skew_of_commute_Jm {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
  obtain ⟨hG, hC⟩ := hX
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hskew : Xᴴ = -X := by
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
      rw [hC]
      exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(X * Jm ε) * Jm ε := by rw [h1]
      _ = -X := by rw [Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  have hY : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
    rw [Matrix.conjTranspose_smul, hskew, ht, smul_neg]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hY,
      ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl ((t : ℂ) • X))), add_neg_cancel,
      NormedSpace.exp_zero]
  · letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    have hc : Commute ((t : ℂ) • X) (Jm ε) := by
      show (t : ℂ) • X * Jm ε = Jm ε * ((t : ℂ) • X)
      rw [Matrix.smul_mul, Matrix.mul_smul, hC]
    exact hc.exp_left.eq

theorem phi_actM_inK (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    [FiniteDimensional ℂ V₁]
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (v u : V₁) (hu : (u : D₁) = actM E₁ X v) :
    ((actM E₂ X ((φ v : V₂) : D₂) : D₂) : H₂) = (((φ u : V₂) : D₂) : H₂) := by
  classical
  have hk : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := fun t => exp_smul_mem_Kset_of_skew_of_commute_Jm hX t
  choose w hwV hw using fun t : ℝ => hVK₁ _ (hk t) (v : D₁) v.2
  let W : ℝ → V₁ := fun t => ⟨w t, hwV t⟩
  have hW : ∀ t, (((W t : V₁) : D₁) : H₁) = σ₁ (NormedSpace.exp ((t : ℂ) • X)) ((v : D₁) : H₁) := hw
  have h1 : HasDerivAt (fun t : ℝ => (((W t : V₁) : D₁) : H₁)) (((u : V₁) : D₁) : H₁) 0 := by
    have hd := hD₁.deriv X hX.1 (v : D₁)
    rw [← hu] at hd
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hW t)
  have h2 : HasDerivAt W u 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at h1 ⊢
    rw [← Asymptotics.isLittleO_norm_left] at h1 ⊢
    exact h1.congr_left (fun h => rfl)
  let L : V₁ →L[ℂ] H₂ := LinearMap.toContinuousLinearMap ((D₂.subtype.comp V₂.subtype).comp φ)
  have h3 : HasDerivAt (fun t => L (W t)) (L u) 0 :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h4 : (fun t => L (W t)) =
      fun t : ℝ => σ₂ (NormedSpace.exp ((t : ℂ) • X)) (((φ v : V₂) : D₂) : H₂) := by
    funext t
    exact hφK _ (hk t) v (W t) (hW t)
  rw [h4] at h3
  exact (hD₂.deriv X hX.1 ((φ v : V₂) : D₂)).unique h3

private theorem eq_half_smul_sub_I_smul_combo {M : Type*} [AddCommGroup M] [Module ℂ M] (A B : M) :
    A = (1 / 2 : ℂ) • ((A - B) - Complex.I • (Complex.I • A - (-Complex.I) • B)) := by
  rw [smul_sub Complex.I, smul_smul, smul_smul, Complex.I_mul_I, mul_neg, Complex.I_mul_I, neg_neg,
    neg_one_smul, one_smul]
  rw [show (A - B) - (-A - B) = (2 : ℂ) • A by module, smul_smul]
  norm_num

theorem phi_E_comm (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    [FiniteDimensional ℂ V₁] (hst : IsKStableSub ε E₁ V₁)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    {a b : Fin n} (hab : ε a = ε b) (v : V₁) :
    E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hst a b hab _ v.2⟩ : V₂) : D₂) := by
  have hmem : ∀ c : ℂ, c • E₁ a b (v : D₁) - star c • E₁ b a (v : D₁) ∈ V₁ := fun c =>
    V₁.sub_mem (V₁.smul_mem _ (hst a b hab _ v.2)) (V₁.smul_mem _ (hst b a hab.symm _ v.2))
  let wc : ℂ → V₁ := fun c => ⟨c • E₁ a b (v : D₁) - star c • E₁ b a (v : D₁), hmem c⟩
  have key : ∀ c : ℂ, c • E₂ a b ((φ v : V₂) : D₂) - star c • E₂ b a ((φ v : V₂) : D₂) =
      ((φ (wc c) : V₂) : D₂) := by
    intro c
    have h := phi_actM_inK hD₁ hD₂ hVK₁ φ hφK (inK_zM hab c) v (wc c) (by rw [actM_zM]; rfl)
    rw [actM_zM, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply] at h
    exact Subtype.ext h
  have hw0 : (⟨E₁ a b v, hst a b hab _ v.2⟩ : V₁) = (1 / 2 : ℂ) • (wc 1 - Complex.I • wc Complex.I) := by
    apply Subtype.ext
    show E₁ a b (v : D₁) = (1 / 2 : ℂ) • (((1 : ℂ) • E₁ a b (v : D₁) - star (1 : ℂ) • E₁ b a (v : D₁)) -
      Complex.I • (Complex.I • E₁ a b (v : D₁) - star Complex.I • E₁ b a (v : D₁)))
    rw [star_one, one_smul, one_smul, Complex.star_def, Complex.conj_I]
    exact eq_half_smul_sub_I_smul_combo _ _
  rw [hw0, map_smul, map_sub, map_smul]
  show E₂ a b ((φ v : V₂) : D₂) =
    (1 / 2 : ℂ) • (((φ (wc 1) : V₂) : D₂) - Complex.I • ((φ (wc Complex.I) : V₂) : D₂))
  rw [← key 1, ← key Complex.I, star_one, one_smul, one_smul, Complex.star_def, Complex.conj_I]
  exact eq_half_smul_sub_I_smul_combo _ _

end Rep

end USum

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix WithLp

namespace ReciprocityTheory.ChartRestriction.DS

namespace USum

variable {n : ℕ}

section Ops

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

def sop (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) : WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).symm.toContinuousLinearMap ∘L
    ((A.prodMap B) ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).toContinuousLinearMap)

theorem sop_apply (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) (x : WithLp 2 (H₁ × H₂)) :
    sop A B x = toLp 2 (A (ofLp x).1, B (ofLp x).2) := rfl

theorem norm_sop {A : H₁ →L[ℂ] H₁} {B : H₂ →L[ℂ] H₂} (hA : ∀ v, ‖A v‖ = ‖v‖)
    (hB : ∀ v, ‖B v‖ = ‖v‖) (x : WithLp 2 (H₁ × H₂)) : ‖sop A B x‖ = ‖x‖ := by
  rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
  show √(‖A (ofLp x).1‖ ^ 2 + ‖B (ofLp x).2‖ ^ 2) = √(‖(ofLp x).1‖ ^ 2 + ‖(ofLp x).2‖ ^ 2)
  rw [hA, hB]

theorem sop_one : sop (1 : H₁ →L[ℂ] H₁) (1 : H₂ →L[ℂ] H₂) = 1 := by
  ext x; rfl

theorem sop_comp (A A' : H₁ →L[ℂ] H₁) (B B' : H₂ →L[ℂ] H₂) :
    sop (A.comp A') (B.comp B') = (sop A B).comp (sop A' B') := by
  ext x; rfl

theorem sop_neg_comm (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) (x : WithLp 2 (H₁ × H₂)) :
    sop 1 (-1) (sop A B x) = sop A B (sop 1 (-1) x) := by
  simp only [sop_apply, WithLp.ofLp_toLp]
  simp

theorem inner_sum (x y : WithLp 2 (H₁ × H₂)) :
    inner ℂ x y = inner ℂ (ofLp x).1 (ofLp y).1 + inner ℂ (ofLp x).2 (ofLp y).2 := rfl

def sD (D₁ : Submodule ℂ H₁) (D₂ : Submodule ℂ H₂) : Submodule ℂ (WithLp 2 (H₁ × H₂)) :=
  (D₁.prod D₂).comap (WithLp.linearEquiv 2 ℂ (H₁ × H₂)).toLinearMap

variable {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}

def toP : sD D₁ D₂ →ₗ[ℂ] D₁ × D₂ where
  toFun x := (⟨(ofLp (x : WithLp 2 (H₁ × H₂))).1, x.2.1⟩, ⟨(ofLp (x : WithLp 2 (H₁ × H₂))).2, x.2.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ofP : D₁ × D₂ →ₗ[ℂ] sD D₁ D₂ where
  toFun p := ⟨toLp 2 ((p.1 : H₁), (p.2 : H₂)), p.1.2, p.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toPrimitive_ofPrimitive (p : D₁ × D₂) : toP (ofP p) = p := rfl

def lift (F₁ : Module.End ℂ D₁) (F₂ : Module.End ℂ D₂) : Module.End ℂ (sD D₁ D₂) :=
  ofP ∘ₗ (F₁.prodMap F₂) ∘ₗ toP

theorem lift_ofP (F₁ : Module.End ℂ D₁) (F₂ : Module.End ℂ D₂) (p : D₁ × D₂) :
    lift F₁ F₂ (ofP p) = ofP (F₁ p.1, F₂ p.2) := rfl

theorem lift_mul (F₁ G₁ : Module.End ℂ D₁) (F₂ G₂ : Module.End ℂ D₂) :
    lift (F₁ * G₁) (F₂ * G₂) = lift F₁ F₂ * lift G₁ G₂ := LinearMap.ext fun _ => rfl

theorem lift_sub (F₁ G₁ : Module.End ℂ D₁) (F₂ G₂ : Module.End ℂ D₂) :
    lift (F₁ - G₁) (F₂ - G₂) = lift F₁ F₂ - lift G₁ G₂ := LinearMap.ext fun _ => rfl

theorem lift_zero : lift (0 : Module.End ℂ D₁) (0 : Module.End ℂ D₂) = 0 :=
  LinearMap.ext fun _ => rfl

def liftL : (Module.End ℂ D₁ × Module.End ℂ D₂) →ₗ[ℂ] Module.End ℂ (sD D₁ D₂) where
  toFun p := lift p.1 p.2
  map_add' _ _ := LinearMap.ext fun _ => rfl
  map_smul' _ _ := LinearMap.ext fun _ => rfl

theorem liftL_apply (p : Module.End ℂ D₁ × Module.End ℂ D₂) : liftL p = lift p.1 p.2 := rfl

def sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂) :
    Fin n → Fin n → Module.End ℂ (sD D₁ D₂) :=
  fun a b => lift (E₁ a b) (E₂ a b)

theorem actM_sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM (sE E₁ E₂) X = lift (actM E₁ X) (actM E₂ X) := by
  have h : ∀ a b, X a b • sE E₁ E₂ a b = liftL (X a b • (E₁ a b, E₂ a b)) := by
    intro a b; rw [map_smul]; rfl
  unfold actM

  simp only [h, ← map_sum]
  rw [liftL_apply]
  congr 1
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]

theorem casimir_sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂) :
    casimir (sE E₁ E₂) = lift (casimir E₁) (casimir E₂) := by
  have h : ∀ a b, sE E₁ E₂ a b * sE E₁ E₂ b a = liftL (E₁ a b * E₁ b a, E₂ a b * E₂ b a) := by
    intro a b; rw [liftL_apply]; exact (lift_mul _ _ _ _).symm
  unfold casimir

  simp only [h, ← map_sum]
  rw [liftL_apply]
  congr 1
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]

section Rep

variable {ε : Fin n → Bool}
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

def sσ (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)) (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)) :
    Matrix (Fin n) (Fin n) ℂ → (WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂)) :=
  fun g => sop (σ₁ g) (σ₂ g)

theorem isURepOn_sσ {G : Set (Matrix (Fin n) (Fin n) ℂ)} (h₁ : IsURepOn G σ₁) (h₂ : IsURepOn G σ₂) :
    IsURepOn G (sσ σ₁ σ₂) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show sop (σ₁ 1) (σ₂ 1) = 1
    rw [h₁.1.1, h₂.1.1]; exact sop_one
  · intro a ha b hb
    show sop (σ₁ (a * b)) (σ₂ (a * b)) = (sop (σ₁ a) (σ₂ a)).comp (sop (σ₁ b) (σ₂ b))
    rw [h₁.1.2 a ha b hb, h₂.1.2 a ha b hb, sop_comp]
  · intro g hg v
    exact norm_sop (h₁.2.1 g hg) (h₂.2.1 g hg) v
  · intro v
    have hc := ((h₁.2.2 (ofLp v).1).prodMk (h₂.2.2 (ofLp v).2))
    exact (WithLp.prod_continuous_toLp 2 H₁ H₂).comp_continuousOn hc

theorem isDerivedOn_sσ {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
    {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
    (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) :
    IsDerivedOn ε (sσ σ₁ σ₂) (sD D₁ D₂) (sE E₁ E₂) where
  glRep := by
    intro a b c d
    have e1 := hD₁.glRep a b c d
    have e2 := hD₂.glRep a b c d
    show lift (E₁ a b) (E₂ a b) * lift (E₁ c d) (E₂ c d) - lift (E₁ c d) (E₂ c d) * lift (E₁ a b) (E₂ a b) =
      (if b = c then lift (E₁ a d) (E₂ a d) else 0) - (if d = a then lift (E₁ c b) (E₂ c b) else 0)
    rw [← lift_mul, ← lift_mul, ← lift_sub, e1, e2]
    split_ifs <;> rw [lift_sub] <;> simp only [lift_zero]
  kStable := by
    intro k hk v hv
    exact ⟨hD₁.kStable k hk _ hv.1, hD₂.kStable k hk _ hv.2⟩
  deriv := by
    intro X hX v
    have h1 := hD₁.deriv X hX (toP v).1
    have h2 := hD₂.deriv X hX (toP v).2
    have h3 := (WithLp.prodContinuousLinearEquiv 2 ℝ H₁ H₂).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (h1.prodMk h2)
    rw [actM_sE]
    exact h3

end Rep

end Ops

end USum

end ReciprocityTheory.ChartRestriction.DS
end
end
