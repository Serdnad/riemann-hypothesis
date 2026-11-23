module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle151
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle152
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

def innerAutTop {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (s : G) : G ≃ₜ* G :=
  { MulAut.conj s with
    continuous_toFun := by
      change Continuous fun g : G => s * g * s⁻¹
      fun_prop
    continuous_invFun := by
      change Continuous fun g : G => s⁻¹ * g * s
      fun_prop }

theorem inUJ_map_conj {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (g.map (starRingEnd ℂ)) := by
  unfold Formalism.REAL.inUJ at hg ⊢
  have hJ : (Formalism.REAL.Jm ε).map (starRingEnd ℂ) = Formalism.REAL.Jm ε := by
    ext i j
    simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hH : (g.map (starRingEnd ℂ))ᴴ = gᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h2
  rw [hH]
  exact h2

noncomputable def conjUJHom {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε →* Formalism.REAL.UJ ε :=
  ((Units.map ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom).comp (Formalism.REAL.UJ ε).subtype).codRestrict
    (Formalism.REAL.UJ ε) fun g => inUJ_map_conj ε g.2

theorem uMat_conjUJHom {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    uMat (conjUJHom ε g) = (uMat g).map (starRingEnd ℂ) := rfl

theorem conjUJHom_invol {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : conjUJHom ε (conjUJHom ε g) = g := by
  apply Subtype.ext
  apply Units.ext
  show uMat (conjUJHom ε (conjUJHom ε g)) = uMat g
  rw [uMat_conjUJHom, uMat_conjUJHom]
  ext i j
  simp

theorem continuous_conjUJHom {n : ℕ} (ε : Fin n → Bool) : Continuous (conjUJHom ε) := by
  have hc : Continuous ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom := by
    show Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)
    exact Continuous.matrix_map continuous_id Complex.continuous_conj
  have hu := Continuous.units_map _ hc
  exact Continuous.subtype_mk (hu.comp continuous_subtype_val) _

noncomputable def conjUJ {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε where
  toFun := conjUJHom ε
  invFun := conjUJHom ε
  left_inv := conjUJHom_invol ε
  right_inv := conjUJHom_invol ε
  map_mul' := map_mul _
  continuous_toFun := continuous_conjUJHom ε
  continuous_invFun := continuous_conjUJHom ε

theorem gauge_map_inner_comp {n : ℕ} (ε : Fin n → Bool) (C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε)
    (hC : ∀ g, Formalism.REAL.hs (uMat (C g) - 1) = Formalism.REAL.hs (uMat g - 1)) (s : Formalism.REAL.UJ ε) (c : ℝ)
    (hc : IsGauge ε c) :
    (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  have hT : ∀ g, (C.trans (innerAutTop s)) (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) = C g := by
    intro g
    show s * C (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) * s⁻¹ = C g
    simp only [map_mul, map_inv, C.apply_symm_apply]
    group
  have key := gauge_map_of_iso n n ε ε rfl (C.trans (innerAutTop s)) (C.symm s⁻¹)
    (fun g => by rw [hT]; exact hC g) c c hc hc
  have hf : (fun g => s * C g * s⁻¹) = ⇑(C.trans (innerAutTop s)) := by
    funext g
    rfl
  rw [hf]
  exact key

theorem exists_conj_gauge_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (τ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → ∃ C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε, (∀ g, uMat (C g) = (uMat g).map τ) ∧ ∀ (s : Formalism.REAL.UJ ε) (c : ℝ), IsGauge ε c → (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  intro n ε τ hτ
  rcases hτ with rfl | rfl
  · refine ⟨ContinuousMulEquiv.refl _, fun g => ?_, fun s c hc => ?_⟩
    · ext i j
      simp
    · exact gauge_map_inner_comp ε (ContinuousMulEquiv.refl _) (fun g => rfl) s c hc
  · refine ⟨conjUJ ε, fun g => uMat_conjUJHom ε g, fun s c hc => ?_⟩
    refine gauge_map_inner_comp ε (conjUJ ε) (fun g => ?_) s c hc
    have h1 : uMat (conjUJ ε g) = (uMat g).map (starRingEnd ℂ) := uMat_conjUJHom ε g
    rw [h1]
    unfold Formalism.REAL.hs
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e : ((uMat g).map (starRingEnd ℂ) - 1) i j = starRingEnd ℂ ((uMat g - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
      congr 1
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    rw [e, Complex.norm_conj]

end GlobalTheory.LeviIso
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.PhiConjDeriv

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma analyticAt_Phi (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Omega n) :
    AnalyticAt ℂ (Phi lam) z := by
  have h := GlobalTheory.PhiEigenfun.analytic_Phi lam (1 : Matrix (Fin n) (Fin n) ℂ) 1 z (by simpa using hz)
  simpa using h

lemma fderiv_Phi_single (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Omega n) {a b : Fin n}
    (hab : a < b) : fderiv ℂ (Phi lam) z (z * Matrix.single a b 1) = 0 := by
  have hne : a ≠ b := ne_of_lt hab
  have hγ : HasDerivAt (fun t : ℂ => z + t • (z * Matrix.single a b 1)) (z * Matrix.single a b 1) 0 := by
    have h0 := ((hasDerivAt_id' (0 : ℂ)).smul_const (z * Matrix.single a b 1)).const_add z
    rwa [one_smul] at h0
  have hP : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) z) (z + (0 : ℂ) • (z * Matrix.single a b 1)) := by
    rw [zero_smul, add_zero]
    exact (analyticAt_Phi lam hz).differentiableAt.hasFDerivAt
  have h1 := hP.comp_hasDerivAt (0 : ℂ) hγ
  have hc : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0 := by
    have hca : ContinuousAt (fun t : ℂ => 1 + t) 0 := (continuous_const.add continuous_id).continuousAt
    exact hca.eventually_ne (by norm_num)
  have hev : (fun t : ℂ => Phi lam (z + t • (z * Matrix.single a b 1))) =ᶠ[nhds 0] fun _ => Phi lam z := by
    filter_upwards [hc] with t ht
    have hm := GlobalTheory.PhiEigenfun.Phi_mul_single lam hz hab.le ht
    rw [if_neg hne, one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at hm
    exact hm
  have h2 : HasDerivAt (fun t : ℂ => Phi lam (z + t • (z * Matrix.single a b 1))) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (Phi lam z)).congr_of_eventuallyEq hev
  exact h1.unique h2

def sgn (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

lemma star_entry {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (a b : Fin n) :
    star (Y a b) = -(sgn ε b * sgn ε a) * Y b a := by
  have h' : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 := congrFun (congrFun h' b) a
  simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h1
  unfold sgn
  rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
    simp only [ha, hb, if_true, if_false, Bool.false_eq_true] at h1 ⊢ <;>
    first | linear_combination h1 | linear_combination -h1

lemma inG_conj {ε : Fin n → Bool} {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hX : inG ε X) :
    inG ε (k⁻¹ * X * k) := by
  obtain ⟨hu, hJ⟩ := hk
  have hkk : kᴴ * k = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkk
  have hJ' : Jm ε * kᴴ = kᴴ * Jm ε := by
    have h2 := congrArg Matrix.conjTranspose hJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose] at h2
    exact h2
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  show (k⁻¹ * X * k)ᴴ * Jm ε + Jm ε * (k⁻¹ * X * k) = 0
  rw [hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc kᴴ * (Xᴴ * k) * Jm ε + Jm ε * (kᴴ * X * k)
      = kᴴ * Xᴴ * (k * Jm ε) + Jm ε * kᴴ * X * k := by simp only [Matrix.mul_assoc]
    _ = kᴴ * (Xᴴ * Jm ε + Jm ε * X) * k := by
        rw [hJ, hJ']; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

theorem exists_deriv_Phi_conj : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), ∃ l : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ c d z, d < c → l c d z = 0) ∧ (∀ c d, ContinuousOn (l c d) (Omega n)) ∧ ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, k⁻¹ * g * k ∈ Omega n → ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → HasDerivAt (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star)) (∑ c, ∑ d, (k⁻¹ * X * k) c d * l c d (k⁻¹ * g * k)) 0 := by
  intro n ε lam
  refine ⟨fun c d z => if d < c then 0 else
    -(sgn ε c * sgn ε d) * star (fderiv ℂ (Phi lam) z (z * Matrix.single d c 1)), ?_, ?_, ?_⟩
  · intro c d z hdc
    simp only [hdc, if_true]
  · intro c d
    by_cases hdc : d < c
    · simp only [hdc, if_true]
      exact continuousOn_const
    · simp only [hdc, if_false]
      have hA : AnalyticOnNhd ℂ (Phi lam) (Omega n) := fun z hz => analyticAt_Phi lam hz
      have hF : ContinuousOn (fderiv ℂ (Phi lam)) (Omega n) := hA.fderiv.continuousOn
      have hv : ContinuousOn (fun z : Matrix (Fin n) (Fin n) ℂ => z * Matrix.single d c 1) (Omega n) :=
        (continuous_id.matrix_mul continuous_const).continuousOn
      exact continuousOn_const.mul (hF.clm_apply hv).star
  · intro k hk g hg hw X hX
    have hkk : kᴴ * k = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hk.1
    have hkk' : k * kᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hk.1
    have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkk
    have hYG : inG ε (k⁻¹ * X * k) := inG_conj hk hX

    let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℂ k⁻¹).comp (LinearMap.mulRight ℂ k))
    have hL : ∀ M, L M = k⁻¹ * (M * k) := fun M => rfl
    have hcurve : HasDerivAt (fun s : ℂ => k⁻¹ * (g * NormedSpace.exp (s • X)) * k)
        ((k⁻¹ * g * k) * (k⁻¹ * X * k)) 0 := by
      have h0 := L.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (GlobalTheory.PhiEigenfun.hasDerivAt_curve g X)
      have hLgX : L (g * X) = (k⁻¹ * g * k) * (k⁻¹ * X * k) := by
        rw [hL, hinv]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc k kᴴ (X * k), hkk', Matrix.one_mul]
      refine (h0.congr_deriv hLgX).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      exact Matrix.mul_assoc _ _ _
    have hP : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) (k⁻¹ * g * k))
        (k⁻¹ * (g * NormedSpace.exp ((0 : ℂ) • X)) * k) := by
      rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
      exact (analyticAt_Phi lam hw).differentiableAt.hasFDerivAt
    have hφ := hP.comp_hasDerivAt (0 : ℂ) hcurve
    have hφ' : HasDerivAt (fun s : ℂ => Phi lam (k⁻¹ * (g * NormedSpace.exp (s • X)) * k))
        (fderiv ℂ (Phi lam) (k⁻¹ * g * k) ((k⁻¹ * g * k) * (k⁻¹ * X * k))) ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero]
      exact hφ
    have hst := hφ'.comp_ofReal.star

    have hexp : ∀ (w Y : Matrix (Fin n) (Fin n) ℂ), fderiv ℂ (Phi lam) w (w * Y) =
        ∑ c, ∑ d, Y c d * fderiv ℂ (Phi lam) w (w * Matrix.single c d 1) := by
      intro w Y
      conv_lhs => rw [Matrix.matrix_eq_sum_single Y]

      simp only [Matrix.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      have hs : Matrix.single c d (Y c d) = Y c d • Matrix.single c d (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, Matrix.mul_smul, map_smul, smul_eq_mul]
    have hD0 : ∀ c d : Fin n, d < c → fderiv ℂ (Phi lam) (k⁻¹ * g * k) ((k⁻¹ * g * k) * Matrix.single d c 1) = 0 :=
      fun c d h => fderiv_Phi_single lam hw h
    have hfun : (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star)) =
        fun t : ℝ => star (Phi lam (k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k)) := by
      funext t
      exact GlobalTheory.Dec.FormF.Phi_star lam _
    rw [hfun]
    refine hst.congr_deriv ?_
    rw [hexp, star_sum]
    simp only [star_sum, star_mul', star_entry hYG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · rw [hD0 _ _ h]
      simp
    · ring

end GlobalTheory.PhiConjDeriv
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramFlag


open InnerProductSpace in
theorem sub_gs_mem {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) (a : Fin r) :
    f a - gramSchmidt ℂ f a ∈ Submodule.span ℂ (f '' Set.Iio a) := by
  have h := gramSchmidt_def'' (𝕜 := ℂ) f a
  have hs : f a - gramSchmidt ℂ f a = ∑ i ∈ Finset.Iio a,
      (⟪gramSchmidt ℂ f i, f a⟫_ℂ / (‖gramSchmidt ℂ f i‖ : ℂ) ^ 2) • gramSchmidt ℂ f i := by
    rw [sub_eq_iff_eq_add']
    exact h
  rw [hs, ← span_gramSchmidt_Iio (𝕜 := ℂ) f a]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩)


open InnerProductSpace in
theorem norm_gs_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) (a : Fin r)
    {w : E} (hw : w ∈ Submodule.span ℂ (f '' Set.Iio a)) : ‖gramSchmidt ℂ f a‖ ≤ ‖f a - w‖ := by
  have horth : ∀ v ∈ Submodule.span ℂ (f '' Set.Iio a), ⟪gramSchmidt ℂ f a, v⟫_ℂ = 0 := by
    intro v hv
    rw [← span_gramSchmidt_Iio (𝕜 := ℂ) f a] at hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact gramSchmidt_orthogonal (𝕜 := ℂ) f (ne_of_gt (Set.mem_Iio.1 hi))
    | zero => exact inner_zero_right _
    | add y y' _ _ hy hy' => rw [inner_add_right, hy, hy', add_zero]
    | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]
  have hy : (f a - gramSchmidt ℂ f a) - w ∈ Submodule.span ℂ (f '' Set.Iio a) :=
    Submodule.sub_mem _ (sub_gs_mem f a) hw
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (gramSchmidt ℂ f a) _ (horth _ hy)
  have heq : gramSchmidt ℂ f a + ((f a - gramSchmidt ℂ f a) - w) = f a - w := by abel
  rw [heq] at hpy
  nlinarith [norm_nonneg (gramSchmidt ℂ f a), norm_nonneg (f a - w),
    mul_self_nonneg ‖(f a - gramSchmidt ℂ f a) - w‖]


open InnerProductSpace in
theorem exists_upper {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) :
    ∃ u : UT r → ℂ, ∀ a, ∑ b, upper u b a • f b = gramSchmidt ℂ f a := by
  classical
  choose l hl hlx using fun a => (Finsupp.mem_span_image_iff_linearCombination ℂ).1 (sub_gs_mem f a)
  refine ⟨fun p => -(l p.1.2 p.1.1), fun a => ?_⟩
  have hz : ∀ b, a ≤ b → l a b = 0 := by
    intro b hab
    by_contra hne
    have hb := (Finsupp.mem_supported ℂ (l a)).1 (hl a) (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
    exact absurd (Set.mem_Iio.1 hb) (not_lt.2 hab)
  have hc : ∀ b, upper (fun p : UT r => -(l p.1.2 p.1.1)) b a = (if b = a then 1 else 0) - l a b := by
    intro b
    rcases lt_trichotomy b a with hba | hba | hba
    · simp [upper, hba, hba.ne]
    · subst hba
      simp [upper, hz b le_rfl]
    · simp [upper, not_lt.2 hba.le, hba.ne', hz b hba.le]
  have hsum := hlx a
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℂ (f i))] at hsum
  simp_rw [hc, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hsum, sub_sub_cancel]

theorem eucl_eq {N : ℕ} (v : Fin N → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq, eucl]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_norm_sq]

theorem gramSchmidt_lengths : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), ∀ x ∈ GG k r, ∃ u : UT r → ℂ, (∀ a : Fin r, eucl (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = lA k r z x a.castSucc ∧ 0 < lA k r z x a.castSucc) ∧ ∀ a a' : Fin r, a ≠ a' → star (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) ⬝ᵥ (∑ b, upper u b a' • (x⁻¹ *ᵥ bvec (eI k r b))) = 0 := by
  intro k r z x hx
  classical
  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    obtain ⟨-, hsq, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
    have h := congrArg Matrix.det hsq
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.2 ⟨_, h⟩
  have hxu : IsUnit x.det := ((Formalism.QuantumDeterminants.uHGroup _ _ hH).2.2 x hx).1
  let L : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin x⁻¹
  have hLapp : ∀ v, L v = WithLp.toLp 2 (x⁻¹ *ᵥ v) := fun v => rfl
  let e : Fin r → Fin (2 * r + k + 1) → ℂ := fun b => bvec (eI k r b)
  let F : Fin r → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun b => L (e b)
  have hLinj : Function.Injective L := by
    intro v w hvw
    rw [hLapp, hLapp] at hvw
    have h1 : x⁻¹ *ᵥ v = x⁻¹ *ᵥ w := congrArg WithLp.ofLp hvw
    have h2 := congrArg (fun t => x *ᵥ t) h1
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv x hxu] using h2
  have heinj : Function.Injective (eI k r) := fun a b h => Fin.ext (by have h' := congrArg Fin.val h; exact h')
  have hlie : LinearIndependent ℂ e := by
    have h0 := (Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp _ heinj
    convert h0 using 1
    funext b
    simp [e, bvec]
  have hli : LinearIndependent ℂ F := hlie.map' L (LinearMap.ker_eq_bot.2 hLinj)
  obtain ⟨u, hu⟩ := exists_upper F
  have hG : ∀ a, WithLp.toLp 2 (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = InnerProductSpace.gramSchmidt ℂ F a := by
    intro a
    have htl : ∀ v : Fin (2 * r + k + 1) → ℂ,
        WithLp.toLp 2 v = (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm v := fun v => rfl

    rw [← hu a, htl, map_sum]
    simp only [map_smul]
    rfl
  have hset : ∀ a : Fin r, (Set.range fun b : {b : Fin r // b.val < (a.castSucc : Fin (r + 1)).val} =>
      bvec (eI k r b.1)) = e '' Set.Iio a := by
    intro a
    ext v
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.1, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hlA : ∀ a : Fin r, lA k r z x a.castSucc = ‖InnerProductSpace.gramSchmidt ℂ F a‖ := by
    intro a
    have hf : Formalism.QuantumDeterminants.fvec k r z a.castSucc = e a := by
      rw [Formalism.QuantumDeterminants.fvec, dite_eq_left (show (a.castSucc : Fin (r + 1)).val < r from a.isLt)]
      rfl
    have hspan : Submodule.span ℂ (F '' Set.Iio a) = (Submodule.span ℂ (e '' Set.Iio a)).map L := by
      rw [Submodule.map_span, Set.image_image]
    unfold lA
    rw [hf, hset a]
    apply IsLeast.csInf_eq
    constructor
    · have hm := sub_gs_mem F a
      rw [hspan] at hm
      obtain ⟨y, hy, hyL⟩ := Submodule.mem_map.1 hm
      refine ⟨y, hy, ?_⟩
      rw [eucl_eq, ← hLapp, map_sub, hyL]
      show _ = ‖F a - (F a - InnerProductSpace.gramSchmidt ℂ F a)‖
      rw [sub_sub_cancel]
    · rintro t ⟨y, hy, rfl⟩
      rw [eucl_eq, ← hLapp, map_sub]
      exact norm_gs_le F a (w := L y) (by rw [hspan]; exact Submodule.mem_map_of_mem hy)
  refine ⟨u, fun a => ⟨by rw [eucl_eq, hG a, hlA a], ?_⟩, fun a a' haa' => ?_⟩
  · rw [hlA a]
    exact norm_pos_iff.2 (InnerProductSpace.gramSchmidt_ne_zero (𝕜 := ℂ) a hli)
  · rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, hG a, hG a']
    exact InnerProductSpace.gramSchmidt_orthogonal (𝕜 := ℂ) F haa'

end GlobalTheory.Amp.GramFlag
end

section

open GlobalTheory.Dec

theorem _root_.GlobalTheory.T.kType_extends_holomorphic_complexifiedK : TauExists := by
  first | exact @GlobalTheory.Dec.TauExt.tauExists | exact GlobalTheory.Dec.TauExt.tauExists | (intros; apply GlobalTheory.Dec.TauExt.tauExists <;> assumption)
end

section

open GlobalTheory.Dec

theorem _root_.GlobalTheory.T.phi_positive_definite_cholesky_formula : PhiPos := by
  first | exact @GlobalTheory.Dec.phiPos | exact GlobalTheory.Dec.phiPos | (intros; apply GlobalTheory.Dec.phiPos <;> assumption)
end

section

open GlobalTheory.Dec

theorem _root_.GlobalTheory.T.phi_centre_eigenfunction_discrete_series : PhiEigen := by
  first | exact @GlobalTheory.PhiEigenfun.phiEigen | exact GlobalTheory.PhiEigenfun.phiEigen | (intros; apply GlobalTheory.PhiEigenfun.phiEigen <;> assumption)
end

section

open GlobalTheory.Dec

theorem _root_.GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one : PsBasic := by
  first | exact @GlobalTheory.Dec.psBasic | exact GlobalTheory.Dec.psBasic | (intros; apply GlobalTheory.Dec.psBasic <;> assumption)
end
