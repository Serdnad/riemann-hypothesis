module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle047
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MatrixCoefficientFrameChangeDiscreteSeries
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle045
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem integrable_of_continuous' {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] {f : KG ε → E} (hf : Continuous f) :
    Integrable f (muK ε) :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem eq_zero_of_integral_mul_star {ε : Fin n → Bool} {φ : KG ε → ℂ} (hc : Continuous φ)
    (h : ∫ k, φ k * star (φ k) ∂(muK ε) = 0) : φ = 0 := by
  have e : (fun k => φ k * star (φ k)) = fun k => ((Complex.normSq (φ k) : ℝ) : ℂ) := by
    funext k; exact Complex.mul_conj (φ k)
  rw [e, integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hcs : Continuous fun k => Complex.normSq (φ k) := Complex.continuous_normSq.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg (φ k))
    (integrable_of_continuous' hcs)).1 h
  have h2 : (fun k => Complex.normSq (φ k)) = 0 := (Continuous.ae_eq_iff_eq (muK ε) hcs continuous_const).1 hae
  funext k
  have := congrFun h2 k
  simpa using this

theorem exists_isKer (ε : Fin n → Bool) (i : ℕ) : ∃ e, IsKer ε i e := by
  classical
  have hlow : lowV ε i ≤ polyV ε i := by
    cases i with
    | zero => simp [lowV]
    | succ j => simpa [lowV] using polyV_mono ε (Nat.le_succ j)
  let W : Submodule ℂ (KG ε → ℂ) :=
    { carrier := {p | p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun q hq => ?_⟩
        have hq' := continuous_of_mem (hlow hq)
        have h1 := integral_add (μ := muK ε) (f := fun k => star (q k) * a k) (g := fun k => star (q k) * b k)
          (integrable_of_continuous' (hq'.star.mul (continuous_of_mem ha)))
          (integrable_of_continuous' (hq'.star.mul (continuous_of_mem hb)))
        simp only [Pi.add_apply, mul_add]
        rw [h1, ha' q hq, hb' q hq, add_zero]
      zero_mem' := ⟨Submodule.zero_mem _, fun q _ => by simp⟩
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨Submodule.smul_mem _ c ha, fun q hq => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        rw [integral_const_mul, ha' q hq, mul_zero] }
  have hW : ∀ p, p ∈ W ↔ p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0 :=
    fun p => Iff.rfl

  let B : polyV ε i →ₗ[ℂ] Module.Dual ℂ (polyV ε i) :=
    LinearMap.mk₂ ℂ (fun e p : polyV ε i => ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε))
      (fun e e' p => by
        have h1 := integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (g := fun k => (e' : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2)))
          (integrable_of_continuous' ((continuous_of_mem e'.2).mul (continuous_of_mem p.2)))
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
        exact h1)
      (fun c e p => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul c _)
      (fun e p p' => by
        have h1 := integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (g := fun k => (e : KG ε → ℂ) k * (p' : KG ε → ℂ) k)
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2)))
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p'.2)))
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact h1)
      (fun c e p => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        exact integral_const_mul c _)
  have hB : ∀ e p : polyV ε i, B e p = ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε) := fun _ _ => rfl
  have hinj : Function.Injective B := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro e he
    have h0 := hB e ⟨_, star_mem e.2⟩
    rw [he] at h0
    have hz : (e : KG ε → ℂ) = 0 := eq_zero_of_integral_mul_star (continuous_of_mem e.2) h0.symm
    exact Subtype.ext hz
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj

  let f : W →ₗ[ℂ] (KG ε → ℂ) ⧸ lowV ε i := (lowV ε i).mkQ ∘ₗ W.subtype
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hwl : (w : KG ε → ℂ) ∈ lowV ε i := (Submodule.Quotient.mk_eq_zero _).1 hw
    have h0 := ((hW w).1 w.2).2 _ hwl
    have hc : (fun k => star ((w : KG ε → ℂ) k) * (w : KG ε → ℂ) k) =
        fun k => (w : KG ε → ℂ) k * star ((w : KG ε → ℂ) k) := funext fun k => mul_comm _ _
    rw [hc] at h0
    exact Subtype.ext (eq_zero_of_integral_mul_star (continuous_of_mem ((hW w).1 w.2).1) h0)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let g : (KG ε → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj 1 : (KG ε → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype ∘ₗ r ∘ₗ (lowV ε i).mkQ
  have hgW : ∀ w ∈ W, g w = w 1 := by
    intro w hw
    have := LinearMap.congr_fun hr ⟨w, hw⟩
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, Submodule.subtype_apply] at this
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, this, LinearMap.proj_apply]
  have hgU : ∀ q ∈ lowV ε i, g q = 0 := by
    intro q hq
    simp only [g, LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero _).2 hq, Submodule.mkQ_apply, map_zero,
      LinearMap.proj_apply]
  obtain ⟨e, he⟩ := hsurj (g ∘ₗ (polyV ε i).subtype)
  refine ⟨e, e.2, fun q hq => ?_, fun p hp hpo => ?_⟩
  · have := LinearMap.congr_fun he ⟨q, hlow hq⟩
    rw [hB] at this
    rw [this]
    exact hgU q hq
  · have := LinearMap.congr_fun he ⟨p, hp⟩
    rw [hB] at this
    rw [this]
    exact hgW p ⟨hp, hpo⟩

end GlobalTheory.KFourier
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KFourier

theorem mono_eq_prod_pow {n : ℕ} (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) (k : KG ε) :
    mono ε s k = ∏ c : Fin n × Fin n × Bool, coord ε c k ^ s.count c := by
  classical
  unfold mono
  rw [Finset.prod_list_map_count]
  have h := Finset.prod_subset (M := ℂ) (f := fun c => coord ε c k ^ s.count c) (Finset.subset_univ (s.toFinset))
    (fun c _ hc => by rw [List.count_eq_zero_of_not_mem (by simpa using hc), pow_zero])
  convert h using 4
  all_goals exact lawful_beq_subsingleton _ _

theorem finrank_polyV_le {n : ℕ} (ε : Fin n → Bool) (d : ℕ) :
    Module.finrank ℂ (polyV ε d) ≤ (d + 1) ^ (2 * n ^ 2) := by
  classical
  let b : ((Fin n × Fin n × Bool) → Fin (d + 1)) → (KG ε → ℂ) :=
    fun f k => ∏ c : Fin n × Fin n × Bool, coord ε c k ^ (f c : ℕ)
  have hle : polyV ε d ≤ Submodule.span ℂ (Set.range b) := by
    rw [polyV_eq]
    refine Submodule.span_le.2 ?_
    rintro φ ⟨s, hs, rfl⟩
    refine Submodule.subset_span ⟨fun c => ⟨s.count c, Nat.lt_succ_of_le ((List.count_le_length).trans hs)⟩, ?_⟩
    funext k
    rw [mono_eq_prod_pow]
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  calc Module.finrank ℂ (polyV ε d) ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range b)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card ((Fin n × Fin n × Bool) → Fin (d + 1)) := finrank_range_le_card b
    _ = (d + 1) ^ (2 * n ^ 2) := by
        simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        ring

end GlobalTheory.KFourier
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KFourier

theorem orth_translate_lowV {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (p κ : KG ε → ℂ) (hκ : κ ∈ lowV ε i)
    (h : ∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) (k : KG ε) :
    ∫ x, star (p x) * κ (x⁻¹ * k) ∂(muK ε) = 0 := by
  cases i with
  | zero =>
    have h0 : κ = 0 := by simpa [lowV] using hκ
    subst h0
    simp
  | succ i =>
    have hq : (fun x : KG ε => star (κ (x⁻¹ * k))) ∈ lowV ε (i + 1) := by
      have h1 : κ ∈ polyV ε i := hκ
      have h2 := mul_right_mem k h1
      have h3 := inv_mem h2
      exact star_mem h3
    have h4 := h _ hq
    have h5 : ∫ x, star (star (κ (x⁻¹ * k)) * p x) ∂(muK ε) = 0 := by
      have := congrArg star h4
      rw [star_zero] at this
      rw [← this]
      exact integral_conj
    rw [← h5]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [star_mul', star_star]
    ring

end GlobalTheory.KFourier
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry_real (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have h2 : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = fun t : ℝ => (NormedSpace.exp (t • X)) i j := by
    funext t; rw [Complex.coe_smul]
  rw [e]; exact h2

theorem coord_mul_expK_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (c : Fin n × Fin n × Bool) (k : KG ε) : coord ε c (k * expK ε X 0) = coord ε c k := by
  simp [coord, toMK_mul, toMK_expK hX, NormedSpace.exp_zero]

theorem mono_mul_expK_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (s : List (Fin n × Fin n × Bool)) (k : KG ε) : mono ε s (k * expK ε X 0) = mono ε s k := by
  simp only [mono, coord_mul_expK_zero hX]

theorem hasDerivAt_coord {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (c : Fin n × Fin n × Bool) : ∃ ψ ∈ polyV ε 1, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => coord ε c (k * expK ε X t)) (ψ k) 0 := by
  obtain ⟨a, b, f⟩ := c
  have hent : ∀ k : KG ε, HasDerivAt (fun t : ℝ => (toMK (k * expK ε X t)) a b)
      (∑ l, toMK k a l * X l b) 0 := by
    intro k
    have e : (fun t : ℝ => (toMK (k * expK ε X t)) a b) =
        fun t : ℝ => ∑ l, toMK k a l * (NormedSpace.exp ((t : ℂ) • X)) l b := by
      funext t; simp only [toMK_mul, toMK_expK hX, Matrix.mul_apply]
    rw [e]
    exact HasDerivAt.fun_sum fun l _ => (hasDerivAt_exp_entry_real X l b).const_mul _
  cases f
  · refine ⟨∑ l, star (X l b) • coord ε (a, l, false), ?_, fun k => ?_⟩
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem ε _)
    · have h := (hent k).star
      have e1 : (fun t : ℝ => coord ε (a, b, false) (k * expK ε X t)) =
          fun t => star ((toMK (k * expK ε X t)) a b) := by
        funext t; simp [coord]
      rw [e1]
      have hv : (∑ l, star (X l b) • coord ε (a, l, false)) k = star (∑ l, toMK k a l * X l b) := by
        rw [Finset.sum_apply, star_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, coord, Bool.false_eq_true, if_false, star_mul']
        exact mul_comm _ _
      rw [hv]; exact h
  · refine ⟨∑ l, X l b • coord ε (a, l, true), ?_, fun k => ?_⟩
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem ε _)
    · have e1 : (fun t : ℝ => coord ε (a, b, true) (k * expK ε X t)) =
          fun t => (toMK (k * expK ε X t)) a b := by
        funext t; simp [coord]
      rw [e1]
      have hv : (∑ l, X l b • coord ε (a, l, true)) k = ∑ l, toMK k a l * X l b := by
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, coord, if_true]
        exact mul_comm _ _
      rw [hv]; exact hent k

theorem hasDerivAt_mono {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (s : List (Fin n × Fin n × Bool)) : ∀ d, s.length ≤ d → ∃ ψ ∈ polyV ε d, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => mono ε s (k * expK ε X t)) (ψ k) 0 := by
  induction s with
  | nil =>
    intro d _
    refine ⟨0, Submodule.zero_mem _, fun k => ?_⟩
    simpa [mono] using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | cons c s ih =>
    intro d hd
    simp only [List.length_cons] at hd
    obtain ⟨ψc, hψc, hc⟩ := hasDerivAt_coord hX c
    obtain ⟨ψs, hψs, hs⟩ := ih (d - 1) (by omega)
    refine ⟨ψc * mono ε s + coord ε c * ψs, ?_, fun k => ?_⟩
    · have hle : 1 + (d - 1) ≤ d := by omega
      exact add_mem (polyV_mono ε hle (mul_mem hψc (mono_mem (by omega))))
        (polyV_mono ε hle (mul_mem (coord_mem ε c) hψs))
    · have h := (hc k).mul (hs k)
      have e : (fun t : ℝ => mono ε (c :: s) (k * expK ε X t)) =
          fun t => coord ε c (k * expK ε X t) * mono ε s (k * expK ε X t) := by
        funext t; simp [mono]
      rw [e]
      rw [coord_mul_expK_zero hX, mono_mul_expK_zero hX] at h
      exact h

theorem hasDerivAt_of_mem {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {d : ℕ}
    {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) : ∃ ψ ∈ polyV ε d, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (ψ k) 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact hasDerivAt_mono hX s d hs
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun k => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y _ _ hx hy =>
    obtain ⟨ψ₁, h₁, d₁⟩ := hx
    obtain ⟨ψ₂, h₂, d₂⟩ := hy
    exact ⟨ψ₁ + ψ₂, add_mem h₁ h₂, fun k => (d₁ k).add (d₂ k)⟩
  | smul a x _ hx =>
    obtain ⟨ψ, h, dψ⟩ := hx
    exact ⟨a • ψ, Submodule.smul_mem _ a h, fun k => by simpa using (dψ k).const_mul a⟩

theorem rder_mem_and_hasDerivAt (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d)
    (X : Mx n) (hX : inK ε X) : rder ε [X] φ ∈ polyV ε d ∧
      ∀ k : KG ε, HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (rder ε [X] φ k) 0 := by
  obtain ⟨ψ, hψ, hd⟩ := hasDerivAt_of_mem hX hφ
  have e : rder ε [X] φ = ψ := by
    funext k
    rw [rder_cons, rder_nil]
    exact (hd k).deriv
  rw [e]
  exact ⟨hψ, hd⟩

end GlobalTheory.KFourier

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology


theorem _root_.GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ContinuousOn (F []) (UJset ε) → ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
    ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (φ : T → GlobalTheory.TypeSum.Mx n),
      Continuous φ → (∀ t, φ t ∈ UJset ε) → Measurable (fun t => F l (φ t)) := by
  first | exact @GlobalTheory.TypeSum.measurable_derFam_comp | exact GlobalTheory.TypeSum.measurable_derFam_comp | (intros; apply GlobalTheory.TypeSum.measurable_derFam_comp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos


theorem _root_.GlobalTheory.T.continuousOn_rightDerivativeFamily_moderateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F →
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε) := by
  first | exact @GlobalTheory.TypeSum.DerFamCont.continuousOn_of_isDerFam | exact GlobalTheory.TypeSum.DerFamCont.continuousOn_of_isDerFam | (intros; apply GlobalTheory.TypeSum.DerFamCont.continuousOn_of_isDerFam <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.matrix_coefficient_frame_change_discrete_series : GlobalTheory.Published.DiscreteSeriesUpqUnique → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam σ → IsDS ε lam σ' →
    ∀ (P P' G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' → Pᴴ * Formalism.REAL.Jm ε * P = G →
      P'ᴴ * Formalism.REAL.Jm ε * P' = G →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (ℓ : H' →ₗ[ℂ] ℂ) (v : H'), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ' ℓ →
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ' v → (∀ y ∈ UJset ε, F (P'⁻¹ * y * P') = ℓ (σ' y v)) →
    ∃ (ℓ' : H →ₗ[ℂ] ℂ) (v' : H), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ' ∧
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ v' ∧ ∀ y ∈ UJset ε, F (P⁻¹ * y * P) = ℓ' (σ y v') := by
  first | exact @GlobalTheory.TypeSum.FrameChange.coef_frame_change | exact GlobalTheory.TypeSum.FrameChange.coef_frame_change | (intros; apply GlobalTheory.TypeSum.FrameChange.coef_frame_change <;> assumption)
end

section

set_option autoImplicit false



noncomputable section

namespace GlobalTheory.RunJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem iInf_le_of_combBound {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hjm : D.R.m ≤ j)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (cb : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hspan : @Submodule.span (𝓞 (recB h.toLawsCore).KO) _ _ _ (WeightFamilies.Prov.modOC (recB h.toLawsCore) j wL)
      (Set.range G.w) = (recPJ h j hj).WWc S.sW wL)
    (hX : CombBound G S cb nus) :
    ∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal) := by
  rintro la _ ⟨y0, rfl⟩
  obtain ⟨y, hy⟩ := pt_realise h j hj la y0
  have hv : ∀ w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1 := fun w F => by
    rw [recPJ_vAt_inc, hy]
  have hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1 := by
    unfold PJ.depth
    rw [← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y)
      ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y)
      (fun _ ha => vAdd_int_nonneg la ha)]
    simp only [hv]
  have h1 := (hX la y).2 hjm
  rw [hd] at h1
  exact h1

theorem combAlg_of_tiedW : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (ka wL wF : WeightFamilies.Wt D j) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (c Gc Prw : ℝ), G.TiedW S Gc Prw → CombBound G S c nus → (j < D.R.m → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ)))) ∧ (j = D.R.m → ∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) := by
  intro D T h j hj ka wL wF S nus G c Gc Prw hW hX
  exact ⟨fun hjm => combAlg_of_combBound h j hj hjm G S c nus hW.1 hX,
    fun hjm => iInf_le_of_combBound h j hj hjm.ge G S c nus hW.1 hX⟩

end GlobalTheory.RunJoin
end
end
