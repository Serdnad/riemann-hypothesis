module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.FiniteOrbit

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem exists_finiteDimensional_stable (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type)
    [Finite ι] (A : ι → Subalgebra ℂ (Module.End ℂ M))
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) (m : M)
    (hm : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ {x : M | ∃ a ∈ A i, x = a m})) :
    ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧ ∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W := by
  first
  | exact @_root_.GlobalTheory.OrbitGrowth.main
  | exact _root_.GlobalTheory.OrbitGrowth.main
  | (apply _root_.GlobalTheory.OrbitGrowth.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrbitGrowth.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrbitGrowth.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrbitGrowth.main ..)

end GlobalTheory.FiniteOrbit
end

section

open Formalism.MainNotions.S Matrix MeasureTheory

namespace GlobalTheory

theorem hilbert_schur_selfAdjoint (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : Type) (π : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, π g * A = A * π g) :
    ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  have hsub : (spectrum ℝ A).Subsingleton := by
    have key : ∀ a ∈ spectrum ℝ A, ∀ b ∈ spectrum ℝ A, ¬ a < b := by
      intro a ha b hb hab
      set m : ℝ := (a + b) / 2 with hm
      let f : ℝ → ℝ := fun x => max (m - x) 0
      let g : ℝ → ℝ := fun x => max (x - m) 0
      have hf : Continuous f := by fun_prop
      have hg : Continuous g := by fun_prop
      have hfg : cfc f A * cfc g A = 0 := by
        rw [← cfc_mul f g A hf.continuousOn hg.continuousOn]
        have : (fun x => f x * g x) = (0 : ℝ → ℝ) := by
          funext x
          simp only [f, g, Pi.zero_apply]
          rcases le_total x m with h | h
          · rw [max_eq_right (by linarith : x - m ≤ 0), mul_zero]
          · rw [max_eq_right (by linarith : m - x ≤ 0), zero_mul]
        rw [this, cfc_zero]
      have hne : ∀ (k : ℝ → ℝ), Continuous k → ∀ x ∈ spectrum ℝ A, k x ≠ 0 → cfc k A ≠ 0 := by
        intro k hk x hx hkx h0
        have h1 : cfc k A = cfc (0 : ℝ → ℝ) A := by rw [h0, cfc_zero]
        exact hkx (eqOn_of_cfc_eq_cfc h1 hk.continuousOn continuousOn_const hA hx)
      have hf0 : cfc f A ≠ 0 := hne f hf a ha (by
        have : 0 < m - a := by rw [hm]; linarith
        simp only [f]; rw [max_eq_left this.le]; exact this.ne')
      have hg0 : cfc g A ≠ 0 := hne g hg b hb (by
        have : 0 < b - m := by rw [hm]; linarith
        simp only [g]; rw [max_eq_left this.le]; exact this.ne')
      have hcomm : ∀ x, Commute (cfc f A) (π x) := fun x =>
        hA.commute_cfc (show Commute A (π x) from (hc x).symm) f
      rcases hirr (LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap) (cfc f A).isClosed_ker (by
        intro x v hv
        have hv' : cfc f A v = 0 := hv
        show cfc f A (π x v) = 0
        have := congrArg (fun T : H →L[ℂ] H => T v) (hcomm x).eq
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hv', map_zero]) with h | h
      · apply hg0
        ext v
        have : cfc g A v ∈ LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap := by
          show cfc f A (cfc g A v) = 0
          have := congrArg (fun T : H →L[ℂ] H => T v) hfg
          simpa using this
        rw [h] at this
        simpa using this
      · apply hf0
        ext v
        have : v ∈ LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap := by
          rw [h]; trivial
        exact this
    intro a ha b hb
    exact le_antisymm (not_lt.1 (key b hb a ha)) (not_lt.1 (key a ha b hb))
  obtain ⟨r, hr⟩ : ∃ r : ℝ, spectrum ℝ A ⊆ {r} := by
    rcases hsub.eq_empty_or_singleton with h | ⟨r, h⟩
    · exact ⟨0, by rw [h]; exact Set.empty_subset _⟩
    · exact ⟨r, h.subset⟩
  refine ⟨r, ?_⟩
  rw [CFC.eq_algebraMap_of_spectrum_subset_singleton A r hr hA, Algebra.algebraMap_eq_smul_one,
    Complex.coe_smul]

theorem hilbert_schur :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)), (∀ g v, ‖π g v‖ = ‖v‖) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ A : H →L[ℂ] H, (∀ g, π g * A = A * π g) → ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  intro H _ _ _ G _ π hn hirr A hc
  have hstar : ∀ g, star (π g) = π g⁻¹ := by
    intro g
    have h1 : star (π g) * π g = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (π g)).1 (hn g)
    calc star (π g) = star (π g) * (π g * π g⁻¹) := by
          rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = π g⁻¹ := by rw [← mul_assoc, h1, one_mul]
  have hc' : ∀ g, π g * star A = star A * π g := by
    intro g
    have := congrArg star (hc g⁻¹)
    rw [star_mul, star_mul, hstar, inv_inv] at this
    exact this.symm
  obtain ⟨b, hb⟩ := hilbert_schur_selfAdjoint H G π hirr (A + star A)
    (IsSelfAdjoint.add_star_self A) (fun g => by rw [mul_add, add_mul, hc, hc'])
  obtain ⟨c, hc2⟩ := hilbert_schur_selfAdjoint H G π hirr (Complex.I • (A - star A))
    (by
      rw [IsSelfAdjoint, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I,
        neg_smul, ← smul_neg, neg_sub])
    (fun g => by rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hc, hc'])
  refine ⟨(1 / 2 : ℂ) * (b - Complex.I * c), ?_⟩
  have h3 : A - star A = (-(Complex.I * c)) • (1 : H →L[ℂ] H) := by
    rw [neg_smul, mul_smul, ← hc2, smul_smul, Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  rw [mul_smul, sub_eq_add_neg, add_smul, ← hb, ← h3]
  module

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory
open scoped Pointwise

namespace GlobalTheory


open Pointwise in
theorem measure_addFundamentalDomain_lt_top_of_cocompact {G : Type} [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}
    (hF : IsAddFundamentalDomain Γ F μ) : μ F < ⊤ := by
  have hsub : F ⊆ ⋃ γ : Γ, ((γ +ᵥ K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, hk⟩ := hcov g
    refine Set.mem_iUnion.2 ⟨-(⟨γ, hγ⟩ : Γ), ?_, hg⟩
    rw [Set.mem_neg_vadd_set_iff]
    exact hk
  calc μ F ≤ μ (⋃ γ : Γ, ((γ +ᵥ K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ +ᵥ K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

theorem meanSquare_addFundamentalDomain_of_cocompact : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) → (∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1) ∧ ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖) → ∃ N : NNReal, ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = μ 𝓕 * N ∧ ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ = (μ 𝓕).toReal * N := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov
  have : Countable Γ := countable_of_discrete_addSubgroup Γ
  have hne : ∀ (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G},
      IsAddFundamentalDomain Γ F μ → μ F ≠ 0 := fun μ _ F hF =>
    hF.measure_ne_zero (NeZero.ne μ)
  have hfin : ∀ (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G},
      IsAddFundamentalDomain Γ F μ → μ F ≠ ⊤ := fun μ _ F hF =>
    (measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ hF).ne
  have hex : ∃ (μ : Measure G) (𝓕 : Set G),
      μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
    obtain ⟨D, -, -, hD⟩ := exists_isAddFundamentalDomain_addSubgroup Γ
    have h0 := hne Measure.addHaar (hD _)
    have h1 := hfin Measure.addHaar (hD _)
    refine ⟨(Measure.addHaar D)⁻¹ • Measure.addHaar, D,
      Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0),
      hD _, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]
  refine ⟨hex, fun f hf hinv => ?_⟩
  obtain ⟨μ₀, F₀, hμ₀, hF₀, h1⟩ := hex
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ w, ‖f w‖ₑ ^ 2 ≤ ENNReal.ofReal C ^ 2 := fun w => by
    obtain ⟨γ, hγ, hk⟩ := hcov w
    have := hC _ hk
    rw [hinv γ hγ] at this
    rw [← ofReal_norm_eq_enorm]
    gcongr
  have hN : ∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hb)
    rw [setLIntegral_const, h1, mul_one]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨(∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀).toNNReal, fun μ F hμ hF => ?_⟩
  have key : ∫⁻ w in F, ‖f w‖ₑ ^ 2 ∂μ =
      μ F * ((∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀).toNNReal : ENNReal) := by
    rw [ENNReal.coe_toNNReal hN]
    obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul μ μ₀⟩
    have hac : μ ≪ μ₀ := hc ▸ Measure.smul_absolutelyContinuous
    have hF₀' : IsAddFundamentalDomain Γ F₀ μ := hF₀.mono hac
    have e1 : μ F = μ F₀ := hF.measure_eq hF₀'
    have e2 : ∫⁻ w in F, ‖f w‖ₑ ^ 2 ∂μ = ∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ :=
      hF.setLIntegral_eq hF₀' _ fun g x => by
        have := hinv g g.2 x
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← this]
        rfl
    rw [e1, e2, hc, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply, h1]
    simp [ENNReal.smul_def]
  refine ⟨hne μ hF, hfin μ hF, key, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖f w‖ ^ 2)
    (Filter.Eventually.of_forall fun w => by positivity)
    (hf.norm.pow 2).aestronglyMeasurable]
  have : ∀ w, ENNReal.ofReal (‖f w‖ ^ 2) = ‖f w‖ₑ ^ 2 := fun w => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  simp only [this]
  rw [key, ENNReal.toReal_mul, ENNReal.coe_toReal]

end GlobalTheory
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory

theorem matrix_exists_sub_mem_trace_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Submodule ℂ (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ n ∈ N, (nᴴ * M₀).trace = 0 := by
  let e : Matrix ι ι ℂ →ₗ[ℂ] EuclideanSpace ℂ (ι × ι) :=
    { toFun := fun A => WithLp.toLp 2 (fun p : ι × ι => A p.1 p.2)
      map_add' := fun A B => rfl
      map_smul' := fun c A => rfl }
  have hin : ∀ A B : Matrix ι ι ℂ, inner ℂ (e A) (e B) = (Aᴴ * B).trace := by
    intro A B
    simp only [e, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
    rfl
  obtain ⟨y, hy, z, hz, h⟩ := (N.map e).exists_add_mem_mem_orthogonal (e M)
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨M - y', by simpa using hy', fun n hn => ?_⟩
  rw [← hin, map_sub, h, add_sub_cancel_left]
  exact (Submodule.mem_orthogonal _ _).1 hz _ ⟨n, hn, rfl⟩

theorem matrix_commutant_lift_mod_stable :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ))
      (N : Submodule ℂ (Matrix ι ι ℂ)), (∀ x ∈ S, xᴴ ∈ S) →
      (∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N) → ∀ M : Matrix ι ι ℂ,
      (∀ x ∈ S, x * M - M * x ∈ N) →
      ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ x ∈ S, x * M₀ = M₀ * x := by
  intro ι _ _ S N hS hN M hM
  obtain ⟨M₀, h1, h2⟩ := matrix_exists_sub_mem_trace_orthogonal N M
  refine ⟨M₀, h1, fun x hx => ?_⟩
  have hw : x * M₀ - M₀ * x ∈ N := by
    have := N.sub_mem (hM x hx) (hN x hx _ h1)
    convert this using 1
    noncomm_ring
  set w := x * M₀ - M₀ * x with hwdef
  have h3 := h2 _ (hN _ (hS x hx) w hw)
  have h4 : (wᴴ * w).trace = 0 := by
    rw [← h3]
    have : (wᴴ * (M₀ * x)).trace = (x * wᴴ * M₀).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    conv_lhs => rw [hwdef, Matrix.mul_sub, ← hwdef]
    rw [Matrix.trace_sub, this]
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc]
  open scoped ComplexOrder in
  exact sub_eq_zero.1 (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h4)

end GlobalTheory
end
