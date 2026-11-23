module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Analysis.Calculus.FDeriv.Congr
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.ChartPullBack

theorem comp_symm_eventuallyEq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : ((f ∘ c) ∘ c.symm) =ᶠ[𝓝 z] f := by
  filter_upwards [c.open_target.mem_nhds hz] with y hy
  simp [Function.comp, c.right_inv hy]

theorem fderiv_comp_symm_eq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : fderiv ℝ ((f ∘ c) ∘ c.symm) z = fderiv ℝ f z :=
  (comp_symm_eventuallyEq c f hz).fderiv_eq

theorem fderiv_comp_symm_eventuallyEq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : fderiv ℝ ((f ∘ c) ∘ c.symm) =ᶠ[𝓝 z] fderiv ℝ f := by
  filter_upwards [c.open_target.mem_nhds hz] with y hy
  exact fderiv_comp_symm_eq c f hy

theorem fderiv_fderiv_comp_symm_eq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) :
    fderiv ℝ (fderiv ℝ ((f ∘ c) ∘ c.symm)) z = fderiv ℝ (fderiv ℝ f) z :=
  (fderiv_comp_symm_eventuallyEq c f hz).fderiv_eq

theorem C2_tendsto_chart_pullback : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (c : OpenPartialHomeomorph X (Fin e → ℂ)) (g : ℝ → (Fin e → ℂ) → ℝ) (p : (Fin e → ℂ) → ℝ) (K' : Set (Fin e → ℂ)), K' ⊆ c.target → (TendstoUniformlyOn g p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (g t)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (g t))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (g t) z - fderiv ℝ p z‖ ≤ M * t) → (TendstoUniformlyOn (fun t => (g t ∘ c) ∘ c.symm) p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ ((g t ∘ c) ∘ c.symm)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ ((g t ∘ c) ∘ c.symm))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ ((g t ∘ c) ∘ c.symm) z - fderiv ℝ p z‖ ≤ M * t) := by
  intro e X _ c g p K' hK h
  obtain ⟨h0, h1, h2, M, hM⟩ := h
  refine ⟨h0.congr (Eventually.of_forall fun t z hz => ?_),
    h1.congr (Eventually.of_forall fun t z hz => ?_),
    h2.congr (Eventually.of_forall fun t z hz => ?_),
    M, hM.mono fun t ht z hz => ?_⟩
  · exact ((comp_symm_eventuallyEq c (g t) (hK hz)).eq_of_nhds).symm
  · exact (fderiv_comp_symm_eq c (g t) (hK hz)).symm
  · exact (fderiv_fderiv_comp_symm_eq c (g t) (hK hz)).symm
  · rw [fderiv_comp_symm_eq c (g t) (hK hz)]
    exact ht z hz

end GlobalTheory.CompanionTheory.Metric.ChartPullBack
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Metric.QuotHol

theorem differentiableOn_det {m n : ℕ} {A : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ}
    {V : Set (Fin n → ℂ)} (hA : ∀ i j, DifferentiableOn ℂ (fun t => A t i j) V) :
    DifferentiableOn ℂ (fun t => (A t).det) V := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  refine DifferentiableOn.const_smul ?_ _
  have hs : ∀ s : Finset (Fin m), DifferentiableOn ℂ (fun t => ∏ i ∈ s, A t (σ i) i) V := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact differentiableOn_const _
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).fun_mul ih
  exact hs Finset.univ

theorem exists_complement {k g' : ℕ} (v : Fin k → Fin (k + g') → ℂ)
    (hv : LinearIndependent ℂ v) :
    ∃ f : Fin g' → Fin (k + g') → ℂ,
      (Matrix.of fun i j => Sum.elim v f (finSumFinEquiv.symm j) i :
        Matrix (Fin (k + g')) (Fin (k + g')) ℂ).det ≠ 0 := by
  classical
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (Submodule.span ℂ (Set.range v))
  have hfr : Module.finrank ℂ W' = g' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW'
    have h2 := finrank_span_eq_card hv
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1 h2
    omega
  let bW := Module.finBasisOfFinrankEq ℂ W' hfr
  let f : Fin g' → Fin (k + g') → ℂ := fun j => (bW j : Fin (k + g') → ℂ)
  have hf : LinearIndependent ℂ f :=
    bW.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  have hdisj : Disjoint (Submodule.span ℂ (Set.range v)) (Submodule.span ℂ (Set.range f)) := by
    refine hW'.disjoint.mono_right ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (bW j).2
  have hs : LinearIndependent ℂ (Sum.elim v f) := hv.sum_type hf hdisj
  have hc := hs.comp _ (finSumFinEquiv.symm.injective)
  refine ⟨f, ?_⟩
  have hu := Matrix.linearIndependent_cols_iff_isUnit
    (A := (Matrix.of fun i j => Sum.elim v f (finSumFinEquiv.symm j) i :
      Matrix (Fin (k + g')) (Fin (k + g')) ℂ)) |>.1 hc
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem exists_holomorphic_quotient (g' k g n : ℕ) (U : Set (Fin n → ℂ))
    (e : Fin k → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ) (hU : IsOpen U) (ht₀ : t₀ ∈ U)
    (hg : k + g' = g) (he : ∀ i, DifferentiableOn ℂ (e i) U)
    (hli : LinearIndependent ℂ (fun i => e i t₀)) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ U ∧
      ∃ q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ),
        (∀ x, DifferentiableOn ℂ (fun t => q t x) V) ∧
        ∀ t ∈ V, Function.Surjective (q t) ∧
          LinearMap.ker (q t) = Submodule.span ℂ (Set.range fun i => e i t) := by
  classical
  subst hg
  obtain ⟨f, hf⟩ := exists_complement (fun i => e i t₀) hli
  let M : (Fin n → ℂ) → Matrix (Fin (k + g')) (Fin (k + g')) ℂ := fun t =>
    Matrix.of fun i j => Sum.elim (fun a => e a t) f (finSumFinEquiv.symm j) i
  have hMc : ∀ t a i, M t i (Fin.castAdd g' a) = e a t i := by
    intro t a i
    simp [M]
  have hMn : ∀ t b i, M t i (Fin.natAdd k b) = f b i := by
    intro t b i
    simp [M]
  have hMent : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) U := by
    intro i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with a | c
    · simp only [finSumFinEquiv_apply_left, hMc]
      exact (differentiableOn_pi.1 (he a)) i
    · simp only [finSumFinEquiv_apply_right, hMn]
      exact differentiableOn_const _
  have hdet : DifferentiableOn ℂ (fun t => (M t).det) U := differentiableOn_det hMent
  let V : Set (Fin n → ℂ) := U ∩ (fun t => (M t).det) ⁻¹' {0}ᶜ
  have hVo : IsOpen V := hdet.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hVU : V ⊆ U := Set.inter_subset_left
  have hinv : ∀ i j, DifferentiableOn ℂ (fun t => (M t)⁻¹ i j) V := by
    intro i j
    have h1 : DifferentiableOn ℂ (fun t => ((M t).det)⁻¹) V :=
      (hdet.mono hVU).inv (fun t ht => ht.2)
    have h2 : DifferentiableOn ℂ (fun t => (M t).adjugate i j) V := by
      simp only [Matrix.adjugate_apply]
      refine differentiableOn_det fun a b => ?_
      by_cases h : a = j
      · subst h
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne h]
        exact (hMent a b).mono hVU
    simpa [Matrix.inv_def, Ring.inverse_eq_inv'] using h1.fun_mul h2
  let q : (Fin n → ℂ) → (Fin (k + g') → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := fun t =>
    LinearMap.funLeft ℂ ℂ (Fin.natAdd k) ∘ₗ ((M t)⁻¹).mulVecLin
  have hq : ∀ t x j, q t x j = ((M t)⁻¹ *ᵥ x) (Fin.natAdd k j) := by
    intro t x j
    simp [q, LinearMap.funLeft_apply]
  refine ⟨V, hVo, ⟨ht₀, hf⟩, hVU, q, ?_, ?_⟩
  · intro x
    refine differentiableOn_pi.2 fun j => ?_
    simp only [hq, Matrix.mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun l _ => (hinv _ l).mul_const _
  · intro t ht
    have hu : IsUnit (M t).det := isUnit_iff_ne_zero.2 ht.2
    have hMi : M t * (M t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    have hiM : (M t)⁻¹ * M t = 1 := Matrix.nonsing_inv_mul _ hu
    refine ⟨fun y => ?_, ?_⟩
    · refine ⟨M t *ᵥ (fun j => Sum.elim 0 y (finSumFinEquiv.symm j)), ?_⟩
      ext j
      rw [hq, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]
      simp
    · apply le_antisymm
      · intro x hx
        have hx0 : ∀ j, ((M t)⁻¹ *ᵥ x) (Fin.natAdd k j) = 0 := by
          intro j
          rw [← hq, LinearMap.mem_ker.1 hx]
          rfl
        have hxc : x = M t *ᵥ ((M t)⁻¹ *ᵥ x) := by
          rw [Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]
        obtain ⟨c, hc⟩ : ∃ c, c = (M t)⁻¹ *ᵥ x := ⟨_, rfl⟩
        rw [← hc] at hx0 hxc
        have hsum : x = ∑ a, c (Fin.castAdd g' a) • e a t := by
          conv_lhs => rw [hxc]
          ext i
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, hx0, mul_zero,
            Finset.sum_const_zero, add_zero, hMc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun a _ => mul_comm _ _
        rw [hsum]
        exact Submodule.sum_mem _ fun a _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        have hcol : e a t = M t *ᵥ Pi.single (Fin.castAdd g' a) 1 := by
          ext i
          simp [hMc]
        refine LinearMap.mem_ker.2 ?_
        ext j
        rw [hq]
        show ((M t)⁻¹ *ᵥ e a t) (Fin.natAdd k j) = 0
        rw [hcol, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]
        refine Pi.single_eq_of_ne ?_ _
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        have := a.2
        omega

end GlobalTheory.CompanionTheory.Metric.QuotHol
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.RealFormIndep

theorem pairing_real_combination {g k : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (u : Fin k → Fin g → ℂ) (a b : Fin k → ℝ) :
    (∑ i, a i • u i) ⬝ᵥ Hm *ᵥ star (∑ j, b j • u j) =
      ∑ i, ∑ j, ((a i * b j : ℝ) : ℂ) * (u i ⬝ᵥ Hm *ᵥ star (u j)) := by
  rw [star_sum, mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_smul, star_trivial, mulVec_smul, smul_dotProduct, dotProduct_smul, Complex.real_smul,
    Complex.real_smul, Complex.ofReal_mul]
  ring

theorem linearIndependent_complex_of_real_form :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℝ u →
        (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) → LinearIndependent ℂ u := by
  intro g k Hm hpos u hu hreal
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro c hc
  have hR : ∀ a b : Fin k → ℝ, ((∑ i, a i • u i) ⬝ᵥ Hm *ᵥ star (∑ j, b j • u j)).im = 0 := by
    intro a b
    rw [pairing_real_combination]
    simp [Complex.im_sum, hreal]
  have hxy : (∑ i, (c i).re • u i) + Complex.I • (∑ i, (c i).im • u i) = 0 := by
    rw [← hc]
    ext t
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Complex.re_add_im (c i)]
    ring
  have hx : (∑ i, (c i).re • u i) = -(Complex.I • ∑ i, (c i).im • u i) := eq_neg_of_add_eq_zero_left hxy
  have hyy : ((∑ i, (c i).im • u i) ⬝ᵥ Hm *ᵥ star (∑ j, (c j).im • u j)).re = 0 := by
    have h := hR (fun i => (c i).re) (fun j => (c j).im)
    rw [hx, neg_dotProduct, smul_dotProduct, smul_eq_mul] at h
    simpa using h
  have hy0 : (∑ i, (c i).im • u i) = 0 := by
    by_contra hne
    have := hpos _ hne
    linarith
  have hx0 : (∑ i, (c i).re • u i) = 0 := by
    rw [hx, hy0, smul_zero, neg_zero]
  intro i
  have h1 := hu (fun i => (c i).re) hx0 i
  have h2 := hu (fun i => (c i).im) hy0 i
  exact Complex.ext (by simpa using h1) (by simpa using h2)

end GlobalTheory.CompanionTheory.Ar.RealFormIndep
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem mem_span_part_of_period_real_comb :
    ∀ (g k n : ℕ) (Λ : Type) [AddCommGroup Λ] (P : Λ →+ (Fin g → ℂ))
      (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n),
      LinearIndependent ℝ (fun j => P (b j)) → Function.Injective f →
      ∀ (x : Λ) (c : Fin k → ℝ), P x = ∑ i, (c i : ℂ) • P (b (f i)) →
        x ∈ Submodule.span ℤ (Set.range fun i => b (f i)) := by
  intro g k n Λ _ P b f hli hf x c hx
  classical

  have hPx : P x = ∑ j, ((b.repr x j : ℤ) : ℝ) • P (b j) := by
    conv_lhs => rw [← b.sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]

  let d : Fin n → ℝ := fun j => ∑ i, if f i = j then c i else 0
  have hPd : P x = ∑ j, d j • P (b j) := by
    rw [hx]
    simp only [d, Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Complex.coe_smul]
  have hcoef : ∀ j, ((b.repr x j : ℤ) : ℝ) = d j := by
    have h0 : ∑ j, (((b.repr x j : ℤ) : ℝ) - d j) • P (b j) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hPx, ← hPd, sub_self]
    intro j
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 j)
  have hzero : ∀ j, j ∉ Set.range f → b.repr x j = 0 := by
    intro j hj
    have hd : d j = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      exact fun h => hj ⟨i, h⟩
    have := hcoef j
    rw [hd] at this
    exact_mod_cast this
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [hzero j hj, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem harmonicAt_update_of_levi_eq_zero :
    ∀ (n : ℕ) (φ : (Fin n → ℂ) → ℝ) (O : Set (Fin n → ℂ)), IsOpen O → ContDiffOn ℝ ∞ φ O →
      (∀ z ∈ O, ∀ w, levi φ z w = 0) → ∀ z ∈ O, ∀ i,
        InnerProductSpace.HarmonicAt (fun t : ℂ => φ (Function.update z i t)) (z i) := by
  intro n φ O hO hφ hl z hz i
  set e : Fin n → ℂ := Pi.single i 1 with he
  let L : ℂ →L[ℝ] (Fin n → ℂ) := ((ContinuousLinearMap.id ℂ ℂ).smulRight e).restrictScalars ℝ
  have hLw : ∀ w : ℂ, L w = w • e := fun _ => rfl
  set z0 : Fin n → ℂ := Function.update z i 0 with hz0
  have hupd : ∀ t : ℂ, Function.update z i t = z0 + t • e := by
    intro t
    funext j
    by_cases h : j = i
    · subst h
      simp [hz0, he]
    · simp [hz0, he, h]
  have hline : ∀ t : ℂ, HasFDerivAt (fun w : ℂ => z0 + w • e) L t := fun t =>
    L.hasFDerivAt.const_add z0
  have hcont : Continuous (fun t : ℂ => z0 + t • e) := by fun_prop
  have hU : IsOpen ((fun t : ℂ => z0 + t • e) ⁻¹' O) := hO.preimage hcont
  have hzU : z i ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O := by
    show z0 + z i • e ∈ O
    rw [← hupd]
    simpa using hz
  have hφ2 : ∀ y ∈ O, ContDiffAt ℝ 2 φ y := fun y hy =>
    ((hφ y hy).contDiffAt (hO.mem_nhds hy)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)
  have hlap : ∀ t ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O,
      Laplacian.laplacian (fun t : ℂ => φ (z0 + t • e)) t = 0 := by
    intro t ht
    have hy : z0 + t • e ∈ O := ht
    have h1 : fderiv ℝ (fun w : ℂ => φ (z0 + w • e)) =ᶠ[𝓝 t]
        fun w : ℂ => (fderiv ℝ φ (z0 + w • e)).comp L := by
      filter_upwards [hU.mem_nhds ht] with w hw
      exact (((hφ2 _ hw).differentiableAt (by simp)).hasFDerivAt.comp w (hline w)).fderiv
    have hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z0 + t • e)) (z0 + t • e) :=
      (((hφ2 _ hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
    have h2 := ((hD.comp t (hline t)).clm_comp (hasFDerivAt_const L t)).fderiv
    simp only [Function.comp_def] at h2
    have hle := hl _ hy e
    unfold levi at hle
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply]
    rw [h1.fderiv_eq, h2]
    simp [hLw]
    linarith
  rw [show (fun t : ℂ => φ (Function.update z i t)) = fun t : ℂ => φ (z0 + t • e) from
    funext fun t => by rw [hupd]]
  refine ⟨?_, ?_⟩
  · have hA : ContDiffAt ℝ 2 (fun t : ℂ => z0 + t • e) (z i) := by
      have : ContDiff ℝ 2 (fun t : ℂ => z0 + L t) := contDiff_const.add L.contDiff
      exact this.contDiffAt
    exact (hφ2 _ hzU).comp (z i) hA
  · filter_upwards [hU.mem_nhds hzU] with t ht
    simpa using hlap t ht

end GlobalTheory.CompanionTheory.Metric
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.ProjReal

theorem orthogonal_projection_real_coefficients :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u →
      (∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ, ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0) →
      (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) →
      ∀ z : Fin g → ℂ, (∀ j, (z ⬝ᵥ Hm *ᵥ star (u j)).im = 0) →
      ∃ c : Fin k → ℝ, ∀ j, (z - ∑ i, (c i : ℂ) • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  intro g k Hm _ u _ hproj hu z hz
  obtain ⟨c, hc⟩ := hproj z
  refine ⟨fun i => (c i).re, fun j => ?_⟩
  have h := hc j
  simp only [sub_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul] at h ⊢
  apply Complex.ext
  · have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.re_sum, Complex.mul_re, hu, mul_zero, sub_zero, Complex.zero_re] at h'
    simpa [Complex.sub_re, Complex.re_sum, Complex.mul_re, hu] using h'
  · simp [Complex.sub_im, Complex.im_sum, Complex.mul_im, hu, hz]

end GlobalTheory.CompanionTheory.Ar.ProjReal
end
