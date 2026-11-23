module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
import Aesop.Main
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Lagrange
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory

theorem fubini_right_convolution_bounded_continuous
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (μ : Measure G) (𝓕 : Set G)
    (h𝓕 : μ 𝓕 < ⊤) (m : Measure H) [SFinite m] (α : H → ℂ) (hα : Integrable α m)
    (ψ φ : G → ℂ) (hψ : Continuous ψ) (hφ : Continuous φ) (A B : ℝ)
    (hA : ∀ g, ‖ψ g‖ ≤ A) (hB : ∀ g, ‖φ g‖ ≤ B) :
    IntegrableOn (fun x => ψ x * ∫ h, α h * φ (x * (h : G)) ∂m) 𝓕 μ ∧
    Integrable (fun h : H => α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) m ∧
    ∫ x in 𝓕, ψ x * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ
      = ∫ h, α h * (∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) ∂m := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simpa [Measure.restrict_apply_univ] using h𝓕⟩
  set F : G → H → ℂ := fun x h => ψ x * (α h * φ (x * (h : G))) with hFdef
  have hcont : Continuous (fun p : G × H => ψ p.1 * φ (p.1 * (p.2 : G))) :=
    (hψ.comp continuous_fst).mul (hφ.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((μ.restrict 𝓕).prod m) := by
    have h1 : AEStronglyMeasurable (fun p : G × H => ψ p.1 * φ (p.1 * (p.2 : G))) ((μ.restrict 𝓕).prod m) :=
      hcont.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : G × H => α p.2) ((μ.restrict 𝓕).prod m) :=
      hα.aestronglyMeasurable.comp_snd
    refine (h1.mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hFdef, Pi.mul_apply]; ring
  have hbd : Integrable (fun p : G × H => (1 : ℝ) * ((A * B) * ‖α p.2‖)) ((μ.restrict 𝓕).prod m) :=
    (integrable_const (1 : ℝ)).mul_prod (hα.norm.const_mul (A * B))
  have hint : Integrable (Function.uncurry F) ((μ.restrict 𝓕).prod m) := by
    refine hbd.mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hFdef, norm_mul, one_mul]
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1)
    calc ‖ψ p.1‖ * (‖α p.2‖ * ‖φ (p.1 * (p.2 : G))‖) ≤ A * (‖α p.2‖ * B) := by
          gcongr
          · exact hA _
          · exact hB _
      _ = A * B * ‖α p.2‖ := by ring
  have hL : ∀ x, ∫ h, F x h ∂m = ψ x * ∫ h, α h * φ (x * (h : G)) ∂m := fun x =>
    integral_const_mul _ _
  have hR : ∀ h : H, ∫ x in 𝓕, F x h ∂μ = α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ := by
    intro h
    rw [← integral_const_mul]
    congr 1; funext x; simp only [hFdef]; ring
  refine ⟨?_, ?_, ?_⟩
  · have := hint.integral_prod_left
    exact (by simpa [Function.uncurry, hL] using this : Integrable _ (μ.restrict 𝓕))
  · have := hint.integral_prod_right
    simpa [Function.uncurry, hR] using this
  · have := integral_integral_swap hint
    simpa [hL, hR] using this

end GlobalTheory
end

section

namespace GlobalTheory

open Complex

theorem mem_closure_of_forall_dual_vanish :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  intro E _ _ _ _ p hp Z x h
  haveI := hp.continuousSMul
  haveI : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  by_contra hx
  rw [← Z.topologicalClosure_coe] at hx
  obtain ⟨f, u, hfx, hf⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
    ((Z.topologicalClosure.restrictScalars ℝ).convex) Z.isClosed_topologicalClosure hx
  simp only [RCLike.re_to_complex] at hfx hf
  have hre : ∀ w ∈ Z, (f w).re = 0 := by
    intro w hw
    by_contra hne
    set t : ℝ := (u - 1) / (f w).re
    have hmem : ((t : ℂ) • w) ∈ Z.topologicalClosure :=
      Z.le_topologicalClosure (Z.smul_mem _ hw)
    have h1 := hf _ hmem
    rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul] at h1
    have : t * (f w).re = u - 1 := by
      simp only [t]; field_simp
    linarith
  have hvan : ∀ z ∈ Z, f z = 0 := by
    intro z hz
    have h1 := hre z hz
    have h2 := hre (Complex.I • z) (Z.smul_mem _ hz)
    rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
    apply Complex.ext
    · simpa using h1
    · simp at h2; simpa using h2
  have h0 := hf 0 (Z.topologicalClosure.zero_mem)
  have hfx0 := h f hvan
  rw [map_zero] at h0
  rw [hfx0] at hfx
  simp at h0 hfx
  linarith

end GlobalTheory
end

section

open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem bilinear_bound_of_dense_right : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by
  intro E _ _ _ _ _ _ p hp X₁ X₂ _ _ _ _ j₁ j₂ hinj hcl D₂ hdense F h₁ h₂ b i
  haveI : ContinuousSMul ℂ E := hp.continuousSMul
  haveI : FirstCountableTopology E := hp.firstCountableTopology
  haveI : PolynormableSpace ℂ E := hp.toPolynormableSpace
  haveI : IsTopologicalAddGroup E := inferInstance
  set Y : Submodule ℂ E := LinearMap.range j₁ with hYdef
  have hYc : IsClosed (Y : Set E) := by simpa [Y, LinearMap.coe_range] using hcl
  haveI : IsUniformAddGroup Y := Y.toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace Y := hYc.completeSpace_coe
  haveI : FirstCountableTopology Y := Topology.IsInducing.subtypeVal.firstCountableTopology
  haveI : (𝓤 Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : BarrelledSpace ℂ Y := inferInstance
  let e : X₁ ≃ₗ[ℂ] Y := LinearEquiv.ofInjective j₁ hinj
  have he : ∀ w, ((e w : Y) : E) = j₁ w := fun w => rfl

  let gl : D₂ → Y →ₗ[ℂ] E := fun a => (F.flip (a : X₂)).comp e.symm.toLinearMap
  have hgl : ∀ a y, gl a y = F (e.symm y) a := fun a y => rfl
  have hgc : ∀ a, Continuous (gl a) := by
    intro a
    refine hp.continuous_of_continuous_comp (gl a) fun k => ?_
    obtain ⟨q, hq, hle⟩ := h₂ a a.2 k
    refine Seminorm.continuous_of_le (q := q.comp Y.subtype) (hq.comp continuous_subtype_val) ?_
    intro y
    have := hle (e.symm y)
    rw [← he, e.apply_symm_apply] at this
    simpa [Seminorm.comp_apply, hgl] using this
  let g : D₂ → Y →L[ℂ] E := fun a => ⟨gl a, hgc a⟩
  let l : Filter D₂ := Filter.comap (fun a : D₂ => j₂ a) (𝓝 (j₂ b))
  haveI : l.NeBot := by
    rw [Filter.comap_neBot_iff]
    intro t ht
    obtain ⟨_, htx, ⟨a, ha, rfl⟩⟩ := mem_closure_iff_nhds.mp (hdense b) t ht
    exact ⟨⟨a, ha⟩, htx⟩
  have hT : Tendsto (fun a y => g a y) l (𝓝 fun y => F (e.symm y) b) := by
    rw [tendsto_pi_nhds]
    intro y
    rw [hp.tendsto_nhds]
    intro k ε hε
    obtain ⟨q, hq, hle⟩ := h₁ (e.symm y) k
    have ht : Tendsto (fun a : D₂ => q (j₂ a - j₂ b)) l (𝓝 0) := by
      have h0 : Tendsto (fun a : D₂ => j₂ a - j₂ b) l (𝓝 (j₂ b - j₂ b)) :=
        tendsto_comap.sub tendsto_const_nhds
      have := (hq.tendsto _).comp h0
      simpa [Function.comp_def] using this
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with a ha
    calc p k (g a y - F (e.symm y) b) = p k (F (e.symm y) ((a : X₂) - b)) := by
          simp [g, hgl, map_sub]
      _ ≤ q (j₂ ((a : X₂) - b)) := hle _
      _ < ε := by simpa [map_sub] using ha
  let G : Y →L[ℂ] E := continuousLinearMapOfTendsto g hT
  have hG : ∀ y, G y = F (e.symm y) b := fun y => rfl
  have hr : Continuous ((p i).comp G.toLinearMap) := (hp.continuous_seminorm i).comp G.continuous
  obtain ⟨q, hq, hle⟩ := Seminorm.exists_le_comp_of_isInducing hr (f := Y.subtype) .subtypeVal
  refine ⟨q, hq, fun w => ?_⟩
  have := hle (e w)
  simpa [Seminorm.comp_apply, hG, he] using this

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory


open scoped Matrix.Norms.L2Operator in
theorem unitary_submonoid_exists_skewAdjoint_log_polynomial (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ)
    (hk : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      star X = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  classical
  have hspec := spectrum.subset_circle_of_unitary (𝕜 := ℂ) hk
  have hfin := Matrix.finite_spectrum k
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k) := fun f => hfin.continuousOn f
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ z ∈ spectrum ℂ k, p.eval z = Complex.log z := by
    refine ⟨Lagrange.interpolate hfin.toFinset id Complex.log, fun z hz => ?_⟩
    have := Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) (i := z) Complex.log
      (Set.injOn_id _) (by simpa using hz)
    simpa using this
  refine ⟨cfc Complex.log k, p, ?_, ?_, ?_⟩
  · rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    have h1 : ‖z‖ = 1 := by simpa using hspec hz
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
  · rw [← CFC.complex_exp_eq_normedSpace_exp, ← cfc_comp Complex.exp Complex.log k
      (hg := (Set.Finite.image _ hfin).continuousOn _) (hf := hcont _)]
    have h0 : ∀ z ∈ spectrum ℂ k, (Complex.exp ∘ Complex.log) z = id z := by
      intro z hz
      have h1 : ‖z‖ = 1 := by simpa using hspec hz
      have : z ≠ 0 := by rintro rfl; simp at h1
      simp [Complex.exp_log this]
    rw [cfc_congr h0, cfc_id ℂ k]
  · rw [← cfc_polynomial p k]
    exact cfc_congr fun z hz => (hp z hz).symm

theorem unitary_exists_skew_log (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ) (hk : kᴴ * k = 1) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  have hmem : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨hk, mul_eq_one_comm.mp hk⟩
  obtain ⟨X, p, h1, h2, h3⟩ := unitary_submonoid_exists_skewAdjoint_log_polynomial n k hmem
  exact ⟨X, p, h1, h2, h3⟩

end GlobalTheory
end

section

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace GlobalTheory

theorem posDef_conjTranspose_mul_self_eq_exp_polynomial :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g →
      ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
        Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧ L = Polynomial.aeval (gᴴ * g) p := by
  intro n g hg
  set h : Matrix (Fin n) (Fin n) ℂ := gᴴ * g with hh
  have hpd : h.PosDef :=
    Matrix.PosDef.conjTranspose_mul_self g (Matrix.mulVec_injective_iff_isUnit.mpr hg)
  have hsp : IsStrictlyPositive h := hpd.isStrictlyPositive
  have hsa : IsSelfAdjoint h := hpd.isHermitian
  have hfin : (spectrum ℝ h).Finite := Matrix.finite_real_spectrum
  classical
  let s : Finset ℝ := hfin.toFinset
  let q : Polynomial ℝ := Lagrange.interpolate s id Real.log
  have hq : ∀ x ∈ spectrum ℝ h, q.eval x = Real.log x := by
    intro x hx
    have hxs : x ∈ s := hfin.mem_toFinset.mpr hx
    exact Lagrange.eval_interpolate_at_node (r := Real.log) (Set.injOn_id _) hxs
  refine ⟨CFC.log h, q.map (algebraMap ℝ ℂ), ?_, CFC.exp_log h hsp, ?_⟩
  · have : IsSelfAdjoint (CFC.log h) := by
      unfold CFC.log; exact cfc_predicate _ _
    exact this
  · rw [Polynomial.aeval_map_algebraMap, ← cfc_polynomial q h]
    unfold CFC.log
    exact cfc_congr (fun x hx => (hq x hx).symm)

end GlobalTheory
end

section

namespace GlobalTheory.QuotientDescentTwistedOperators

open Topology

noncomputable def desc {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G)
    (f : G → ℂ) (hf : Continuous f) (hΓ : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) : C(G ⧸ Γ, ℂ) where
  toFun := fun q => Quotient.liftOn' q f (by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply] at hab
    have := hΓ _ hab a
    rw [← this]
    congr 1
    abel)
  continuous_toFun := hf.quotient_liftOn' _

theorem desc_mk {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G)
    (f : G → ℂ) (hf : Continuous f) (hΓ : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) (x : G) :
    desc Γ f hf hΓ (QuotientAddGroup.mk x) = f x := rfl

theorem approx : ∀ (G : Type) [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [inst_6 : MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology ↥Γ] (K : Set G), IsCompact K → (∀ (x : G), ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [inst_9 : AddCommGroup A] (χ : A → G → ℂ), (∀ (a : A), Continuous (χ a)) → (∀ (a : A) (x y : G), χ a (x + y) = χ a x * χ a y) → (∀ (a b : A) (x : G), χ (a + b) x = χ a x * χ b x) → (∀ (x : G), χ (0 : A) x = (1 : ℂ)) → (∀ (a : A) (x : G), ‖χ a x‖ = (1 : ℝ)) → (∀ (x : G), (∀ (a : A), χ a x = (1 : ℂ)) ↔ x ∈ Γ) → ∀ (Φ : G → ℂ), Continuous Φ → (∀ γ ∈ Γ, ∀ (x : G), Φ (γ + x) = Φ x) → ∀ (ε : ℝ), (0 : ℝ) < ε → ∃ (s : Finset A) (c : A → ℂ), ∀ (x : G), ‖Φ x - ∑ a ∈ s, c a * χ a x‖ ≤ ε := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ χ hc hmulx hadd hzero hnorm hker Φ hΦ hΦinv ε hε

  have : CompactSpace (G ⧸ Γ) := by
    refine ⟨?_⟩
    have hU : (Set.univ : Set (G ⧸ Γ)) = QuotientAddGroup.mk '' K := by
      ext q
      refine QuotientAddGroup.induction_on q fun x => ?_
      obtain ⟨γ, hγ, hk⟩ := hcov x
      refine ⟨fun _ => ⟨γ + x, hk, ?_⟩, fun _ => Set.mem_univ _⟩
      rw [QuotientAddGroup.eq]
      have : -(γ + x) + x = -γ := by abel
      rw [this]
      exact Γ.neg_mem hγ
    rw [hU]
    exact hK.image continuous_quot_mk
  have hχ0 : ∀ a, χ a 0 = 1 := fun a => (hker 0).2 Γ.zero_mem a
  have hinv : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := by
    intro a γ hγ x
    rw [hmulx, (hker γ).2 hγ a, one_mul]

  let e : A → C(G ⧸ Γ, ℂ) := fun a => desc Γ (χ a) (hc a) (hinv a)
  have he_apply : ∀ a x, e a (QuotientAddGroup.mk x) = χ a x := fun a x =>
    desc_mk Γ (χ a) (hc a) (hinv a) x
  have he_add : ∀ a b, e (a + b) = e a * e b := by
    intro a b
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.mul_apply, he_apply, he_apply, he_apply, hadd]
  have he_zero : e 0 = 1 := by
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.one_apply, he_apply, hzero]
  have he_star : ∀ a, star (e a) = e (-a) := by
    intro a
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.star_apply, he_apply, he_apply]
    have h1 : χ (-a) x * χ a x = 1 := by rw [← hadd, neg_add_cancel, hzero]
    have h2 : χ a x * star (χ a x) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    linear_combination (-(star (χ a x))) * h1 + χ (-a) x * h2

  let S : Submodule ℂ C(G ⧸ Γ, ℂ) := Submodule.span ℂ (Set.range e)
  have hone : (1 : C(G ⧸ Γ, ℂ)) ∈ S := he_zero ▸ Submodule.subset_span ⟨0, rfl⟩
  have hmul : ∀ f g, f ∈ S → g ∈ S → f * g ∈ S := by
    intro f g hf hg
    have h := Submodule.mul_mem_mul hf hg
    rw [Submodule.span_mul_span] at h
    refine (Submodule.span_le.mpr ?_) h
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨a + b, he_add a b⟩
  have hstar : ∀ f ∈ S, star f ∈ S := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span ⟨-a, (he_star a).symm⟩
    | zero => rw [star_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact S.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact S.smul_mem _ hx
  let B : StarSubalgebra ℂ C(G ⧸ Γ, ℂ) :=
    { carrier := S
      mul_mem' := fun {f g} hf hg => hmul f g hf hg
      one_mem' := hone
      add_mem' := fun hf hg => S.add_mem hf hg
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem c hone
      star_mem' := fun {f} hf => hstar f hf }

  have hsep : B.SeparatesPoints := by
    intro q₁ q₂
    refine QuotientAddGroup.induction_on q₁ fun x => QuotientAddGroup.induction_on q₂ fun y => ?_
    intro hne
    have hex : ∃ a, χ a x ≠ χ a y := by
      by_contra hall
      simp only [not_exists, ne_eq, not_not] at hall
      apply hne
      rw [QuotientAddGroup.eq]
      refine (hker _).1 fun a => ?_
      rw [hmulx, ← hall a, ← hmulx, neg_add_cancel, hχ0 a]
    obtain ⟨a, ha⟩ := hex
    refine ⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ?_⟩
    rwa [he_apply, he_apply]

  have hB := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hsep
  let Φq : C(G ⧸ Γ, ℂ) := desc Γ Φ hΦ hΦinv
  have hmem : Φq ∈ closure (B : Set C(G ⧸ Γ, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, hB]
    trivial
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨c, hcg⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (show g ∈ S from hg)
  refine ⟨c.support, c, fun x => ?_⟩
  have hval : ∑ a ∈ c.support, c a * χ a x = g (QuotientAddGroup.mk x) := by
    rw [← hcg, Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ContinuousMap.smul_apply, he_apply, smul_eq_mul]
  rw [hval, ← desc_mk Γ Φ hΦ hΦinv x]
  calc ‖Φq (QuotientAddGroup.mk x) - g (QuotientAddGroup.mk x)‖
      = ‖(Φq - g) (QuotientAddGroup.mk x)‖ := rfl
    _ ≤ ‖Φq - g‖ := ContinuousMap.norm_coe_le_norm _ _
    _ = dist Φq g := (dist_eq_norm _ _).symm
    _ ≤ ε := hdist.le

end GlobalTheory.QuotientDescentTwistedOperators
end
