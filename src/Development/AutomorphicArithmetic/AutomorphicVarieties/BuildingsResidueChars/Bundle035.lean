module

import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CongNum
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle028
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.AdelDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.ScatteringLimits

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.exists_int_eq_prod_of_galois_permuted_integral :
    ∀ (T : Type) [Fintype T] (f : T → ℂ), (∀ t, IsIntegral ℤ (f t)) → (∀ σ : ℂ ≃+* ℂ, ∃ u : T ≃ T, ∀ t, f (u t) = σ (f t)) → ∃ n : ℤ, (n : ℂ) = ∏ t, f t := by
  apply UpperTheory.V.CongNum.exists_int_prod <;> assumption
end

section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

theorem UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → w.asIdeal.inertiaDeg ℤ = 1 → IsSplitAt w := by
  intro E _ _ _ w hun hf
  classical
  set F := maximalRealSubfield E
  set P : Ideal (𝓞 E) := w.asIdeal
  set p : Ideal (𝓞 F) := P.under (𝓞 F)
  have hfin : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F E
  have he : P.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one P (𝓞 F)
  have hf' : P.inertiaDeg (𝓞 F) = 1 := by
    have h := Ideal.inertiaDeg_tower (R := ℤ) p P
    rw [hf] at h
    exact (Nat.eq_one_of_mul_eq_one_left h.symm)
  by_contra hns
  have hone : ∀ q : p.primesOver (𝓞 E), q.1 = P := by
    intro q
    by_contra hq
    apply hns
    have hq0 : q.1 ≠ ⊥ := by
      intro h0
      have hP0 : p = ⊥ := by
        have := q.2.2
        rw [Ideal.liesOver_iff, h0] at this
        rw [this]
        exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      apply w.ne_bot
      exact Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 F) hP0
    refine ⟨⟨q.1, q.2.1, hq0⟩, ?_, ?_⟩
    · intro h
      exact hq (congrArg HeightOneSpectrum.asIdeal h)
    · ext1
      change Ideal.under (𝓞 F) q.1 = p
      exact (Ideal.liesOver_iff _ _).mp q.2.2 |>.symm
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hPmem : P ∈ p.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  have huniq : (Finset.univ : Finset (p.primesOver (𝓞 E))) = {⟨P, hPmem⟩} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subtype.ext (hone q)
  rw [huniq, Finset.sum_singleton, he, hf', hfin] at hsum
  omega
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private theorem finite_translation_mul (g h : GL (Fin a) (Af F)) (φ : TR.Sm F a) :
    TR.finRep F a (g * h) φ = TR.finRep F a g (TR.finRep F a h φ) := by
  rw [map_mul]; rfl

private theorem center_algebra_translation_comm (g : GL (Fin a) (Af F)) {z : Module.End ℂ (TR.Sm F a)} (hz : z ∈ TR.Zalg F a) :
    TR.finRep F a g * z = z * TR.finRep F a g := by
  have key : TR.Zalg F a ≤ Subalgebra.centralizer ℂ {TR.finRep F a g} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, u, rfl⟩
    have hE : ∀ i j, TR.Eop v i j ∈ Subalgebra.centralizer ℂ {TR.finRep F a g} := by
      intro i j
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (TR.lie_rt_fin _ g).symm
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (intCast_mem _ _)
      (Subalgebra.list_prod_mem _ fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine Subalgebra.add_mem _ ?_ (hE _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (key hz) _ rfl

private theorem compact_finite_translation_comm (g : GL (Fin a) (Af F)) (k : TR.Kinf F a) (φ : TR.Sm F a) :
    TR.cptRep F a k (TR.finRep F a g φ) = TR.finRep F a g (TR.cptRep F a k φ) := by
  refine Subtype.ext (funext fun x => ?_)
  change φ.1 (x * TR.infGL F a (Unitary.toUnits k) * finGL F a g) =
    φ.1 (x * finGL F a g * TR.infGL F a (Unitary.toUnits k))
  rw [mul_assoc, mul_assoc, TR.infGL_comm]

private theorem automorphic_form_translate (φ : TR.Sm F a) (g : GL (Fin a) (Af F)) (h : TR.IsAutForm φ) :
    TR.IsAutForm (TR.finRep F a g φ) := by
  refine ⟨fun γ x => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · change φ.1 (ratGL F a γ * x * finGL F a g) = φ.1 (x * finGL F a g)
    rw [mul_assoc, h.left]
  · have e : {k | TR.finRep F a k (TR.finRep F a g φ) = TR.finRep F a g φ} =
        (fun k => g⁻¹ * k * g) ⁻¹' {k | TR.finRep F a k φ = φ} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · intro hk
        rw [finite_translation_mul, finite_translation_mul, hk, ← finite_translation_mul, inv_mul_cancel, map_one]
        rfl
      · intro hk
        have := congrArg (TR.finRep F a g) hk
        rwa [← finite_translation_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, finite_translation_mul] at this
    rw [e]
    exact h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k => TR.cptRep F a k φ)).map (TR.finRep F a g)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (compact_finite_translation_comm g k φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a)).map (TR.finRep F a g))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨z, hz, rfl⟩, LinearMap.congr_fun (center_algebra_translation_comm g hz) φ⟩
  · obtain ⟨C, N, hC⟩ := h.growth (x * finGL F a g)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (x * TR.infGL F a y * finGL F a g)‖ ≤ _
    rw [mul_assoc, TR.infGL_comm, ← mul_assoc]
    exact hC y

private theorem automorphic_form_linear_combination (φ ψ : TR.Sm F a) (c : ℂ) (h : TR.IsAutForm φ) (h' : TR.IsAutForm ψ) :
    TR.IsAutForm (φ + c • ψ) := by
  refine ⟨fun γ x => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · change φ.1 _ + c * ψ.1 _ = φ.1 _ + c * ψ.1 _
    rw [h.left, h'.left]
  · rw [isOpen_iff_mem_nhds]
    intro k₀ hk₀
    have hO : IsOpen ((fun k => k₀⁻¹ * k) ⁻¹' ({k | TR.finRep F a k φ = φ} ∩ {k | TR.finRep F a k ψ = ψ})) :=
      (h.level.inter h'.level).preimage (continuous_const.mul continuous_id)
    refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
    · simp
    · rintro k ⟨h1, h2⟩
      have h1' : TR.finRep F a (k₀⁻¹ * k) φ = φ := h1
      have h2' : TR.finRep F a (k₀⁻¹ * k) ψ = ψ := h2
      have h3 : TR.finRep F a (k₀⁻¹ * k) (φ + c • ψ) = φ + c • ψ := by rw [map_add (f := _), map_smul, h1', h2']
      have h4 : TR.finRep F a k₀ (φ + c • ψ) = φ + c • ψ := hk₀
      change TR.finRep F a k (φ + c • ψ) = φ + c • ψ
      rw [← mul_inv_cancel_left k₀ k, finite_translation_mul, h3, h4]
  · have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun k => TR.cptRep F a k φ) ⊔
        Submodule.span ℂ (Set.range fun k => TR.cptRep F a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z ψ) '' TR.Zalg F a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩))
  · obtain ⟨C, N, hC⟩ := h.growth x
    obtain ⟨D, M, hD⟩ := h'.growth x
    refine ⟨|C| + ‖c‖ * |D|, N + M, fun y => ?_⟩
    have h1 : 1 ≤ TR.height y := by
      unfold TR.height
      have := norm_nonneg (TR.toL y.val)
      have := norm_nonneg (TR.toL (y⁻¹).val)
      linarith
    have bound : ∀ (B : ℝ) (n : ℕ), n ≤ N + M → B * TR.height y ^ n ≤ |B| * TR.height y ^ (N + M) := fun B n hn =>
      mul_le_mul (le_abs_self B) (pow_le_pow_right₀ h1 hn) (pow_nonneg (zero_le_one.trans h1) n) (abs_nonneg B)
    have b1 := (hC y).trans (bound C N (Nat.le_add_right _ _))
    have b2 := (hD y).trans (bound D M (Nat.le_add_left _ _))
    change ‖φ.1 _ + c * ψ.1 _‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, add_mul, mul_assoc]
    exact add_le_add b1 (mul_le_mul_of_nonneg_left b2 (norm_nonneg c))

end SlopeTestRemainingChoices

theorem UpperTheory.hecke_operators_commute_on_automorphic_forms :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), TR.IsAutForm (0 : TR.Sm F a) ∧ (∀ (φ : TR.Sm F a) (g : GL (Fin a) (Af F)), TR.IsAutForm φ → TR.IsAutForm (TR.finRep F a g φ)) ∧ ∀ (φ ψ : TR.Sm F a) (z : ℂ), TR.IsAutForm φ → TR.IsAutForm ψ → TR.IsAutForm (φ + z • ψ) := by
  intro F _ _ _ a
  exact ⟨TR.isAutForm_const (Submodule.zero_mem _), automorphic_form_translate, automorphic_form_linear_combination⟩
end

section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
  (μ : Measure G) [μ.IsHaarMeasure]

private theorem inner_eq_setIntegral_of_ae (w v : Lp ℂ 2 (quotientMeasure Γ μ)) {g : G → ℂ}
    (h : ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = g y) :
    inner ℂ w v = ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * g y ∂μ := by
  rw [L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h] with y hy
  rw [hy]
  simp [RCLike.inner_apply, mul_comm]

private theorem closed_stable [IsFiniteMeasure (quotientMeasure Γ μ)]
    (τ : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))) (hτ : IsClosed (τ : Set (Lp ℂ 2 (quotientMeasure Γ μ))))
    (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (lam : Measure U) [IsFiniteMeasure lam] (Ψ : U → G → ℂ)
    (hc : Continuous (fun p : U × G => Ψ p.1 p.2)) (hb : ∃ C : ℝ, ∀ u m, ‖Ψ u m‖ ≤ C)
    (hinv : ∀ u, ∀ γ ∈ Γ, ∀ m, Ψ u (γ * m) = Ψ u m)
    (hrep : ∀ u, ∃ v ∈ τ, ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = Ψ u y) :
    ∃ v ∈ τ, ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = ∫ u, Ψ u y ∂lam := by
  obtain ⟨C, hC⟩ := hb
  choose v hvτ hvr using hrep
  let Φ : G → ℂ := fun m => ∫ u, Ψ u m ∂lam
  have hΦc : Continuous Φ := by
    refine continuous_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const _) ?_
    · intro m
      exact (hc.comp (by fun_prop : Continuous fun u : U => (u, m))).aestronglyMeasurable
    · intro m
      exact Eventually.of_forall fun u => hC u m
    · exact Eventually.of_forall fun u => hc.comp (by fun_prop : Continuous fun m => (u, m))
  have hΦb : ∀ m, ‖Φ m‖ ≤ C * lam.real univ := fun m =>
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun u => hC u m)
  let f : RightCosetSpace Γ → ℂ := Quotient.lift Φ (by
    rintro a b ⟨γ, rfl⟩
    change Φ ((γ : G) * b) = Φ b
    simp only [Φ, hinv _ _ γ.2])
  have hfc : Continuous f :=
    (isOpenQuotientMap_mk Γ).isQuotientMap.continuous_iff.2 hΦc
  have hf2 : MemLp f 2 (quotientMeasure Γ μ) :=
    MemLp.of_bound hfc.aestronglyMeasurable (C * lam.real univ) (Eventually.of_forall fun q => by
      obtain ⟨y, rfl⟩ := mk_surjective Γ q
      exact hΦb y)
  have hrepΦ : ∀ᵐ y ∂μ, ((hf2.toLp f : Lp ℂ 2 (quotientMeasure Γ μ)) : RightCosetSpace Γ → ℂ) (mk Γ y) = Φ y := by
    have h := QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk Γ μ) (MemLp.coeFn_toLp hf2)
    filter_upwards [h] with y hy
    rw [hy]
    rfl
  refine ⟨hf2.toLp f, ?_, hrepΦ⟩
  haveI : CompleteSpace τ := hτ.completeSpace_coe
  rw [← Submodule.orthogonal_orthogonal τ, Submodule.mem_orthogonal]
  intro w hw
  rw [inner_eq_setIntegral_of_ae Γ μ w _ hrepΦ]
  have hw1 : Integrable (fun y => w (mk Γ y)) (μ.restrict (fundamentalDomain Γ)) := by
    have h1 : Integrable w (quotientMeasure Γ μ) :=
      (Lp.memLp w).integrable (by norm_num)
    exact Integrable.comp_measurable h1 (measurable_mk Γ)
  have hwm : StronglyMeasurable (fun y => w (mk Γ y)) := stronglyMeasurable_lift Γ μ w
  have hint : Integrable (Function.uncurry fun (u : U) (y : G) =>
      conj (w (mk Γ y)) * Ψ u y) (lam.prod (μ.restrict (fundamentalDomain Γ))) := by
    refine Integrable.mono' ((hw1.norm.mul_const C).comp_snd lam) ?_ ?_
    · have h1 : StronglyMeasurable (fun p : U × G => conj (w (mk Γ p.2))) :=
        continuous_star.comp_stronglyMeasurable (hwm.comp_measurable measurable_snd)
      exact h1.aestronglyMeasurable.mul hc.aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hC p.1 p.2) (norm_nonneg _)
  calc ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Φ y ∂μ
      = ∫ y in fundamentalDomain Γ, ∫ u, conj (w (mk Γ y)) * Ψ u y ∂lam ∂μ := by
        simp only [Φ, integral_const_mul]
    _ = ∫ u, ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Ψ u y ∂μ ∂lam :=
        (integral_integral_swap hint).symm
    _ = 0 := by
        have h0 : ∀ u, ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Ψ u y ∂μ = 0 := by
          intro u
          rw [← inner_eq_setIntegral_of_ae Γ μ w (v u) (hvr u)]
          exact Submodule.inner_left_of_mem_orthogonal (hvτ u) hw
        simp [h0]

end Gen

theorem UpperTheory.reps_integral_mem_closed_submodule :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)), IsClosed (τ : Set (L2 μ)) →
      ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (lam : Measure U) [IsFiniteMeasure lam] (Ψ : U → G1 K n → ℂ),
        Continuous (fun p : U × G1 K n => Ψ p.1 p.2) → (∃ C : ℝ, ∀ u m, ‖Ψ u m‖ ≤ C) → (∀ u, ∀ γ ∈ Gam K n, ∀ m, Ψ u (γ * m) = Ψ u m) → (∀ u, ∃ v ∈ τ, Reps μ v (Ψ u)) →
        ∃ v ∈ τ, Reps μ v fun m => ∫ u, Ψ u m ∂lam := by
  intro K _ _ n μ _ τ hτ U _ _ _ _ lam _ Ψ hc hb hinv hrep
  haveI : IsFiniteMeasure (quotientMeasure (Gam K n) μ) :=
    isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  exact closed_stable (Gam K n) μ τ hτ U lam Ψ hc hb hinv hrep
end
