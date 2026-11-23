module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle005
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle015
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle017
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramMinorSwapAdjacentColumns
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Topology.Algebra.Valued.NormedValued

@[expose] public section

section

open scoped ContDiff

namespace GlobalTheory


open MeasureTheory in
theorem exists_normalise_meanSquare_of_cocompact : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x : G, ∃ g ∈ Γ, g + x ∈ K) → ∀ f : G → ℂ, Continuous f → f ≠ 0 → (∀ g ∈ Γ, ∀ w, ‖f (g + w)‖ = ‖f w‖) → (∃ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1) ∧ ∃ c : ℂ, ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∫ w in 𝓕, ‖c * f w‖ ^ 2 ∂μ = 1 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov f hf hf0 hinv
  have : Countable Γ := countable_of_discrete_addSubgroup Γ
  obtain ⟨hex, h⟩ := meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov
  obtain ⟨N, hN⟩ := h f hf hinv
  refine ⟨hex, ?_⟩
  have hN0 : N ≠ 0 := by
    intro h0
    obtain ⟨μ, F, hμ, hF, h1⟩ := hex
    have h2 := (hN μ F hμ hF).2.2.1
    rw [h0, ENNReal.coe_zero, mul_zero] at h2
    have h3 : ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ = 0 := by
      rw [hF.lintegral_eq_tsum'']
      have e : ∀ (g : Γ) (x : G), ‖f (g +ᵥ x)‖ₑ = ‖f x‖ₑ := fun g x => by
        have := hinv g g.2 x
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← this]
        rfl
      simp only [e, h2, tsum_zero]
    rw [lintegral_eq_zero_iff (hf.enorm.measurable.pow_const 2)] at h3
    apply hf0
    rw [← hf.ae_eq_iff_eq μ continuous_zero]
    filter_upwards [h3] with w hw
    simpa using hw
  have hpos : (0 : ℝ) < N := by positivity
  refine ⟨((√(N : ℝ))⁻¹ : ℝ), fun μ F hμ hF h1 => ?_⟩
  have h2 := (hN μ F hμ hF).2.2.2
  rw [h1, ENNReal.toReal_one, one_mul] at h2
  simp only [norm_mul, mul_pow]
  rw [integral_const_mul, h2, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.InfAdeleMixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toMixed [_root_.NumberField.IsTotallyComplex E] {R : Type} [CommRing R]
    (θ : {w : InfinitePlace E // w.IsComplex} → (R →+* ℂ)) : R →+* mixedSpace E :=
  RingHom.prod
    (Pi.ringHom fun w : {w : InfinitePlace E // w.IsReal} =>
      (False.elim (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2) : R →+* ℝ))
    (Pi.ringHom θ)

theorem mixed_ext [_root_.NumberField.IsTotallyComplex E] {x y : mixedSpace E} (h : ∀ w, x.2 w = y.2 w) : x = y :=
  Prod.ext (funext fun w =>
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2).elim) (funext h)

theorem exists_place_over [_root_.NumberField.IsTotallyComplex E] [IsTotallyReal F] (v : InfinitePlace F) :
    ∃ w : {w : InfinitePlace E // w.IsComplex}, InfinitePlace.mk (w.1.embedding.comp (algebraMap F E)) = v := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  refine ⟨⟨w, IsTotallyComplex.isComplex w⟩, ?_⟩
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw

theorem exists_equiv_mixedSpace :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
      (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
      ∃ θ : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E,
        (∀ x : E, θ (1 ⊗ₜ[F] x) = mixedEmbedding E x) ∧
        @Continuous _ _ inferInstance
          (moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)) θ.symm ∧
        ∀ u : (mixedSpace E)ˣ, (∀ w, ((u : mixedSpace E).2 w).im = 0) →
          ∃ a : (InfiniteAdeleRing F)ˣ, θ ((a : InfiniteAdeleRing F) ⊗ₜ[F] 1) = u := by
  intro F E _ _ _ _ _ σ hF hE h2 hσ
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (InfiniteAdeleRing F ⊗[F] E) := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) _
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hθ := fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)
  obtain ⟨δ, hδ0, hcδ, hs⟩ := GlobalTheory.InfAdeleCM.exists_delta c h2 hc hc'
  have hre : ∀ τ : E →+* ℂ, (τ δ).re = 0 := by
    intro τ
    have := congrArg Complex.re (hc' τ δ)
    rw [hcδ, map_neg, Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0 := by
    intro τ h
    exact hδ0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))
  let r : ∀ v : InfinitePlace F, v.Completion ≃ᵢ ℝ := fun v =>
    InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hr : ∀ v x, r v x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x :=
    fun _ _ => rfl
  let p : {w : InfinitePlace E // w.IsComplex} → InfinitePlace F := fun w =>
    InfinitePlace.mk (w.1.embedding.comp (algebraMap F E))
  let Θ : InfiniteAdeleRing F ⊗[F] E →+* mixedSpace E := toMixed fun w => θ0 w.1.embedding
  have hΘ : ∀ z w, (Θ z).2 w = θ0 w.1.embedding z := fun _ _ => rfl
  have hval : ∀ (w) (a b : InfiniteAdeleRing F), (Θ (a ⊗ₜ 1 + b ⊗ₜ δ)).2 w =
      ⟨r _ (a (p w)), r _ (b (p w)) * (w.1.embedding δ).im⟩ := by
    intro w a b
    rw [hΘ, map_add (f := _), hθ, hθ, GlobalTheory.InfAdeleCM.ext_eq_ofReal, GlobalTheory.InfAdeleCM.ext_eq_ofReal, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, hr, p]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, hr, p]
  choose t ht using exists_place_over (F := F) (E := E)
  have ht' : ∀ v, p (t v) = v := ht
  have htp : ∀ w, t (p w) = w := by
    intro w
    apply Subtype.ext
    rw [← InfinitePlace.mk_embedding (t (p w)).1, ← InfinitePlace.mk_embedding w.1]
    rcases GlobalTheory.InfAdeleCM.eq_or_conj c hc' hδ0 hcδ hs _ _ (GlobalTheory.InfAdeleCM.mk_eq_iff (ht (p w))) with e | e
    · rw [e]
    · rw [e, InfinitePlace.mk_conjugate_eq]
  let A : (({w : InfinitePlace E // w.IsComplex}) → ℝ) → InfiniteAdeleRing F := fun y v => (r v).symm (y (t v))
  have hA : Continuous A := continuous_pi fun v => (r v).symm.continuous.comp (continuous_apply (t v))
  have hA' : ∀ y w, r _ (A y (p w)) = y w := by
    intro y w
    simp only [A, IsometryEquiv.apply_symm_apply, htp]
  let G : mixedSpace E → InfiniteAdeleRing F ⊗[F] E := fun z =>
    A (fun w => (z.2 w).re) ⊗ₜ[F] (1 : E) + A (fun w => (z.2 w).im / (w.1.embedding δ).im) ⊗ₜ[F] δ
  have hG : ∀ z, Θ (G z) = z := by
    intro z
    refine mixed_ext fun w => ?_
    rw [hval]
    refine Complex.ext (hA' (fun w => (z.2 w).re) w) ?_
    have h := hA' (fun w => (z.2 w).im / (w.1.embedding δ).im) w
    exact (congrArg (· * (w.1.embedding δ).im) h).trans (div_mul_cancel₀ _ (him _))
  have hinj : Function.Injective Θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, b, rfl⟩ := GlobalTheory.InfAdeleCM.exists_decomp hs z
    have key : ∀ v, a v = 0 ∧ b v = 0 := by
      intro v
      have h := hval (t v) a b
      rw [hz, ht' v] at h
      have h1 := congrArg Complex.re h
      have h3 := congrArg Complex.im h
      simp only [Prod.snd_zero, Pi.zero_apply, Complex.zero_re, Complex.zero_im] at h1 h3
      have z0 : r v 0 = 0 := by rw [hr, map_zero]
      exact ⟨(r v).injective (by rw [z0, ← h1]),
        (r v).injective (by rw [z0]; exact (mul_eq_zero.1 h3.symm).resolve_right (him _))⟩
    have ha : a = 0 := funext fun v => (key v).1
    have hb : b = 0 := funext fun v => (key v).2
    rw [ha, hb, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  let e : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E := RingEquiv.ofBijective Θ ⟨hinj, fun z => ⟨G z, hG z⟩⟩
  have he : ∀ z, e z = Θ z := fun _ => rfl
  have htm : ∀ x : E, Continuous fun a : InfiniteAdeleRing F => a ⊗ₜ[F] x := by
    intro x
    have : (fun a : InfiniteAdeleRing F => a ⊗ₜ[F] x) = fun a => a • ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x) := by
      funext a
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Continuous.fun_smul continuous_id' continuous_const
  refine ⟨e, fun x => mixed_ext fun w => ?_, ?_, fun u hu => ?_⟩
  · rw [he, hΘ, h0, mixedEmbedding_apply_isComplex]
  · have : (e.symm : mixedSpace E → _) = G := by
      funext z
      rw [RingEquiv.symm_apply_eq, he, hG]
    rw [this]
    have c1 : Continuous fun z : mixedSpace E => (fun w => (z.2 w).re) := by fun_prop
    have c2 : Continuous fun z : mixedSpace E => (fun w => (z.2 w).im / (w.1.embedding δ).im) := by fun_prop
    exact Continuous.fun_add ((htm 1).comp' (hA.comp' c1)) ((htm δ).comp' (hA.comp' c2))
  · have hne : ∀ w, ((u : mixedSpace E).2 w).re ≠ 0 := by
      intro w h
      have h1 : (u : mixedSpace E).2 w = 0 := Complex.ext h (hu w)
      have h3 := congrArg (fun z : mixedSpace E => z.2 w) u.mul_inv
      simp only [Prod.snd_mul, Pi.mul_apply, h1, zero_mul, Prod.snd_one, Pi.one_apply] at h3
      exact zero_ne_one h3
    have hunit : IsUnit (A fun w => ((u : mixedSpace E).2 w).re) := by
      refine Pi.isUnit_iff.2 fun v => IsUnit.mk0 _ fun h => hne (t v) ?_
      have h1 : (r v).symm ((u : mixedSpace E).2 (t v)).re = 0 := h
      have h3 := congrArg (r v) h1
      rwa [IsometryEquiv.apply_symm_apply, hr, map_zero] at h3
    refine ⟨hunit.unit, mixed_ext fun w => ?_⟩
    have h := hval w (A fun w => ((u : mixedSpace E).2 w).re) 0
    rw [TensorProduct.zero_tmul, add_zero] at h
    rw [IsUnit.unit_spec, he, h]
    refine Complex.ext (hA' (fun w => ((u : mixedSpace E).2 w).re) w) ?_
    have z0 : r (p w) ((0 : InfiniteAdeleRing F) (p w)) = 0 := by
      rw [hr]
      exact map_zero _
    rw [hu w]
    simp only [z0, zero_mul]

end GlobalTheory.InfAdeleMixed
end
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mul_pow_mem_nhds {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
    {p : ℕ} (hp : 0 < p) {y : K} (hy : y ≠ 0) :
    {a : K | a ≠ 0 ∧ ∃ r : K, a = y * r ^ p} ∈ nhds y := by
  have hd : HasStrictDerivAt (fun r : K => y * r ^ p) (y * ((p : K) * 1 ^ (p - 1))) 1 :=
    (hasStrictDerivAt_pow p (1 : K)).const_mul y
  have hne : y * ((p : K) * 1 ^ (p - 1)) ≠ 0 := by
    have : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
    simp [hy, this]
  have h := hd.map_nhds_eq hne
  simp only [one_pow, mul_one] at h
  have hpow : {a : K | ∃ r : K, a = y * r ^ p} ∈ nhds y := by
    rw [← h]
    exact Filter.mem_map.2 (Filter.Eventually.of_forall fun r => ⟨r, rfl⟩)
  filter_upwards [isOpen_ne.mem_nhds hy, hpow] with a ha hb
  exact ⟨ha, hb⟩

theorem exists_approx_mod_powers :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F), 0 < p → (∀ v, y v ≠ 0) → ∃ x : F, x ≠ 0 ∧ ∀ v ∈ S, ∃ r : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = y v * r ^ p := by
  intro p F _ _ S y hp hy
  let U : Set (((v : S) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) :=
    ⋂ v : S, {q | q.1 v ≠ 0 ∧ ∃ r : v.1.adicCompletion F, q.1 v = y v.1 * r ^ p}
  have hU : U ∈ nhds ((fun v : S => y v.1), (0 : (F →+* ℝ) → ℝ)) := by
    refine Filter.iInter_mem.2 fun v => ?_
    have hc : Continuous fun q : ((v : S) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ) => q.1 v :=
      (continuous_apply v).comp continuous_fst
    have : CharZero (v.1.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.1.adicCompletion F)).injective
    letI : NontriviallyNormedField (v.1.adicCompletion F) :=
      Valued.toNontriviallyNormedField (v.1.adicCompletion F) ℤᵐ⁰
    exact hc.continuousAt.preimage_mem_nhds
      (mul_pow_mem_nhds (K := v.1.adicCompletion F) hp (hy v.1))
  obtain ⟨x, hx⟩ := (GlobalTheory.LocalQuad.denseRange_finite_real F S).mem_nhds hU
  have h1 : ∀ v : S, algebraMap F (v.1.adicCompletion F) x ≠ 0 ∧
      ∃ r : v.1.adicCompletion F, algebraMap F (v.1.adicCompletion F) x = y v.1 * r ^ p :=
    fun v => Set.mem_iInter.1 hx v
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨1, one_ne_zero, fun v hv => absurd (map_zero _) (h1 ⟨v, hv⟩).1⟩
  · exact ⟨x, hx0, fun v hv => (h1 ⟨v, hv⟩).2⟩

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem norm_coeff_minpoly_le_one_of_norm_le_one (K : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) (h : ‖Algebra.norm K x‖ ≤ 1) (n : ℕ) :
    ‖(minpoly K x).coeff n‖ ≤ 1 := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖(minpoly K x).coeff 0‖ ≤ 1 := by
    rw [Algebra.norm_eq_norm_adjoin K x, ← IntermediateField.adjoin.powerBasis_gen hx,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
      IntermediateField.minpoly_gen, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Module.finrank_pos).ne').1 h
  have h1 : spectralNorm K L x ≤ 1 := by
    rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L x]
    exact Real.rpow_le_one (norm_nonneg _) h0 (by positivity)
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h1
  exact h1 n

theorem isIntegral_iff_valued_norm_le_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (L : Type) [Field L] [Algebra (v.adicCompletion F) L]
    [FiniteDimensional (v.adicCompletion F) L] [Algebra (v.adicCompletionIntegers F) L]
    [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) L] (x : L) :
    IsIntegral (v.adicCompletionIntegers F) x ↔
      Valued.v (Algebra.norm (v.adicCompletion F) x) ≤ 1 := by
  constructor
  · intro h
    have h1 : IsIntegral (v.adicCompletionIntegers F) (Algebra.norm (v.adicCompletion F) x) :=
      Algebra.isIntegral_norm (v.adicCompletion F) h
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := v.adicCompletion F)).1 h1
    rw [← hy]
    exact y.2
  · intro h
    letI : NontriviallyNormedField (v.adicCompletion F) :=
      Valued.toNontriviallyNormedField (v.adicCompletion F) ℤᵐ⁰
    haveI : IsUltrametricDist (v.adicCompletion F) :=
      inferInstanceAs (@IsUltrametricDist (v.adicCompletion F)
        (Valued.toNormedField (v.adicCompletion F) ℤᵐ⁰).toDist)
    have hc : ∀ n, Valued.v ((minpoly (v.adicCompletion F) x).coeff n) ≤ 1 := fun n =>
      Valued.toNormedField.norm_le_one_iff.1
        (norm_coeff_minpoly_le_one_of_norm_le_one (v.adicCompletion F) L x
          (Valued.toNormedField.norm_le_one_iff.2 h) n)
    have hx : IsIntegral (v.adicCompletion F) x := Algebra.IsIntegral.isIntegral x
    have hl : minpoly (v.adicCompletion F) x ∈
        Polynomial.lifts (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (v.adicCompletion F), hq,
      minpoly.aeval]

end GlobalTheory.CNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed :
    ∀ z : ℂ, (∀ σ : ℂ ≃+* ℂ, σ z = z) → ∃ q : ℚ, z = q := by
  intro z hz
  by_contra h
  push_neg at h
  by_cases ha : IsAlgebraic ℚ z
  · obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.ClassFin.exists_ringEquiv_apply_ne_of_isAlgebraic z ha h
    exact hσ (hz σ)
  · obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.ClassFin.exists_ringEquiv_ne_of_transcendental z ha
    exact hσ (hz σ)

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isNilpotent_tmul_sub_tmul_of_const_on_fibres' : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A] [Algebra.FiniteType ℂ A] (f : A), (∀ χ χ' : A →ₐ[ℂ] ℂ, (∀ b : B, χ (algebraMap B A b) = χ' (algebraMap B A b)) → χ f = χ' f) → IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f) := by
  first | exact @GlobalTheory.ClassFin.isNilpotent_tmul_sub_tmul_of_const_on_fibres | exact GlobalTheory.ClassFin.isNilpotent_tmul_sub_tmul_of_const_on_fibres | (intros; apply GlobalTheory.ClassFin.isNilpotent_tmul_sub_tmul_of_const_on_fibres <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.unipotent_upper_size_reduction : ∀ (N : ℕ) (n : Matrix (Fin N) (Fin N) ℝ), (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → ∃ ν : Matrix (Fin N) (Fin N) ℤ, (∀ i, ν i i = 1) ∧ (∀ i j, j < i → ν i j = 0) ∧ ∀ i j, i < j → |(n * ν.map (Int.cast : ℤ → ℝ)) i j| ≤ 1 / 2 := by
  first | exact @GlobalTheory.ClassFin.unipotent_size_reduction | exact GlobalTheory.ClassFin.unipotent_size_reduction | (intros; apply GlobalTheory.ClassFin.unipotent_size_reduction <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.gram_leading_minor_lower_bound_integral : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ γ : Matrix (Fin N) (Fin N) ℤ, γ.det ≠ 0 → ∀ (j : ℕ) (h : j ≤ N), c ≤ (((g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ))).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  first | exact @GlobalTheory.ClassFin.gram_leading_minor_lower_bound | exact GlobalTheory.ClassFin.gram_leading_minor_lower_bound | (intros; apply GlobalTheory.ClassFin.gram_leading_minor_lower_bound <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.det_leading_minor_gram_iwasawa : ∀ (N : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 → (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → ∀ (j : ℕ) (h : j ≤ N), (((k * diagonal a * n)ᵀ * (k * diagonal a * n)).submatrix (Fin.castLE h) (Fin.castLE h)).det = ∏ i : Fin j, a (Fin.castLE h i) ^ 2 := by
  first | exact @GlobalTheory.ClassFin.det_leading_gram_iwasawa | exact GlobalTheory.ClassFin.det_leading_gram_iwasawa | (intros; apply GlobalTheory.ClassFin.det_leading_gram_iwasawa <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.iwasawa_decomposition_real_matrix : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ g = k * diagonal a * n := by
  first | exact @GlobalTheory.ClassFin.iwasawa_real | exact GlobalTheory.ClassFin.iwasawa_real | (intros; apply GlobalTheory.ClassFin.iwasawa_real <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.gram_minor_swap_adjacent_columns : ∀ (N : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n g g' : Matrix (Fin N) (Fin N) ℝ) (p q : Fin N), kᵀ * k = 1 → (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (q : ℕ) = p + 1 → g = k * diagonal a * n → g' = g.submatrix id (Equiv.swap p q) → (∀ (j : ℕ) (h : j ≤ N), j ≠ q → ((g'ᵀ * g').submatrix (Fin.castLE h) (Fin.castLE h)).det = ((gᵀ * g).submatrix (Fin.castLE h) (Fin.castLE h)).det) ∧ ∀ h : (q : ℕ) ≤ N, ((g'ᵀ * g').submatrix (Fin.castLE h) (Fin.castLE h)).det = (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := by
  first | exact @GlobalTheory.ClassFin.gram_minor_swap_columns | exact GlobalTheory.ClassFin.gram_minor_swap_columns | (intros; apply GlobalTheory.ClassFin.gram_minor_swap_columns <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.two_pow_card_le_index_iInf_of_independent : ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 → 2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  first | exact @GlobalTheory.QNorm.two_pow_card_le_index_iInf | exact GlobalTheory.QNorm.two_pow_card_le_index_iInf | (intros; apply GlobalTheory.QNorm.two_pow_card_le_index_iInf <;> assumption)
end
