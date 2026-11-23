module

public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpanGenerators
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle040
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle015
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import Formalism.RealPlaceAnalysis.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

@[expose] public section

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.SpanGenerators : SpanG := by
  first | exact @GlobalTheory.CompanionTheory.BmuSpan.spanG | exact GlobalTheory.CompanionTheory.BmuSpan.spanG | (intros; apply GlobalTheory.CompanionTheory.BmuSpan.spanG <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.EulerPos

theorem ofReal_re_prod {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (h : ∀ i, 0 ≤ (z i).re ∧ (z i).im = 0) :
    ENNReal.ofReal (∏ i ∈ s, z i).re = ∏ i ∈ s, ENNReal.ofReal (z i).re := by
  have e : ∏ i ∈ s, z i = ((∏ i ∈ s, (z i).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun i _ => Complex.ext (by simp) (by simp [(h i).2])
  rw [e, Complex.ofReal_re, ENNReal.ofReal_prod_of_nonneg fun i _ => (h i).1]

theorem hasProd_ofReal {ι : Type*} {a : ι → ℝ} {p : ℝ} (hp : HasProd a p) (h0 : ∀ i, 0 ≤ a i) :
    HasProd (fun i => ENNReal.ofReal (a i)) (ENNReal.ofReal p) := by
  have h := (ENNReal.continuous_ofReal.tendsto p).comp hp
  refine h.congr fun s => ?_
  simp only [Function.comp_apply]
  exact ENNReal.ofReal_prod_of_nonneg fun i _ => h0 i

theorem hasProd_of_tail {ι : Type} (L : ι → ℝ≥0∞) (a : ι → ℝ) (S : Finset ι) (hL : ∀ v, L v ≠ ⊤)
    (ha0 : ∀ v, 0 ≤ a v) (hoff : ∀ v, v ∉ S → L v = ENNReal.ofReal (a v))
    (hsum : Summable fun v => |a v - 1|) :
    HasProd L ((∏ v ∈ S, L v) * ENNReal.ofReal (∏' v : {v // v ∉ S}, a v.1)) := by
  classical
  let r : ι → ℝ := fun v => (L v).toReal
  have hr0 : ∀ v, 0 ≤ r v := fun v => ENNReal.toReal_nonneg
  have hLr : ∀ v, ENNReal.ofReal (r v) = L v := fun v => ENNReal.ofReal_toReal (hL v)
  have hra : ∀ v, v ∉ S → r v = a v := fun v hv => by
    simp only [r]
    rw [hoff v hv, ENNReal.toReal_ofReal (ha0 v)]
  have hsr : Summable fun v => |r v - 1| := by
    refine hsum.congr_cofinite ?_
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
    rw [hra v (by simpa using hv)]
  obtain ⟨hm, hsplit, -, -⟩ := AbsTprod.abs_tprod ι r hsr
  obtain ⟨-, htp⟩ := hsplit S
  have hT : ∏' v : {v // v ∉ S}, r v.1 = ∏' v : {v // v ∉ S}, a v.1 :=
    tprod_congr fun v => hra v.1 v.2
  have hp := hasProd_ofReal hm.hasProd hr0
  have e : (fun i => ENNReal.ofReal (r i)) = L := funext hLr
  rw [e, htp, hT, ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hr0 v),
    ENNReal.ofReal_prod_of_nonneg fun v _ => hr0 v] at hp
  simpa only [hLr] using hp

theorem finprod_eq_indicator {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d n M : ℕ}
    (b : Module.Basis (Fin d) F E)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v, v ∉ S → Φv v = (latV b v).indicator 1)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    ∏ᶠ v, Φv v (projV v (projFin X)) =
      (intOff b S).indicator (fun Y => ∏ v ∈ S, Φv v (projV v (projFin Y))) X := by
  classical
  by_cases hX : X ∈ intOff b S
  · rw [Set.indicator_of_mem hX]
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro v hv
    by_contra hvS
    apply hv
    have hvS' : v ∉ S := by simpa using hvS
    simp only [hS v hvS']
    exact Set.indicator_of_mem (hX v hvS') _
  · rw [Set.indicator_of_notMem hX]
    have : ∃ v, v ∉ S ∧ projV v (projFin X) ∉ latV b v := by
      by_contra hne
      push Not at hne
      exact hX hne
    obtain ⟨v, hvS, hv⟩ := this
    refine finprod_eq_zero _ v ?_ ?_
    · simp only [hS v hvS]
      exact Set.indicator_of_notMem hv _
    · have hfin : {w | projV w (projFin X) ∉ latV b w}.Finite :=
        Filter.eventually_cofinite.1 (MeasProj.eventually_mem_latV b (projFin X))
      refine (hfin.union S.finite_toSet).subset ?_
      intro w hw
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
      apply hw
      simp only [hS w hc.2]
      exact Set.indicator_of_mem hc.1 _

end GlobalTheory.CompanionTheory.SW.EulerPos

theorem GlobalTheory.CompanionTheory.SW.EulerPos.euler_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → (∀ v, IsLocallyFiniteMeasure (m v)) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → ∀ (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Measurable Φi → IsPureFin b Φf Φv → (∀ v Y, 0 ≤ (Φv v Y).re ∧ (Φv v Y).im = 0) → (∀ X, Φ X = Φi (projInf X) * ENNReal.ofReal (Φf (projFin X)).re) → Measurable Φ ∧ Multipliable (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(c v • m v)) ∧ ∫⁻ X, Φ X ∂I = (∫⁻ X, Φi X ∂(cinf • minf)) * ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(c v • m v) := by
  intro F E _ _ _ _ _ σ hCM d b n M I minf m hEu hm cinf c hc Φ Φi Φf Φv hΦi hpure hpos hprod
  classical
  obtain ⟨hpi, hpf, hpv, hlat, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM d b n M
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_af F E σ hCM n M
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_ainf F E σ hCM n M
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun v => GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hCM n M v
  obtain ⟨hfin, hsum, S₀, hEP⟩ := hEu
  obtain ⟨-, -, -, -, -, -, -, S₁, hS₁⟩ := GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F cinf cinf c c hc hc
  let S : Finset (HeightOneSpectrum (𝓞 F)) :=
    (S₀ ∪ S₁) ∪ (Filter.eventually_cofinite.1 hpure.2.1).toFinset
  have hS : ∀ v, v ∉ S → Φv v = (latV b v).indicator 1 := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_right _ (by simpa using h))
  have hS₀ : S₀ ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hS₁S : S₁ ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  obtain ⟨hc1, hcS⟩ := hS₁ S hS₁S
  let φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞ :=
    fun v X => ENNReal.ofReal (Φv v X).re
  have hcv : ∀ v, Continuous (Φv v) := fun v => (hpure.1 v).1.continuous
  have hφ : ∀ v, Measurable (φ v) := fun v =>
    ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp (hcv v).measurable)
  have hΦ : Φ = pureL b S Φi φ := by
    funext X
    rw [hprod X, hpure.2.2 (projFin X), GlobalTheory.CompanionTheory.SW.EulerPos.finprod_eq_indicator b Φv S hS X]
    unfold pureL
    by_cases hX : X ∈ intOff b S
    · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX,
        GlobalTheory.CompanionTheory.SW.EulerPos.ofReal_re_prod S _ fun v => hpos v _]
    · simp [Set.indicator_of_notMem hX]
  have hBfin : ∀ v, ∫⁻ X, φ v X ∂(m v) ≠ ⊤ := by
    intro v
    haveI := hm v
    have hi : Integrable (Φv v) (m v) :=
      (hcv v).integrable_of_hasCompactSupport (hpure.1 v).2
    exact hi.re.lintegral_lt_top.ne
  have hLB : ∀ v, ∫⁻ X, φ v X ∂(c v • m v) = (c v : ℝ≥0∞) * ∫⁻ X, φ v X ∂(m v) := by
    intro v
    rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have hLfin : ∀ v, ∫⁻ X, φ v X ∂(c v • m v) ≠ ⊤ := fun v => by
    rw [hLB v]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (hBfin v)
  let a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (m v (latV b v)).toReal
  have hoff : ∀ v, v ∉ S → ∫⁻ X, φ v X ∂(c v • m v) = ENNReal.ofReal (a v) := by
    intro v hv
    have hl : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
      (hlat v).2.measurableSet
    have hφv : φ v = (latV b v).indicator 1 := by
      funext X
      simp only [φ, hS v hv]
      by_cases hX : X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))
      · simp [Set.indicator_of_mem hX]
      · simp [Set.indicator_of_notMem hX]
    rw [hLB v, hc1 v hv, hφv, lintegral_indicator_one hl]
    simp only [ENNReal.coe_one, one_mul, a]
    exact (ENNReal.ofReal_toReal (hfin v).ne).symm
  have hHP := GlobalTheory.CompanionTheory.SW.EulerPos.hasProd_of_tail (fun v => ∫⁻ X, φ v X ∂(c v • m v)) a S hLfin
    (fun _ => ENNReal.toReal_nonneg) hoff hsum
  refine ⟨?_, hHP.multipliable, ?_⟩
  · rw [hΦ]
    exact GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL F E σ hCM d b n M S Φi φ hΦi hφ
  · change ∫⁻ X, Φ X ∂I = (∫⁻ X, Φi X ∂(cinf • minf)) * ∏' v, ∫⁻ X, φ v X ∂(c v • m v)
    have h1 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by exact_mod_cast hcS
    rw [hHP.tprod_eq, hΦ, hEP S hS₀ Φi φ hΦi hφ, lintegral_smul_measure, ENNReal.smul_def,
      smul_eq_mul, Finset.prod_congr rfl fun v _ => hLB v, Finset.prod_mul_distrib]
    calc _ = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) * ((∫⁻ X, Φi X ∂minf) *
            (∏ v ∈ S, ∫⁻ X, φ v X ∂(m v)) *
            ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal)) := by
          rw [h1]; simp
      _ = _ := by ring
end
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.CompanionTheory.Unitarize

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {X : Type*} [AddCommGroup X] [Module ℂ X]

theorem injective_of_simple {M : Type*} [AddCommGroup M] [Module ℂ M]
    {E : Fin n → Fin n → Module.End ℂ X} {F : Fin n → Fin n → Module.End ℂ M}
    (hS : ∀ W : Submodule ℂ X, (∀ a b, ∀ x ∈ W, E a b x ∈ W) → W = ⊥ ∨ W = ⊤)
    (c : X →ₗ[ℂ] M) (hc : ∀ a b x, c (E a b x) = F a b (c x)) (h0 : c ≠ 0) :
    Function.Injective c := by
  have hst : ∀ a b, ∀ x ∈ LinearMap.ker c, E a b x ∈ LinearMap.ker c := by
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hc, hx, map_zero]
  rcases hS _ hst with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

theorem adjSign_eq_sgn (ε : Fin n → Bool) (a b : Fin n) :
    adjSign ε a b = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) := by
  unfold adjSign Formalism.REAL.sgn
  split_ifs <;> simp

theorem exists_unitary_image {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {E : Fin n → Fin n → Module.End ℂ X}
    (hS : ∀ W : Submodule ℂ X, (∀ a b, ∀ x ∈ W, E a b x ∈ W) → W = ⊥ ∨ W = ⊤)
    (c : X →ₗ[ℂ] smD ε σ) (hc : ∀ a b x, c (E a b x) = smE ε σ a b (c x)) (h0 : c ≠ 0) :
    ∃ (V : Submodule ℂ H) (E' : Fin n → Fin n → Module.End ℂ V) (e : X ≃ₗ[ℂ] V),
      (∀ x, ((e x : V) : H) = ((c x : smD ε σ) : H)) ∧
      Formalism.REAL.GlRel E' ∧ Formalism.REAL.IsUnitary ε E' ∧
      ∀ a b x, e (E a b x) = E' a b (e x) := by
  have hinj : Function.Injective c := injective_of_simple hS c hc h0
  set d : X →ₗ[ℂ] H := (smD ε σ).subtype ∘ₗ c with hd
  have hdinj : Function.Injective d := Subtype.val_injective.comp hinj
  let e : X ≃ₗ[ℂ] LinearMap.range d := LinearEquiv.ofInjective d hdinj
  have he : ∀ x, ((e x : LinearMap.range d) : H) = ((c x : smD ε σ) : H) := fun x => rfl
  let E' : Fin n → Fin n → Module.End ℂ (LinearMap.range d) := fun a b =>
    e.toLinearMap ∘ₗ E a b ∘ₗ e.symm.toLinearMap
  have hE' : ∀ a b x, E' a b (e x) = e (E a b x) := by
    intro a b x
    simp [E']
  have hcoe : ∀ a b x, ((E' a b (e x) : LinearMap.range d) : H) =
      ((smE ε σ a b (c x) : smD ε σ) : H) := by
    intro a b x
    rw [hE', he, hc]
  have hgl : IsGlRep (smE ε σ) := (isDerivedOn_smE hσ).glRep
  have hU : IsInfUnitary ε (smE ε σ) := isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)
  refine ⟨LinearMap.range d, E', e, he, ?_, ?_, fun a b x => (hE' a b x).symm⟩
  · intro a b c' d'
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    have h := LinearMap.congr_fun (hgl a b c' d') (c x)
    have h' := congrArg (Subtype.val) h
    apply Subtype.ext
    have hEE : ∀ a b c' d', ((E' a b (E' c' d' (e x)) : LinearMap.range d) : H) =
        ((smE ε σ a b (smE ε σ c' d' (c x)) : smD ε σ) : H) := by
      intro a b c' d'
      rw [hE', hcoe, hc]
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Submodule.coe_sub] at h' ⊢
    rw [hEE, hEE, h']
    split_ifs <;> simp [hcoe]
  · intro a b y z
    obtain ⟨u, rfl⟩ := e.surjective y
    obtain ⟨v, rfl⟩ := e.surjective z
    have h := hU a b (c u) (c v)
    rw [← adjSign_eq_sgn]
    rw [Submodule.coe_inner, Submodule.coe_inner, hcoe, hcoe, he, he]
    simpa [Submodule.coe_inner] using h

end GlobalTheory.CompanionTheory.Unitarize
end
end
