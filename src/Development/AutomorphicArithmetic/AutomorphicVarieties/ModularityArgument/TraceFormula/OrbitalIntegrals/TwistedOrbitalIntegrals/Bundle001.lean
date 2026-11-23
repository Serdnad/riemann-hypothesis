module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
import Aesop.Main
import GroundTheory.LocalFields.Integers
public import GroundTheory.LocalFields.Uniqueness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open MeasureTheory PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.quotFubini :
    UpperTheory.V.Z.Tf.Orb.QuotMass → UpperTheory.V.Z.Tf.Orb.QuotFubini := by
  intro hM G _ _ _ _ _ _ _ _ μG hμG H hH μ hμ hinv F hF hFH hsupp
  obtain ⟨Y, C, hY, hC, hsupp⟩ := hsupp
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  swap
  · simp only [quotIntegral, dif_neg hex, integral_zero]
  simp only [quotIntegral, dif_pos hex]
  have hρ := hex.choose_spec
  generalize hex.choose = ρ at hρ ⊢
  obtain ⟨hS, hfin⟩ := (hM G μG hμG H hH μ hμ hinv ρ hρ).2 C hC
  set S : Set G := {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} with hSdef
  obtain ⟨M, hMb⟩ := (hY.prod hC).exists_bound_of_continuousOn hF.continuousOn
  have h1 : Integrable (S.indicator fun g => (ρ g).toReal) μG := by
    rw [integrable_indicator_iff hS.measurableSet]
    exact integrable_toReal_of_lintegral_ne_top hρ.1.aemeasurable hfin
  have h2 : Integrable (Y.indicator fun _ => M) μG := by
    rw [integrable_indicator_iff hY.isClosed.measurableSet]
    exact integrableOn_const hY.measure_lt_top.ne
  have hint : Integrable (Function.uncurry fun g y => F y g * ((ρ g).toReal : ℂ)) (μG.prod μG) := by
    refine (h1.mul_prod h2).mono' ?_ (Filter.Eventually.of_forall ?_)
    · have a1 : Measurable fun p : G × G => F p.2 p.1 :=
        (hF.comp continuous_swap).measurable
      have a2 : Measurable fun p : G × G => ((ρ p.1).toReal : ℂ) :=
        Complex.measurable_ofReal.comp ((hρ.1.comp measurable_fst).ennreal_toReal)
      exact (a1.mul a2).aestronglyMeasurable
    · rintro ⟨g, y⟩
      show ‖F y g * ((ρ g).toReal : ℂ)‖ ≤ S.indicator (fun g => (ρ g).toReal) g * Y.indicator (fun _ => M) y
      by_cases h0 : F y g = 0
      · rw [h0, zero_mul, norm_zero]
        by_cases hg : g ∈ S
        · by_cases hy : y ∈ Y
          · obtain ⟨h, -, c, hc, -⟩ := hg
            have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMb (y, c) ⟨hy, hc⟩)
            exact mul_nonneg (Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) _)
              (Set.indicator_nonneg (fun _ _ => hM0) _)
          · rw [Set.indicator_of_notMem hy, mul_zero]
        · rw [Set.indicator_of_notMem hg, zero_mul]
      · obtain ⟨hy, hg⟩ := hsupp y g h0
        have hg' : g ∈ S := hg
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hg', norm_mul, Complex.norm_real,
          Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_comm]
        obtain ⟨h, hh, c, hc, rfl⟩ := hg
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        rw [hFH y h hh c]
        exact hMb (y, c) ⟨hy, hc⟩
  rw [← integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  exact (integral_mul_const _ _).symm
end

section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.extCont :
    UpperTheory.V.Z.Tf.Orb.ExtCont := by
  intro k _ _ _ _ E _ _ _ _ _ _ _
  let _ := GroundTheory.LocalField.nontriviallyNormedField k
  have := GroundTheory.LocalField.completeSpace_nontriviallyNormedField k
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  have h1 : Continuous (algebraMap k E) := (Algebra.linearMap k E).continuous_of_finiteDimensional
  have h2 : ∀ σ : E ≃ₐ[k] E, Continuous σ := fun σ => σ.toLinearMap.continuous_of_finiteDimensional
  refine ⟨h1, h2, fun n => ⟨?_, fun σ => ?_⟩⟩
  · exact Continuous.units_map ((algebraMap k E).mapMatrix (m := Fin n)).toMonoidHom (continuous_id.matrix_map h1)
  · exact Continuous.units_map ((σ.toAlgHom.toRingHom).mapMatrix (m := Fin n)).toMonoidHom (continuous_id.matrix_map (h2 σ))
end

section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotPos :
    UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotInt → UpperTheory.V.Z.Tf.Orb.QuotMass → UpperTheory.V.Z.Tf.Orb.QuotPos := by
  intro _ hInt hMass G _ _ _ _ _ _ _ _ μG hμG H hH μ hμ hinv hex F hF hFH hC hnn hne
  have hρ := hex.choose_spec
  rw [quotIntegral, dite_eq_left hex]
  generalize hex.choose = ρ at hρ
  have hI := hInt G μG hμG H hH μ hμ hinv F hF hFH hC ρ hρ
  have hfin := (hMass G μG hμG H hH μ hμ hinv ρ hρ).1
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : SFinite μ := inferInstance
  have hre : (∫ g, F g * ((ρ g).toReal : ℂ) ∂μG).re = ∫ g, (F g).re * (ρ g).toReal ∂μG := by
    have := integral_re hI
    simpa using this.symm
  have hI' : Integrable (fun g => (F g).re * (ρ g).toReal) μG := by
    simpa using hI.re
  rw [hre]
  have h0 : 0 ≤ fun g => (F g).re * (ρ g).toReal := fun g => mul_nonneg (hnn g) ENNReal.toReal_nonneg
  refine lt_of_le_of_ne (integral_nonneg h0) fun hz => ?_
  have hae := (integral_eq_zero_iff_of_nonneg h0 hI').1 hz.symm
  set Φ : G → ℝ≥0∞ := fun g => ENNReal.ofReal (F g).re with hΦ
  have hΦc : Continuous Φ := ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp hF)
  have hΦm : Measurable Φ := hΦc.measurable
  have h1 : ∫⁻ g, Φ g * ρ g ∂μG = 0 := by
    refine (lintegral_eq_zero_iff (f := fun g => Φ g * ρ g) (hΦm.mul hρ.1)).2 ?_
    filter_upwards [hae, hfin] with g hg hg'
    simp only [Pi.zero_apply, mul_eq_zero, ENNReal.toReal_eq_zero_iff] at hg ⊢
    rcases hg with hg | hg | hg
    · left; simp [hΦ, hg]
    · right; exact hg
    · exact absurd hg hg'
  have hmul : Measurable fun p : G × H => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have h2 : ∫⁻ g, Φ g ∂μG = 0 := by
    calc ∫⁻ g, Φ g ∂μG = ∫⁻ g, ∫⁻ h : H, Φ g * ρ ((h : G) * g) ∂μ ∂μG := by
          refine lintegral_congr fun g => ?_
          rw [lintegral_const_mul, hρ.2 g, mul_one]
          exact hρ.1.comp (measurable_subtype_coe.mul_const g)
      _ = ∫⁻ h : H, ∫⁻ g, Φ g * ρ ((h : G) * g) ∂μG ∂μ :=
          lintegral_lintegral_swap ((hΦm.comp measurable_fst).mul (hρ.1.comp hmul)).aemeasurable
      _ = ∫⁻ _h : H, 0 ∂μ := by
          refine lintegral_congr fun h => ?_
          rw [← h1, ← lintegral_mul_left_eq_self (fun g => Φ g * ρ g) (h : G)]
          refine lintegral_congr fun g => ?_
          simp only [hΦ, hFH _ h.2]
      _ = 0 := lintegral_zero
  rw [lintegral_eq_zero_iff hΦm] at h2
  have h3 : Φ = 0 := (Continuous.ae_eq_iff_eq μG hΦc continuous_zero).1 h2
  obtain ⟨g, hg⟩ := hne
  have h4 := congrFun h3 g
  simp only [hΦ, Pi.zero_apply, ENNReal.ofReal_eq_zero] at h4
  exact hg (le_antisymm h4 (hnn g))
end

section

noncomputable section

open MeasureTheory Topology

namespace UpperTheory.V.Z.Tf.Orb

theorem finPres : FinPres := by
  intro G _ _ _ _ _ _ _ _ μ hμ θ hθ l hl hθl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  have hpow : ∀ j : ℕ, Continuous (θ ^ j : Monoid.End G) := by
    intro j
    induction j with
    | zero => exact continuous_id
    | succ j ih =>
      rw [pow_succ]
      exact ih.comp hθ
  have h1 : ∀ x, (θ ^ m : Monoid.End G) (θ x) = x := fun x => by
    have : (θ ^ (m + 1) : Monoid.End G) x = x := by rw [hθl]; rfl
    rw [pow_succ] at this
    exact this
  have h2 : ∀ x, θ ((θ ^ m : Monoid.End G) x) = x := fun x => by
    have : (θ ^ (m + 1) : Monoid.End G) x = x := by rw [hθl]; rfl
    rw [pow_succ'] at this
    exact this
  let e : G ≃* G :=
    { toFun := θ, invFun := (θ ^ m : Monoid.End G), left_inv := h1, right_inv := h2,
      map_mul' := map_mul θ }
  have hν : (Measure.map θ μ).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e hθ (hpow m)
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map θ μ = c • μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (Measure.map θ μ) μ⟩
  have hj : ∀ j : ℕ, Measure.map (θ ^ j : Monoid.End G) μ = c ^ j • μ := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_zero, one_smul]
      exact Measure.map_id
    | succ j ih =>
      have hcomp : ((θ ^ (j + 1) : Monoid.End G) : G → G) = (θ ^ j : Monoid.End G) ∘ θ := by
        rw [pow_succ]; rfl
      rw [hcomp, ← Measure.map_map (hpow j).measurable hθ.measurable, hc, Measure.map_smul c (hpow j).aemeasurable, ih,
        smul_smul, pow_succ']
  have hfin : c ^ (m + 1) • μ = μ := by
    rw [← hj, hθl]
    exact Measure.map_id
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hK0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hKt : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hc1 : c ^ (m + 1) = 1 := by
    have h := congrArg (fun ν : Measure G => ν K) hfin
    simp only [Measure.coe_nnreal_smul_apply] at h
    have h' : ((c ^ (m + 1) : NNReal) : ENNReal) * μ K = 1 * μ K := by rw [one_mul]; exact h
    exact_mod_cast (ENNReal.mul_left_inj hK0 hKt).mp h'
  have hc2 : c = 1 := (pow_eq_one_iff_of_nonneg (by positivity) (Nat.succ_ne_zero m)).mp hc1
  refine ⟨hθ.measurable, ?_⟩
  rw [hc, hc2, one_smul]

end UpperTheory.V.Z.Tf.Orb
end
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.orbComm :
    UpperTheory.V.Z.Tf.Orb.TwOrbComm → UpperTheory.V.Z.Tf.Orb.Untwist → UpperTheory.V.Z.Tf.Orb.OrbComm := by
  intro hT hU k _ _ _ _ _ n _ _ μk hμk γ hγ μ hμ f f' p1 p2 p3 p4
  haveI : ValuativeExtension k k := ⟨fun {_ _} => Iff.rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := hU k n μk γ
  obtain ⟨μ', a, b, c⟩ := h3 μ hμ
  have t := hT k k 1 h0 n μk hμk γ (h2 hγ) μ' a f f' p1 p2 p3 p4 fun x => by rw [h1]
  simpa only [c] using t
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.orbLin :
    UpperTheory.V.Z.Tf.Orb.TwOrbLin → UpperTheory.V.Z.Tf.Orb.Untwist → UpperTheory.V.Z.Tf.Orb.OrbLin := by
  intro hT hU k _ _ _ _ _ n _ _ μk hμk γ hγ μ hμ
  haveI : ValuativeExtension k k := ⟨fun {_ _} => Iff.rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := hU k n μk γ
  obtain ⟨μ', a, b, c⟩ := h3 μ hμ
  have t := hT k k 1 h0 n μk hμk γ (h2 hγ) μ' a
  simpa only [c] using t
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem aux {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μG : Measure G) (H H' : Subgroup G) (e : H' = H)
    (μ : Measure H) (hμ : μ.IsHaarMeasure) : ∃ μ' : Measure H', μ'.IsHaarMeasure ∧
      (∀ ρ, IsQuotNormaliser H' μ' ρ ↔ IsQuotNormaliser H μ ρ) ∧ ∀ F, quotIntegral μG H' μ' F = quotIntegral μG H μ F := by
  subst e
  exact ⟨μ, hμ, fun _ => Iff.rfl, fun _ => rfl⟩

theorem UpperTheory.V.Z.Tf.Orb.untwist :
    UpperTheory.V.Z.Tf.Orb.Untwist := by
  intro k _ _ _ _ n _ _ μk γ
  have h1 : ∀ g : GL (Fin n) k, sigmaGL (1 : k ≃ₐ[k] k) g = g := fun g => by rw [sigmaGL_one]; rfl
  refine ⟨fun τ => ?_, h1, fun h => ?_, fun μ hμ => ?_⟩
  · have : τ = 1 := AlgEquiv.ext fun x => τ.commutes x
    rw [this]
    exact one_mem _
  · have : normGL (1 : k ≃ₐ[k] k) γ = γ := by
      rw [normGL, Module.finrank_self]
      simp [twNorm]
    rwa [IsTwRegSemisimple, this]
  · have e : twCent (sigmaGL (1 : k ≃ₐ[k] k)) γ = Subgroup.centralizer {γ} := by
      ext x
      rw [mem_twCent, h1, Subgroup.mem_centralizer_singleton_iff, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]
      rw [commute_iff_eq]
    obtain ⟨μ', a, b, c⟩ := aux μk _ _ e μ hμ
    refine ⟨μ', a, b, fun f => ?_⟩
    rw [twOrbIntegralC, orbIntegralC, c]
    simp only [twConj, h1]
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbComm :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.OrbProper → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.Unimod → UpperTheory.V.Z.Tf.Orb.AbsComm → UpperTheory.V.Z.Tf.Orb.TwOrbComm := by
  intro hG hX hC hP hH hU hA k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE δ hδ μ hμ a b a1 a2 b1 b2 ha
  obtain ⟨g1, g2, g3, -, -⟩ := hG E n
  obtain ⟨c1, c2⟩ := hC k E σ hσ n δ hδ
  obtain ⟨-, i2, -⟩ := hH _ _ c1 c2 μ hμ
  obtain ⟨u1, u2⟩ := hU E n μE hμE
  have hs := ((hX k E).2.2 n).2 σ
  have hl : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hp : ∀ (m : ℕ) x, a (((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) x) = a x := fun m => by
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [pow_succ_apply', ha, ih]
  have t := hA _ μE hμE u1 u2 (sigmaGL σ) hs _ Module.finrank_pos.ne' hl δ (hP k E σ hσ n δ hδ) μ hμ i2 a b a1 a2 b1 b2
  simpa only [hp] using t
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbLin :
    UpperTheory.V.Z.Tf.Orb.TwOrbFin → UpperTheory.V.Z.Tf.Orb.TwOrbLin := by
  intro hT k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE δ hδ μ hμ
  refine ⟨fun c φ => ?_, fun φ ψ a1 a2 b1 b2 => ?_⟩
  · simp only [twOrbIntegralC, quotIntegral]
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _
    · simp
  · obtain ⟨h, p, -⟩ := hT k E σ hσ n μE hμE φ a1 a2 δ hδ μ hμ
    obtain ⟨-, q, -⟩ := hT k E σ hσ n μE hμE ψ b1 b2 δ hδ μ hμ
    simp only [twOrbIntegralC, quotIntegral, dif_pos h, Pi.add_apply, add_mul]
    exact integral_add (p _ h.choose_spec) (q _ h.choose_spec)
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

section Core

variable {G T : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [Group T] [MeasurableSpace T] [MeasurableInv T]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν] {j : T →* G}

omit [MeasurableInv G] [MeasurableInv T] in
private theorem ae_fin (hj : Measurable j) {ρ : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) :
    ∀ᵐ g ∂μ, ρ g < ∞ := by
  have hA : MeasurableSet {g | ρ g = ∞} := hm (measurableSet_singleton _)
  have hmul : Measurable fun p : G × T => j p.2 * p.1 := (hj.comp measurable_snd).mul measurable_fst
  have h1 : ∫⁻ g, ∫⁻ t, {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g) ∂ν ∂μ = 0 := by
    refine (lintegral_congr fun g => ?_).trans lintegral_zero
    have h2 : ∀ᵐ t ∂ν, ρ (j t * g) < ∞ := ae_lt_top (hm.comp (hj.mul_const g)) (by rw [h]; exact ENNReal.one_ne_top)
    refine (lintegral_congr_ae (h2.mono fun t ht => ?_)).trans lintegral_zero
    exact Set.indicator_of_notMem (s := {g | ρ g = ∞}) ht.ne _
  rw [lintegral_lintegral_swap (f := fun g t => {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g))
    ((measurable_one.indicator hA).comp hmul).aemeasurable] at h1
  have h3 : ∀ t : T, ∫⁻ g, {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g) ∂μ = μ {g | ρ g = ∞} := fun t => by
    rw [lintegral_mul_left_eq_self, lintegral_indicator_one hA]
  simp only [h3, lintegral_const, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · rw [ae_iff]
    simpa using h1
  · have := h 1
    rw [Measure.measure_univ_eq_zero.1 h1] at this
    simp at this

private theorem lint_eq [ν.IsInvInvariant] (hj : Measurable j) {F : G → ℝ≥0∞} (hF : Measurable F) (hFH : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) (hm' : Measurable ρ') (h' : ∀ x, ∫⁻ t, ρ' (j t * x) ∂ν = 1) :
    ∫⁻ g, F g * ρ g ∂μ = ∫⁻ g, F g * ρ' g ∂μ := by
  have hmul : Measurable fun p : G × T => j p.2 * p.1 := (hj.comp measurable_snd).mul measurable_fst
  have hmul' : Measurable fun p : G × T => j p.2⁻¹ * p.1 := (hj.comp measurable_snd.inv).mul measurable_fst
  have a : ∀ g, F g * ρ g = ∫⁻ t, F g * ρ g * ρ' (j t * g) ∂ν := fun g => by
    rw [lintegral_const_mul _ (f := fun t => ρ' (j t * g)) (hm'.comp (hj.mul_const g)), h', mul_one]
  have b : ∀ g, F g * ρ' g = ∫⁻ t, F g * ρ' g * ρ (j t⁻¹ * g) ∂ν := fun g => by
    rw [lintegral_const_mul _ (f := fun t => ρ (j t⁻¹ * g)) (hm.comp ((hj.comp measurable_inv).mul_const g)),
      lintegral_inv_eq_self (fun t : T => ρ (j t * g)), h, mul_one]
  rw [lintegral_congr a, lintegral_congr b,
    lintegral_lintegral_swap (f := fun g t => F g * ρ g * ρ' (j t * g))
      (((hF.comp measurable_fst).mul (hm.comp measurable_fst)).mul (hm'.comp hmul)).aemeasurable,
    lintegral_lintegral_swap (f := fun g t => F g * ρ' g * ρ (j t⁻¹ * g))
      (((hF.comp measurable_fst).mul (hm'.comp measurable_fst)).mul (hm.comp hmul')).aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [← lintegral_mul_left_eq_self _ (j t⁻¹)]
  refine lintegral_congr fun g => ?_
  rw [hFH, ← mul_assoc (j t), ← map_mul, mul_inv_cancel, map_one, one_mul]
  ring

private theorem wd_eq [ν.IsInvInvariant] (hj : Measurable j) {F : G → ℂ} (hF : Measurable F) (hFH : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) (hm' : Measurable ρ') (h' : ∀ x, ∫⁻ t, ρ' (j t * x) ∂ν = 1) :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = ∫ g, F g * ((ρ' g).toReal : ℂ) ∂μ := by
  have key : ∀ {ρ : G → ℝ≥0∞}, Measurable ρ → (∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) →
      ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = ∫ z, z ∂((μ.withDensity ρ).map F) := fun {ρ} hm h => by
    rw [integral_map (f := fun z : ℂ => z) hF.aemeasurable aestronglyMeasurable_id, integral_withDensity_eq_integral_toReal_smul hm (ae_fin hj hm h)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [mul_comm]
  rw [key hm h, key hm' h']
  congr 1
  ext A hA
  rw [Measure.map_apply hF hA, Measure.map_apply hF hA, withDensity_apply _ (hF hA), withDensity_apply _ (hF hA),
    ← lintegral_indicator (hF hA), ← lintegral_indicator (hF hA)]
  have e : ∀ ρ : G → ℝ≥0∞, (F ⁻¹' A).indicator ρ = fun g => (F ⁻¹' A).indicator 1 g * ρ g := fun ρ => funext fun g => by
    by_cases hg : g ∈ F ⁻¹' A <;> simp [hg]
  rw [e, e ρ']
  refine lint_eq hj (measurable_one.indicator (hF hA)) (fun t g => ?_) hm h hm' h'
  by_cases hg : F g ∈ A <;> simp [Set.indicator, hFH, hg]

end Core

theorem UpperTheory.V.Z.Tf.Orb.quotIndep :
    UpperTheory.V.Z.Tf.Orb.QuotIndep := by
  intro G _ _ _ _ _ _ _ _ μG hμ H μ _ _ F hF hFH ρ hρ
  have : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hex : ∃ ρ, IsQuotNormaliser H μ ρ := ⟨ρ, hρ⟩
  rw [quotIntegral, dite_eq_left hex]
  exact wd_eq (j := H.subtype) measurable_subtype_coe hF (fun t g => hFH t t.2 g) hex.choose_spec.1 hex.choose_spec.2 hρ.1 hρ.2
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.haarConj :
    UpperTheory.V.Z.Tf.Orb.HaarConj := by
  intro G _ _ _ _ _ _ _ _ H H' y hy μ hμ
  let e : H ≃ₜ* H' :=
    { toFun := fun x => ⟨y⁻¹ * x * y, (hy x).1 x.2⟩
      invFun := fun z => ⟨y * z * y⁻¹, (hy _).2 (by simp [mul_assoc])⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨μ.map e, e.isHaarMeasure_map μ, ?_⟩
  have he : Measurable (e : H → H') := (map_continuous e).measurable
  exact (Measure.map_map (g := fun x : H' => (x : G)) measurable_subtype_coe he).symm
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotInt :
    UpperTheory.V.Z.Tf.Orb.QuotMass → UpperTheory.V.Z.Tf.Orb.QuotInt := by
  intro hM G _ _ _ _ _ _ _ _ μG hμ H hH μ hh hi F hF hFH ⟨C, hC, hs⟩ ρ hρ
  obtain ⟨hf, hm⟩ := hM G μG hμ H hH μ hh hi ρ hρ
  obtain ⟨hcl, hfin⟩ := hm C hC
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  have h1 : IntegrableOn (fun g => (ρ g).toReal) {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} μG :=
    integrable_toReal_of_lintegral_ne_top hρ.1.aemeasurable hfin
  have h2 := ((integrable_indicator_iff hcl.measurableSet).2 h1).const_mul M
  refine h2.mono' (hF.measurable.mul (Complex.measurable_ofReal.comp hρ.1.ennreal_toReal)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  by_cases hg : g ∈ {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}
  · rw [Set.indicator_of_mem hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    obtain ⟨h, hh, c, hc, rfl⟩ := hg
    rw [hFH h hh]
    exact mul_le_mul_of_nonneg_right (hM c hc) ENNReal.toReal_nonneg
  · have : F g = 0 := by
      by_contra h0
      exact hg (hs g h0)
    simp [this, Set.indicator_of_notMem hg]
end
