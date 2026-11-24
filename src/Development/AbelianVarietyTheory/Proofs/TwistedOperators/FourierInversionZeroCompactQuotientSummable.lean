module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.SeparatingCharacters

theorem tsum_coefficients_eq_value_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ) → ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ = Φ 0 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hKcov A _ χ hχc hχmul hχadd hχ0 hχnorm hχker hχinj μ 𝓕 hμ h𝓕 h𝓕1 Φ hΦc hΦper hsum
  classical
  haveI := hμ
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance

  have hχz : ∀ a, χ a 0 = 1 := by
    intro a
    have hne : χ a 0 ≠ 0 := by
      intro h; have := hχnorm a 0; rw [h, norm_zero] at this; exact zero_ne_one this
    have h2 : χ a 0 * χ a 0 = χ a 0 * 1 := by rw [← hχmul, add_zero, mul_one]
    exact (mul_left_cancel₀ hne h2)
  have hχper : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := by
    intro a γ hγ x
    rw [hχmul, (hχker γ).mpr hγ a, one_mul]

  have lift : ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) →
      ∃ F : C(G ⧸ Γ, ℂ), ∀ x : G, F (QuotientAddGroup.mk x) = f x := by
    intro f hf hper
    have hwd : ∀ x y : G, (QuotientAddGroup.mk x : G ⧸ Γ) = QuotientAddGroup.mk y → f x = f y := by
      intro x y hxy
      have h1 := hper _ (QuotientAddGroup.eq.mp hxy) x
      have e : -x + y + x = y := by abel
      rw [e] at h1
      exact h1.symm
    refine ⟨⟨fun q => Quotient.liftOn' q f (fun x y h => hwd x y (Quotient.sound' h)), ?_⟩, fun x => rfl⟩
    exact (QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr hf

  haveI : CompactSpace (G ⧸ Γ) := by
    refine ⟨?_⟩
    have himg : (QuotientAddGroup.mk '' K : Set (G ⧸ Γ)) = Set.univ := by
      refine Set.eq_univ_of_forall fun q => ?_
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨γ, hγ, hk⟩ := hKcov x
      refine ⟨γ + x, hk, QuotientAddGroup.eq.mpr ?_⟩
      rw [show -(γ + x) + x = -γ by abel]
      exact neg_mem hγ
    rw [← himg]
    exact hK.image QuotientAddGroup.continuous_mk
  have hc : ∀ a, ∃ F : C(G ⧸ Γ, ℂ), ∀ x : G, F (QuotientAddGroup.mk x) = χ a x :=
    fun a => lift _ (hχc a) (hχper a)
  choose e he using hc
  obtain ⟨P, hP⟩ := lift Φ hΦc hΦper

  have h𝓕lt : μ 𝓕 < ⊤ := by rw [h𝓕1]; exact ENNReal.one_lt_top
  have hint : ∀ w : C(G ⧸ Γ, ℂ), IntegrableOn (fun x => w (QuotientAddGroup.mk x)) 𝓕 μ := by
    intro w
    exact Measure.integrableOn_of_bounded h𝓕lt.ne
      (w.continuous.comp QuotientAddGroup.continuous_mk).aestronglyMeasurable
      (M := ‖w‖) (Filter.Eventually.of_forall fun x => w.norm_coe_le_norm _)
  obtain ⟨I, hI⟩ : ∃ I : C(G ⧸ Γ, ℂ) →L[ℂ] ℂ,
      ∀ w, I w = ∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ := by
    refine ⟨LinearMap.mkContinuous
      { toFun := fun w => ∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ
        map_add' := fun v w => by
          simp only [ContinuousMap.add_apply]
          exact integral_add (hint v) (hint w)
        map_smul' := fun c w => by
          simp only [ContinuousMap.smul_apply, RingHom.id_apply]
          exact integral_smul c _ } 1 (fun w => ?_), fun w => rfl⟩
    calc ‖∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ‖ ≤ ‖w‖ * μ.real 𝓕 :=
          norm_setIntegral_le_of_norm_le_const h𝓕lt (fun x _ => w.norm_coe_le_norm _)
      _ = 1 * ‖w‖ := by simp [Measure.real, h𝓕1]

  have hprod : ∀ a a', e a * e a' = e (a + a') := by
    intro a a'; ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp [he, hχadd]
  have hnorm1 : ∀ a, ‖e a‖ ≤ 1 := by
    intro a
    refine (ContinuousMap.norm_le _ zero_le_one).mpr fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [he, hχnorm]

  have hortho : ∀ a, I (e a) = if a = 0 then 1 else 0 := by
    intro a
    rw [hI]
    simp_rw [he]
    split_ifs with ha
    · subst ha
      simp [hχ0, Measure.real, h𝓕1]
    · obtain ⟨y, hy⟩ : ∃ y, χ a y ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact ha (hχinj a hcon)
      have htr : IsAddFundamentalDomain Γ (y +ᵥ 𝓕) μ := h𝓕.vadd_of_comm y
      have key : (∫ x in 𝓕, χ a x ∂μ) = χ a y * ∫ x in 𝓕, χ a x ∂μ := by
        calc (∫ x in 𝓕, χ a x ∂μ) = ∫ x in y +ᵥ 𝓕, χ a x ∂μ :=
              h𝓕.setIntegral_eq htr (fun γ x => hχper a γ γ.2 x)
          _ = ∫ x in 𝓕, χ a (y + x) ∂μ := by
              rw [← Set.image_vadd]
              exact (measurePreserving_add_left μ y).setIntegral_image_emb
                (measurableEmbedding_addLeft y) _ _
          _ = ∫ x in 𝓕, χ a y * χ a x ∂μ := by simp_rw [hχmul]
          _ = χ a y * ∫ x in 𝓕, χ a x ∂μ := integral_const_mul _ _
      have h1 : (1 - χ a y) * ∫ x in 𝓕, χ a x ∂μ = 0 := by
        rw [sub_mul, one_mul]
        exact sub_eq_zero.mpr key
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hy
      · exact h

  set c : A → ℂ := fun b => ∫ x in 𝓕, χ b x * Φ x ∂μ with hcdef
  have hcoef : ∀ b, c b = I (e b * P) := by
    intro b
    rw [hI]
    simp [hcdef, he, hP]
  have hsumn : Summable (fun a => ‖c a‖) := summable_norm_iff.mpr hsum
  have hgs : Summable (fun a => c a • e (-a)) := by
    refine Summable.of_norm_bounded hsumn fun a => ?_
    calc ‖c a • e (-a)‖ ≤ ‖c a‖ * ‖e (-a)‖ := norm_smul_le _ _
      _ ≤ ‖c a‖ * 1 := by gcongr; exact hnorm1 _
      _ = ‖c a‖ := mul_one _
  set g : C(G ⧸ Γ, ℂ) := ∑' a, c a • e (-a) with hgdef
  have hgcoef : ∀ b, I (e b * g) = c b := by
    intro b
    have step : I (e b * g) = ∑' a, (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))) (c a • e (-a)) :=
      (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))).map_tsum hgs
    rw [step]
    have hterm : ∀ a, (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))) (c a • e (-a)) =
        if a = b then c b else 0 := by
      intro a
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', mul_smul_comm, map_smul,
        hprod, hortho, smul_eq_mul]
      by_cases h : a = b
      · subst h; simp
      · have h' : b + -a ≠ 0 := fun h' => h (add_neg_eq_zero.mp h').symm
        simp [h, h']
    rw [tsum_congr hterm, tsum_ite_eq]
  set H : C(G ⧸ Γ, ℂ) := P - g with hHdef
  have hH : ∀ b, I (e b * H) = 0 := by
    intro b
    rw [hHdef, mul_sub, map_sub, ← hcoef, hgcoef, sub_self]

  let k : G → ℂ := fun x => H (QuotientAddGroup.mk x)
  have hkc : Continuous k := H.continuous.comp QuotientAddGroup.continuous_mk
  have hkper : ∀ γ ∈ Γ, ∀ x, k (γ + x) = k x := by
    intro γ hγ x
    apply congrArg H
    refine QuotientAddGroup.eq.mpr ?_
    rw [show -(γ + x) + x = -γ by abel]
    exact Γ.neg_mem hγ
  have hk : k = 0 :=
    _root_.GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hKcov A χ
      hχc hχmul hχadd hχ0 hχnorm hχker μ 𝓕 hμ h𝓕 k hkc hkper (fun b => by
        have hb := hH b
        rw [hI] at hb
        simpa only [ContinuousMap.mul_apply, he] using hb)
  have hk0 : k 0 = 0 := congrFun hk 0
  have hg0 : g (QuotientAddGroup.mk 0) = ∑' a, c a := by
    have hev := (ContinuousMap.evalCLM ℂ (QuotientAddGroup.mk 0 : G ⧸ Γ)).map_tsum hgs
    simp only [ContinuousMap.evalCLM_apply] at hev
    rw [hgdef, hev]
    congr 1; funext a
    rw [ContinuousMap.smul_apply, he, hχz, smul_eq_mul, mul_one]
  have : k 0 = Φ 0 - ∑' a, c a := by
    change H (QuotientAddGroup.mk 0) = _
    simp only [hHdef, ContinuousMap.sub_apply, hP]
    rw [hg0]
  rw [hk0] at this
  exact (sub_eq_zero.mp this.symm).symm

end GlobalTheory.SeparatingCharacters
