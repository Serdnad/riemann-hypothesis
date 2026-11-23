module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private lemma UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk {G : Type} [Group G] (T K : Subgroup G)
    (q : DoubleCoset.Quotient (T : Set G) (K : Set G)) (g : G) :
    (∃ t ∈ T, ∃ y ∈ K, g = t * Quotient.out q * y) ↔ DoubleCoset.mk T K g = q := by
  have h := @DoubleCoset.eq _ _ T K (Quotient.out q) g
  rw [DoubleCoset.out_eq'] at h
  exact h.symm.trans eq_comm

theorem UpperTheory.Gal.InertialTypesAlt.L.sumCoset :
    UpperTheory.Gal.InertialTypesAlt.L.SumCoset := by
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 T hTc hcomm ν hν F hF hFT hFC
  obtain ⟨hsf, hinv, hrinv⟩ := haarComm_holds G T hTc hcomm ν hν
  obtain ⟨ρ, hρ, -⟩ := normEx_holds G ⟨K, hKo, hKc⟩ T hTc ν hν hrinv
  have hInt := quotInt_holds G μ hμ T hTc ν hν hinv F hF hFT hFC ρ hρ
  obtain ⟨C, hC, hFC'⟩ := hFC
  have hFm : Measurable F := hF.measurable
  have hmk : ∀ h ∈ T, ∀ g : G, DoubleCoset.mk T K (h * g) = DoubleCoset.mk T K g :=
    fun h hh g => ((@DoubleCoset.eq _ _ T K g (h * g)).2 ⟨h, hh, 1, K.one_mem, by simp⟩).symm
  set Q : Set (DoubleCoset.Quotient (T : Set G) (K : Set G)) :=
    {q | ∃ y ∈ K, F (Quotient.out q * y) ≠ 0} with hQ
  have hkey : ∀ g, F g ≠ 0 → DoubleCoset.mk T K g ∈ Q := by
    intro g hg
    obtain ⟨t, ht, y, hy, he⟩ :=
      (UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk T K (DoubleCoset.mk T K g) g).2 rfl
    refine ⟨y, hy, ?_⟩
    have e : Quotient.out (DoubleCoset.mk T K g) * y = t⁻¹ * g := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc]
      exact he.symm
    rw [e, hFT t⁻¹ (T.inv_mem ht) g]
    exact hg
  have hfin : Q.Finite := by
    obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun c : G => {z : G | c⁻¹ * z ∈ K})
      (fun c => hKo.preimage (continuous_const_mul c⁻¹))
      (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [K.one_mem]⟩)
    refine (s.finite_toSet.image (DoubleCoset.mk T K)).subset ?_
    rintro q ⟨y, hy, hq⟩
    obtain ⟨t, ht, c, hc, he⟩ := hFC' _ hq
    obtain ⟨i, hi, hci⟩ := Set.mem_iUnion₂.1 (hs hc)
    refine ⟨i, hi, ?_⟩
    rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
    refine ⟨t, ht, i⁻¹ * c * y⁻¹, K.mul_mem hci (K.inv_mem hy), ?_⟩
    calc Quotient.out q = Quotient.out q * y * y⁻¹ := by group
      _ = t * c * y⁻¹ := by rw [he]
      _ = t * i * (i⁻¹ * c * y⁻¹) := by group
  refine ⟨hfin, ?_⟩
  have hS : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      {g | ∃ t ∈ T, ∃ y ∈ K, g = t * Quotient.out q * y} = {g | DoubleCoset.mk T K g = q} :=
    fun q => Set.ext (UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk T K q)
  simp_rw [hS]
  have hSo : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      IsOpen {g | DoubleCoset.mk T K g = q} := by
    intro q
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨{z | g⁻¹ * z ∈ K}, fun z hz => ?_, hKo.preimage (continuous_const_mul g⁻¹),
      by simp [K.one_mem]⟩
    show DoubleCoset.mk T K z = q
    rw [← (show DoubleCoset.mk T K g = q from hg), eq_comm, DoubleCoset.eq]
    exact ⟨1, T.one_mem, g⁻¹ * z, hz, by group⟩
  have hSinv : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), ∀ h ∈ T, ∀ g : G,
      {g | DoubleCoset.mk T K g = q}.indicator F (h * g) =
        {g | DoubleCoset.mk T K g = q}.indicator F g := by
    intro q h hh g
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hmk h hh g, hFT h hh g]
  have hq_eq : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F) =
        ∫ g, {g | DoubleCoset.mk T K g = q}.indicator
          (fun g => F g * ((ρ g).toReal : ℂ)) g ∂μ := by
    intro q
    rw [quotIndep_holds G μ hμ T ν hsf hinv _ (hFm.indicator (hSo q).measurableSet) (hSinv q) ρ hρ]
    congr 1
    funext g
    simp [Set.indicator_apply]
  have hsupp : (Function.support fun q : DoubleCoset.Quotient (T : Set G) (K : Set G) =>
      quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F)) ⊆
        ↑hfin.toFinset := by
    intro q hq
    rw [Set.Finite.coe_toFinset]
    by_contra hqQ
    apply hq
    have h0 : {g | DoubleCoset.mk T K g = q}.indicator F = 0 := by
      funext g
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.zero_apply]
      split_ifs with hg
      · by_contra hne
        exact hqQ (hg ▸ hkey g hne)
      · rfl
    show quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F) = 0
    rw [h0]
    simp [quotIntegral]
  rw [quotIndep_holds G μ hμ T ν hsf hinv F hFm hFT ρ hρ, finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_congr rfl (fun q _ => hq_eq q),
    ← integral_finsetSum _ (fun q _ => hInt.indicator (hSo q).measurableSet)]
  congr 1
  funext g
  by_cases hg : F g = 0
  · simp [Set.indicator_apply, hg]
  · rw [Finset.sum_eq_single (DoubleCoset.mk T K g)]
    · simp [Set.indicator_apply]
    · intro b _ hb
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_neg (fun h => hb h.symm)]
    · intro hn
      exact absurd (hfin.mem_toFinset.2 (hkey g hg)) hn
end
end

section

open MeasureTheory PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb
open scoped ENNReal

theorem UpperTheory.Gal.InertialTypesAlt.L.oneCoset :
    UpperTheory.Gal.InertialTypesAlt.L.OneCoset := by
  classical
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 T hTc hTcomm ν hν F hF hFT q
  haveI := hμ
  haveI := hν
  obtain ⟨hsf, hinv, hright⟩ := haarComm_holds G T hTc hTcomm ν hν
  haveI := hsf
  haveI := hinv
  haveI := hright
  obtain ⟨ρ, hρ, -⟩ := normEx_holds G ⟨K, hKo, hKc⟩ T hTc ν hν hright
  set D : Set G := {g | ∃ t ∈ T, ∃ y ∈ K, g = t * q * y} with hD
  set Hs : Set T := {t : T | q⁻¹ * (t : G) * q ∈ K} with hHs
  set qK : Set G := {g | q⁻¹ * g ∈ K} with hqK

  have hqKo : IsOpen qK := hKo.preimage (continuous_const.mul continuous_id)
  have hDo : IsOpen D := by
    have : D = ⋃ t : T, (fun g : G => ((t : G) * q)⁻¹ * g) ⁻¹' (K : Set G) := by
      ext g
      simp only [hD, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
      constructor
      · rintro ⟨t, ht, y, hy, rfl⟩
        refine ⟨⟨t, ht⟩, ?_⟩
        simpa [mul_assoc] using hy
      · rintro ⟨t, ht⟩
        exact ⟨t, t.2, _, ht, by group⟩
    rw [this]
    exact isOpen_iUnion fun t => hKo.preimage (continuous_const.mul continuous_id)
  have hHo : IsOpen Hs :=
    hKo.preimage (((continuous_const.mul continuous_subtype_val).mul continuous_const))
  have hHc : IsCompact Hs := by
    have hS : IsCompact ((fun x : G => q * x * q⁻¹) '' (K : Set G)) :=
      hKc.image (by fun_prop)
    have hpc := hTc.isClosedEmbedding_subtypeVal.isCompact_preimage hS
    have e : Hs = Subtype.val ⁻¹' ((fun x : G => q * x * q⁻¹) '' (K : Set G)) := by
      ext t
      simp only [hHs, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
      constructor
      · intro h
        exact ⟨_, h, by group⟩
      · rintro ⟨x, hx, hxt⟩
        have : q⁻¹ * (t : G) * q = x := by rw [← hxt]; group
        rwa [this]
    rw [e]
    exact hpc
  have h1H : (1 : T) ∈ Hs := by
    simpa [hHs] using K.one_mem
  set v : ℝ≥0∞ := ν Hs with hv
  have hv0 : v ≠ 0 := hHo.measure_ne_zero ν ⟨1, h1H⟩
  have hvt : v ≠ ∞ := hHc.measure_lt_top.ne
  have hqKD : qK ⊆ D := fun g hg => ⟨1, T.one_mem, q⁻¹ * g, hg, by group⟩
  have hDT : ∀ h ∈ T, ∀ g, h * g ∈ D ↔ g ∈ D := by
    intro h hh g
    constructor
    · rintro ⟨t, ht, y, hy, e⟩
      refine ⟨h⁻¹ * t, T.mul_mem (T.inv_mem hh) ht, y, hy, ?_⟩
      calc g = h⁻¹ * (h * g) := by group
        _ = _ := by rw [e]; group
    · rintro ⟨t, ht, y, hy, rfl⟩
      exact ⟨h * t, T.mul_mem hh ht, y, hy, by group⟩
  set ρ' : G → ℝ≥0∞ := D.piecewise (qK.indicator fun _ => v⁻¹) ρ with hρ'def
  have hρ' : IsQuotNormaliser T ν ρ' := by
    refine ⟨Measurable.piecewise hDo.measurableSet
      (measurable_const.indicator hqKo.measurableSet) hρ.1, fun g => ?_⟩
    by_cases hg : g ∈ D
    · obtain ⟨t₀, ht₀, y, hy, rfl⟩ := hg
      set A : Set T := (fun h : T => h * (⟨t₀, ht₀⟩ : T)) ⁻¹' Hs with hA
      have hAm : MeasurableSet A := (hHo.preimage (continuous_mul_const _)).measurableSet
      have hpt : ∀ h : T, ρ' ((h : G) * (t₀ * q * y)) = A.indicator (fun _ => v⁻¹) h := by
        intro h
        have hmem : (h : G) * (t₀ * q * y) ∈ D :=
          (hDT _ h.2 _).2 ⟨t₀, ht₀, y, hy, rfl⟩
        rw [hρ'def, Set.piecewise_eq_of_mem _ _ _ hmem]
        have hiff : (h : G) * (t₀ * q * y) ∈ qK ↔ h ∈ A := by
          have e : q⁻¹ * ((h : G) * (t₀ * q * y)) = (q⁻¹ * ((h : G) * t₀) * q) * y := by group
          simp only [hqK, hA, hHs, Set.mem_setOf_eq, Set.mem_preimage, e, Subgroup.coe_mul]
          exact Subgroup.mul_mem_cancel_right K hy
        by_cases hh : h ∈ A
        · rw [Set.indicator_of_mem (hiff.2 hh), Set.indicator_of_mem hh]
        · rw [Set.indicator_of_notMem (fun c => hh (hiff.1 c)), Set.indicator_of_notMem hh]
      simp_rw [hpt]
      rw [lintegral_indicator_const hAm, hA, measure_preimage_mul_right, ← hv]
      exact ENNReal.inv_mul_cancel hv0 hvt
    · have hpt : ∀ h : T, ρ' ((h : G) * g) = ρ ((h : G) * g) := by
        intro h
        rw [hρ'def, Set.piecewise_eq_of_notMem _ _ _ (fun c => hg ((hDT _ h.2 _).1 c))]
      simp_rw [hpt]
      exact hρ.2 g
  have hFm : Measurable (D.indicator F) := hF.measurable.indicator hDo.measurableSet
  have hFinv : ∀ h ∈ T, ∀ g, D.indicator F (h * g) = D.indicator F g := by
    intro h hh g
    by_cases hg : g ∈ D
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hDT h hh g).2 hg), hFT h hh]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun c => hg ((hDT h hh g).1 c))]
  rw [quotIndep_holds G μ hμ T ν hsf hinv _ hFm hFinv ρ' hρ']
  have hpt : ∀ g, D.indicator F g * ((ρ' g).toReal : ℂ) =
      qK.indicator (fun g => ((v.toReal : ℝ) : ℂ)⁻¹ * F g) g := by
    intro g
    by_cases hg : g ∈ D
    · rw [Set.indicator_of_mem hg, hρ'def, Set.piecewise_eq_of_mem _ _ _ hg]
      by_cases hq : g ∈ qK
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, ENNReal.toReal_inv]
        push_cast
        ring
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
        simp
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun c => hg (hqKD c)), zero_mul]
  simp_rw [hpt]
  rw [integral_indicator hqKo.measurableSet, integral_const_mul]
  have hpre : (fun y : G => q * y) ⁻¹' qK = (K : Set G) := by
    ext y
    simp [hqK]
  have := (measurePreserving_mul_left μ q).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft q) F qK
  rw [hpre] at this
  rw [this]
  rfl
end
