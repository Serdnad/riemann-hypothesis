module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle005
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDSerre
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.OpenMapping
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem isPreconnected_punctured_ball {R : ℝ} (hR : 0 < R) :
    IsPreconnected (Metric.ball (0 : ℂ) R \ {0}) := by
  have hH : IsPreconnected {z : ℂ | z.re < Real.log R} := (convex_halfSpace_re_lt _).isPreconnected
  have himage : Complex.exp '' {z : ℂ | z.re < Real.log R} = Metric.ball (0 : ℂ) R \ {0} := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_ball, dist_zero_right,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, Complex.exp_ne_zero z⟩
      rw [Complex.norm_exp]
      exact (Real.exp_lt_exp.2 hz).trans_eq (Real.exp_log hR)
    · rintro ⟨hw, hw0⟩
      refine ⟨Complex.log w, ?_, Complex.exp_log hw0⟩
      rw [Complex.log_re]
      exact Real.log_lt_log (norm_pos_iff.2 hw0) hw
  rw [← himage]
  exact hH.image _ Complex.continuous_exp.continuousOn

theorem PuncturedBranchInOneBranch.proof (h₁ : BranchImageNhdOffCentre.Statement) :
    PuncturedBranchInOneBranch.Statement := by
  intro n I q m c ν ρ _ hdim hρ hcov hdisj
  obtain ⟨N, hN, hNc⟩ := h₁ n I q hdim
  have hnorm : ∀ τ : ℂ, ‖(fun _ ↦ τ : Fin 1 → ℂ)‖ = ‖τ‖ := fun τ ↦ by simp [pi_norm_const]
  have hball : ∀ τ : ℂ, ‖τ‖ < ν.radius → (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball 0 ν.radius := fun τ hτ ↦ by
    rwa [Metric.mem_ball, dist_zero_right, hnorm]
  have h0r : ‖(0 : ℂ)‖ < ν.radius := by simpa using ν.radius_pos

  have hcont : ∀ τ : ℂ, ‖τ‖ < ν.radius → ContinuousAt (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) τ := fun τ hτ ↦
    (ν.differentiableOn.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (hball τ hτ))).comp
      (f := fun τ : ℂ ↦ (fun _ ↦ τ : Fin 1 → ℂ)) (continuous_pi fun _ ↦ continuous_id).continuousAt
  have hq : ν.toFun (fun _ ↦ (0 : ℂ)) = q := ν.map_zero
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ν.toFun (fun _ ↦ τ) ∈ N :=
    (hcont 0 h0r).preimage_mem_nhds (by show N ∈ 𝓝 (ν.toFun fun _ ↦ (0 : ℂ)); rw [hq]; exact hN)
  obtain ⟨ε, hε, hεN⟩ := Metric.eventually_nhds_iff.1 hev

  obtain ⟨R, hR0, hRρ, hRε, hRν⟩ : ∃ R, 0 < R ∧ R ≤ ρ ∧ R ≤ ε ∧ R ≤ ν.radius :=
    ⟨min ρ (min ε ν.radius), lt_min hρ (lt_min hε ν.radius_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  let D : Set ℂ := Metric.ball 0 R \ {0}
  have hD : ∀ τ ∈ D, 0 < ‖τ‖ ∧ ‖τ‖ < R := fun τ hτ ↦
    ⟨norm_pos_iff.2 (by simpa using hτ.2), by simpa using hτ.1⟩
  have hne : ∀ τ ∈ D, ν.toFun (fun _ ↦ τ) ≠ q := by
    intro τ hτ h
    have h' := ν.injOn (hball τ ((hD τ hτ).2.trans_le hRν)) (hball 0 h0r) (h.trans hq.symm)
    exact (norm_pos_iff.1 (hD τ hτ).1) (by simpa using congrFun h' 0)

  let Vb : Fin m → Set ℂ := fun b ↦ D ∩ (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) ⁻¹' (c b).image
  have hDo : IsOpen D := Metric.isOpen_ball.sdiff isClosed_singleton
  have hVo : ∀ b, IsOpen (Vb b) := by
    intro b
    rw [isOpen_iff_mem_nhds]
    rintro τ ⟨hτD, hτb⟩
    have hτN : ν.toFun (fun _ ↦ τ) ∈ N := hεN (by rw [dist_zero_right]; exact (hD τ hτD).2.trans_le hRε)
    obtain ⟨U, hU, hUc⟩ := hNc (c b) _ ⟨hτb, hτN⟩ (hne τ hτD)
    filter_upwards [hDo.mem_nhds hτD, (hcont τ ((hD τ hτD).2.trans_le hRν)).preimage_mem_nhds hU]
      with σ hσD hσU
    exact ⟨hσD, hUc ⟨ν.mapsTo (hball σ ((hD σ hσD).2.trans_le hRν)), hσU⟩⟩
  have hVd : ∀ b b', b ≠ b' → Disjoint (Vb b) (Vb b') := fun b b' hbb ↦
    Set.disjoint_left.2 fun τ hτ hτ' ↦ hne τ hτ.1 (hdisj b b' hbb ⟨hτ.2, hτ'.2⟩)
  have hcovD : ∀ τ ∈ D, ∃ b, τ ∈ Vb b := fun τ hτ ↦ by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hcov τ (hD τ hτ).1 ((hD τ hτ).2.trans_le hRρ))
    exact ⟨b, hτ, hb⟩

  have hτ₀ : ((R / 2 : ℝ) : ℂ) ∈ D := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · simp [hR0.ne']
  obtain ⟨b, hb⟩ := hcovD _ hτ₀
  have hsub : D ⊆ Vb b := by
    refine (isPreconnected_punctured_ball hR0).subset_left_of_subset_union (hVo b)
      (isOpen_iUnion fun b' ↦ isOpen_iUnion fun (_ : b' ≠ b) ↦ hVo b') ?_ ?_ ⟨_, hτ₀, hb⟩
    · exact Set.disjoint_iUnion_right.2 fun b' ↦ Set.disjoint_iUnion_right.2 fun hb' ↦ hVd b b' (Ne.symm hb')
    · intro τ hτ
      obtain ⟨b', hb'⟩ := hcovD τ hτ
      by_cases h : b' = b
      · exact Or.inl (h ▸ hb')
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨b', h, hb'⟩)
  refine ⟨b, R, hR0, fun τ hτ0 hτR ↦ (hsub ⟨?_, ?_⟩).2⟩
  · rwa [Metric.mem_ball, dist_zero_right]
  · simpa using norm_pos_iff.1 hτ0

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

theorem exists_nat_eq_of_ne_bot_of_le {x : WithBot ℕ∞} {d : ℕ} (h0 : x ≠ ⊥) (hle : x ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, x = e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe y =>
    have hy : y ≤ (d : ℕ∞) := by exact_mod_cast hle
    have hyt : y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hy
    exact ⟨y.toNat, by rw [← ENat.natCast_toNat hyt]; rfl⟩

theorem quotient_mk_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] (hJ : J ≤ maximalIdeal S) {r : S} (hr : r ∈ maximalIdeal S) :
    Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  have h1 : r * s - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, map_one, sub_self]
  have h2 : (1 : S) ∈ maximalIdeal S := by
    have := sub_mem ((maximalIdeal S).mul_mem_right s hr) (hJ h1)
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)

theorem mem_maximalIdeal_of_quotient_mk {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] {r : S} (hr : Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J)) : r ∈ maximalIdeal S := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
  exact fun hu => hr (hu.map _)

theorem isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing
    (hlow : AuslanderBuchsbaumDepthLower.Statement.{0}) (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0})
    (hlen : RegularSequenceLengthLeDim.Statement.{0}) (hcm : CMHeightAddDim.Statement.{0})
    {S : Type} [CommRing S] [IsRegularLocalRing S] (J : Ideal S) (hJm : J ≤ maximalIdeal S) :
    IsCohenMacaulayLocalRing (S ⧸ J) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) ℓ ∧ (ℓ : ℕ∞) ≤ J.height := by
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨rs0, hrs0, hofl, hlen0⟩ := GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := S)
  have hrs0m : ∀ r ∈ rs0, r ∈ maximalIdeal S := fun r hr => hofl ▸ Ideal.subset_span hr
  set d := rs0.length with hd_def
  have hcmS : IsCohenMacaulayLocalRing S :=
    { exists_isWeaklyRegular := ⟨rs0, hrs0m, hrs0.toIsWeaklyRegular, hlen0.symm⟩ }
  have hsum := hcm S J hJ
  rw [← hlen0] at hsum
  obtain ⟨e, he⟩ := exists_nat_eq_of_ne_bot_of_le (x := ringKrullDim (S ⧸ J)) (d := d)
    (ringKrullDim_ne_bot) (hlen0 ▸ ringKrullDim_quotient_le J)
  have hht : J.height ≠ ⊤ := by
    intro h
    rw [h, he] at hsum
    have h2 : ((⊤ : ℕ∞) + e : ℕ∞) = d := by exact_mod_cast hsum
    simp at h2
  obtain ⟨h, hh⟩ : ∃ h : ℕ, J.height = h := ⟨J.height.toNat, (ENat.natCast_toNat hht).symm⟩
  have hhe : h + e = d := by
    rw [hh, he] at hsum; exact_mod_cast hsum
  have hserre : HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) d :=
    GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing hlen0.symm (S ⧸ J)
  constructor
  · intro hCM
    obtain ⟨as, has_m, has_reg, has_len⟩ := hCM.exists_isWeaklyRegular
    obtain ⟨ms, hms⟩ : ∃ ms : List S, ms.map (algebraMap S (S ⧸ J)) = as :=
      ⟨as.map fun a => (Ideal.Quotient.mk_surjective a).choose, by
        rw [List.map_map]; conv_rhs => rw [← List.map_id as]
        exact List.map_congr_left fun a _ => (Ideal.Quotient.mk_surjective a).choose_spec⟩
    have hmsreg : IsWeaklyRegular (S ⧸ J) ms := by
      rw [← isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) ms, hms]; exact has_reg
    have hmsm : ∀ r ∈ ms, r ∈ maximalIdeal S := fun r hr =>
      mem_maximalIdeal_of_quotient_mk (has_m _ (hms ▸ List.mem_map_of_mem hr))
    have hmslen : ms.length = e := by
      have : (as.length : WithBot ℕ∞) = e := has_len.symm.trans he
      rw [← hms, List.length_map] at this; exact_mod_cast this
    have hbound : ∀ rs : List S, (∀ r ∈ rs, r ∈ maximalIdeal S) → IsWeaklyRegular S rs → rs.length ≤ d :=
      fun rs hm hr => by have := hlen S rs hm hr; rw [← hlen0] at this; exact_mod_cast this
    refine ⟨d - e, ?_, ?_⟩
    · have := hup S (S ⧸ J) d d ms hserre hbound hmsm hmsreg
      rwa [hmslen] at this
    · rw [hh]; exact_mod_cast (by omega : d - e ≤ h)
  · rintro ⟨ℓ, hpd, hℓ⟩
    obtain ⟨ms, hmsm, hmsreg, hmslen⟩ := hlow S (S ⧸ J) ℓ rs0 hpd hrs0m hrs0.toIsWeaklyRegular
    have hℓh : ℓ ≤ h := by rw [hh] at hℓ; exact_mod_cast hℓ
    have hle : e ≤ ms.length := by rw [hmslen]; omega
    have hreg' : IsWeaklyRegular (S ⧸ J) (ms.take e) := by
      have := hmsreg; rw [← List.take_append_drop e ms] at this
      exact ((isWeaklyRegular_append_iff (S ⧸ J) _ _).mp this).1
    refine { exists_isWeaklyRegular := ⟨(ms.take e).map (algebraMap S (S ⧸ J)), ?_, ?_, ?_⟩ }
    · intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact quotient_mk_mem_maximalIdeal hJm (hmsm r (List.mem_of_mem_take hr))
    · exact (isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) _).mpr hreg'
    · rw [he, List.length_map, List.length_take, min_eq_left hle]

theorem CMProjDimCriterion.proof (hlow : AuslanderBuchsbaumDepthLower.Statement.{0})
    (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0}) (hlen : RegularSequenceLengthLeDim.Statement.{0})
    (hcm : CMHeightAddDim.Statement.{0}) : CMProjDimCriterion.Statement := by
  intro n I Q _ hIQ
  have : Algebra.Smooth ℂ (MvPolynomial (Fin n) ℂ) := {}
  have : IsRegularLocalRing (Localization.AtPrime Q) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth ℂ (MvPolynomial (Fin n) ℂ) Q
  refine isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing hlow hup hlen hcm _ ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono hIQ

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

theorem CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime (hreg : CMRegularElement.Statement.{u}) :
    ∀ (n : ℕ) (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B], ringKrullDim B = n →
      ∀ (P : Ideal B) [P.IsPrime], (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) = ringKrullDim B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B _ _ hn P hP
  refine le_antisymm (height_add_ringKrullDim_quotient_le P) ?_
  by_cases hmin : P ∈ minimalPrimes B
  · rw [Ideal.height_eq_zero_iff.mpr hmin, ringKrullDim_quotient_eq_of_mem_minimalPrimes hmin]
    simp

  have hfin := minimalPrimes.finite_of_isNoetherianRing (R := B)
  obtain ⟨y, hyP, hyq⟩ : ∃ y ∈ P, ∀ q ∈ minimalPrimes B, y ∉ q := by
    by_contra! h
    have hsub : (P : Set B) ⊆ ⋃ i ∈ (↑hfin.toFinset : Set (Ideal B)), (id i : Set B) := by
      intro z hz
      obtain ⟨q, hq, hzq⟩ := h z hz
      exact Set.mem_biUnion (by simpa using hq) hzq
    obtain ⟨q, hq, hPq⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun i hi _ _ => ((Set.Finite.mem_toFinset hfin).mp hi).1.1)).mp hsub
    have hq' : q ∈ minimalPrimes B := (Set.Finite.mem_toFinset hfin).mp hq
    have hqP : q ≤ P := hq'.2 ⟨hP, bot_le⟩ hPq
    exact hmin (le_antisymm hPq hqP ▸ hq')
  have hym : y ∈ maximalIdeal B := le_maximalIdeal hP.ne_top hyP
  obtain ⟨hynzd, hCM⟩ := hreg B y hym hyq
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hynzd hym
  obtain ⟨rs', -, -, hd'⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B ⧸ Ideal.span {y})
  have hlt : rs'.length < n := by
    have h1 : ((rs'.length + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [← hn, ← hdim, hd']
      push_cast
      rfl
    have h2 : rs'.length + 1 = n := by exact_mod_cast h1
    omega
  have hle : Ideal.span {y} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk (Ideal.span {y}))).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hle
  have hIH := ih rs'.length hlt (B ⧸ Ideal.span {y}) hd' (P.map (Ideal.Quotient.mk (Ideal.span {y})))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hIH
  have hc := height_map_add_one_le_of_mem_nonZeroDivisors hynzd P hyP
  calc ringKrullDim B = ringKrullDim (B ⧸ Ideal.span {y}) + 1 := hdim.symm
    _ = ((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) + 1 := by
        rw [hIH]
    _ = (((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 : ℕ∞) : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        rw [WithBot.coe_add, WithBot.coe_one, add_right_comm]
    _ ≤ (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        gcongr

theorem CMHeightAddDim.proof (hreg : CMRegularElement.Statement.{u}) : CMHeightAddDim.Statement.{u} := by
  intro B _ _ J hJ
  obtain ⟨rs, -, -, hd⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hprime := CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime hreg rs.length B hd
  refine le_antisymm ?_ ?_
  ·
    have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    have : Nonempty (PrimeSpectrum (B ⧸ J)) := inferInstance
    rw [show ringKrullDim (B ⧸ J) = Order.krullDim (PrimeSpectrum (B ⧸ J)) from rfl,
      Order.krullDim_eq_iSup_coheight_of_nonempty, ← WithBot.coe_add, ENat.add_iSup,
      WithBot.coe_iSup (OrderTop.bddAbove _)]
    refine iSup_le fun a => ?_
    obtain ⟨a, ha⟩ := a
    set Q := a.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hJQ : J ≤ Q := fun z hz => by
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact Ideal.zero_mem _
    have hmap : a = Q.map (Ideal.Quotient.mk J) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective a).symm
    have hco : (Order.coheight (⟨a, ha⟩ : PrimeSpectrum (B ⧸ J)) : WithBot ℕ∞) = ringKrullDim (B ⧸ Q) := by
      rw [← ringKrullDim_quotient_eq_coheight a,
        ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hmap).trans (DoubleQuot.quotQuotEquivQuotOfLE hJQ))]
    rw [WithBot.coe_add, hco, ← hprime Q]
    gcongr
  ·
    obtain ⟨P, hPmin, hPle⟩ := Set.exists_min_image J.minimalPrimes Ideal.height
      (Ideal.finite_minimalPrimes_of_isNoetherianRing B J) (Set.nonempty_coe_sort.mp (Ideal.nonempty_minimalPrimes hJ))
    have : P.IsPrime := hPmin.1.1
    have hht : J.height = P.height := by
      rw [Ideal.height_eq_inf_minimalPrimes]
      exact le_antisymm (iInf₂_le P hPmin) (le_iInf₂ fun Q hQ => hPle Q hQ)
    rw [hht, ← hprime P]
    gcongr
    exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hPmin.1.2)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchImageNhdOffCentre.proof (h₁ : CurveRegularOffCentre.Statement) :
    BranchImageNhdOffCentre.Statement := by
  intro n I q hdim
  obtain ⟨N, hN, hreg⟩ := h₁ n I q hdim
  refine ⟨N, hN, fun c x hx hxq => ?_⟩
  obtain ⟨⟨σ₀, hσ₀, rfl⟩, hxN⟩ := hx
  obtain ⟨A, O, V, g, -, hV, hxV, -, hAg, hZV⟩ := hreg (c.toFun σ₀) ⟨c.mapsTo hσ₀, hxN⟩ hxq

  let e : ℂ → Fin 1 → ℂ := fun τ _ => τ
  have he_diff : Differentiable ℂ e := differentiable_pi.2 fun _ => differentiable_id
  have he_inj : Function.Injective e := fun a b h => congrFun h 0
  have hσe : e (σ₀ 0) = σ₀ := funext fun i => by fin_cases i; rfl
  have hBe : ∀ τ ∈ Metric.ball (0 : ℂ) c.radius, e τ ∈ Metric.ball 0 c.radius := by
    intro τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    rwa [pi_norm_const]
  have ht₀ : σ₀ 0 ∈ Metric.ball (0 : ℂ) c.radius := by
    have h := hσ₀
    rw [← hσe, mem_ball_zero_iff, pi_norm_const] at h
    rwa [mem_ball_zero_iff]
  have hB : Metric.ball (0 : ℂ) c.radius ∈ 𝓝 (σ₀ 0) := Metric.isOpen_ball.mem_nhds ht₀
  let f : ℂ → Fin n → ℂ := fun τ => c.toFun (e τ)
  have hfd : DifferentiableOn ℂ f (Metric.ball 0 c.radius) :=
    c.differentiableOn.comp he_diff.differentiableOn hBe
  have hfV : f ⁻¹' V ∈ 𝓝 (σ₀ 0) :=
    (hfd.continuousOn.continuousAt hB).preimage_mem_nhds (by
      show V ∈ 𝓝 (c.toFun (e (σ₀ 0)))
      rw [hσe]
      exact hV.mem_nhds hxV)
  let Δ : Set ℂ := Metric.ball 0 c.radius ∩ f ⁻¹' V
  have hΔ : Δ ∈ 𝓝 (σ₀ 0) := inter_mem hB hfV

  have hfg : ∀ τ ∈ Δ, f τ = g (A (f τ)) := by
    rintro τ ⟨hτB, hτV⟩
    have h : f τ ∈ zeroSet I ∩ V := ⟨c.mapsTo (hBe τ hτB), hτV⟩
    rw [hZV] at h
    obtain ⟨y, hy, hgy⟩ := h
    rw [← hgy, hAg y hy]
  let φ : ℂ → ℂ := fun τ => A (f τ)
  have hφ : AnalyticAt ℂ φ (σ₀ 0) := (A.differentiable.comp_differentiableOn hfd).analyticAt hB

  have hopen : φ '' Δ ∈ 𝓝 (φ (σ₀ 0)) := by
    rcases hφ.eventually_constant_or_nhds_le_map_nhds with hconst | hle
    · exfalso
      have hev : ∀ᶠ τ in 𝓝[≠] (σ₀ 0), (φ τ = φ (σ₀ 0) ∧ τ ∈ Δ) ∧ τ ≠ σ₀ 0 :=
        ((hconst.and hΔ).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
      obtain ⟨τ, ⟨hτφ, hτΔ⟩, hτne⟩ := hev.exists
      have h1 : f τ = f (σ₀ 0) := by
        calc f τ = g (φ τ) := hfg τ hτΔ
          _ = g (φ (σ₀ 0)) := by rw [hτφ]
          _ = f (σ₀ 0) := (hfg (σ₀ 0) (mem_of_mem_nhds hΔ)).symm
      exact hτne (he_inj (c.injOn (hBe τ hτΔ.1) (hBe _ ht₀) h1))
    · exact hle (Filter.image_mem_map hΔ)
  have hφx : φ (σ₀ 0) = A (c.toFun σ₀) := by
    show A (c.toFun (e (σ₀ 0))) = _
    rw [hσe]
  refine ⟨V ∩ A ⁻¹' (φ '' Δ), inter_mem (hV.mem_nhds hxV)
    (A.continuous.continuousAt.preimage_mem_nhds (hφx ▸ hopen)), ?_⟩
  rintro y ⟨hyZ, hyV, τ, hτΔ, hτy⟩
  have hy : y ∈ g '' O := hZV ▸ ⟨hyZ, hyV⟩
  obtain ⟨w, hw, rfl⟩ := hy
  refine ⟨e τ, hBe τ hτΔ.1, ?_⟩
  calc c.toFun (e τ) = f τ := rfl
    _ = g (φ τ) := hfg τ hτΔ
    _ = g w := by rw [hτy, hAg w hw]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

theorem PosPartSplit.proof : PosPartSplit.Statement := by
  classical
  intro n d J A f φ E y hA hE hcov
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartPosDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]

  set T : ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ := fun g x =>
    if h : ∃ s, IsSheetAt J A x s then
      max (g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y) 0 else 0 with hT
  have hT0 : ∀ g x, 0 ≤ T g x := fun g x => by
    simp only [hT]; split_ifs <;> simp
  have hpt : ∀ x ∈ hfin.toFinset,
      ENNReal.ofReal (T f x) = ∑' k, ENNReal.ofReal (T ((E k).indicator f) x) := by
    intro x hx
    have hx' : x ∈ fibre J A y := hfin.mem_toFinset.mp hx
    by_cases hs : ∃ s, IsSheetAt J A x s
    · obtain ⟨k₀, hk₀⟩ := hcov x hx' hs
      rw [tsum_eq_single k₀]
      · simp only [hT, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : x ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [hT, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [hT, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 f x), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 _ x)).symm

end

end GroundTheory.Heights₂.Heights
end
