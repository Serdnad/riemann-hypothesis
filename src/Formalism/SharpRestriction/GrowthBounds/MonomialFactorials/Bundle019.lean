module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle015
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundOfDualFamilies
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle017
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.EpsilonBoundMConstant
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem thresholds_mono_normalized {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, 1 ≤ C0 → 2 ≤ CYb → 0 ≤ CD → 1 ≤ Cb → 0 ≤ CE1 → 0 ≤ CE2 →
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : TransportedAlt P) : TransportedAlt Q := by
  unfold Formalism.MainNotions.flipOneThree.TransportedAlt at hP ⊢
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨max T0 1, lt_max_of_lt_left hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 (le_trans (le_max_left _ _) hC0)
  refine ⟨T1, hT1, fun CE1 CE2 hE1 hE2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 hE1 hE2
  refine ⟨max T2 2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb hY hde hk hD hb => ?_⟩
  have hT2' : T2 ≤ max T2 2 := le_max_left _ _
  have h2' : (2 : ℝ) ≤ max T2 2 := le_max_right _ _
  have h1' : (1 : ℝ) ≤ max T0 1 := le_max_right _ _
  exact h C0 CYb Cde Ck CD Cb CE1 CE2 Cc (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
    (h2 CYb Cde Ck CD Cb (hT2'.trans hY) (hT2'.trans hde) (hT2'.trans hk) (hT2'.trans hD) (hT2'.trans hb))

def RestOpen4 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestPlusA C0 CE1 CE2 X CM ∧ RestPlusB C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X

def RestOpen4E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen4 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem openE_of_open4 (D : Formalism.BasicNotions.D7) (h : RestOpen4E D) : RestOpenE D := by
  obtain ⟨CM, hCM, hTM⟩ := restTM_closed
  exact thresholds_mono_normalized (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hC0 hY hD hb h1 h2 hP Ckap Cs =>
    ⟨CM, by linarith, fun X hA hH => by
      obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
      have hY0 : (0 : ℝ) < X.L.Y := by linarith [hH.1.1]
      exact ⟨block_bound_of_dual_families C0 CE1 CE2 X (block_valuation_over_Zp_holds C0 CE1 CE2 X (by linarith) h1 h2 hH) a,
        restPlus_of CM hY0 b (restRankL_proved C0 CE1 CE2 X) c,
        hTM D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hY hb hD hC0 h1 h2 hH, d⟩⟩) h

theorem closed_of_open_directions (D : Formalism.BasicNotions.D7) (h : RestOpen4E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_conditions D (openE_of_open4 D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

def OrthMin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) → (∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) →
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x

def SplitRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (L L' : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (x : MvPolynomial σ ℚ_[p]),
    FiniteDimensional ℚ_[p] W → (∀ y ∈ L, y ∈ W) → L.FG → L' ≤ L → x ∈ L → x ≠ 0 →
    Submodule.span ℤ_[p] {x} ⊔ L' = L → (∀ (c : ℤ_[p]) (y : MvPolynomial σ ℚ_[p]), y ∈ L' → c • x + y = 0 → c = 0) →
    Module.finrank ℤ_[p] L' < Module.finrank ℤ_[p] L

theorem zsmul_eq' {p : ℕ} [Fact p.Prime] {σ : Type} (c : ℤ_[p]) (u : MvPolynomial σ ℚ_[p]) :
    c • u = (c : ℚ_[p]) • u := rfl

theorem orthSplit_of (hM : OrthMin) (hR : SplitRank) : OrthSplit := by
  intro p _ σ B L W hp hW hLW hfg hsm hadd hsym hne
  obtain ⟨x, hxL, hxx, hdiv⟩ := hM p σ B L W hp hW hLW hfg hsm hadd hsym hne
  have hB0 : ∀ v, B 0 v = 0 := by
    intro v
    have h := hsm 0 0 v
    rwa [zero_smul, zero_mul] at h
  have hsub : ∀ u v w, B (u - v) w = B u w - B v w := by
    intro u v w
    have h := hadd (u - v) v w
    rw [sub_add_cancel] at h
    rw [h]
    ring
  let K : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]) :=
    { carrier := {u | u ∈ L ∧ B u x = 0}
      add_mem' := fun {u v} hu hv => ⟨L.add_mem hu.1 hv.1, by rw [hadd, hu.2, hv.2, add_zero]⟩
      zero_mem' := ⟨L.zero_mem, hB0 x⟩
      smul_mem' := fun c u hu => ⟨L.smul_mem c hu.1, by
        rw [zsmul_eq' c u, hsm, hu.2, mul_zero]⟩ }
  have hKL : K ≤ L := fun u hu => hu.1
  have hx0 : x ≠ 0 := by
    intro h
    apply hxx
    rw [h, hB0]
  have hdirect : ∀ (c : ℤ_[p]) (y : MvPolynomial σ ℚ_[p]), y ∈ K → c • x + y = 0 → c = 0 := by
    intro c y hy hcy
    have h1 : B (c • x + y) x = 0 := by
      rw [hcy, hB0]
    rw [hadd, zsmul_eq' c x, hsm, hy.2, add_zero] at h1
    have h2 : (c : ℚ_[p]) = 0 := (mul_eq_zero.mp h1).resolve_right hxx
    first
    | exact PadicInt.coe_eq_zero.mp h2
    | exact Subtype.ext h2
  have hsup : Submodule.span ℤ_[p] {x} ⊔ K = L := by
    apply le_antisymm
    · exact sup_le ((Submodule.span_le).mpr (Set.singleton_subset_iff.mpr hxL)) hKL
    · intro u hu
      obtain ⟨c, hc⟩ := hdiv u hu
      refine Submodule.mem_sup.mpr ⟨c • x, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩, u - c • x, ⟨?_, ?_⟩, ?_⟩
      · exact L.sub_mem hu (L.smul_mem c hxL)
      · rw [hsub, zsmul_eq' c x, hsm, hc, sub_self]
      · abel
  refine ⟨x, hxL, K, hKL, hfg.of_le hKL, hR p σ L K W x hW hLW hfg hKL hxL hx0 hsup hdirect, ?_, hsup, hdirect⟩
  intro u hu
  rw [hsym x hxL u hu.1]
  exact hu.2

theorem splitRank_proved : SplitRank := by
  intro p _ σ L L' W x hW hLW hfg hL'L hxL hx0 hsup hdirect
  haveI : NoZeroSMulDivisors ℤ_[p] (MvPolynomial σ ℚ_[p]) := by
    constructor
    intro c y h
    rw [zsmul_eq'] at h
    rcases smul_eq_zero.mp h with h | h
    · left
      first
      | exact PadicInt.coe_eq_zero.mp h
      | exact Subtype.ext h
    · right
      exact h
  haveI : Module.Finite ℤ_[p] L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ_[p] L' := Module.Finite.iff_fg.mpr (hfg.of_le hL'L)
  haveI : Module.Free ℤ_[p] L' := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free ℤ_[p] L := Module.free_of_finite_type_torsion_free'
  let f : (ℤ_[p] × L') →ₗ[ℤ_[p]] L :=
    { toFun := fun q => ⟨q.1 • x + (q.2 : MvPolynomial σ ℚ_[p]), L.add_mem (L.smul_mem _ hxL) (hL'L q.2.2)⟩
      map_add' := fun q q' => by
        apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
        abel
      map_smul' := fun c q => by
        apply Subtype.ext
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply, smul_add,
          mul_smul] }
  have hbij : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨c, y⟩ hq
      have h1 : c • x + (y : MvPolynomial σ ℚ_[p]) = 0 := congrArg Subtype.val hq
      have hc : c = 0 := hdirect c y y.2 h1
      subst hc
      rw [zero_smul, zero_add] at h1
      exact Prod.ext rfl (Subtype.ext h1)
    · rintro ⟨u, hu⟩
      rw [← hsup] at hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact ⟨(c, ⟨b, hb⟩), rfl⟩
  have he := (LinearEquiv.ofBijective f hbij).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at he
  omega

theorem orthSplit_of_min (hM : OrthMin) : OrthSplit := by
  exact orthSplit_of hM splitRank_proved

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
