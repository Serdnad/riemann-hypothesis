module

public import Development.DiscreteGroups.GlobalIrreducibility.Bundle006
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Development.DiscreteGroups.GlobalIrreducibility.KmatMulKinv
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002

@[expose] public section

section

noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands ValuativeRel Filter Topology

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

def ballLe (r : ValueGroupWithZero k) : AddSubgroup k where
  carrier := {x | valuation k x ≤ r}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact ((valuation k).map_add a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa [Valuation.map_neg] using ha

def ballLt (γ : (ValueGroupWithZero k)ˣ) : AddSubgroup k where
  carrier := {x | valuation k x < γ}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact (valuation k).map_add_lt ha hb
  zero_mem' := by simp [Units.zero_lt]
  neg_mem' {a} ha := by simpa [Valuation.map_neg] using ha

theorem isOpen_ballLt (γ : (ValueGroupWithZero k)ˣ) : IsOpen ((ballLt γ : AddSubgroup k) : Set k) :=
  (ballLt γ).isOpen_of_mem_nhds (g := 0) ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun _ hx => hx⟩)

theorem psi_ball (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ γ : (ValueGroupWithZero k)ˣ, ∀ x : k, valuation k x < γ → ψ x = 1 := by
  have hU : {t : k | ‖((ψ t : Circle) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : k) := by
    have hc : Continuous fun t : k => ‖((ψ t : Circle) : ℂ) - 1‖ :=
      ((continuous_subtype_val.comp hψ).sub continuous_const).norm
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hU
  let H : Subgroup Circle :=
    { carrier := ψ '' {x | valuation k x < γ}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, (valuation k).map_add_lt ha hb, AddChar.map_add_eq_mul ψ a b⟩
      one_mem' := ⟨0, by simp [Units.zero_lt], AddChar.map_zero_eq_one ψ⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, by simpa [Valuation.map_neg] using ha, AddChar.map_neg_eq_inv ψ a⟩ }
  have hH := GroundTheory.Global.Circle.subgroup_eq_bot_of_norm_sub_one_lt H (by
    rintro _ ⟨a, ha, rfl⟩; exact hγ ha)
  refine ⟨γ, fun x hx => ?_⟩
  have : ψ x ∈ H := ⟨x, hx, rfl⟩
  rw [hH] at this
  exact Subgroup.mem_bot.1 this

theorem small_of_triv (ψ : AddChar k Circle) (y : k) (hy : ψ y ≠ 1) (γ : (ValueGroupWithZero k)ˣ) (b : k)
    (h : ∀ t : k, valuation k t ≤ valuation k y * ↑γ⁻¹ → ψ (b * t) = 1) : valuation k b < γ := by
  by_contra hb'
  have hb := not_lt.1 hb'
  have hb0 : (0 : ValueGroupWithZero k) < valuation k b := lt_of_lt_of_le (Units.zero_lt γ) hb
  have hb0' : b ≠ 0 := fun h0 => by simp [h0] at hb0
  apply hy
  have e : b * (y / b) = y := by field_simp
  rw [← e]
  refine h _ ?_
  rw [map_div₀, div_eq_mul_inv, Units.val_inv_eq_inv_val]
  gcongr (valuation k y) * ?_
  exact (inv_le_inv₀ hb0 (Units.zero_lt γ)).2 hb

theorem continuous_U (c : Fin (m + 1)) : Continuous (fun x : Fin (m + 1) → k => U c x) := by
  have hc : ∀ x' : (Fin (m + 1) → k) → (Fin (m + 1) → k), Continuous x' →
      Continuous fun x => colM c (x' x) := by
    intro x' hx'
    refine continuous_const.add (continuous_matrix fun p q => ?_)
    by_cases h : q = c ∧ p < c
    · simp only [Matrix.of_apply, if_pos h]; exact (continuous_apply p).comp hx'
    · simp only [Matrix.of_apply, if_neg h]; exact continuous_const
  exact Units.continuous_iff.2 ⟨hc id continuous_id, hc (fun x => -x) continuous_neg⟩

end DiscreteGroups.sglob.LConvKir
end
end

section

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands ValuativeRel Filter Topology

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem continuous_Kmat (jj : Fin (m + 1)) :
    Continuous (Kmat jj : (Fin (m + 1) → k) → Matrix (Fin (m + 1)) (Fin (m + 1)) k) :=
  continuous_matrix fun p q => by
    by_cases hp : p = jj
    · simp only [Kmat, Matrix.of_apply, if_pos hp]; exact continuous_apply q
    · simp only [Kmat, Matrix.of_apply, if_neg hp]; exact continuous_const

theorem continuous_Kinv2 (jj : Fin (m + 1)) :
    Continuous (Kinv2 jj : (Fin (m + 1) → k) × k → Matrix (Fin (m + 1)) (Fin (m + 1)) k) :=
  continuous_matrix fun p q => by
    by_cases hp : p = jj
    · by_cases hq : q = jj
      · simp only [Kinv2, Matrix.of_apply, if_pos hp, if_pos hq]; exact continuous_snd
      · simp only [Kinv2, Matrix.of_apply, if_pos hp, if_neg hq]
        exact ((continuous_apply q).comp continuous_fst).neg.mul continuous_snd
    · simp only [Kinv2, Matrix.of_apply, if_neg hp]; exact continuous_const

theorem kappa_nbhd (S : Set (GL (Fin (m + 1)) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin (m + 1)) k) ∈ S)
    (jj : Fin (m + 1)) : ∃ γ : (ValueGroupWithZero k)ˣ, ∀ a : Fin (m + 1) → k,
      (∀ i, valuation k (a i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) < γ) →
      ∃ κ : GL (Fin (m + 1)) k, κ ∈ S ∧ (κ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = Kmat jj a ∧
        ((κ⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = Kinv jj a := by
  obtain ⟨O, hO, hOS⟩ := Units.isInducing_embedProduct.isOpen_iff.1 hS
  let H : (Fin (m + 1) → k) → Matrix (Fin (m + 1)) (Fin (m + 1)) k × (Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵐᵒᵖ :=
    fun a => (Kmat jj a, MulOpposite.op (Kinv jj a))
  have hee : (Pi.single jj (1 : k) : Fin (m + 1) → k) jj = 1 := by simp
  have hHc : ContinuousAt H (Pi.single jj 1) := by
    have hinv : ContinuousAt (fun a : Fin (m + 1) → k => (a jj)⁻¹) (Pi.single jj 1) := by
      have h0 : (Pi.single jj (1 : k) : Fin (m + 1) → k) jj ≠ 0 := by rw [hee]; exact one_ne_zero
      exact ((continuous_apply jj).continuousAt (x := Pi.single jj 1)).inv₀ h0
    exact (continuous_Kmat jj).continuousAt.prodMk (MulOpposite.continuous_op.continuousAt.comp
      ((continuous_Kinv2 jj).continuousAt.comp (continuousAt_id.prodMk hinv)))
  have hHe : H (Pi.single jj 1) ∈ O := by
    have h1' : (1 : GL (Fin (m + 1)) k) ∈ (Units.embedProduct (Matrix (Fin (m + 1)) (Fin (m + 1)) k)) ⁻¹' O := by
      rw [hOS]; exact h1
    have hH1 : H (Pi.single jj 1) = Units.embedProduct _ (1 : GL (Fin (m + 1)) k) := by
      simp only [H, Units.embedProduct_apply, Units.val_one, inv_one, Kmat_single, Kinv_single]
    rw [hH1]; exact h1'
  have hcomp : ContinuousAt (fun b : Fin (m + 1) → k => H (Pi.single jj 1 + b)) 0 :=
    hHc.comp_of_eq ((continuous_const.add continuous_id).continuousAt) (by simp)
  have hN := hcomp.preimage_mem_nhds (hO.mem_nhds (by show H (Pi.single jj 1 + 0) ∈ O; rw [add_zero]; exact hHe))
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hT : (⋂ i, t i) ∩ {x : k | valuation k x < ((1 : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)} ∈ 𝓝 (0 : k) :=
    Filter.inter_mem (Filter.iInter_mem.2 ht) ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun _ hx => hx⟩)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hT
  refine ⟨γ, fun a ha => ?_⟩
  have hb : ∀ i, a i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i ∈
      (⋂ i, t i) ∩ {x : k | valuation k x < ((1 : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)} :=
    fun i => hγ (ha i)
  have hmem : H a ∈ O := by
    have := hIt (a := a - Pi.single jj 1) (fun i _ => Set.mem_iInter.1 (hb i).1 i)
    simpa using this
  have haj : a jj ≠ 0 := by
    intro h0
    have h2 := (hb jj).2
    simp [h0] at h2
  refine ⟨⟨Kmat jj a, Kinv jj a, Kmat_mul_Kinv jj a haj, Kinv_mul_Kmat jj a haj⟩, ?_, rfl, rfl⟩
  rw [← hOS]
  show Units.embedProduct _ _ ∈ O
  rw [Units.embedProduct_apply]
  exact hmem

end DiscreteGroups.sglob.LConvKir
end
end
