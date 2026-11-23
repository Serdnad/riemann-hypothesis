module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAuxiliaryPlacesSquarePatternsSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle057
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle061
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle055
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle046
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup {G : Type} [CommGroup G] (U W : Subgroup G) :
    W.index = W.relIndex U * (U ⊔ W).index := by
  rw [← Subgroup.relIndex_mul_index (le_sup_right : W ≤ U ⊔ W), Subgroup.relIndex_sup_right]

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.sqs_le_locSq (F : Type) [Field F] [NumberField F]
    (U : Subgroup Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    _root_.GlobalTheory.QNorm.sqs U ≤ _root_.GlobalTheory.QNorm.locSq F S := by
  intro x hx
  unfold _root_.GlobalTheory.QNorm.sqs at hx
  obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp hx
  unfold _root_.GlobalTheory.QNorm.locSq _root_.GlobalTheory.QNorm.finSq
  rw [Subgroup.mem_inf]
  simp only [Subgroup.mem_iInf, _root_.GlobalTheory.QNorm.mem_sqSub, powMonoidHom_apply,
    Units.val_pow_eq_pow_val, map_pow]
  exact ⟨fun v _ => ⟨_, sq _⟩, fun σ => ⟨_, sq _⟩⟩

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma eq_one_of_mul_self_eq_one_withZero (a : WithZero (Multiplicative ℤ))
    (h : a * a = 1) : a = 1 := by
  induction a using WithZero.recZeroCoe with
  | zero => simp at h
  | coe m =>
    have h1 : m * m = 1 := by exact_mod_cast h
    have h2 : Multiplicative.toAdd m + Multiplicative.toAdd m = 0 := by
      rw [← toAdd_mul, h1, toAdd_one]
    have h3 : Multiplicative.toAdd m = 0 := by omega
    have h4 : m = 1 := by rw [← ofAdd_toAdd m, h3, ofAdd_zero]
    rw [h4, WithZero.coe_one]

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.mem_sqs_sUnits_of_isSquare (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Fˣ) (hy : y ∈ _root_.GlobalTheory.QNorm.sUnits F S)
    (h : IsSquare (y : F)) : y ∈ _root_.GlobalTheory.QNorm.sqs (_root_.GlobalTheory.QNorm.sUnits F S) := by
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact y.ne_zero hs
  unfold _root_.GlobalTheory.QNorm.sqs
  refine Subgroup.mem_map.mpr ⟨Units.mk0 s hs0, ?_, ?_⟩
  · rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hy ⊢
    intro v hv
    have h1 := hy v hv
    rw [hs, map_mul] at h1
    exact eq_one_of_mul_self_eq_one_withZero _ h1
  · ext
    simp [hs, sq]

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma sqs_le_self {G : Type} [CommGroup G] (U : Subgroup G) :
    _root_.GlobalTheory.QNorm.sqs U ≤ U := by
  intro y hy
  unfold _root_.GlobalTheory.QNorm.sqs at hy
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
  rw [powMonoidHom_apply]
  exact U.pow_mem hs 2


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), _root_.GlobalTheory.QNorm.admitted F S → δ ∈ _root_.GlobalTheory.QNorm.sUnits F S → ¬ IsSquare (δ : F) → ∀ x ∈ _root_.GlobalTheory.QNorm.sUnits F S, x ∈ _root_.GlobalTheory.QNorm.locNorm F δ S → x ∈ _root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) := by
  intro F _ _ δ S hS hδ hns x hx hxN
  classical
  obtain ⟨T, hST, hcard, hδT, hpat⟩ :=
    _root_.GlobalTheory.QNorm.exists_auxiliary_places F δ S hS hδ hns
  have htop := _root_.GlobalTheory.QNorm.sUnits_union_sup_finSq_eq_top F S T hS hST hpat
  have hS' := hS.mono (Finset.subset_union_left (s₂ := T))
  have hUU : _root_.GlobalTheory.QNorm.sUnits F S ≤ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T) := by
    intro z hz
    rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hz ⊢
    intro v hv
    exact hz v (fun h => hv (Finset.mem_union_left _ h))
  have hsq_eq : _root_.GlobalTheory.QNorm.locSq F S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T) =
      _root_.GlobalTheory.QNorm.sqs (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) := by
    apply le_antisymm
    · rintro y ⟨hyL, hyU⟩
      exact _root_.GlobalTheory.QNorm.mem_sqs_sUnits_of_isSquare F _ y hyU
        (_root_.GlobalTheory.QNorm.isSquare_of_mem_locSq F S T hS htop y hyU hyL)
    · exact le_inf (_root_.GlobalTheory.QNorm.sqs_le_locSq F _ S) (sqs_le_self _)
  obtain ⟨hL0, hL⟩ := _root_.GlobalTheory.QNorm.index_locSq_le F S
  have hrel := _root_.GlobalTheory.QNorm.relIndex_sqs_sUnits F (S ∪ T)
  have hL' := _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.locSq F S)
  rw [← Subgroup.inf_relIndex_right, hsq_eq, hrel, Finset.card_union_of_disjoint hST] at hL'
  have hJ0 : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locSq F S).index ≠ 0 := by
    rw [hL'] at hL0
    exact right_ne_zero_of_mul hL0
  have hJ : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locSq F S).index ≤ 2 := by
    have h4 : (4 : ℕ) ^ (S.card + Fintype.card (InfinitePlace F)) =
        2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ]
      congr 1
      omega
    rw [hL', h4] at hL
    exact le_of_mul_le_mul_left hL (by positivity)
  have hLN : _root_.GlobalTheory.QNorm.locSq F S ≤ _root_.GlobalTheory.QNorm.locNorm F δ S := by
    intro y hy
    unfold _root_.GlobalTheory.QNorm.locSq _root_.GlobalTheory.QNorm.finSq at hy
    unfold _root_.GlobalTheory.QNorm.locNorm
    rw [Subgroup.mem_inf] at hy ⊢
    simp only [Subgroup.mem_iInf] at hy ⊢
    exact ⟨fun v hv => _root_.GlobalTheory.QNorm.sqSub_le_normSub _ _ (hy.1 v hv),
      fun σ => _root_.GlobalTheory.QNorm.sqSub_le_normSub _ _ (hy.2 σ)⟩
  haveI : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locSq F S).FiniteIndex :=
    ⟨hJ0⟩
  have hK : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locNorm F δ S).index ≤ 2 :=
    le_trans (Subgroup.index_antitone (sup_le_sup_left hLN _)) hJ
  obtain ⟨hR0, hR⟩ := _root_.GlobalTheory.QNorm.first_inequality_sUnits F δ (S ∪ T) hS' (hUU hδ) hns
  obtain ⟨-, hN⟩ := _root_.GlobalTheory.QNorm.two_pow_le_index_locNorm F (δ : F) S δ.ne_zero
  have hcnt : _root_.GlobalTheory.QNorm.tFin F δ (S ∪ T) = _root_.GlobalTheory.QNorm.tFin F δ S := by
    unfold _root_.GlobalTheory.QNorm.tFin
    congr 1
    ext v
    simp only [Set.mem_setOf_eq, Finset.mem_union]
    constructor
    · rintro ⟨hv | hv, h⟩
      · exact ⟨hv, h⟩
      · exact absurd (hδT v hv) h
    · rintro ⟨hv, h⟩
      exact ⟨Or.inl hv, h⟩
  have hNidx := _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.locNorm F δ S)
  have hGN := _root_.GlobalTheory.QNorm.normSub_id_le_locNorm F (δ : F) S
  have hRle : (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F)).relIndex
      (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) ≤
      (_root_.GlobalTheory.QNorm.locNorm F δ S).relIndex (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) := by
    have h2 : 2 * (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F)).relIndex
        (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) ≤
        (_root_.GlobalTheory.QNorm.locNorm F δ S).relIndex (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) * 2 := by
      calc _ ≤ _ := hR
        _ = 2 ^ (_root_.GlobalTheory.QNorm.tFin F δ S + _root_.GlobalTheory.QNorm.tReal F δ) := by rw [hcnt]
        _ ≤ _ := hN
        _ = _ := hNidx
        _ ≤ _ := Nat.mul_le_mul_left _ hK
    omega
  have hchain := Subgroup.relIndex_mul_relIndex
    (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.locNorm F δ S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) (inf_le_inf_right _ hGN) inf_le_right
  rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at hchain
  have hne : (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)).relIndex
      (_root_.GlobalTheory.QNorm.locNorm F δ S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hchain
    exact hR0 hchain.symm
  have hNpos := lt_of_lt_of_le (Nat.pos_of_ne_zero hR0) hRle
  have hone : (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)).relIndex
      (_root_.GlobalTheory.QNorm.locNorm F δ S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) = 1 := by
    have hle1 := hchain.le.trans hRle
    have h3 := le_of_mul_le_mul_right (hle1.trans (one_mul _).symm.le) hNpos
    omega
  exact (Subgroup.relIndex_eq_one.mp hone ⟨hxN, hUU hx⟩).1

end GlobalTheory.QNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_integral_split_idempotent_over_two : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (2 : 𝓞 D.host.F) ∈ v.asIdeal → ∃ e : Formalism.L2.Theta.AE D, e * e = e ∧ e * cA D e = 0 ∧ e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) ∧ ∃ α ∈ intAf D.host.F, ∃ β ∈ intAf D.host.F, ∃ ω : 𝓞 D.host.E, e = pairA D.host.F 0 α ⊗ₜ[D.host.F] (ω : D.host.E) + pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E) := by
  first | exact @GlobalTheory.SplitIdem.exists_split_idempotent | exact GlobalTheory.SplitIdem.exists_split_idempotent | (intros; apply GlobalTheory.SplitIdem.exists_split_idempotent <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.addChar_trivial_integralFiniteAdele_mul : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : F, (∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1) → ∀ α ∈ intAf F, ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := by
  first | exact @GlobalTheory.IntDense.addChar_eq_one_of_integral | exact GlobalTheory.IntDense.addChar_eq_one_of_integral | (intros; apply GlobalTheory.IntDense.addChar_eq_one_of_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.one_eq_sum_placeIdempotents_over_two_add_two_mul : ∀ (F : Type) [Field F] [NumberField F], ∃ P : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ P, (2 : 𝓞 F) ∈ v.asIdeal) ∧ (∀ v : HeightOneSpectrum (𝓞 F), singleV F v 1 ∈ intAf F ∧ evalV F v (singleV F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV F v' (singleV F v 1) = 0) ∧ ∃ β ∈ intAf F, (1 : Af F) = ∑ v ∈ P, singleV F v 1 + 2 * β := by
  first | exact @GlobalTheory.LatVac.one_eq_sum_singleV_add_two_mul | exact GlobalTheory.LatVac.one_eq_sum_singleV_add_two_mul | (intros; apply GlobalTheory.LatVac.one_eq_sum_singleV_add_two_mul <;> assumption)
end
