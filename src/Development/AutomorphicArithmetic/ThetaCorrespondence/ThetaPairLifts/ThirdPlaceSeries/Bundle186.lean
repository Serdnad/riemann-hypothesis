module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle171
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
public import Development.AutomorphicArithmetic.ResidueCharacters.LenUnitInvariantsLe
public import Development.AutomorphicArithmetic.ResidueCharacters.LocAll
public import Development.AutomorphicArithmetic.ResidueCharacters.NumCost
import Development.AutomorphicArithmetic.ResidueCharacters.NumParameters
public import Development.AutomorphicArithmetic.ResidueCharacters.Bundle004
public import Development.AutomorphicArithmetic.ResidueCharacters.Bundle005
public import Development.AutomorphicArithmetic.ResidueCharacters.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle183
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AutomorphicArithmetic.ResidueCharacters.ExistsUnion

@[expose] public section

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem rowThreeAt_of_setup_alt (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    RowOnAt L X.ρ (fun l => l = 3 ∧ l ∉ D.host.small) 6000 30000 := by
  rintro i hTw ⟨h3, hs⟩ π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have h2 : D.nd.l i ≠ 2 := by omega
  have hq : D.nd.l i ≠ D.host.q := h3 ▸ (three_ne_q D).1
  have hd : D.nd.l i ≠ D.host.d := h3 ▸ (three_ne_q D).2
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k => h3 ▸ three_ne_g D k
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hle : D.nd.l i ≤ D.host.splitBound := by have := S.split; omega
  have hN : ¬ D.nd.l i ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small hl).1 h with h | h | h
    exacts [hs h, hq h, hd h]
  have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, D.host.cls_splitK_or_small hl hle hq hd,
    fun _ v hv => GlobalTheory.HubLoc.ramIdx_eq_one D.host hl hN v hv, hgk 0, hgk 1⟩
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 := D.host.split_small _ hl h2 hle
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (cycAt_of i fun e => absurd e h2) hL (decl_split D i h2 hj) (locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs0 : D.nd.s0 i = 1 := UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hs
  have hsl : D.nd.s0 i = RowSmall.sl D (D.nd.l i) := by
    unfold RowSmall.sl
    rw [hs0, Nat.factorization_eq_zero_of_not_dvd hN]; rfl
  have hh := h0_le D i dc.col (fun e => absurd e h2) hs0.ge (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine bound_smallPrime_of_splitBound_cyclotomic_of_level_eq L P X.ρ S.kill S.sha i hTw hsl π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
end UpperTheory.N
theorem UpperTheory.N.exists_nonneg_threeC_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.ThirdBoundCondition A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.rowThreeAt_of_setup_alt hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.onAt_eq_two_bounds_of_setup (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    UpperTheory.N.RowOnAt L X.ρ (fun l => l = 2) 6000 30000 := by
  intro i hTw h2 π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hs : D.nd.l i ∈ D.host.small := by rw [show D.nd.l i = 2 from h2]; exact UpperTheory.Small.two_mem D.host
  have h4 : 2 ^ 2 ∣ D.host.QS := (pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k e =>
    UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k) (e ▸ hs)
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, Or.inr hs, fun h => absurd hs h, hgk 0, hgk 1⟩
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (UpperTheory.N.cycAt_of i fun _ => (h4.mul_right _).mul_right _) hL (UpperTheory.N.Two.decl_split D i h2)
    (UpperTheory.N.locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs2 : 2 ≤ D.nd.s0 i := by
    rw [D.nd.restNLevelExponent_of_two i h2]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization D.host.QS_pos.ne').1 h4
  have hh := UpperTheory.N.h0_le D i dc.col (fun _ => hs2) (by omega) (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := UpperTheory.N.Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (UpperTheory.N.Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine UpperTheory.N.bound_smallPrime_of_splitBound_cyclotomic L P X.ρ S.kill S.sha i hTw hs π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
theorem UpperTheory.N.exists_nonneg_twoC_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.SecondBoundCondition A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.onAt_eq_two_bounds_of_setup hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.n_at_bounds_of_setup (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    UpperTheory.N.RowAt L X.ρ 6000 30000 := by
  intro i hTw hs h2 π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k e =>
    UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k) (e ▸ hs)
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hL : EmbeddingTypes.hypL i := ⟨by have := hl.two_le; omega, Or.inr hs, fun h => absurd hs h, hgk 0, hgk 1⟩
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 :=
    D.host.QS_split _ hl h2 (Nat.dvd_of_mem_primeFactors hs)
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (UpperTheory.N.cycAt_of i fun e => absurd e h2) hL (UpperTheory.N.decl_split D i h2 hj) (UpperTheory.N.locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs1 : 1 ≤ D.nd.s0 i := by rw [D.nd.restNLevelExponent_of_odd i h2]; exact le_max_left _ _
  have hh := UpperTheory.N.h0_le D i dc.col (fun e => absurd e h2) hs1 (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := UpperTheory.N.Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (UpperTheory.N.Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine UpperTheory.N.bound_smallPrime_of_splitBound_cyclotomic L P X.ρ S.kill S.sha i hTw hs π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
theorem UpperTheory.N.exists_nonneg_c_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.RowCAlt A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.n_at_bounds_of_setup hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end
