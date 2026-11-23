module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableSetPreSingleton
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFunctionEquivalence
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GLVolumeIndex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Std.Tactic.BVDecide.Normalize.BitVec
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

open Matrix


theorem _root_.GlobalTheory.T.oneParamUnitaryMatrix_eq_exp_lieAlgebra : ∀ {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ), Continuous u → u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) → ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  first | exact @GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | exact GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | (intros; apply GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU <;> assumption)
end

section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainStepIdentities

theorem volAdd_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (r : ℕ) :
    volAdd ν r = ∏ i ∈ Finset.Icc 1 r, (zetaAt (resCard k) i)⁻¹ := by
  have := hν.1
  have h := GlobalTheory.IndexVolume.volumeOfGL ν hν.2 (Fin r)
  have hS : (Units.val '' (KO k (Fin r) : Set (GL (Fin r) k)) : Set (Matrix (Fin r) (Fin r) k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.groupSet (⊤ : Subgroup (GL (Fin r) 𝒪[k])) := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, trivial, rfl⟩
    · rintro ⟨g, -, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, rfl⟩
  have e : volAdd ν r = GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.volGroup ν (⊤ : Subgroup (GL (Fin r) 𝒪[k])) := by
    unfold volAdd GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.volGroup
    rw [hS]
    rfl
  rw [e, h, Fintype.card_fin, Formalism.MainNotions.ZetaProductPairs.qE]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [zetaAt, GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.resCard, resCard, _root_.zpow_neg, _root_.zpow_natCast]

end GlobalTheory.ChainStepIdentities
end
end

section

open Formalism.L2.Theta

namespace GlobalTheory.WordSep

open GlobalTheory.SignedHC

private theorem v_le {G : GridData} {i j : ℕ} (hi : 2 ≤ i) (hij : i ≤ j) (hj : j ≤ G.k) : G.v j ≤ G.v i := by
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (G.v_anti i j hi h hj).le

private theorem b_ge {G : GridData} {l : ℕ} (hl : 1 ≤ l) (hlm : l ≤ G.m) : G.b 1 ≤ G.b l := by
  rcases hl.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (G.b_mono 1 l le_rfl h hlm).le

theorem sep_rat {G : GridData} (hga : 0 < G.ga)
    (hgap : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) (hb : 2 ≤ G.v G.k + G.b 1)
    {x y : ℚ} (hx : (∃ l, l ≤ G.m ∧ x = G.a l) ∨ ∃ j, 2 ≤ j ∧ j ≤ G.k ∧ x = G.vHalf j)
    (hy : (∃ j, 2 ≤ j ∧ j ≤ G.k ∧ y = G.v j) ∨ ∃ l, 1 ≤ l ∧ l ≤ G.m ∧ y = -(G.b l : ℚ)) :
    (y < x → y + 1 < x) ∧ x ≠ y := by
  have hk := G.two_le_k
  rcases hx with ⟨l, hl, rfl⟩ | ⟨j, hj2, hjk, rfl⟩
  · have hal : (G.v 2 : ℚ) + 3 / 2 ≤ G.a l := by
      unfold GridData.a
      have h1 : (1 : ℚ) ≤ (G.m : ℚ) + 1 - l := by
        have : (l : ℚ) ≤ G.m := by exact_mod_cast hl
        linarith
      have h2 : (1 : ℚ) ≤ G.ga := by exact_mod_cast hga
      nlinarith
    obtain ⟨z, hz, hzle⟩ : ∃ z : ℤ, y = z ∧ z ≤ G.v 2 := by
      rcases hy with ⟨j, hj2, hjk, rfl⟩ | ⟨l', hl1, hlm, rfl⟩
      · exact ⟨_, rfl, v_le le_rfl hj2 hjk⟩
      · refine ⟨-G.b l', by push_cast; ring, ?_⟩
        have := b_ge (G := G) hl1 hlm
        have := v_le (G := G) le_rfl hk le_rfl
        linarith
    have : (z : ℚ) ≤ G.v 2 := by exact_mod_cast hzle
    subst hz
    constructor
    · intro _; linarith
    · intro h; linarith
  · obtain ⟨z, hz, hzc⟩ : ∃ z : ℤ, y = z ∧ (G.v j ≤ z ∨ z ≤ G.v j - 2) := by
      rcases hy with ⟨j', hj2', hjk', rfl⟩ | ⟨l', hl1, hlm, rfl⟩
      · refine ⟨_, rfl, ?_⟩
        rcases le_or_gt j' j with h | h
        · exact Or.inl (v_le hj2' h hjk)
        · right
          have h1 := v_le (G := G) (by omega : 2 ≤ j + 1) (by omega : j + 1 ≤ j') hjk'
          have h2 := hgap j hj2 (by omega)
          linarith
      · refine ⟨-G.b l', by push_cast; ring, Or.inr ?_⟩
        have := b_ge (G := G) hl1 hlm
        have := v_le (G := G) hj2 hjk le_rfl
        linarith
    subst hz
    unfold GridData.vHalf
    rcases hzc with h | h
    · have : (G.v j : ℚ) ≤ z := by exact_mod_cast h
      constructor
      · intro h'; linarith
      · intro h'; linarith
    · have : (z : ℚ) ≤ G.v j - 2 := by exact_mod_cast h
      constructor
      · intro _; linarith
      · intro h'; linarith

theorem word_sep : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) →
    2 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' →
    (∀ a i, mu i < lam a → mu i + 1 < lam a) ∧ ∀ a i, lam a ≠ mu i := by
  rintro G n lam ε mu ε' hga hgap hb ⟨-, q, hq, hS⟩ ⟨-, q', hq', hT⟩
  have key : ∀ a i, (q' i < q a → q' i + 1 < q a) ∧ q a ≠ q' i := by
    intro a i
    have ha : (q a, ε a) ∈ G.lam := by
      rw [← G.parPi_zero, hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    have hi : (q' i, ε' i) ∈ G.parD0 := by
      rw [hT]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    refine sep_rat hga hgap hb ?_ ?_
    · rcases GridData.mem_lam.1 ha with ⟨l, hl, e⟩ | ⟨h, -⟩
      · exact Or.inl ⟨l, hl, (Prod.ext_iff.1 e).1⟩
      · exact Or.inr (GridData.mem_cloudHalf.1 h)
    · rcases GridData.mem_discrete_parameter_iff.1 hi with ⟨h, -⟩ | ⟨l, h1, h2, e⟩
      · exact Or.inl (GridData.mem_cloud.1 h)
      · exact Or.inr ⟨l, h1, h2, (Prod.ext_iff.1 e).1⟩
  refine ⟨fun a i h => ?_, fun a i h => ?_⟩
  · rw [hq, hq'] at h ⊢
    have := (key a i).1 (by exact_mod_cast h)
    exact_mod_cast this
  · rw [hq, hq'] at h
    exact (key a i).2 (by exact_mod_cast h)

end GlobalTheory.WordSep
end

section

open Formalism.L2.Theta

namespace GlobalTheory.SignedHC.GridData

theorem v_bounds_of_mem (G : GridData) {i : ℕ} (h2 : 2 ≤ i) (hk : i ≤ G.k) : G.v G.k ≤ G.v i ∧ G.v i ≤ G.v 2 := by
  constructor
  · rcases eq_or_lt_of_le hk with h | h
    · rw [h]
    · exact le_of_lt (G.v_anti i G.k h2 h le_rfl)
  · rcases eq_or_lt_of_le h2 with h | h
    · rw [← h]
    · exact le_of_lt (G.v_anti 2 i le_rfl h hk)

theorem b_bounds_of_mem (G : GridData) {l : ℕ} (h1 : 1 ≤ l) (hm : l ≤ G.m) : G.b 1 ≤ G.b l ∧ G.b l ≤ G.b G.m := by
  constructor
  · rcases eq_or_lt_of_le h1 with h | h
    · rw [← h]
    · exact le_of_lt (G.b_mono 1 l le_rfl h hm)
  · rcases eq_or_lt_of_le hm with h | h
    · rw [h]
    · exact le_of_lt (G.b_mono l G.m h1 h le_rfl)

theorem abs_le_a_zero_of_mem_lam (G : GridData) (hv : 0 ≤ G.v G.k) {x : ℚ × Bool} (hx : x ∈ G.lam) :
    |x.1| ≤ G.a 0 := by
  have hv2 : (0 : ℚ) ≤ G.v 2 := by
    have := (G.v_bounds_of_mem le_rfl G.two_le_k).1
    exact_mod_cast hv.trans this
  have hga : (0 : ℚ) ≤ G.ga := by positivity
  rcases G.mem_lam.1 hx with ⟨l, hl, rfl⟩ | ⟨hc, -⟩
  · have e := G.a_sub_a 0 l
    simp only [Nat.cast_zero, sub_zero] at e
    have hm := G.a_m
    have e2 := G.a_sub_a l G.m
    have hl' : (l : ℚ) ≤ G.m := by exact_mod_cast hl
    have hl0 : (0 : ℚ) ≤ l := by positivity
    have h1 : (0 : ℚ) ≤ (l : ℚ) * G.ga := mul_nonneg hl0 hga
    have h2 : (0 : ℚ) ≤ ((G.m : ℚ) - l) * G.ga := mul_nonneg (by linarith) hga
    simp only
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨i, h2, hk, e⟩ := G.mem_cloudHalf.1 hc
    obtain ⟨hlo, hhi⟩ := G.v_bounds_of_mem h2 hk
    have hlo' : (0 : ℚ) ≤ G.v i := by exact_mod_cast hv.trans hlo
    have hhi' : (G.v i : ℚ) ≤ G.v 2 := by exact_mod_cast hhi
    have ha0 : G.a 0 = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1) * G.ga := by simp [a]
    have h3 : (0 : ℚ) ≤ ((G.m : ℚ) + 1) * G.ga := by positivity
    rw [e, vHalf, abs_le]; constructor <;> linarith

theorem abs_le_of_mem_D0 (G : GridData) (hv : 0 ≤ G.v G.k) (hb : 0 < G.b 1) {x : ℚ × Bool} (hx : x ∈ G.parD0) :
    |x.1| ≤ G.a 0 ∨ |x.1| ≤ G.b G.m := by
  rcases G.mem_discrete_parameter_iff.1 hx with ⟨hc, -⟩ | ⟨l, h1, hm, rfl⟩
  · left
    obtain ⟨i, h2, hk, e⟩ := G.mem_cloud.1 hc
    obtain ⟨hlo, hhi⟩ := G.v_bounds_of_mem h2 hk
    have hlo' : (0 : ℚ) ≤ G.v i := by exact_mod_cast hv.trans hlo
    have hhi' : (G.v i : ℚ) ≤ G.v 2 := by exact_mod_cast hhi
    have ha0 : G.a 0 = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1) * G.ga := by simp [a]
    have h3 : (0 : ℚ) ≤ ((G.m : ℚ) + 1) * G.ga := by positivity
    rw [e, abs_le]; constructor <;> linarith
  · right
    obtain ⟨hlo, hhi⟩ := G.b_bounds_of_mem h1 hm
    have hlo' : (0 : ℚ) < G.b l := by exact_mod_cast hb.trans_le hlo
    have hhi' : (G.b l : ℚ) ≤ G.b G.m := by exact_mod_cast hhi
    simp only
    rw [abs_le]; constructor <;> linarith

end GlobalTheory.SignedHC.GridData

namespace GlobalTheory.Twist

open GlobalTheory.SignedHC

theorem parPi_parD0_entries_bounded : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ}
    {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {B : ℝ}, 0 ≤ G.v G.k → 0 < G.b 1 →
    ((G.a 0 : ℚ) : ℝ) ≤ B → (G.b G.m : ℝ) ≤ B → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' →
    (∀ a, |lam a| ≤ B) ∧ ∀ i, |mu i| ≤ B := by
  intro G n lam ε mu ε' B hv hb hA hBm hP hD
  obtain ⟨-, q, hq, hS⟩ := hP
  obtain ⟨-, q', hq', hS'⟩ := hD
  constructor
  · intro a
    have hmem : (q a, ε a) ∈ G.lam := by
      rw [← G.parPi_zero, hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    have h := G.abs_le_a_zero_of_mem_lam hv hmem
    rw [hq a]
    have h' : |((q a : ℚ) : ℝ)| ≤ ((G.a 0 : ℚ) : ℝ) := by rw [← Rat.cast_abs]; exact_mod_cast h
    exact h'.trans hA
  · intro i
    have hmem : (q' i, ε' i) ∈ G.parD0 := by
      rw [hS']; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rw [hq' i]
    rcases G.abs_le_of_mem_D0 hv hb hmem with h | h
    · have h' : |((q' i : ℚ) : ℝ)| ≤ ((G.a 0 : ℚ) : ℝ) := by rw [← Rat.cast_abs]; exact_mod_cast h
      exact h'.trans hA
    · have h' : |((q' i : ℚ) : ℝ)| ≤ ((G.b G.m : ℤ) : ℝ) := by
        rw [← Rat.cast_abs]
        have : ((G.b G.m : ℤ) : ℝ) = (((G.b G.m : ℤ) : ℚ) : ℝ) := by push_cast; rfl
        rw [this]; exact_mod_cast h
      exact h'.trans hBm

end GlobalTheory.Twist
end

section

open Formalism.L2.Theta

namespace GlobalTheory.SignedHC

open Finset

theorem card_minus_of_isEnum {n : ℕ} {S : Finset (ℚ × Bool)} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    (univ.filter fun a => ε a = false).card = nMinus S := by
  obtain ⟨hanti, f, hf, rfl⟩ := h
  have hinj : Function.Injective f := fun a b h => hanti.injective (by rw [hf, hf, h])
  rw [nMinus, filter_image, card_image_of_injective _ fun a b h => hinj (congrArg Prod.fst h)]

namespace GridData

theorem nMinus_lam_of_even (G : GridData) (hm : Even G.m) (hg : 0 < G.ga) : nMinus G.lam = G.m / 2 := by
  obtain ⟨k, hk⟩ := hm
  have hS : G.lam.filter (fun x => x.2 = false) = (range k).image fun j => (G.a (2 * j + 1), false) := by
    ext x
    simp only [mem_filter, mem_lam, mem_image, mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩ | ⟨-, h⟩, h2⟩
      · simp only [decide_eq_false_iff_not, Nat.not_even_iff] at h2
        refine ⟨i / 2, by omega, ?_⟩
        have e : 2 * (i / 2) + 1 = i := by omega
        have : ¬ Even (G.m - i) := by rw [Nat.not_even_iff]; exact h2
        simp [e, this]
      · simp [h] at h2
    · rintro ⟨j, hj, rfl⟩
      have : ¬ Even (G.m - (2 * j + 1)) := by rw [Nat.not_even_iff]; omega
      exact ⟨Or.inl ⟨2 * j + 1, by omega, by simp [this]⟩, rfl⟩
  rw [nMinus, hS, card_image_of_injective, card_range]
  · omega
  · intro i j h
    have h1 : G.a (2 * i + 1) = G.a (2 * j + 1) := congrArg Prod.fst h
    have h2 := G.a_sub_a (2 * i + 1) (2 * j + 1)
    rw [h1, sub_self] at h2
    have hg' : (G.ga : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2.symm).resolve_right hg')
    have h4 : 2 * j + 1 = 2 * i + 1 := by exact_mod_cast h3
    omega

theorem minus_signs_of_D0_eq_half (G : GridData) : nMinus G.parD0 = G.m / 2 := by
  have hS : G.parD0.filter (fun x => x.2 = false) =
      (range (G.m / 2)).image fun j => (-(G.b (2 * j + 2) : ℚ), false) := by
    ext x
    simp only [mem_filter, mem_discrete_parameter_iff, mem_image, mem_range]
    constructor
    · rintro ⟨⟨-, h⟩ | ⟨i, hi, hi', rfl⟩, h2⟩
      · simp [h] at h2
      · simp only [decide_eq_false_iff_not, Nat.not_even_iff] at h2
        refine ⟨i / 2 - 1, by omega, ?_⟩
        have e : 2 * (i / 2 - 1) + 2 = i := by omega
        have : ¬ Even (i - 1) := by rw [Nat.not_even_iff]; exact h2
        simp [e, this]
    · rintro ⟨j, hj, rfl⟩
      have : ¬ Even (2 * j + 2 - 1) := by rw [Nat.not_even_iff]; omega
      exact ⟨Or.inr ⟨2 * j + 2, by omega, by omega, by rw [decide_eq_false this]⟩, rfl⟩
  rw [nMinus, hS, card_image_of_injOn, card_range]
  intro i hi j hj h
  have h1 : -(G.b (2 * i + 2) : ℚ) = -(G.b (2 * j + 2) : ℚ) := congrArg Prod.fst h
  have h2 : G.b (2 * i + 2) = G.b (2 * j + 2) := by exact_mod_cast neg_injective h1
  have hi' : i < G.m / 2 := by simpa using hi
  have hj' : j < G.m / 2 := by simpa using hj
  rcases lt_trichotomy i j with hl | hl | hl
  · have := G.b_mono (2 * i + 2) (2 * j + 2) (by omega) (by omega) (by omega); omega
  · exact hl
  · have := G.b_mono (2 * j + 2) (2 * i + 2) (by omega) (by omega) (by omega); omega

theorem card_minus_signs_interlacing_parameters {G : GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool} (hm : Even G.m) (hg : 0 < G.ga) (h1 : IsEnum (G.parPi 0) lam ε)
    (h2 : IsEnum G.parD0 mu ε') :
    (Finset.univ.filter fun a => ε a = false).card = G.m / 2 ∧
      (Finset.univ.filter fun i => ε' i = false).card = G.m / 2 :=
  ⟨by rw [card_minus_of_isEnum h1, G.parPi_zero, G.nMinus_lam_of_even hm hg],
    by rw [card_minus_of_isEnum h2, G.minus_signs_of_D0_eq_half]⟩

end GridData

end GlobalTheory.SignedHC
end

section

open Formalism.L2.Theta

namespace GlobalTheory.HCEnum

open GlobalTheory.SignedHC GlobalTheory.SignedHC.GridData

theorem isHCParam_parPi_zero_parD0 : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ}
    {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.k → Even G.m → n + 1 = G.k + G.m →
    IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.IsHCParam mu := by
  intro G n lam ε mu ε' hk hm hn hl hmu
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  have hkR : (G.k : ℝ) = k' + k' := by rw [hk']; push_cast; ring
  have hmR : (G.m : ℝ) = m' + m' := by rw [hm']; push_cast; ring
  have hnR : (n : ℝ) = (G.k : ℝ) + G.m - 1 := by
    have : ((n + 1 : ℕ) : ℝ) = ((G.k + G.m : ℕ) : ℝ) := by rw [hn]
    push_cast at this; linarith
  refine ⟨⟨hl.1, fun a => ?_⟩, ⟨hmu.1, fun a => ?_⟩⟩
  · obtain ⟨-, q, hq, hS⟩ := hl
    have hmem : (q a, ε a) ∈ G.parPi 0 := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [parPi_zero, mem_lam] at hmem
    rw [hq a]
    rcases hmem with ⟨i, -, he⟩ | ⟨hc, -⟩
    · have e : q a = G.a i := congrArg Prod.fst he
      refine ⟨G.v 2 + ((G.m : ℤ) + 1 - i) * G.ga + 1 - (k' + m'), ?_⟩
      rw [e]; simp only [GridData.a]; push_cast; rw [hnR, hkR, hmR]; ring
    · obtain ⟨i, -, -, hx⟩ := mem_cloudHalf.1 hc
      simp only at hx
      refine ⟨G.v i - (k' + m'), ?_⟩
      rw [hx]; simp only [vHalf]; push_cast; rw [hnR, hkR, hmR]; ring
  · obtain ⟨-, q, hq, hS⟩ := hmu
    have hmem : (q a, ε' a) ∈ G.parD0 := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [mem_discrete_parameter_iff] at hmem
    rw [hq a]
    rcases hmem with ⟨hc, -⟩ | ⟨l, -, -, he⟩
    · obtain ⟨i, -, -, hx⟩ := mem_cloud.1 hc
      simp only at hx
      refine ⟨G.v i - (k' + m' - 1), ?_⟩
      rw [hx]; push_cast; rw [hnR, hkR, hmR]; ring
    · have e : q a = -(G.b l : ℚ) := congrArg Prod.fst he
      refine ⟨-G.b l - (k' + m' - 1), ?_⟩
      rw [e]; push_cast; rw [hnR, hkR, hmR]; ring

end GlobalTheory.HCEnum
end

section

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.Exponents

theorem nonempty_piTensor_detRep_equiv (R β : Type) [CommRing R] [Fintype β] (c : β → Type)
    [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) :
    Nonempty ((piTensor fun j => detRep (c j) (χ j)).Equiv (ofChar (leviChar c χ))) := by
  classical
  refine ⟨LocGL.equivOfBijective
    ⟨(PiTensorProduct.constantBaseRingEquiv β ℂ).toLinearMap, fun g => ?_⟩
    (PiTensorProduct.constantBaseRingEquiv β ℂ).bijective⟩
  ext x
  simp [leviChar_apply, detRep, Finset.prod_mul_distrib]

end GlobalTheory.SmGL.Exponents
end
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.lowest_K_type_function_equivalence : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : W →ₗᵢ[ℂ] V), LowData ε E (lowK ε lam) u j → TauTie ε E j τ → FunEquiv ε E j (ps ε lam τ w) := by
  first | exact @GlobalTheory.SphJet.PsEquivar.psFunEquiv | exact GlobalTheory.SphJet.PsEquivar.psFunEquiv | (intros; apply GlobalTheory.SphJet.PsEquivar.psFunEquiv <;> assumption)
end

section

open Formalism.L2.Ker MvPolynomial

theorem _root_.GlobalTheory.T.blockAction_diagonal_coefficientSpace_smul : ∀ {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ) (Q : Formalism.L2.DIV.Pol ℂ ι n), Q ∈ Formalism.L2.DIV.VV ℂ lam → Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q = (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  first | exact @GlobalTheory.blockAct_diag_mem_VV | exact GlobalTheory.blockAct_diag_mem_VV | (intros; apply GlobalTheory.blockAct_diag_mem_VV <;> assumption)
end
