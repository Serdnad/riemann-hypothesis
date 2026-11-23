module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle116
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle117
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle118
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEmbeddedDataWithGivenFixedLattice
public import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantOrderCommonFixedLatticeEmbeddedData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
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
public import Mathlib.Data.Set.Card.Arithmetic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.fixedLattice_inf_eq_and_pairing_of_isometry : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), ∀ p ∈ Trip H g L₀ j x x', fixLat p.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) = fixLat p.2.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) ∧ ∀ y ∈ fixLat p.1.2, ∀ y' ∈ fixLat p.2.1.2, ∃ t : 𝓞 K, H.B y (y' - p.2.2 y') = (g : K) * (t : K) := by
  first | exact @GlobalTheory.DegCnt.trip_fixLat_inf_eq_and_pairing | exact GlobalTheory.DegCnt.trip_fixLat_inf_eq_and_pairing | (intros; apply GlobalTheory.DegCnt.trip_fixLat_inf_eq_and_pairing <;> assumption)
end

section

noncomputable section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.FirstPattern

def front (N k s : ℕ) (h : k + s ≤ N) : Equiv.Perm (Fin N) where
  toFun a := ⟨if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a, by
    have := a.2; split_ifs <;> omega⟩
  invFun a := ⟨if (a : ℕ) < s then k + a else if (a : ℕ) < k + s then a - s else a, by
    have := a.2; split_ifs <;> omega⟩
  left_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega

theorem front_val (N k s : ℕ) (h : k + s ≤ N) (a : Fin N) :
    ((front N k s h a : Fin N) : ℕ) = if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a := rfl

theorem phI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    phI k s 0 (front N k s h a) (front N k s h b) ↔ (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) := by
  simp only [phI, IsW, Fin.lt_def, front_val]
  split_ifs <;> omega

theorem eeI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    eeI k s (front N k s h a) (front N k s h b) ↔ (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k := by
  simp only [eeI, IsW, front_val]
  split_ifs <;> omega

theorem eDat_congr (g N : ℕ) [NeZero g] (P P' : Mt g N → Prop) (φ φ' : Mt g N → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (hP : ∀ M, P M ↔ P' M) (hφ : ∀ M, P' M → φ M = φ' M) :
    eDat g N P φ ψ = eDat g N P' φ' ψ := by
  obtain rfl : P = P' := funext fun M => propext (hP M)
  unfold eDat
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [hφ _ (Finset.mem_filter.1 hu).2]

theorem inPat_iff {g : ℕ} [Fact g.Prime] (N k : ℕ) (hk : k < N) (M : Mt g N) :
    InPat (fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k)) M ↔
      IsUniUp M ∧ ∀ a, a < k → entN M a k = 0 := by
  constructor
  · intro h
    refine ⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun a ha => ?_⟩
    · have hab' : (b : ℕ) < a := hab
      rw [h a b (by omega), Matrix.one_apply_ne hab.ne']
    · subst hab
      rw [h a a (by omega), Matrix.one_apply_eq]
    · have haN : a < N := by omega
      rw [entN, dite_eq_left ⟨haN, hk⟩, h _ _ (by simp [ha]), Matrix.one_apply_ne]
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
  · rintro ⟨hU, hz⟩ a b hab
    rcases lt_trichotomy a b with h | h | h
    · have h' : (a : ℕ) < b := h
      have h2 : (a : ℕ) < k ∧ (b : ℕ) = k := by
        by_contra hh
        exact hab ⟨h', hh⟩
      have := hz a h2.1
      rw [entN, dite_eq_left ⟨a.2, hk⟩] at this
      have hb : b = ⟨k, hk⟩ := Fin.ext h2.2
      rw [Matrix.one_apply_ne h.ne, hb]
      exact this
    · rw [(hU a b).2 h, h, Matrix.one_apply_eq]
    · rw [(hU a b).1 h, Matrix.one_apply_ne h.ne']

theorem sumAt_eq {g : ℕ} [Fact g.Prime] (N k : ℕ) (M : Mt g N) (hz : ∀ a, a < k → entN M a k = 0) :
    sumAt (fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) M =
      ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) := by
  have h1 : ∀ a : Fin N, (∑ b : Fin N, if ((b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) then M a b else 0) =
      entN M a (a + 1) := by
    intro a
    by_cases ha : (a : ℕ) + 1 < N
    · rw [Finset.sum_eq_single (⟨a + 1, ha⟩ : Fin N)]
      · by_cases hk : (a : ℕ) + 1 = k
        · rw [if_neg (by simp [hk]), hk, hz a (by omega)]
        · rw [if_pos (by simp [hk]), entN, dite_eq_left ⟨a.2, ha⟩]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨e, -⟩
        exact hb (Fin.ext e)
      · simp
    · rw [entN, dite_eq_right (by omega)]
      refine Finset.sum_eq_zero fun b _ => if_neg ?_
      have := b.2
      omega
  have h2 : ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) = ∑ i ∈ Finset.range N, entN M i (i + 1) := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun i _ hi => ?_
    rw [Finset.mem_range] at hi
    rw [entN, dite_eq_right (by omega)]
  rw [h2, Finset.sum_range, sumAt]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← h1 a]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr

theorem tr_first_pattern : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N k s : ℕ), N = k + 2 * s + 1 →
    ∀ χ : Gn g N → ℂ, IsClass χ → tr (ePat g N (phI k s 0) (eeI k s) ψ) χ = tr (eJ' g N k ψ) χ := by
  intro g _ ψ N k s hN χ hχ
  have h : k + s ≤ N := by omega
  rw [← GlobalTheory.GLm.tr_ePat_renumber g ψ N (phI k s 0) (eeI k s) (front N k s h) χ hχ]
  congr 1
  have e1 : (fun a b => phI k s 0 (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) :=
    funext fun a => funext fun b => propext (phI_front N k s h a b)
  have e2 : (fun a b => eeI k s (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k :=
    funext fun a => funext fun b => propext (eeI_front N k s h a b)
  rw [e1, e2, ePat, eJ']
  exact eDat_congr g N _ _ _ _ ψ (inPat_iff N k (by omega)) fun M hM => sumAt_eq N k M hM.2

end GlobalTheory.GLm.FirstPattern
end
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ) (h : Gn g i), i ≤ n → der ψ i F h = ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * ∑ x : Gn g n, if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
  first | exact @GlobalTheory.GLm.der_eq_sum | exact GlobalTheory.GLm.der_eq_sum | (intros; apply GlobalTheory.GLm.der_eq_sum <;> assumption)
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.patternGroup_subgroup_order_character : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ) (Φ : Fin N → Fin N → Prop), (∀ a, ¬ Φ a a) → (∀ a b c, Φ a b → Φ b c → Φ a c) → (∃ H : Subgroup (Gn g N), (∀ x, x ∈ H ↔ InPat Φ (x : Mt g N)) ∧ Nat.card H = g ^ (Finset.univ.filter fun p : Fin N × Fin N => Φ p.1 p.2).card) ∧ (∀ M : Mt g N, InPat Φ M → IsUnit M) ∧ ∀ E : Fin N → Fin N → Prop, (∀ a b c, Φ a b → Φ b c → ¬ E a c) → (∀ a, ¬ E a a) → ∀ M M' : Mt g N, InPat Φ M → InPat Φ M' → sumAt E (M * M') = sumAt E M + sumAt E M' := by
  first | exact @GlobalTheory.GLm.Pattern.pattern_group | exact GlobalTheory.GLm.Pattern.pattern_group | (intros; apply GlobalTheory.GLm.Pattern.pattern_group <;> assumption)
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.isClassFunction_bernsteinZelevinskyDerivative : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ), i < n → IsMirClass F → IsClass (der ψ i F) := by
  first | exact @GlobalTheory.GLm.DerClass.isClass_der | exact GlobalTheory.GLm.DerClass.isClass_der | (intros; apply GlobalTheory.GLm.DerClass.isClass_der <;> assumption)
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.isMirabolicConjInvariant_twistedTailMeanFun : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (m n : ℕ) (F : Gn g n → ℂ), 1 ≤ m → m ≤ n → IsMirClass F → IsMirClass (tail ψ m F) := by
  first | exact @GlobalTheory.GLm.TailClass.isMirClass_tail | exact GlobalTheory.GLm.TailClass.isMirClass_tail | (intros; apply GlobalTheory.GLm.TailClass.isMirClass_tail <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.encard_lattices_near_reference_lattice_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ → ((({P : Submodule (𝓞 K) V | 𝔪 • N.P0 ≤ P ∧ 𝔪 • P ≤ N.P0}).encard : ℕ∞) : ℝ≥0∞) ≤ (Ideal.absNorm 𝔪 : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.NearCount.main | exact GlobalTheory.DegCnt.NearCount.main | (intros; apply GlobalTheory.DegCnt.NearCount.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.card_embeddedData_with_given_fixedLattice : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (La : Submodule (𝓞 K) V) (x : ℕ), ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞) ≤ ((x : ℝ≥0∞) * D₀) ^ (3 * (2 * j + 1)) := by
  first | exact @GlobalTheory.DegCnt.DatCount.main | exact GlobalTheory.DegCnt.DatCount.main | (intros; apply GlobalTheory.DegCnt.DatCount.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem finrank_sub_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) L ≤ Module.finrank K V := by
  apply Module.finrank_le_of_rank_le
  apply rank_le
  intro s hs
  have h := hs.map' L.subtype (Submodule.ker_subtype L)
  rw [LinearIndependent.iff_fractionRing (R := 𝓞 K) (K := K)] at h
  simpa using h.fintype_card_le_finrank

theorem sublat_count {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG) (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.Finite ∧
      (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ) ≤
        (x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) L := inferInstance
  have : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K L x hx
  have hsub : {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x} ⊆
      (Submodule.map L.subtype) '' {N : Submodule (𝓞 K) L | N.toAddSubgroup.index = x} := by
    rintro N ⟨hN, hi⟩
    refine ⟨N.comap L.subtype, ?_, ?_⟩
    · exact hi
    · rw [Submodule.map_comap_subtype, inf_eq_right.2 hN]
  refine ⟨(h1.image _).subset hsub, ?_⟩
  have h3 := (Set.ncard_le_ncard hsub (h1.image _)).trans (Set.ncard_image_le h1)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x Module.finrank_pos hx
  have h5 : ((Module.finrank (𝓞 K) L : ℕ) : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast finrank_sub_le L
  calc (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ)
      ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ Module.finrank (𝓞 K) L := by
        exact_mod_cast h3.trans h2
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) L :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ (((Module.finrank (𝓞 K) L : ℕ) : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)

theorem encard_isDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ x : ℕ, 1 ≤ x → ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) * ((x : ℝ) * D₀) ^ (3 * (2 * j + 1))) := by
  intro K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x hx
  have hfib := GlobalTheory.DegCnt.DatCount.main K V H hK hP L₀ g j D₀ hL hD hG hg
  obtain ⟨hfin, hcnt⟩ := sublat_count L₀ hL.1.fg x hx
  set S := {N : Submodule (𝓞 K) V | N ≤ L₀ ∧ idx L₀ N = x} with hS
  have hsub : {d | IsDat H g L₀ j x d} ⊆
      ⋃ La ∈ hfin.toFinset, {d | IsDat H g L₀ j x d ∧ fixLat d.2 = La} := by
    intro d hd
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
    refine ⟨fixLat d.2, ⟨?_, hd.2.2.2.1⟩, hd, rfl⟩
    intro y hy
    exact (hd.2.2.1.1 hy).2
  have h1 := (Set.encard_le_encard hsub).trans (Finset.set_encard_biUnion_le _ _)
  have h2 : ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤
      ∑ La ∈ hfin.toFinset, ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞) := by
    refine (ENat.toENNReal_le.2 h1).trans (le_of_eq ?_)
    exact map_sum ENat.toENNRealRingHom _ _
  refine h2.trans ((Finset.sum_le_card_nsmul _ _ _ fun La _ => hfib La x).trans ?_)
  rw [nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  gcongr
  rw [← ENNReal.ofReal_natCast, ← Set.ncard_eq_toFinset_card S hfin]
  exact ENNReal.ofReal_le_ofReal hcnt

end GlobalTheory.DegCnt
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ s ∈ N.R, N.IsTerm g (s • Λ) ∧ N.SameDat g Λ (s • Λ) ∧ latTh N.F N.F' (s • Λ) = latTh N.F N.F' Λ ∧ N.bI (s • Λ) = N.bI Λ := by
  first | exact @GlobalTheory.DegCnt.StabInv.main | exact GlobalTheory.DegCnt.StabInv.main | (intros; apply GlobalTheory.DegCnt.StabInv.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ∀ p ∈ Trip H g L₀ j x x', (GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (fixSp p.2.2)) (GlobalTheory.Mass.latIn (fixSp p.2.2) (fixLat p.1.2)) : ℝ) ≤ (2 / (g : ℝ)) ^ (2 * ((Module.finrank K V) - Module.finrank K (fixSp p.2.2)) * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' := by
  first | exact @GlobalTheory.DegCnt.FixDisc.main | exact GlobalTheory.DegCnt.FixDisc.main | (intros; apply GlobalTheory.DegCnt.FixDisc.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_star_stable_ideal_absorbing_minors : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔠 : Ideal (𝓞 K), (Ideal.absNorm 𝔠 : ℝ) ≤ (N.Db * N.NT) ^ 2 ∧ 1 ≤ N.Db ∧ 1 ≤ N.Del ∧ ∀ Q : Prop, (𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → Q) → Q := by
  first | exact @GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal | exact GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal | (intros; apply GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal <;> assumption)
end
