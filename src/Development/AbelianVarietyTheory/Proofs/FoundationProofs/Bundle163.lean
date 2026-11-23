module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle136
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle053
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeTo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle149
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle141
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle004
public import Mathlib.NumberTheory.Modular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_hasDivisorOfDegree_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N a : ℕ, 0 < a → a < N → mass g N (HasDiv g a) ≤ 7 / 8 := by
  first | exact @GlobalTheory.BadShare.mass_hasDiv_le | exact GlobalTheory.BadShare.mass_hasDiv_le | (intros; apply GlobalTheory.BadShare.mass_hasDiv_le <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem one_le_rk_of_not_sharp (g : ℕ) [Fact g.Prime] (N : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M) (hρ : IsGeneric ρ) (L : Lev g N)
    (hL : L.sharp = false) : 1 ≤ rk ρ L.e := by
  obtain ⟨L₀, h₀, x, hx, hu⟩ := hρ
  let L' : Lev g N := { L₀ with s := L.s, k := L.k, hk := L.hk }
  have hs : L'.sharp = false := h₀
  rw [GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape g N M ρ L L' (hL.trans hs.symm) rfl rfl]
  obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L'
  obtain ⟨-, -, -, h⟩ := GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ L'.Mem L'.chi a1 a2 a3 a4
  refine h 1 (fun _ => x) (linearIndependent_unique_iff.2 hx) ?_
  intro i u hm
  have hchi : L'.chi u = L₀.chi u := by
    simp only [Lev.chi, Lev.Edge, hs, h₀, Bool.false_eq_true, if_false]
    rfl
  rw [hchi]
  exact hu u hm.1

theorem rk_lower_of_sharp (g : ℕ) [Fact g.Prime] (N : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M) (hρ : IsGeneric ρ) (s : ℕ) :
    ∀ L : Lev g N, L.sharp = true → L.s = s → (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  induction s with
  | zero => exact fun L h1 h2 => GlobalTheory.T.levelDatum_idempotent_rank_ge_of_generic_free_rows_first g N M ρ hρ L h1 h2
  | succ s ih =>
    intro L h1 h2
    have hk : s + L.k < N := by have := L.hk; omega
    let L' : Lev g N := { L with s := s, hk := hk }
    have h3 := ih L' h1 rfl
    have h4 := GlobalTheory.T.levelDatum_idempotent_rank_le_root_exchange g N M ρ L L' h1 h1 rfl h2
    exact h3.trans (by exact_mod_cast h4)

theorem rk_lev_lower : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, (1 - 1 / (g : ℝ)) * (g : ℝ) ^ (if L.sharp = true then L.k else 0) ≤ (rk ρ L.e : ℝ) := by
  intro g _ N M _ _ _ ρ hρ L
  by_cases h : L.sharp = true
  · rw [if_pos h]
    exact rk_lower_of_sharp g N M ρ hρ L.s L h rfl
  · rw [if_neg h, pow_zero, mul_one]
    have h1 : (1 : ℝ) ≤ rk ρ L.e := by
      exact_mod_cast one_le_rk_of_not_sharp g N M ρ hρ L (by simpa using h)
    have h2 : (0 : ℝ) ≤ 1 / (g : ℝ) := by positivity
    linarith

end GlobalTheory.BadShare
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.exists_primitive_quotient_level_prime_to : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → ∃ (M' : ℕ) (a b : X.K) (c : Ω), 0 < M' ∧ Nat.Coprime q M' ∧ M₀ * l ^ k ∣ M' ∧ Lev X M' a ∧ Lev X M' b ∧ Prim X V a ∧ Prim X V b ∧ c ≠ 0 ∧ f * b = algebraMap Ω X.K c * a := by
  first | exact @GlobalTheory.KZ.ES.Quot.quot_prim | exact GlobalTheory.KZ.ES.Quot.quot_prim | (intros; apply GlobalTheory.KZ.ES.Quot.quot_prim <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.LevelField

theorem finiteDimensional_adjoin_restrict {F K : Type} [Field F] [Field K] [Algebra F K] (α : K)
    (L : IntermediateField (IntermediateField.adjoin F {α}) K)
    (hL : FiniteDimensional (IntermediateField.adjoin F {α}) L) (hα : α ∈ L.restrictScalars F) :
    FiniteDimensional (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) := by
  letI : Algebra (IntermediateField.adjoin F {α}) (L.restrictScalars F) :=
    inferInstanceAs (Algebra (IntermediateField.adjoin F {α}) L)
  haveI : Module.Finite (IntermediateField.adjoin F {α}) (L.restrictScalars F) := hL
  have hmap : (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map (L.restrictScalars F).val =
      IntermediateField.adjoin F {α} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin F {α},
      algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c ∈
        IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)} := by
    intro c
    have hc : (c : K) ∈ (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map
        (L.restrictScalars F).val := by rw [hmap]; exact c.2
    obtain ⟨y, hy, hyc⟩ := (IntermediateField.mem_map _).1 hc
    have e : algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c = y := Subtype.ext hyc.symm
    rw [e]
    exact hy
  letI : Algebra (IntermediateField.adjoin F {α}) (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) :=
    ((algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F)).codRestrict
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) hmem).toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin F {α})
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite (IntermediateField.adjoin F {α}) _ _


open GlobalTheory.FN.LevelGal in
theorem finiteDimensional_lvl {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (M : ℕ) (hM : 0 < M) :
    FiniteDimensional (IntermediateField.adjoin Ω {X.jK}) (lvl X M) := by
  let H := (rho X M).range
  haveI : Finite H := finite_range X M hM
  have hbot : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxF : (x : X.K) ∈ IntermediateField.adjoin Ω {X.jK} := by
      refine LevelOneFrac.mem_adjoin_of_sl_inv ε X hj x fun γ => ?_
      have h1 := congrArg Subtype.val (hx (rho X M γ⁻¹) ⟨γ⁻¹, rfl⟩)
      rw [rho_val, inv_inv] at h1
      exact h1
    rw [IntermediateField.mem_bot]
    exact ⟨⟨x, hxF⟩, Subtype.ext rfl⟩
  haveI hfd0 : FiniteDimensional (IntermediateField.fixedField H) (lvl X M) :=
    (inferInstance : FiniteDimensional (FixedPoints.subfield H (lvl X M)) (lvl X M))
  have : FiniteDimensional (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M) :=
    hbot ▸ hfd0
  exact Module.Finite.trans (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M)

theorem exists_level_field : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M →
    ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧
      ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := by
  intro Ω _ _ _ ε X _ hj M hM
  have hjL : X.jK ∈ (GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω := fun γ _ => X.j_inv γ
  exact ⟨(GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω, fun f => Iff.rfl, hjL,
    finiteDimensional_adjoin_restrict X.jK _ (finiteDimensional_lvl ε X hj M hM) hjL⟩

end GlobalTheory.KZ.LevelField
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

namespace GlobalTheory.Eis.ConvCover

theorem exists_int_near {F : Type} [Field F] {w : InfinitePlace F} (hw : w.IsReal)
    (N : ℕ) (t : w.Completion) (ht : ‖t‖ ≤ N) :
    ∃ n ∈ Finset.Icc (-(N : ℤ)) N, ‖t - (n : w.Completion)‖ ≤ 1 := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw
  set e := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw with he
  have hn : ∀ s, ‖e s‖ = ‖s‖ := fun s => hi.norm_map_of_map_zero (map_zero e) s
  rw [← hn, Real.norm_eq_abs, abs_le] at ht
  refine ⟨⌊e t⌋, Finset.mem_Icc.2 ⟨?_, ?_⟩, ?_⟩
  · rw [Int.le_floor]; push_cast; exact ht.1
  · have : (⌊e t⌋ : ℝ) ≤ ((N : ℤ) : ℝ) := by
      push_cast; exact (Int.floor_le _).trans ht.2
    exact_mod_cast this
  · rw [← hn, map_sub, map_intCast, Real.norm_eq_abs, abs_le]
    have h1 := Int.floor_le (e t)
    have h2 := Int.lt_floor_add_one (e t)
    constructor <;> linarith

theorem norm_two_pow_le {F : Type} [Field F] (w : InfinitePlace F) (m : ℕ) :
    ‖(2 : w.Completion) ^ m‖ ≤ 2 ^ m := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  rw [← hi.norm_map_of_map_zero (map_zero _), map_pow, map_ofNat, norm_pow]
  simp

theorem exists_cover : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ (Ω : Set (AF F)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C * ((2 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω := by
  intro F _ _ _
  classical
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have := GlobalTheory.AdeleCocompact.properSpace_completion F
  have hb : ∃ R : ℕ, ∀ k ∈ K, ∀ w : InfinitePlace F, ‖k.1 w‖ ≤ R := by
    have hc : Continuous fun k : AdeleRing (𝓞 F) F => ∑ w : InfinitePlace F, ‖k.1 w‖ :=
      continuous_finsetSum _ fun w _ => ((continuous_apply w).comp continuous_fst).norm
    obtain ⟨B, hB⟩ := (hK.image hc).bddAbove
    refine ⟨⌈B⌉₊, fun k hk w => ?_⟩
    refine le_trans ?_ ((hB ⟨k, hk, rfl⟩).trans (Nat.le_ceil B))
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => ‖k.1 w‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  obtain ⟨R, hR⟩ := hb
  let h : InfiniteAdeleRing F := algebraMap F (InfiniteAdeleRing F) 2⁻¹
  have h2 : h * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (InfiniteAdeleRing F)) 2, ← map_mul,
      inv_mul_cancel₀ two_ne_zero, map_one]
  let ι : (InfinitePlace F → ℤ) → InfiniteAdeleRing F := fun n w => (n w : w.Completion)
  refine ⟨((Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1 :
      Set (InfiniteAdeleRing F)) ×ˢ (Prod.snd '' K) :
        Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)),
    (2 * R + 1 : ℝ) ^ Fintype.card (InfinitePlace F),
    (isCompact_univ_pi fun v => isCompact_closedBall _ _).prod (hK.image continuous_snd),
    fun m => ?_⟩
  refine ⟨(Fintype.piFinset fun _ : InfinitePlace F =>
      Finset.Icc (-((2 ^ m * R : ℕ) : ℤ)) ((2 ^ m * R : ℕ) : ℤ)).image
      fun n => ((h ^ m * ι n, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F), ?_, fun a => ?_⟩
  · refine le_trans (Nat.cast_le.2 Finset.card_image_le) ?_
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm _ m,
      pow_mul, ← mul_pow, Nat.cast_pow]
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
    have hc : (Finset.Icc (-((2 ^ m * R : ℕ) : ℤ)) ((2 ^ m * R : ℕ) : ℤ)).card
        = 2 * (2 ^ m * R) + 1 := by
      rw [Int.card_Icc]; omega
    rw [hc]
    push_cast
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ one_le_two
    nlinarith
  · obtain ⟨x, hx⟩ := hKx a
    set k := a - algebraMap F (AdeleRing (𝓞 F) F) x with hk
    have hn : ∀ w : InfinitePlace F, ∃ n ∈ Finset.Icc (-((2 ^ m * R : ℕ) : ℤ)) ((2 ^ m * R : ℕ) : ℤ),
        ‖(2 : w.Completion) ^ m * k.1 w - (n : w.Completion)‖ ≤ 1 := fun w => by
      refine exists_int_near (IsTotallyReal.isReal w) _ _ ((norm_mul_le _ _).trans ?_)
      push_cast
      exact mul_le_mul (norm_two_pow_le w m) (hR k hx w) (norm_nonneg _) (by positivity)
    choose n hn1 hn2 using hn
    refine ⟨x, _, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hn1),
      ((2 ^ m * k.1 - ι n, k.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F),
      ⟨fun w _ => ?_, ⟨k, hx, rfl⟩⟩, ?_⟩
    · exact mem_closedBall_zero_iff.2 (hn2 w)
    · have ha : a = algebraMap F (AdeleRing (𝓞 F) F) x + k := by rw [hk]; ring
      refine ha.trans (Eq.trans (congrArg (algebraMap F (AF F) x + ·) ?_) (add_assoc (G := AF F) _ _ _).symm)
      refine Prod.ext ?_ ?_
      · change k.1 = h ^ m * ι n + h ^ m * (2 ^ m * k.1 - ι n)
        rw [← mul_add, add_sub_cancel, ← mul_assoc, ← mul_pow, h2, one_pow, one_mul]
      · change k.2 = 0 + 1 ^ m * k.2
        rw [one_pow, one_mul, zero_add]

end GlobalTheory.Eis.ConvCover
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

def constHom {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) : Ω →+* ring ε.range where
  toFun c := ⟨fun _ => ε c, mem_ring_of_inR ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).2 _ ⟨c, rfl⟩)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def evAt (E : Subring ℂ) (τ : ℍ) : ring E →+* ℂ := (Pi.evalRingHom (fun _ : ℍ => ℂ) τ).comp (ring E).subtype

theorem evAt_apply (E : Subring ℂ) (τ : ℍ) (x : ring E) : evAt E τ x = (x : ℍ → ℂ) τ := rfl

theorem evAt_comp_constHom {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (τ : ℍ) :
    (evAt ε.range τ).comp (constHom ε) = ε := by
  ext c; rfl

theorem io_comp_constHom {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Frac Ω ε) :
    T.io.comp (constHom ε) = algebraMap Ω T.K := by
  ext c; exact T.io_c c _ rfl

theorem isIntegral_io_adjoin_j (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (a : ring ε.range) (ha : (a : ℍ → ℂ) = jT) (b : ring ε.range) :
    IsIntegral (IntermediateField.adjoin Ω {T.io a}) (T.io b) := by
  set L := IntermediateField.adjoin Ω {T.io a}
  obtain ⟨n, c, hc, hrel⟩ := GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver ε.range b (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 b).1 b.2)
  have hl : ∀ i, c i ∈ Polynomial.lifts ε := fun i =>
    (Polynomial.lifts_iff_coeff_lifts _).2 fun k => RingHom.mem_range.1 (hc i k)
  choose d hd using fun i => (Polynomial.mem_lifts (c i)).1 (hl i)
  let xa : L := ⟨T.io a, IntermediateField.mem_adjoin_simple_self Ω _⟩
  let φ : Polynomial Ω →ₐ[Ω] L := Polynomial.aeval xa

  have hr : b ^ n + ∑ i, (d i).eval₂ (constHom ε) a * b ^ (i : ℕ) = 0 := by
    apply Subtype.ext; funext τ
    have h := hrel τ
    have key : evAt ε.range τ (b ^ n + ∑ i, (d i).eval₂ (constHom ε) a * b ^ (i : ℕ)) = 0 := by

      simp only [map_add (f := _), map_sum, map_mul, map_pow, Polynomial.hom_eval₂, evAt_comp_constHom,
      evAt_apply, ha]
      simpa [← Polynomial.eval_map, hd] using h
    simpa [evAt_apply] using key
  have hK : T.io b ^ n + ∑ i, Polynomial.aeval (T.io a) (d i) * T.io b ^ (i : ℕ) = 0 := by
    have := congrArg T.io hr

    simp only [map_add (f := _), map_sum, map_mul, map_pow, Polynomial.hom_eval₂, io_comp_constHom, map_zero] at this
    simpa [Polynomial.aeval_def] using this
  refine ⟨Polynomial.X ^ n + ∑ i, Polynomial.C (φ (d i)) * Polynomial.X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  have hφ : ∀ i, algebraMap L T.K (φ (d i)) = Polynomial.aeval (T.io a) (d i) := fun i => by
    show L.val (φ (d i)) = _
    rw [← Polynomial.aeval_algHom_apply L.val xa (d i)]
    rfl
  have hsum := map_sum (Polynomial.eval₂AddMonoidHom (algebraMap L T.K) (T.io b))
    (fun i => Polynomial.C (φ (d i)) * Polynomial.X ^ (i : ℕ)) Finset.univ
  change Polynomial.eval₂ (algebraMap L T.K) (T.io b) (∑ i, Polynomial.C (φ (d i)) * Polynomial.X ^ (i : ℕ)) = _ at hsum
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, hsum, Polynomial.eval₂AddMonoidHom_apply,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, hφ]
  exact hK

theorem frac_isAlgebraic_adjoin_j : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (a : GlobalTheory.FN.ring ε.range), (a : ℍ → ℂ) = jT → ∀ f : T.K, IsAlgebraic (IntermediateField.adjoin Ω {T.io a}) f := by
  intro Ω _ _ _ ε T a ha f
  obtain ⟨x, y, hy, hxy⟩ := T.io_surj f
  have hy' : T.io y ≠ 0 := fun h => hy (T.io_inj (h.trans (map_zero T.io).symm))
  have hf : f = T.io x * (T.io y)⁻¹ := by rw [← hxy, mul_inv_cancel_right₀ hy']
  rw [hf]
  exact (isIntegral_io_adjoin_j Ω ε T a ha x).isAlgebraic.mul (isIntegral_io_adjoin_j Ω ε T a ha y).isAlgebraic.inv

end GlobalTheory.FN
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.exists_dlog_derivations_towerLevel_mod_integral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m →
  ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq := by
  first | exact @GlobalTheory.LevDer.exists_levDer | exact GlobalTheory.LevDer.exists_levDer | (intros; apply GlobalTheory.LevDer.exists_levDer <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.towerLevelAdjoinRoots_integrallyClosed_quotient : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ a ∈ Lev T m, ∀ b ∈ Lev T m, b ≠ 0 →
  GlobalTheory.K5.IsInt (p := p) (a / b) → a / b ∈ Lev T m := by
  intro p _ Ω _ _ hΩ T m hm a ha b hb hb0 hint
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T m
  obtain ⟨-, hrange⟩ := GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hΩ T m hm ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
  rw [← hrange] at ha hb ⊢
  obtain ⟨a', rfl⟩ := (AlgHom.mem_range ι).1 ha
  obtain ⟨b', rfl⟩ := (AlgHom.mem_range ι).1 hb
  rcases ValuationRing.dvd_total b' a' with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine (AlgHom.mem_range ι).2 ⟨c, ?_⟩
    rw [hc, map_mul, mul_div_cancel_left₀ _ hb0]
  · have ha0 : ι a' ≠ 0 := by
      intro h
      apply hb0
      rw [hc, map_mul, h, zero_mul]
    have hz0 : ι a' / ι b' ≠ 0 := div_ne_zero ha0 hb0
    have hzi : (ι a' / ι b')⁻¹ = ι c := by
      rw [inv_div, hc, map_mul, mul_div_cancel_left₀ _ ha0]
    have hmem := GlobalTheory.K5.LevClosed.mem_adjoin_inv_of_isIntegral (R := O0 p) hz0 hint
    rw [hzi] at hmem
    have hle : Algebra.adjoin (O0 p) {ι c} ≤ ι.range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 ⟨c, rfl⟩)
    exact hle hmem
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory

theorem exists_tameGenAt_of_isPlaceOver :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)),
      IsPlaceOver A v → ∃ γ : G E Ω, TameGenAt A γ :=
  fun E Ω _ _ _ _ _ A v h => GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω v A h

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.tendsto_sum_Icc_inv_add_mul_eq_pi_div_mul_cot : ∀ (L : ℕ) (z : ℂ) (r : ℕ), 0 < L → 0 < z.im → Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹) atTop (𝓝 (π / L * Complex.cot (π * ((z + r) / L)))) := by
  first | exact @GlobalTheory.tendsto_sum_Icc_inv_residue_cot | exact GlobalTheory.tendsto_sum_Icc_inv_residue_cot | (intros; apply GlobalTheory.tendsto_sum_Icc_inv_residue_cot <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem finite_smul_mem_fd : ∀ τ : ℍ, {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd}.Finite := by
  intro τ
  have hP : {p : Fin 2 → ℤ | ¬ (2 * τ.im < Complex.normSq ((p 0 : ℂ) * τ + p 1))}.Finite :=
    Filter.eventually_cofinite.1
      ((ModularGroup.tendsto_normSq_coprime_pair τ).eventually_gt_atTop (2 * τ.im))
  have hrow : ∀ p : Fin 2 → ℤ, {γ : SL(2, ℤ) | γ 1 = p ∧ |(γ • τ).re| ≤ 1 / 2}.Finite := by
    intro p
    by_cases hp : IsCoprime (p 0) (p 1)
    · have h := Filter.eventually_cofinite.1
        ((ModularGroup.tendsto_abs_re_smul τ hp).eventually_gt_atTop (1 / 2 : ℝ))
      refine (h.image Subtype.val).subset ?_
      rintro γ ⟨h1, h2⟩
      exact ⟨⟨γ, h1⟩, not_lt.2 h2, rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro γ ⟨h1, -⟩
      exact hp (h1 ▸ ModularGroup.bottom_row_coprime γ)
  refine (hP.biUnion fun p _ => hrow p).subset ?_
  intro γ hγ
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  have hpos := (γ • τ).im_pos
  have hhalf : (1 : ℝ) / 2 ≤ (γ • τ).im := by nlinarith
  rw [ModularGroup.im_smul_eq_div_normSq, le_div_iff₀ (Complex.normSq_pos.2 (denom_ne_zero _ _))] at hhalf
  rw [Set.mem_iUnion₂]
  refine ⟨γ 1, ?_, rfl, hγ.2⟩
  simp only [Set.mem_setOf_eq, not_lt]
  simp [UpperHalfPlane.denom] at hhalf ⊢
  linarith

end GlobalTheory.EisM
end
