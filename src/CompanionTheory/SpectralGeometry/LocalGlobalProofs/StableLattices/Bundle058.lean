module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.NonemptyRepresentations.TypeExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionIsGlRepresentation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.NonemptyRepresentations.NonemptyOfAntitone
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle057
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.KHighestExists

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P CompanionTheory.D.Inhab CompanionTheory.D.DSIC

theorem gl_exists (n : ℕ) (ν : Fin n → ℤ) (hν : Antitone ν) :
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : FiniteDimensional ℂ U)
      (E : Fin n → Fin n → Module.End ℂ U) (u : U),
      GlRel E ∧ (∀ a b x y, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ) ∧ u ≠ 0 ∧ IsHW E (fun a => (ν a : ℂ)) u := by
  obtain ⟨R⟩ := HWRep.nonempty_of_antitone ν hν
  obtain ⟨hz, h1⟩ := base_vector_exists n 0
  have hT : 0 < Tz n 0 (bvec (wI n 0 (Fin.last n))) := by rw [h1]; exact one_pos
  obtain ⟨B, hB⟩ := Qx8.frame_exists hz hT
  have hπ := TypeExists.πR_isRepW R hz hT hB
  exact ⟨EuclideanSpace ℂ R.I, inferInstance, inferInstance, inferInstance, EB (TypeExists.πR R B) B,
    WithLp.toLp 2 R.v0, (frame_general_linear _ n 0 n _ _ B hπ hB).1,
    Formalism.FourierDecayAlt.P5.Kfp.EB_adj hπ.1 hπ.2 (TypeExists.πR_unitary R hz hT hB) hB,
    fun h => R.v0_ne (congrArg WithLp.ofLp h), TypeExists.isHW_πR R hz hT hB⟩

theorem reorder (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℤ) (hγ : ∀ c d, c < d → ε c = ε d → γ d ≤ γ c) :
    ∃ (σ : Fin n ≃ Fin n) (N : ℤ), (∀ c d, c < d → ε c = ε d → σ.symm c < σ.symm d) ∧
      Antitone fun i => γ (σ i) + if ε (σ i) then N else 0 := by
  let f : Fin n → ℕ := fun c => if ε c then (c : ℕ) else n + c
  have hm : Monotone (f ∘ Tuple.sort f) := Tuple.monotone_sort f
  have hb : ∀ c, |γ c| ≤ ∑ d, |γ d| := fun c =>
    Finset.single_le_sum (f := fun d => |γ d|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c)
  refine ⟨Tuple.sort f, 2 * ∑ d, |γ d|, fun c d hcd he => ?_, fun i j hij => ?_⟩
  · by_contra h
    have := hm (not_lt.1 h)
    simp only [Function.comp, Equiv.apply_symm_apply, f, he] at this
    split_ifs at this <;> omega
  · have h := hm hij
    simp only [Function.comp, f] at h
    show γ (Tuple.sort f j) + _ ≤ γ (Tuple.sort f i) + _
    generalize Tuple.sort f i = a at *
    generalize Tuple.sort f j = b at *
    have ha := abs_le.1 (hb a)
    have hb' := abs_le.1 (hb b)
    have key : ε a = ε b → (a : ℕ) ≤ b → γ b ≤ γ a := fun he hab => by
      rcases (show a ≤ b from hab).lt_or_eq with h | h
      · exact hγ a b h he
      · rw [h]
    have := b.2
    cases h1 : ε a <;> cases h2 : ε b <;> simp only [h1, h2] at h key ⊢ <;> simp at h ⊢
    · exact key trivial h
    · omega
    · linarith [ha.1, hb'.2]
    · exact key trivial h

theorem khwExists : CompanionTheory.D.DSIC.KHWExists := by
  intro n ε γ hγ
  obtain ⟨σ, N, hσ, hν⟩ := reorder n ε γ hγ
  obtain ⟨U, _, _, _, E, u, hgl, hadj, hu, hw⟩ := gl_exists n _ hν
  let s : Fin n → ℤ := fun c => if ε c then N else 0
  refine ⟨U, inferInstance, inferInstance, inferInstance,
    fun c d => E (σ.symm c) (σ.symm d) - (if c = d then (s c : ℂ) else 0) • 1, u, ?_, ?_, hu, ?_, ?_⟩
  · intro a b c d hab _
    have h := hgl (σ.symm a) (σ.symm b) (σ.symm c) (σ.symm d)
    simp only [EmbeddingLike.apply_eq_iff_eq] at h
    have e : ∀ (X Y : Module.End ℂ U) (p q : ℂ),
        (X - p • 1) * (Y - q • 1) - (Y - q • 1) * (X - p • 1) = X * Y - Y * X := by
      intro X Y p q
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_smul]
      module
    show (_ - _ • 1) * (_ - _ • 1) - (_ - _ • 1) * (_ - _ • 1) = _
    rw [e, h]
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2
      have : s d = s b := by simp only [s, hab]
      simp [this]
    · simp [h1, h2, Ne.symm h2]
    · simp [h1, h2, Ne.symm h1]
    · simp [h1, h2]
  · intro a b _ x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, hadj]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro a
    have h := hw.1 (σ.symm a)
    simp only [Equiv.apply_symm_apply] at h
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h, if_true, s, ← sub_smul]
    congr 1
    push_cast
    ring
  · intro a b hab he
    simp [hw.2 _ _ (hσ a b hab he), hab.ne]

end GlobalTheory.CompanionTheory.KHighestExists
end
end

section

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.TopU

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_app (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    ann i x B = if i ∈ B then 0 else CompanionTheory.D.LK.sg i B • x (insert i B) := rfl

theorem cre_app (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    cre i x B = if i ∈ B then CompanionTheory.D.LK.sg i B • x (B.erase i) else 0 := rfl

theorem sg_erase (i : Pos n) (B : Finset (Pos n)) : CompanionTheory.D.LK.sg i (B.erase i) = CompanionTheory.D.LK.sg i B := by
  unfold CompanionTheory.D.LK.sg
  congr 2
  ext j
  simp only [mem_filter, mem_erase]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · exact fun h => ⟨⟨fun e => by subst e; exact lt_irrefl _ h.2, h.1⟩, h.2⟩

theorem sg_sq (i : Pos n) (B : Finset (Pos n)) : CompanionTheory.D.LK.sg i B * CompanionTheory.D.LK.sg i B = 1 := by
  unfold CompanionTheory.D.LK.sg; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem cre_ann (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    cre i (ann i x) B = if i ∈ B then x B else 0 := by
  rw [cre_app]
  split_ifs with h
  · rw [ann_app, if_neg (notMem_erase i B), insert_erase h, sg_erase, smul_smul, sg_sq, one_smul]
  · rfl

theorem adC_self (a : Fin n) (i k : Pos n) :
    adC a a i k = if k = i then ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) else 0 := by
  unfold adC
  have e1 : (a = i.1.1 ∧ k.1 = (a, i.1.2)) ↔ (k = i ∧ i.1.1 = a) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext (h2.trans (Prod.ext h1 rfl)), h1.symm⟩
    · rintro ⟨rfl, h⟩; exact ⟨h.symm, Prod.ext h rfl⟩
  have e2 : (i.1.2 = a ∧ k.1 = (i.1.1, a)) ↔ (k = i ∧ i.1.2 = a) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext (h2.trans (Prod.ext rfl h1.symm)), h1⟩
    · rintro ⟨rfl, h⟩; exact ⟨h, Prod.ext rfl h⟩
  simp only [e1, e2]
  by_cases hk : k = i <;> simp [hk]

theorem adL_self_apply (a : Fin n) (x : Cn n V) (B : Finset (Pos n)) :
    adL a a x B = ∑ i : Pos n, (((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ)) •
      cre i (ann i x) B := by
  simp only [adL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, Module.End.mul_apply,
    adC_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem top_cycle_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), Monotone lev → KHighest ε E γ u →
    bd (allT n) E (Pi.single (omU ε lev) u) = 0 ∧
    ∀ a, lF E a a (Pi.single (omU ε lev) u) = (((γ a + wt (omU ε lev) a : ℝ)) : ℂ) • (Pi.single (omU ε lev) u : Cn n V) := by
  intro n ε lev V _ _ E γ u _ hu
  have memA : ∀ i : Pos n, i ∈ omU ε lev ↔ ε i.1.1 = ε i.1.2 ∧ lev i.1.1 < lev i.1.2 := fun i => by simp [omU]
  refine ⟨?_, fun a => ?_⟩
  · funext B
    rw [CompanionTheory.D.LK.bd_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, Pi.zero_apply]
    · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      split_ifs with ht
      · by_contra h
        obtain ⟨h1, -, -, h4⟩ := CompanionTheory.D.LK.tri_ne h
        have e : insert i (insert j (B.erase k)) = omU ε lev := by
          by_contra h'; exact h4 (Pi.single_eq_of_ne h' _)
        have ci := (memA i).1 (e ▸ mem_insert_self _ _)
        have cj := (memA j).1 (e ▸ mem_insert_of_mem (mem_insert_self _ _))
        obtain ⟨-, -, t1, t2, t3⟩ := ht
        have ck : k ∈ omU ε lev := (memA k).2
          ⟨by rw [t2, t3, ci.1, t1]; exact cj.1,
           by rw [t2, t3]; exact (ci.2.trans_eq (congrArg lev t1)).trans cj.2⟩
        rw [← e] at ck
        have pi := i.2
        have pj := j.2
        rcases mem_insert.1 ck with h | h
        · subst h; rw [← t1, t3] at pj; exact lt_irrefl _ pj
        · rcases mem_insert.1 h with h | h
          · subst h; rw [← t2, t1] at pi; exact lt_irrefl _ pi
          · exact notMem_erase _ _ h
      · rfl
    · intro i _
      rw [if_pos rfl, ann_app]
      split_ifs with hi
      · exact map_zero _
      · by_cases e : insert i B = omU ε lev
        · have hiA := (memA i).1 (e ▸ mem_insert_self i B)
          rw [e, Pi.single_eq_same, map_smul, hu.2 _ _ i.2 hiA.1, smul_zero]
        · rw [Pi.single_eq_of_ne e, smul_zero, map_zero]
  · funext B
    show E a a ((Pi.single (omU ε lev) u : Cn n V) B) + adL a a (Pi.single (omU ε lev) u) B = _
    rw [adL_self_apply]
    simp only [cre_ann]
    by_cases e : B = omU ε lev
    · subst e
      rw [Pi.single_eq_same, hu.1 a, Pi.smul_apply, Pi.single_eq_same]
      have hs : ∀ i : Pos n, ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) •
          (if i ∈ omU ε lev then u else 0) =
          (if i ∈ omU ε lev then ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) else 0) • u := by
        intro i; split_ifs <;> simp
      rw [Finset.sum_congr rfl fun i _ => hs i, ← Finset.sum_smul, ← add_smul]
      congr 1
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, univ_inter, Finset.sum_sub_distrib, Finset.sum_boole,
        Finset.sum_boole]
      simp only [wt]
      push_cast
      ring
    · simp [Pi.single_eq_of_ne e]

end GlobalTheory.CompanionTheory.RgCOBlock.TopU
end
end

section

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

theorem _root_.GlobalTheory.T.levi_action_preserves_support_degree : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q, lev p = lev q → SuppIn (inU lev) (lF E p q x) ∧ ∀ j, Deg j x → Deg j (lF E p q x) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg | exact GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg <;> assumption)
end

section

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

theorem _root_.GlobalTheory.T.levi_action_is_gl_representation : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → GlRel E → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q r v, lev p = lev q → lev r = lev v → lF E p q (lF E r v x) - lF E r v (lF E p q x) = (if q = r then lF E p v x else 0) - (if v = p then lF E r q x else 0) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.lF_glRel | exact GlobalTheory.CompanionTheory.RgCOBlock.lF_glRel | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.lF_glRel <;> assumption)
end

end

section

@[expose] public section

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

theorem _root_.GlobalTheory.T.highest_weight_class_boundary_and_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), Monotone lev → KHighest ε E γ u →
    bd (allT n) E (Pi.single (omU ε lev) u) = 0 ∧
    ∀ a, lF E a a (Pi.single (omU ε lev) u) = (((γ a + wt (omU ε lev) a : ℝ)) : ℂ) • (Pi.single (omU ε lev) u : Cn n V) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.TopU.top_cycle_weight | exact GlobalTheory.CompanionTheory.RgCOBlock.TopU.top_cycle_weight | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.TopU.top_cycle_weight <;> assumption)

end
end
