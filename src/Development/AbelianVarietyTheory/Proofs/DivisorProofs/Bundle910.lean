module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Mathlib.RepresentationTheory.Character
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle879
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TaylorCoefficientForms
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle243
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle881
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle880
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle009
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.IsotypicMap

open Representation

variable {H V V' W : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W]

theorem exists_comp_ne_zero {τ : Representation ℂ H V} {τ' : Representation ℂ H V'} {ρ : Representation ℂ H W}
    (h : IsIsotypicOf τ ρ) (T : IntertwiningMap τ τ') (hT : T ≠ 0) :
    ∃ f : IntertwiningMap ρ τ, T.comp f ≠ 0 := by
  by_contra hc
  push Not at hc
  apply hT
  apply IntertwiningMap.ext
  rw [IntertwiningMap.zero_toLinearMap, ← LinearMap.ker_eq_top, ← top_le_iff, ← (show _ = _ from h)]
  refine iSup_le fun f => ?_
  rintro _ ⟨w, rfl⟩
  exact congrArg (fun g : IntertwiningMap ρ τ' => g w) (hc f)

theorem exists_leftInverse [Finite H] {τ : Representation ℂ H V} {ρ : Representation ℂ H W}
    (f : IntertwiningMap ρ τ) (hf : Function.Injective f) :
    ∃ s : IntertwiningMap τ ρ, ∀ w, s (f w) = w := by
  have : NeZero (Nat.card H : ℂ) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  obtain ⟨g, hg⟩ := MonoidAlgebra.exists_leftInverse_of_injective
    (IntertwiningMap.equivLinearMapAsModule ρ τ f) (LinearMap.ker_eq_bot.2 hf)
  exact ⟨(IntertwiningMap.equivLinearMapAsModule τ ρ).symm g, fun w => LinearMap.congr_fun hg w⟩

theorem equiv_of_isotypic_map : ∀ (H : Type) [Group H] [Finite H] (V V' W W' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (τ : Representation ℂ H V) (τ' : Representation ℂ H V') (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W'), ρ.IsIrreducible → ρ'.IsIrreducible → IsIsotypicOf τ ρ → IsIsotypicOf τ' ρ' → ∀ T : Representation.IntertwiningMap τ τ', T ≠ 0 → Nonempty (Representation.Equiv ρ ρ') := by
  intro H _ _ V V' W W' _ _ _ _ _ _ _ _ τ τ' ρ ρ' hρ hρ' h h' T hT
  obtain ⟨f, hf⟩ := exists_comp_ne_zero h T hT
  have hi := (Representation.IsIrreducible.injective_or_eq_zero (T.comp f)).resolve_right hf
  obtain ⟨s, hs⟩ := exists_leftInverse (T.comp f) hi
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hf
    apply IntertwiningMap.ext
    ext w
    have hw : w = 0 := (hs w).symm
    subst hw
    simp
  obtain ⟨f', hf'⟩ := exists_comp_ne_zero h' s hs0
  have hb := (Representation.IsIrreducible.bijective_or_eq_zero (s.comp f')).resolve_right hf'
  exact ⟨(IntertwiningMap.ofBijective _ hb).symm⟩

end GlobalTheory.IsotypicMap
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.IsotypicFactors

open Representation Module

section One

variable {H W V : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]

theorem finiteDimensional_of_isotypic [FiniteDimensional ℂ V] [Nontrivial V]
    (τ : Representation ℂ H V) (ρ : Representation ℂ H W) (hρ : ρ.IsIrreducible)
    (h : IsIsotypicOf τ ρ) : FiniteDimensional ℂ W := by
  have : ∃ g : IntertwiningMap ρ τ, g ≠ 0 := by
    by_contra hc
    push Not at hc
    have : (⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap) = ⊥ := by
      refine iSup_eq_bot.2 fun f => ?_
      rw [hc f]
      exact LinearMap.range_eq_bot.2 rfl
    exact bot_ne_top (this.symm.trans h)
  obtain ⟨g, hg⟩ := this
  have hi := (IsIrreducible.injective_or_eq_zero g).resolve_right hg
  exact FiniteDimensional.of_injective g.toLinearMap hi

theorem classSum_scalar [Fintype H] [FiniteDimensional ℂ W] (ρ : Representation ℂ H W)
    (hρ : ρ.IsIrreducible) (h : H) : ∃ s : ℂ, ∀ w, (∑ k, ρ (k * h * k⁻¹)) w = s • w := by
  have hT : ∀ g v, (∑ k, ρ (k * h * k⁻¹)) (ρ g v) = ρ g ((∑ k, ρ (k * h * k⁻¹)) v) := by
    intro g v

    simp only [LinearMap.sum_apply, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2
    ((∑ k, ρ (k * h * k⁻¹)).intertwiningMap_of_isIntertwiningMap ρ ρ hT)
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun f : IntertwiningMap ρ ρ => f v) hc
  simpa using this.symm

theorem classSum_of_isotypic [Fintype H] (τ : Representation ℂ H V) (ρ : Representation ℂ H W)
    (hi : IsIsotypicOf τ ρ) (h : H) (s : ℂ) (hs : ∀ w, (∑ k, ρ (k * h * k⁻¹)) w = s • w) :
    (∑ k, τ (k * h * k⁻¹)) = s • (1 : Module.End ℂ V) := by
  have : (⊤ : Submodule ℂ V) ≤ LinearMap.eqLocus (∑ k, τ (k * h * k⁻¹)) (s • (1 : Module.End ℂ V)) := by
    rw [← (show _ = ⊤ from hi)]
    refine iSup_le fun f => ?_
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_eqLocus]
    have e := congrArg f.toLinearMap (hs w)

    simp only [LinearMap.sum_apply, map_sum, map_smul] at e
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply, ← e]
    exact Finset.sum_congr rfl fun k _ => (f.isIntertwining _ _ _ w).symm
  exact LinearMap.ext fun v => this Submodule.mem_top

theorem card_mul_character {M : Type} [Group M] [Fintype H] (τ : Representation ℂ M V) (f : H →* M)
    (h : H) (s : ℂ) (hs : (∑ k, τ (f (k * h * k⁻¹))) = s • (1 : Module.End ℂ V)) (a : M)
    (ha : ∀ k, Commute (f k) a) :
    (Fintype.card H : ℂ) * τ.character (f h * a) = s * τ.character a := by
  have e := congrArg (fun T => LinearMap.trace ℂ V (T * τ a)) hs

  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, one_mul, map_smul, smul_eq_mul] at e
  have e2 : ∀ k, LinearMap.trace ℂ V (τ (f (k * h * k⁻¹)) * τ a) = τ.character (f h * a) := by
    intro k
    rw [← map_mul, ← char_conj τ (f h * a) (f k)]
    have : f (k * h * k⁻¹) * a = f k * (f h * a) * (f k)⁻¹ := by
      rw [map_mul, map_mul, mul_assoc, (ha k⁻¹).eq, map_inv]
      simp only [mul_assoc]
    rw [this]
    rfl
  simp only [e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e
  exact e

end One

theorem exists_ne_zero {G V W : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [Nontrivial V]
    [Nontrivial W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : ∀ g, (finrank ℂ W : ℂ) * ρ.character g = (finrank ℂ V : ℂ) * σ.character g) :
    ∃ f : IntertwiningMap ρ σ, f ≠ 0 := by
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  have h2 := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have h4 : (finrank ℂ W : ℂ) * finrank ℂ (IntertwiningMap ρ ρ)
      = (finrank ℂ V : ℂ) * finrank ℂ (IntertwiningMap ρ σ) := by
    rw [← h1, ← h2, mul_left_comm, mul_left_comm (finrank ℂ V : ℂ),
      Finset.mul_sum _ _ (finrank ℂ V : ℂ), Finset.mul_sum _ _ (finrank ℂ W : ℂ)]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← mul_assoc, ← mul_assoc, h]
  have : Nontrivial (IntertwiningMap ρ ρ) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨IntertwiningMap.id ρ, 0, fun e => hv (congrArg (fun f : IntertwiningMap ρ ρ => f v) e)⟩⟩
  have h5 : finrank ℂ W * finrank ℂ (IntertwiningMap ρ ρ)
      = finrank ℂ V * finrank ℂ (IntertwiningMap ρ σ) := by exact_mod_cast h4
  have h3 : 0 < finrank ℂ (IntertwiningMap ρ σ) := by
    have : 0 < finrank ℂ W * finrank ℂ (IntertwiningMap ρ ρ) :=
      Nat.mul_pos Module.finrank_pos Module.finrank_pos
    rw [h5] at this
    exact Nat.pos_of_mul_pos_left this
  have := Module.nontrivial_of_finrank_pos h3
  exact exists_ne 0

theorem exists_intertwining_ne_zero : ∀ (M : Type) [Group M] [Finite M] (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Group (H c)] [∀ c, Finite (H c)] (f : ∀ c, H c →* M), (⨆ c, (f c).range) = ⊤ → (∀ c c', c ≠ c' → ∀ (x : H c) (y : H c'), Commute (f c x) (f c' y)) → ∀ (W : ι → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)] (ρ : ∀ c, Representation ℂ (H c) (W c)), (∀ c, (ρ c).IsIrreducible) → ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] [Nontrivial V'] (τ : Representation ℂ M V) (τ' : Representation ℂ M V'), (∀ c, IsIsotypicOf (show Representation ℂ (H c) V from τ.comp (f c)) (ρ c)) → (∀ c, IsIsotypicOf (show Representation ℂ (H c) V' from τ'.comp (f c)) (ρ c)) → ∃ T : Representation.IntertwiningMap τ τ', T ≠ 0 := by
  intro M _ _ ι _ H _ _ f htop hcomm W _ _ ρ hρ V V' _ _ _ _ _ _ _ _ τ τ' hτ hτ'
  classical
  have := Fintype.ofFinite ι
  have hcomm' : Pairwise fun i j : ι => ∀ (x : H i) (y : H j), Commute (f i x) (f j y) :=
    fun i j hij => hcomm i j hij
  refine exists_ne_zero τ τ' fun m => ?_
  obtain ⟨h, rfl⟩ : m ∈ (MonoidHom.noncommPiCoprod f hcomm').range := by
    rw [MonoidHom.noncommPiCoprod_range, htop]
    exact Subgroup.mem_top m
  have key : ∀ (S : Finset ι) (comm : (S : Set ι).Pairwise (Function.onFun Commute fun i => f i (h i))),
      (finrank ℂ V' : ℂ) * τ.character (S.noncommProd (fun i => f i (h i)) comm)
        = (finrank ℂ V : ℂ) * τ'.character (S.noncommProd (fun i => f i (h i)) comm) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro comm; simp [mul_comm]
    | insert c S hc ih =>
      intro comm
      have := Fintype.ofFinite (H c)
      have := finiteDimensional_of_isotypic _ _ (hρ c) (hτ c)
      obtain ⟨s, hs⟩ := classSum_scalar (ρ c) (hρ c) (h c)
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hc]
      have ha : ∀ comm k, Commute (f c k) (S.noncommProd (fun i => f i (h i)) comm) := fun comm k =>
        Finset.noncommProd_commute _ _ _ _ fun i hi => hcomm c i (fun e => hc (e ▸ hi)) _ _
      have hcard : (Fintype.card (H c) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      refine mul_left_cancel₀ hcard ?_
      rw [mul_left_comm, card_mul_character τ (f c) (h c) s (classSum_of_isotypic _ _ (hτ c) _ _ hs) _ (ha _),
        mul_left_comm (Fintype.card (H c) : ℂ),
        card_mul_character τ' (f c) (h c) s (classSum_of_isotypic _ _ (hτ' c) _ _ hs) _ (ha _),
        mul_left_comm, ih, mul_left_comm]
  exact key Finset.univ fun _ _ _ _ hij => hcomm' hij _ _

end GlobalTheory.IsotypicFactors
end

section

set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion qClass qRel)
open GlobalTheory.PairFourier (pairPt pairCoef qClass_eq tsum_natCast_eq pairPt_ne_zero)

namespace GlobalTheory.HilbFam

theorem fourier_with_support :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ),
      HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧
        a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ (∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n) ∧
        (∀ ξ, ξ ≠ 0 → a ξ ≠ 0 → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : Emb F, 0 < i ξ) ∧
        ∀ w ∈ upperHalf F, HasSum (fun ξ : F ↦ a ξ * qPow ξ w)
          ((cK F k : ℂ) * G w / (omegaFactor 𝔞 : ℂ) ^ k) := by
  classical
  intro F _ _ _ k 𝔞 𝔟 G hG
  obtain ⟨Z, hZ, hE⟩ := hG
  set C : ℂ := (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) with hC
  let p : Quotient (qRel 𝔞 𝔟) → F := fun c ↦ (pairPt 𝔞 𝔟 c : F)
  let a' : F → ℂ := fun ξ ↦ ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ)
  have ha' : ∀ ξ, a' ξ = ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ) := fun _ ↦ rfl
  have hfib : ∀ (z : Emb F → ℂ) (ξ : F) (c : p ⁻¹' {ξ}),
      qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * qPow ξ z := by
    rintro z ξ ⟨c, hc⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    subst hc
    exact qClass_eq 𝔞 𝔟 k z c
  refine ⟨Z, fun ξ ↦ a' ξ + if ξ = 0 then C else 0, hZ, ?_, ?_, ?_, ?_⟩
  · show a' 0 + (if (0 : F) = 0 then C else 0) = C
    rw [if_pos rfl]
    have : IsEmpty (p ⁻¹' {0}) :=
      ⟨fun ⟨c, hc⟩ ↦ pairPt_ne_zero 𝔞 𝔟 c
        (Subtype.ext (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hc)))⟩
    rw [ha']
    simp only [tsum_empty, zero_add]
  · intro ξ hξ
    set z₀ : Emb F → ℂ := fun _ ↦ Complex.I
    have hz₀ : z₀ ∈ upperHalf F := fun _ ↦ by simp [z₀]
    have hq : qPow ξ z₀ ≠ 0 := Complex.exp_ne_zero _
    have hsum : Summable (fun c : p ⁻¹' {ξ} ↦ (pairCoef 𝔞 𝔟 k c : ℂ)) := by
      have := ((hE z₀ hz₀).1.subtype (fun c ↦ c ∈ p ⁻¹' {ξ})).mul_right (qPow ξ z₀)⁻¹
      refine this.congr fun c ↦ ?_
      simp only [Function.comp_apply]
      rw [hfib z₀ ξ c, mul_assoc, mul_inv_cancel₀ hq, mul_one]
    obtain ⟨m, hm⟩ := tsum_natCast_eq _ hsum
    refine ⟨m, ?_⟩
    show a' ξ + (if ξ = 0 then C else 0) = _
    rw [if_neg hξ, add_zero, ha']
    simp only [hm]
    simp
  · intro ξ hξ hne
    have hne' : a' ξ ≠ 0 := by
      intro h
      apply hne
      show a' ξ + (if ξ = 0 then C else 0) = 0
      rw [if_neg hξ, h, add_zero]
    by_cases hem : IsEmpty (p ⁻¹' {ξ})
    · exact absurd (by rw [ha']; exact tsum_empty) hne'
    obtain ⟨c, hc⟩ := not_isEmpty_iff.1 hem
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨(pairPt 𝔞 𝔟 c).2, c.out.2.2.2⟩
  · intro z hz
    obtain ⟨hs, heq⟩ := hE z hz
    have h1 := hs.hasSum.tsum_fiberwise p
    have h2 : (fun ξ ↦ ∑' c : p ⁻¹' {ξ}, qClass 𝔞 𝔟 k z c) = fun ξ ↦ a' ξ * qPow ξ z := by
      funext ξ
      rw [ha', ← tsum_mul_right]
      exact tsum_congr (hfib z ξ)
    rw [h2] at h1
    have h3 : HasSum (fun ξ : F ↦ (if ξ = 0 then C else 0) * qPow ξ z) C := by
      convert hasSum_ite_eq (0 : F) C using 1
      funext ξ
      split_ifs with h
      · subst h; simp [qPow]
      · simp
    have hv : (cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k =
        (∑' c, qClass 𝔞 𝔟 k z c) + C := by rw [heq]; ring
    show HasSum (fun ξ : F ↦ (a' ξ + if ξ = 0 then C else 0) * qPow ξ z)
      ((cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k)
    rw [hv]
    simp only [add_mul]
    exact h1.add h3

end GlobalTheory.HilbFam
end
end

section

open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.JetFrameCompare

open GlobalTheory.IndefiniteRowSideFullHecke Formalism.DimensionVariation

section Calculus

variable {E κ W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem wordDeriv_eq_lineDerivList (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) (w : List κ) :
    TensorCoordinateForms.wordDeriv v w F = lineDerivList ℂ (w.map v) F := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    funext z
    have h := (analyticAt_lineDerivList
      (SCV.analyticOnNhd_of_differentiable hF Set.univ z (Set.mem_univ z)) (w.map v)).differentiableAt
    rw [List.map_cons, lineDerivList_cons]
    change TensorCoordinateForms.dirDeriv (v x) (TensorCoordinateForms.wordDeriv v w F) z = _
    rw [ih]
    exact h.lineDeriv_eq_fderiv.symm

theorem wordDeriv_perm (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) {w w' : List κ}
    (h : w.Perm w') : TensorCoordinateForms.wordDeriv v w F = TensorCoordinateForms.wordDeriv v w' F := by
  funext z
  rw [wordDeriv_eq_lineDerivList v hF, wordDeriv_eq_lineDerivList v hF]
  exact lineDerivList_perm (SCV.analyticOnNhd_of_differentiable hF Set.univ z (Set.mem_univ z)) (h.map v)

def stdWord [Fintype κ] (e : κ → ℕ) : List κ :=
  (univ : Finset κ).toList.flatMap fun x => List.replicate (e x) x


omit [FiniteDimensional ℂ E] in
theorem monoDeriv_eq_wordDeriv [Fintype κ] (v : κ → E) (e : κ → ℕ) (F : E → ℂ) :
    TaylorCoefficientForms.monoDeriv v e F = TensorCoordinateForms.wordDeriv v (stdWord e) F := by
  unfold TaylorCoefficientForms.monoDeriv TensorCoordinateForms.wordDeriv stdWord
  induction (univ : Finset κ).toList with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, List.flatMap_cons, List.foldr_append, ← ih]
    generalize List.foldr (fun x G => (TaylorCoefficientForms.dirDeriv (v x))^[e x] G) F l = G
    induction e x with
    | zero => rfl
    | succ n ihn => rw [Function.iterate_succ_apply', List.replicate_succ, List.foldr_cons, ← ihn]; rfl

theorem isSpelling_stdWord [Fintype κ] [DecidableEq κ] : TensorCoordinateForms.IsSpelling (stdWord (κ := κ)) := by
  intro e x
  rw [stdWord, List.count_flatMap, Finset.sum_map_toList]
  simp [List.count_replicate]

theorem wordDeriv_eq_monoDeriv [Fintype κ] [DecidableEq κ] {w : (κ → ℕ) → List κ}
    (hw : TensorCoordinateForms.IsSpelling w) (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) (e : κ → ℕ) :
    TensorCoordinateForms.wordDeriv v (w e) F = TaylorCoefficientForms.monoDeriv v e F := by
  rw [monoDeriv_eq_wordDeriv]
  exact wordDeriv_perm v hF (List.perm_iff_count.2 fun x => (hw e x).trans (isSpelling_stdWord e x).symm)

theorem coordVec_eq [DecidableEq κ] : (TensorCoordinateForms.coordVec : κ → κ → ℂ) = TaylorCoefficientForms.coordVec := by
  funext p
  unfold TensorCoordinateForms.coordVec TaylorCoefficientForms.coordVec
  congr
  exact Subsingleton.elim _ _

theorem hasSum_taylorCoeff [Fintype κ] {F : (κ → ℂ) → ℂ} (hF : Differentiable ℂ F) (u : κ → ℂ) :
    HasSum (fun e => TaylorCoefficientForms.taylorCoeff F e * mono u e) (F u) := by
  classical
  have han := SCV.analyticOnNhd_of_differentiable hF Set.univ 0 (Set.mem_univ _)
  have hw : TensorCoordinateForms.IsSpelling fun e : κ → ℕ =>
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm e)).toList := fun e x => by
    rw [← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]
    rfl
  have key : ∀ α : κ →₀ ℕ, TaylorCoefficientForms.monoDeriv TaylorCoefficientForms.coordVec α F =
      lineDerivList ℂ ((Finsupp.toMultiset α).toList.map fun k => Pi.single k (1 : ℂ)) F := fun α => by
    rw [← wordDeriv_eq_monoDeriv hw _ hF, wordDeriv_eq_lineDerivList _ hF, ← coordVec_eq]
    simp only [Finsupp.equivFunOnFinite_symm_coe]
    rfl
  have hne : ∀ α : κ →₀ ℕ, ((∏ i, (α i).factorial : ℕ) : ℂ) ≠ 0 := cast_prod_factorial_ne_zero
  have hc : ∀ α : κ →₀ ℕ,
      (∏ j, ((α j).factorial : ℂ)) * TaylorCoefficientForms.taylorCoeff F α = pderivIter α F 0 := fun α => by
    rw [TaylorCoefficientForms.taylorCoeff, key, mfact,
      ← Nat.cast_prod, mul_div_cancel₀ _ (hne α)]
    rfl
  have hc' : ∀ α : κ →₀ ℕ,
      TaylorCoefficientForms.taylorCoeff F α = MvPowerSeries.coeff α (GlobalTheory.taylor F) := fun α => by
    rw [GlobalTheory.taylor, coeff_taylorDir_eq_lineDerivList _ han (Multiset.coe_toList _), TaylorCoefficientForms.taylorCoeff, key,
      mfact, div_eq_inv_mul]
  have h1 := EntireTaylor.summable_of_entire hF (fun α => TaylorCoefficientForms.taylorCoeff F α) hc u
  have h2 := ProdThetaConj.tsum_of_entire hF (fun α => TaylorCoefficientForms.taylorCoeff F α) hc hc' u
  rw [← h2, ← (Finsupp.equivFunOnFinite (α := κ) (M := ℕ)).hasSum_iff]
  exact h1.hasSum

end Calculus

section Objects

variable {Pl : Type} [Fintype Pl] [DecidableEq Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ} (ξ D : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
  (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ))

end Objects

section Clauses

variable {Pl : Type} [Fintype Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ}

end Clauses

end GlobalTheory.JetFrameCompare
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_global_bound_of_period_class : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F), K.Rich → ∀ (r : Real K s σ) (f : Form s) (per : Λ →+ Hol F.V), r.coef.pull1 (Form.cl s f) = K.perCl per → ∃ (q : GlobalTheory.CatCoh.C0 K.Oc) (G : Tot I g → ℂ), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 ∧ AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, Hol.fn (W := K.W k) (q (K.triv k)) p = G p) ∧ ∀ (l : Λ) (p : Tot I g), p.1 ∈ F.V → G (F.shift l p) = G p + (per l).fn p.1 := by
  first | exact @GlobalTheory.AnPer.Charts.exists_bound_glue | exact GlobalTheory.AnPer.Charts.exists_bound_glue | (intros; apply GlobalTheory.AnPer.Charts.exists_bound_glue <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_finiteDim_stable_polyAverages_weights : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A := by
  first | exact @GlobalTheory.PsCo.PolyAvg.polyAvg | exact GlobalTheory.PsCo.PolyAvg.polyAvg | (intros; apply GlobalTheory.PsCo.PolyAvg.polyAvg <;> assumption)
end
