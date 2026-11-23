module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle743
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetAdjQuot
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle188
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle190
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle191
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle192
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
public import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.CasimirLowest

open GlobalTheory.CasimirHighest

theorem casimir_on_vector {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (Λ : Ix p q → ℚ) (e : V)
    (hv : e ∈ hwSub act Λ) (hk : KilledByLower act e) :
    casimir act e = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • e := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
  obtain ⟨hw, hr⟩ := hv
  have h1 := casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j)))
    (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) e
    (fun i => Λ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h2 := casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j)))
    (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) e
    (fun i => Λ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h3 : ∀ (a : Fin p) (b : Fin q),
      act (Eab (.inl a) (.inr b)) (act (Eab (.inr b) (.inl a)) e) = 0 := by
    intro a b; rw [hk a b, map_zero]
  have h4 : ∀ (b : Fin q) (a : Fin p),
      act (Eab (.inr b) (.inl a)) (act (Eab (.inl a) (.inr b)) e) =
        ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e := by
    intro b a
    have h5 := congrArg (fun f : Module.End ℂ V => f e)
      (act_Eab_comm h (.inr b) (.inl a) (.inl a) (.inr b))
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, h3, sub_zero, hw] at h5
    rw [h5, Rat.cast_sub, sub_smul]
  have h6 : ∑ b : Fin q, ∑ a : Fin p, ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e =
      ((∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) : ℚ) : ℂ) • e := by
    simp only [Rat.cast_sum, Finset.sum_smul]
  simp only [casimir, LinearMap.sum_apply, LinearMap.add_apply, Module.End.mul_apply,
    Fintype.sum_sum_type, Finset.sum_add_distrib, h3, h4, Finset.sum_const_zero, zero_add]
  rw [h1, h2, h6, ← add_smul, ← add_smul, ← Rat.cast_add, ← Rat.cast_add]
  congr 2
  have e1 : ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) =
      ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ)) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ)) =
      ∑ j : Fin q, Λ (Sum.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ)) + p * ∑ j : Fin q, Λ (Sum.inr j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) =
      p * ∑ j : Fin q, Λ (Sum.inr j) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum]
  rw [e1, e2, e3]
  ring

theorem casimir_on_generated : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (Λ : Ix p q → ℚ) (e : V), e ∈ hwSub act Λ → KilledByLower act e → genSub act {e} = ⊤ → ∀ x, casimir act x = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • x := by
  intro p q V _ _ act h Λ e hv hk hg x
  have he := casimir_on_vector h Λ e hv hk
  generalize (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) = c at he ⊢
  have hc := (casimir_central_and_highest p q V act h).1
  have hle : genSub act {e} ≤ LinearMap.ker (casimir act - c • LinearMap.id) := by
    refine sInf_le ⟨?_, ?_⟩
    · rintro y rfl
      simp [he]
    · intro Z y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hy ⊢
      have := congrArg (fun f : Module.End ℂ V => f y) (hc Z)
      simp only [Module.End.mul_apply] at this
      rw [this, hy, map_smul]
  have hx := hle (hg ▸ Submodule.mem_top : x ∈ genSub act {e})
  simpa [sub_eq_zero] using hx

end GlobalTheory.CasimirLowest
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_self_pos_gamma1InterGamma0 : ∀ (N l : ℕ) (k : ℤ), 0 < N → 0 < l → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, f ≠ 0 → 0 < (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑f).re ∧ (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑f).im = 0 := by
  first | exact @GlobalTheory.Hk.pet_self_pos | exact GlobalTheory.Hk.pet_self_pos | (intros; apply GlobalTheory.Hk.pet_self_pos <;> assumption)
end

section

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_finiteIndex' (N l : ℕ) (hN : 0 < N) (hl : 0 < l) : (lev N l).FiniteIndex := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

theorem pet_eq_quotInt (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) :
    pet Γ k f g = UpperTheory.V.Lit.KT.quotInt Γ (petersson k f g) := rfl

theorem pet_sesq : ∀ (N l : ℕ) (k : ℤ), 0 < N → 0 < l → ∀ (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (c : ℂ), GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f (⇑g + c • ⇑h) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g + c * GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑h ∧ GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑g ⇑f = (starRingEnd ℂ) (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g) := by
  intro N l k hN hl f g h c
  haveI := lev_finiteIndex' N l hN hl
  haveI : Fintype (SL(2, ℤ) ⧸ lev N l) := Fintype.ofFinite _
  refine ⟨?_, ?_⟩
  · have e : petersson k ⇑f (⇑g + c • ⇑h) = fun z => petersson k f g z + c * petersson k f h z := by
      funext z
      simp only [petersson, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨B, hB⟩ := CuspFormClass.petersson_bounded_left k _ f g
    obtain ⟨B', hB'⟩ := CuspFormClass.petersson_bounded_left k _ f h
    have hc := petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous g)
    have hc' := petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous h)
    have hb'' : ∀ z, ‖c * petersson k f h z‖ ≤ ‖c‖ * B' := fun z => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB' z) (norm_nonneg _)
    rw [pet_eq_quotInt, pet_eq_quotInt, pet_eq_quotInt, e,
      UpperTheory.V.Lit.KT.quotInt_add (ψ := fun z => c * petersson k f h z) _ hc hB (continuous_const.mul hc') hb'', UpperTheory.V.Lit.KT.quotInt_mul]
  · simp only [pet, finsum_eq_sum_of_fintype]

    rw [map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← integral_conj]
    congr 1
    funext z
    exact petersson_symm _ _ _ _

end GlobalTheory.Hk
end
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.ValuationAlmostSeparation

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem orbit_finite (h : IsClo p Ω) (H : Subgroup (Gal p Ω)) (s : Ω) :
    (MulAction.orbit H s).Finite := by
  classical
  obtain ⟨P, hP0, hPs⟩ := (h.alg.isAlgebraic s)
  have hQ : P.map (algebraMap (O0 p) Ω) ≠ 0 :=
    (Polynomial.map_ne_zero_iff h.inj).2 hP0
  refine (P.map (algebraMap (O0 p) Ω)).roots.toFinset.finite_toSet.subset ?_
  rintro _ ⟨g, rfl⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hQ, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  show Polynomial.aeval ((g : Gal p Ω) s) P = 0
  rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  simp [hPs]

theorem fix_top (H : Subgroup (Gal p Ω)) :
    Fix Ω (⊤ : Subgroup H) = Fix Ω H := by
  ext x
  constructor
  · intro hx g
    exact hx ⟨g, Subgroup.mem_top g⟩
  · intro hx g
    exact hx g.1

end GlobalTheory.ValuationAlmostSeparation

open GlobalTheory.ValuationAlmostSeparation

theorem GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω), ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) ∧ (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 ∧ ∀ S : Finset Ω, ∃ U : Subgroup ↥(⨅ n, Gn T n), U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix Ω U) ∧ AlmostSep v U := by
  intro p _ Ω _ _ hp2 hclo T
  obtain ⟨v, hint, hinv, hp0, hp1⟩ := GlobalTheory.T.exists_galoisInvariant_valuation_integers_eq_integral p Ω hclo
  refine ⟨v, hint, hinv, hp0, hp1, fun S => ?_⟩
  obtain ⟨U, hUn, hUf, hUS, hUsep⟩ := GlobalTheory.T.exists_normal_finiteIndex_fixing_finite_orbits Ω (↥(⨅ n, Gn T n)) S
    (fun s _ => orbit_finite hclo _ s)
  refine ⟨U, hUn, hUf, hUS, ?_⟩
  have hR := GlobalTheory.T.approxPthRoot_fixedField_cyclotomic_tower p Ω hp2 hclo T v hint hp0 hp1
  refine GlobalTheory.T.almostPurity_of_normal_finiteIndex_subgroup Ω v p (Fact.out) hp0 hp1 (↥(⨅ n, Gn T n)) (fun g x => hinv g.1 x)
    (T.ζ 1) (by simpa using T.prim 1) ?_ (by rw [fix_top]; exact hR) U hUn hUf hUsep
  intro g
  have hg : (g : Gal p Ω) ∈ Gn T 1 := (iInf_le (fun n => Gn T n) 1) g.2
  exact hg.1
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

variable {Ω : Type} [Field Ω] (ε : Ω →+* ℂ)

theorem exists_isExp_of_mem_ring (a : ring ε.range) : ∃ h : HahnSeries ℚ Ω, IsExp ε a h :=
  GlobalTheory.T.exists_cuspExpansionAtInfinity_of_someLevel Ω ε a (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 a).1 a.2)

def expan (a : ring ε.range) : HahnSeries ℚ Ω := Classical.choose (exists_isExp_of_mem_ring ε a)

theorem isExp_expan (a : ring ε.range) : IsExp ε a (expan ε a) :=
  Classical.choose_spec (exists_isExp_of_mem_ring ε a)

theorem expan_eq_of_isExp {a : ring ε.range} {h : HahnSeries ℚ Ω} (ha : IsExp ε a h) : expan ε a = h :=
  (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 _ _ _ (isExp_expan ε a) ha

def expanHom : ring ε.range →+* HahnSeries ℚ Ω where
  toFun := expan ε
  map_one' := by
    apply expan_eq_of_isExp
    have h := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.1 1
    have e1 : ((1 : ring ε.range) : ℍ → ℂ) = fun _ => ε 1 := by ext; simp
    rw [e1]; simpa using h
  map_mul' a b := by
    apply expan_eq_of_isExp
    have h := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).2.2
    simpa using h
  map_zero' := by
    apply expan_eq_of_isExp
    have h := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.1 0
    have e0 : ((0 : ring ε.range) : ℍ → ℂ) = fun _ => ε 0 := by ext; simp
    rw [e0]; simpa using h
  map_add' a b := by
    apply expan_eq_of_isExp
    have h := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).1
    simpa using h

theorem expanHom_injective : Function.Injective (expanHom ε) := by
  intro a b hab
  have hsub := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).2.1
  have h0 : expan ε a - expan ε b = 0 := sub_eq_zero.mpr hab
  rw [h0] at hsub
  have hmem : ((a - b : ring ε.range) : ℍ → ℂ) ∈ ring ε.range := (a - b).2
  have hin : InR ε.range ((a - b : ring ε.range) : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 hmem
  have hhol := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ε.range _ hin
  push_cast at hhol
  have := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.2.1 _ hhol hsub
  exact Subtype.ext (sub_eq_zero.mp this)

theorem expansion_injective_ringHom :
    ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ e : GlobalTheory.FN.ring ε.range →+* HahnSeries ℚ Ω,
      Function.Injective e ∧ ∀ a : GlobalTheory.FN.ring ε.range, IsExp ε a (e a) :=
  fun _ _ ε => ⟨expanHom ε, expanHom_injective ε, isExp_expan ε⟩

end GlobalTheory.FN
end
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.smoothedSiegelUnit_modularS_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x (ModularGroup.S • τ) = sg c (act x ModularGroup.S) τ := by
  first | exact @GlobalTheory.Sieg.sg_S | exact GlobalTheory.Sieg.sg_S | (intros; apply GlobalTheory.Sieg.sg_S <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem dif_comm (L : ℕ) (v w : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (dif L w F) = dif L w (dif L v F) := by
  funext x
  simp only [dif]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h : ∑ s ∈ Finset.range L, ∑ r ∈ Finset.range L, F (x + (s : ℤ) • v + (r : ℤ) • w)
      = ∑ r ∈ Finset.range L, ∑ s ∈ Finset.range L, F (x + (r : ℤ) • w + (s : ℤ) • v) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [add_right_comm]
  rw [h]
  ring

theorem sum_dif_dif (L : ℕ) (w : ℤ × ℤ) (Φ G : ℤ × ℤ → ℂ) (hL : 0 < L) (hΦ : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C)
    (hw : Kills L w Φ) (hG : Summable fun x => ‖G x‖) :
    ∑' x, Φ x * dif L w (dif L w G) x = ∑' x, Φ x * G x := by
  obtain ⟨hs1, he1⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L w Φ G hL hΦ hw hG
  obtain ⟨_, he2⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L w Φ (dif L w G) hL hΦ hw hs1
  exact he2.trans he1

theorem lat_indep : ∀ (j L : ℕ) (v w : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 1 ≤ j → 0 < L →
    (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → Kills L w Φ → lat j 0 L v Φ τ = lat j 0 L w Φ τ := by
  intro j L v w Φ τ hj hL hΦ hv hw
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hsv := GlobalTheory.T.summable_regularizedEisensteinLatticeTerm j L v τ hj hL
  have hsw := GlobalTheory.T.summable_regularizedEisensteinLatticeTerm j L w τ hj hL
  simp only [lat]
  calc ∑' x, Φ x * dif L v (dif L v T) x
      = ∑' x, Φ x * dif L w (dif L w (dif L v (dif L v T))) x :=
        (sum_dif_dif L w Φ _ hL hΦ hw hsv).symm
    _ = ∑' x, Φ x * dif L v (dif L v (dif L w (dif L w T))) x := by
        have c1 : ∀ F : ℤ × ℤ → ℂ, dif L w (dif L v (dif L v F)) = dif L v (dif L v (dif L w F)) := by
          intro F; rw [dif_comm L w v (dif L v F), dif_comm L w v F]
        rw [c1 T, c1 (dif L w T)]
    _ = ∑' x, Φ x * dif L w (dif L w T) x := sum_dif_dif L v Φ _ hL hΦ hv hsw

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem polyB_add_smul {u v : ℕ → ℂ} (c : ℂ) (hu : PolyB u) (hv : PolyB v) :
    PolyB (fun n => u n + c * v n) := by
  obtain ⟨C₁, A₁, h₁⟩ := hu
  obtain ⟨C₂, A₂, h₂⟩ := hv
  have hC₁ : 0 ≤ C₁ := by
    have := h₁ 0; simp at this; exact le_trans (norm_nonneg _) this
  have hC₂ : 0 ≤ C₂ := by
    have := h₂ 0; simp at this; exact le_trans (norm_nonneg _) this
  refine ⟨C₁ + ‖c‖ * C₂, A₁ + A₂, fun n => ?_⟩
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have e1 : ((n : ℝ) + 1) ^ A₁ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) := pow_le_pow_right₀ h1 (by omega)
  have e2 : ((n : ℝ) + 1) ^ A₂ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) := pow_le_pow_right₀ h1 (by omega)
  calc ‖u n + c * v n‖ ≤ ‖u n‖ + ‖c‖ * ‖v n‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ C₁ * ((n : ℝ) + 1) ^ A₁ + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ A₂) := by
        gcongr; exacts [h₁ n, h₂ n]
    _ ≤ C₁ * ((n : ℝ) + 1) ^ (A₁ + A₂) + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ (A₁ + A₂)) := by
        gcongr
    _ = (C₁ + ‖c‖ * C₂) * ((n : ℝ) + 1) ^ (A₁ + A₂) := by ring

theorem qs_To_hsum : ∀ (k q : ℕ) (ε : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → 0 < q → ε 1 = 1 → PolyB a →
    PolyB (To k (ε q) q a) ∧ qs (To k (ε q) q a) = hsum k ε (repT q) (qs a) := by
  intro k q ε a hk hq hε ha
  obtain ⟨hU, hUq⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k q a hk hq ha
  obtain ⟨hV, hVq⟩ := GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion q a hq ha
  have hTo : To k (ε q) q a = fun n => Uo q a n + (ε q * (q : ℂ) ^ (k - 1)) * Vo q a n := by
    funext n; simp only [To, Uo]
  refine ⟨by rw [hTo]; exact polyB_add_smul _ hU hV, ?_⟩
  funext τ
  have sU : Summable fun n : ℕ => Uo q a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous _ hU).1 τ).of_norm
  have sV : Summable fun n : ℕ => Vo q a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous _ hV).1 τ).of_norm
  have hsplit : qs (To k (ε q) q a) τ = qs (Uo q a) τ + (ε q * (q : ℂ) ^ (k - 1)) * qs (Vo q a) τ := by
    rw [hTo]; simp only [qs]
    rw [← tsum_mul_left, ← sU.tsum_add (sV.mul_left _)]
    congr 1; funext n; ring
  have him : 0 < ((q : ℂ) * (τ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hq) τ.im_pos
  have hσ : qs (Vo q a) τ = qs a ⟨(q : ℂ) * τ, him⟩ := hVq τ ⟨(q : ℂ) * τ, him⟩ rfl
  rw [hsplit, hUq τ, hσ, hsum, Fintype.sum_option]
  have hnone : ε (repT q none 0 0) * slz k (repT q none) (qs a) τ
      = (ε q * (q : ℂ) ^ (k - 1)) * qs a ⟨(q : ℂ) * τ, him⟩ := by
    have : ofComplex ((((q : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ))) = ⟨(q : ℂ) * τ, him⟩ := by
      rw [show (((q : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ)) = (q : ℂ) * τ by
        push_cast; ring]
      exact ofComplex_apply_of_im_pos him
    simp only [repT, slz, Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    rw [this]
    push_cast
    simp
    ring
  have hsome : ∀ j : Fin q, ε (repT q (some j) 0 0) * slz k (repT q (some j)) (qs a) τ
      = slz k (repU q j) (qs a) τ := by
    intro j
    simp only [repT, repU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hε, one_mul]
  rw [hnone, Finset.sum_congr rfl (fun j _ => hsome j)]
  ring

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.atkinLehner_slash_isModularFormCoeffSeq : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → MF k (N * l) (ch χ) a → ∃ a' : ℕ → ℂ, MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) := by
  first | exact @GlobalTheory.EisM.atkinLehner_MF | exact GlobalTheory.EisM.atkinLehner_MF | (intros; apply GlobalTheory.EisM.atkinLehner_MF <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.integral_coprime_sum_unfold_to_unitStrip : ∀ (L : ℕ) (ρ : ℍ → ℝ) (Ψ : ℍ → ℂ) (W : ℤ × ℤ → ℍ → ℂ), Wt L ρ → IntegrableOn Ψ strip → AEStronglyMeasurable Ψ → (∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ, Ψ (γ • τ) = W (γ 1 0, γ 1 1) τ) → ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ = ∫ τ in strip, Ψ τ := by
  first | exact @GlobalTheory.EisM.unfold_strip | exact GlobalTheory.EisM.unfold_strip | (intros; apply GlobalTheory.EisM.unfold_strip <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.conj_blockLower_mem_principalSeriesCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ g ∈ grp ψ, (∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → g.val a b = 0) → z⁻¹ * g * z ∈ grp ψ ∧ theta ψ (z⁻¹ * g * z) = theta ψ g := by
  first | exact @GlobalTheory.PsType.conj_blockLower_mem_theta | exact GlobalTheory.PsType.conj_blockLower_mem_theta | (intros; apply GlobalTheory.PsType.conj_blockLower_mem_theta <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.modular_function_tower_integrality : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l : ℕ) [Fact l.Prime], (∀ (g : GQ), ∀ a ∈ X.A l, X.kmap l (X.sl g).toRingEquiv a ∈ X.A l) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ a ∈ X.A l, X.kmap l (X.gal s) a ∈ X.A l := by
  first | exact @GlobalTheory.KZ.kmap_A_stable | exact GlobalTheory.KZ.kmap_A_stable | (intros; apply GlobalTheory.KZ.kmap_A_stable <;> assumption)
end
