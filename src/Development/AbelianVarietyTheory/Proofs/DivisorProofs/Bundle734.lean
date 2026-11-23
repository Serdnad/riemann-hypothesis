module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankThreeRootIndexOfCards
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle694
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMonomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle210
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle698
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin

@[expose] public section

section

noncomputable section

open Formalism.UG

namespace GlobalTheory.SatakeWeyl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q n m : ℕ}

theorem mem_radU_iff (u : GU σ n) : u ∈ radU σ (Fin.val : Fin n → ℕ) ↔ IsUnipU u := by
  refine ⟨fun h => ⟨fun i j hij => ?_, fun i => ?_⟩, fun h i j hij => ?_⟩
  · exact (h i j (le_of_lt hij)).trans (Matrix.one_apply_ne (ne_of_gt hij))
  · exact (h i i le_rfl).trans (Matrix.one_apply_eq i)
  · rcases hij.eq_or_lt with e | e
    · obtain rfl : j = i := Fin.ext e
      exact (h.2 j).trans (Matrix.one_apply_eq j).symm
    · exact (h.1 i j e).trans (Matrix.one_apply_ne (ne_of_gt (show j < i from e))).symm

theorem satU_eq (T : (Fin m → ℤ) → GU σ n) (hT : ∀ a, mat (T a) = tMat ϖ n m a) (h : GU σ n → ℂ) (α : Fin m → ℂ) :
    SatU ϖ q h α = ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) *
      ((q : ℂ) ^ 0 * (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
        cellSum (KU σ n) (radU σ Fin.val) h (T a)) := by
  unfold SatU cellSum
  refine finsum_congr fun a => ?_
  rw [Finset.prod_mul_distrib, pow_zero, one_mul, mul_assoc]
  congr 2
  refine finsum_congr fun x => ?_
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u, hu, k, hk, e⟩
    exact ⟨u, (mem_radU_iff u).2 hu, k, hk, mat_injective (by rw [mat_mul, mat_mul, hT]; exact e)⟩
  · rintro ⟨u, hu, k, hk, e⟩
    refine ⟨u, (mem_radU_iff u).1 hu, k, hk, ?_⟩
    have := congrArg mat e
    rw [mat_mul, mat_mul, hT] at this
    exact this

theorem sum_perm (S : (Fin m → ℤ) → ℂ) (π : Equiv.Perm (Fin m)) (hS : ∀ a, S (a ∘ π) = S a) (α : Fin m → ℂ) :
    ∑ᶠ a : Fin m → ℤ, (∏ i, (α ∘ π) i ^ a i) * S a = ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) * S a := by
  rw [← finsum_comp_equiv (Equiv.arrowCongr π.symm (Equiv.refl ℤ))]
  refine finsum_congr fun a => ?_
  have e : (Equiv.arrowCongr π.symm (Equiv.refl ℤ)) a = a ∘ π := by ext i; simp
  rw [e, hS]
  congr 1
  exact Equiv.prod_comp π (fun i => α i ^ a i)

theorem sum_neg (S : (Fin m → ℤ) → ℂ) (j : Fin m) (hS : ∀ a, S (Function.update a j (-a j)) = S a) (α : Fin m → ℂ) :
    ∑ᶠ a : Fin m → ℤ, (∏ i, Function.update α j (α j)⁻¹ i ^ a i) * S a =
      ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) * S a := by
  have hinv : Function.Involutive fun a : Fin m → ℤ => Function.update a j (-a j) := fun a => by simp
  rw [← finsum_comp_equiv hinv.toPerm]
  refine finsum_congr fun a => ?_
  rw [Function.Involutive.coe_toPerm, hS]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i = j
  · subst hi
    simp
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

theorem perm_of_swap (S : (Fin m → ℤ) → ℂ)
    (hS : ∀ (i j : Fin m), j.val = i.val + 1 → ∀ a, S (a ∘ Equiv.swap i j) = S a) (π : Equiv.Perm (Fin m)) :
    ∀ a, S (a ∘ π) = S a := by
  cases m with
  | zero => intro a; congr 1; funext i; exact i.elim0
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    induction hπ using Submonoid.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hS _ _ (by simp)
    | one => intro a; rfl
    | mul x y _ _ hx hy => intro a; rw [← hx a, ← hy (a ∘ x)]; rfl

theorem satWeyl_of_coeff (hswap : CoeffSwap) (hneg : CoeffNeg) : SatWeyl := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α _ h hh
  choose T hT using fun a : Fin m → ℤ => P.fSatake_tMat_exists (n := n) hU hm a
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hp : ∀ f : Fin m → ℤ, ∏ i, (q : ℂ) ^ f i = (q : ℂ) ^ ∑ i, f i := fun f =>
    (map_prod (zpowersHom ℂˣ (Units.mk0 (q : ℂ) hq)) (fun i => Multiplicative.ofAdd (f i)) Finset.univ) |>
      congrArg (Units.coeHom ℂ) |> fun e => by
        simpa [map_prod, ← ofAdd_sum] using e.symm
  set S : (Fin m → ℤ) → ℂ := fun a => (q : ℂ) ^ 0 *
    (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      cellSum (KU σ n) (radU σ Fin.val) h (T a) with hSdef
  have h1 : ∀ π : Equiv.Perm (Fin m), ∀ a, S (a ∘ π) = S a := by
    refine perm_of_swap S fun i j hij a => ?_
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    simp only [hSdef]
    rw [hswap L ϖ σ q n m hU hm hm' h hh a i j hij _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem i j (by simp) (by simp) hne]
    · simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
      push_cast
      ring
    · rintro c - ⟨hc, hc'⟩
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hc hc', sub_self]
  have h2 : ∀ j : Fin m, j.val + 1 = m → ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j hj a
    simp only [hSdef]
    rw [hneg L ϖ σ q n m hU hm hm' h hh a j hj _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [Function.update_self]
      ring
    · intro c _ hc
      rw [Function.update_of_ne hc, sub_self]
    · simp
  have h3 : ∀ j : Fin m, ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j a
    have hj := j.2
    let l : Fin m := ⟨m - 1, by omega⟩
    rw [← h1 (Equiv.swap j l) a, ← h2 l (by show m - 1 + 1 = m; omega) (a ∘ Equiv.swap j l),
      ← h1 (Equiv.swap j l) (Function.update a j (-a j))]
    congr 1
    rw [Function.update_comp_equiv]
    simp
  refine ⟨fun π => ?_, fun i => ?_⟩
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_perm S π (h1 π) α
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_neg S i (h3 i) α

theorem satWeyl : SatWeyl := by
  have hr : RankOne := GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps GlobalTheory.T.cell_sum_two_stage_descent_unipotent GlobalTheory.T.cell_sum_left_right_invariance_normaliser
    (GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity (GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex GlobalTheory.T.finite_index_left_right_coset_sums_eq) GlobalTheory.T.contracting_automorphism_subgroup_chain_index)
  have hl : LeviStep := GlobalTheory.T.unitaryCellSumLeviReduction_of_steps hr GlobalTheory.T.exists_smaller_unitary_group_embedding GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts GlobalTheory.T.unitary_diagonal_factorization_along_embedding GlobalTheory.T.unitary_levi_normalizes_unipotent_radical
    (GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart GlobalTheory.T.unitary_block_triangular_levi_part_unitary) GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq
  have hi : IntIndex := GlobalTheory.T.card_integers_mod_uniformizer_eq_q_sq
  have ht : TraceZeroIndex := GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq hi
  exact satWeyl_of_coeff (GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction hl (GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq hi) GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets)
    (GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction hl (GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard ht) (GlobalTheory.T.unitaryRankThreeRootIndex_of_cards hi ht))

end GlobalTheory.SatakeWeyl

end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LawDer.ConstLin

variable {R : Type} [CommRing R] {d : ℕ}

end GlobalTheory.LawDer.ConstLin

theorem GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → (∀ i, swap (μ i) = μ i) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R), ∃ r : R, constantCoeff ((invDer μ u)^[p] F) - ∑ j, constantCoeff ((invDer μ u)^[p] (X j)) * coeff (Finsupp.single j 1) F = p * r := by
  first
  | exact @_root_.GlobalTheory.LinearPartIteration.iterate_linear_part
  | exact _root_.GlobalTheory.LinearPartIteration.iterate_linear_part
  | (apply _root_.GlobalTheory.LinearPartIteration.iterate_linear_part <;> assumption)
  | (intros; apply _root_.GlobalTheory.LinearPartIteration.iterate_linear_part <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LinearPartIteration.iterate_linear_part <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LinearPartIteration.iterate_linear_part ..)
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.constantCoeff_iterate_invariant_derivation_monomial : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → (∀ i, swap (μ i) = μ i) → ∀ (u : Fin d → R) (α : Fin d →₀ ℕ), constantCoeff ((invDer μ u)^[α.degree] (monomial α (1 : R))) = (α.degree.factorial : R) * ∏ i, u i ^ α i := by
  first | exact @GlobalTheory.LawDer.MonoIter.constantCoeff_iterate_invDer_monomial | exact GlobalTheory.LawDer.MonoIter.constantCoeff_iterate_invDer_monomial | (intros; apply GlobalTheory.LawDer.MonoIter.constantCoeff_iterate_invDer_monomial <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by
  first | exact @GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound | exact GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound | (intros; apply GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen

theorem zpow_two_var {G : Type*} [CommGroup G] (x y : G) (a b c d a' b' : ℤ) :
    (x ^ a * y ^ b) ^ a' * (x ^ c * y ^ d) ^ b' = x ^ (a * a' + c * b') * y ^ (b * a' + d * b') := by
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  exact _root_.mul_mul_mul_comm _ _ _ _

theorem comp_zpow_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {G X Y : C} [GrpObj G]
    (f : X ⟶ Y) (g : Y ⟶ G) (n : ℤ) : f ≫ g ^ n = (f ≫ g) ^ n := by
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast, comp_pow]
  | negSucc n => simp only [zpow_negSucc, GrpObj.comp_inv, comp_pow]

theorem psiMap_comp {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (a b c d a' b' c' d' : ℤ) :
    psiMap A a b c d ≫ psiMap A a' b' c' d' =
      psiMap A (a * a' + c * b') (b * a' + d * b') (a * c' + c * d') (b * c' + d * d') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, psiMap_fst, psiMap_fst, comp_mul, comp_zpow_hom, comp_zpow_hom, psiMap_fst,
      psiMap_snd, zpow_two_var]
  · rw [Category.assoc, psiMap_snd, psiMap_snd, comp_mul, comp_zpow_hom, comp_zpow_hom, psiMap_fst,
      psiMap_snd, zpow_two_var]

theorem psiMap_diag {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (n : ℕ) :
    psiMap A n 0 0 n = Out.mulA (A ⊗ A) n := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [psiMap_fst, Out.mulA, pow_comp, Category.id_comp, zpow_zero, _root_.mul_one, zpow_natCast]
  · rw [psiMap_snd, Out.mulA, pow_comp, Category.id_comp, zpow_zero, _root_.one_mul, zpow_natCast]

theorem finite_etale_of_comp_eq {X S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p]
    [LocallyOfFiniteType p] (f g m : X ⟶ X) [IsFinite m] [Etale m] (hg : g ≫ p = p)
    (h1 : f ≫ g = m) (h2 : g ≫ f = m) : IsFinite f ∧ Etale f := by
  have hgs : IsSeparated g :=
    MorphismProperty.of_postcomp (W' := ⊤) @IsSeparated g p trivial (by rw [hg]; infer_instance)
  haveI : LocallyOfFiniteType (g ≫ p) := by rw [hg]; infer_instance
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g p
  haveI : FormallyUnramified (g ≫ f) := by rw [h2]; infer_instance
  haveI : FormallyUnramified g := FormallyUnramified.of_comp g f
  haveI : Etale (f ≫ g) := by rw [h1]; infer_instance
  haveI : IsFinite (f ≫ g) := by rw [h1]; infer_instance
  exact ⟨MorphismProperty.of_postcomp @IsFinite (W' := @IsSeparated) f g hgs inferInstance,
    Etale.of_comp f g⟩

theorem exists_sign_mul (d : ℤ) : ∃ s : ℤ, s * d = (d.natAbs : ℤ) := by
  rcases Int.natAbs_eq d with h | h
  · exact ⟨1, by rw [_root_.one_mul]; exact h⟩
  · exact ⟨-1, by rw [h]; ring_nf; simp⟩

theorem psiMap_finite_locallyFree : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K))
    [GrpObj A], IsAbelianScheme A → ∀ a₁ b₁ a₂ b₂ : ℤ, ((a₁ * b₂ - b₁ * a₂ : ℤ) : K) ≠ 0 →
    IsFinite (psiMap A a₁ b₁ a₂ b₂).left ∧ Flat (psiMap A a₁ b₁ a₂ b₂).left ∧
      LocallyOfFinitePresentation (psiMap A a₁ b₁ a₂ b₂).left ∧
      ∃ r : ℕ, (∀ y, (psiMap A a₁ b₁ a₂ b₂).left.finrank y = r) ∧ (r : K) ≠ 0 := by
  intro K _ _ A _ hA a₁ b₁ a₂ b₂ hd
  haveI := hA.comm
  set n := (a₁ * b₂ - b₁ * a₂).natAbs with hn_def
  have hn : (n : K) ≠ 0 := by
    rcases Int.natAbs_eq (a₁ * b₂ - b₁ * a₂) with h | h
    · rw [h, Int.cast_natCast] at hd; exact hd
    · rw [h, Int.cast_neg, Int.cast_natCast, neg_ne_zero] at hd; exact hd
  haveI hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨hfin, -, het, r, hr0, -, hall, -⟩ :=
    GlobalTheory.AbelianMulFin.mulA_finite_locallyFree K (A ⊗ A) n hn
  obtain ⟨s, hs⟩ := exists_sign_mul (a₁ * b₂ - b₁ * a₂)
  rw [← hn_def] at hs
  set ψ := psiMap A a₁ b₁ a₂ b₂ with hψ
  set ψ' := psiMap A (s * b₂) (-(s * b₁)) (-(s * a₂)) (s * a₁) with hψ'
  have h1 : ψ ≫ ψ' = Out.mulA (A ⊗ A) n := by
    rw [hψ, hψ', psiMap_comp, ← psiMap_diag]
    congr 1 <;> push_cast <;> first | ring1 | linear_combination hs
  have h2 : ψ' ≫ ψ = Out.mulA (A ⊗ A) n := by
    rw [hψ, hψ', psiMap_comp, ← psiMap_diag]
    congr 1 <;> push_cast <;> first | ring1 | linear_combination hs
  have h1' : ψ.left ≫ ψ'.left = (Out.mulA (A ⊗ A) n).left := by rw [← Over.comp_left, h1]
  have h2' : ψ'.left ≫ ψ.left = (Out.mulA (A ⊗ A) n).left := by rw [← Over.comp_left, h2]
  haveI := hAA.proper
  haveI := hAA.smooth
  haveI := hAA.geomConnected
  obtain ⟨hψfin, hψet⟩ := finite_etale_of_comp_eq (A ⊗ A).hom ψ.left ψ'.left _ (Over.w ψ') h1' h2'
  obtain ⟨hψ'fin, hψ'et⟩ := finite_etale_of_comp_eq (A ⊗ A).hom ψ'.left ψ.left _ (Over.w ψ) h2' h1'
  haveI : ConnectedSpace (A ⊗ A).left :=
    GeometricallyConnected.connectedSpace (A ⊗ A).hom (A ⊗ A).hom.isOpenMap
  let o : (A ⊗ A).left := Classical.arbitrary _
  set r' := ψ.left.finrank o with hr'
  have hall' : ∀ y, ψ.left.finrank y = r' := fun y =>
    (Scheme.Hom.isLocallyConstant_finrank ψ.left).apply_eq_of_preconnectedSpace y o
  refine ⟨hψfin, inferInstance, inferInstance, r', hall', fun h0 => hr0 ?_⟩
  have e := GlobalTheory.FinrankComp.finrank_comp_of_const ψ.left ψ'.left r' hall' o
  rw [h1', hall o] at e
  rw [e, Nat.cast_mul, h0, zero_mul]

end GlobalTheory.AmpleGen
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.spread_torsor_to_etale_algebra : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  first | (exact @GlobalTheory.LocAcyc.spread_torsor_to_etale) | (exact GlobalTheory.LocAcyc.spread_torsor_to_etale) | (intros; apply GlobalTheory.LocAcyc.spread_torsor_to_etale  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCoinductionComplexAugmentation_quasiIso : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R), (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → QuasiIso (coindAug φ J) := by
  first | (exact @GlobalTheory.EtC.coindAug_quasiIso) | (exact GlobalTheory.EtC.coindAug_quasiIso) | (intros; apply GlobalTheory.EtC.coindAug_quasiIso  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.extendScalars_tateTwistResolution_hom_ext_augmentation : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ) (K : Cx (ZMod q)) (u u' : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map (u.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ)) = Sec.map (u'.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ))) → extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u = extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u' := by
  first | (exact @GlobalTheory.EtC.extAug_comp_ext) | (exact GlobalTheory.EtC.extAug_comp_ext) | (intros; apply GlobalTheory.EtC.extAug_comp_ext  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.acyclic_extendScalars_zmod_of_flat_boundedBelow : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (K : Cx (ZMod Q)) (a : ℤ) [K.IsStrictlyGE a], (∀ n, FlatS (K.X n)) → K.Acyclic → (extCx (ZMod.castHom hq (ZMod q)) K).Acyclic := by
  first | exact @GlobalTheory.EtC.flatExtAcyc.main | exact GlobalTheory.EtC.flatExtAcyc.main | (intros; apply GlobalTheory.EtC.flatExtAcyc.main <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

theorem _root_.GlobalTheory.T.kummerRelation_boundary_kernel_generator_sum_zero : ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q)), (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) - freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0 → (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := by
  first
  | exact @GlobalTheory.EtC.KummerSplit.relation_kernel
  | exact GlobalTheory.EtC.KummerSplit.relation_kernel
  | (intros; apply GlobalTheory.EtC.KummerSplit.relation_kernel <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

theorem _root_.GlobalTheory.T.etale_atPrime_baseChange_of_integralClosureEtale : ∀ (A R R₁ DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R₁]
    [CommRing DA] [Algebra (GenFib A R) DA] (κ : R →+* R₁) (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    letI := closureAlg A R DA
    letI : Algebra R (Localization.AtPrime P₁) :=
      ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
    Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) :=
  @GlobalTheory.KeyOriginEnlarge.closureEtaleAt_comap_baseChange_atPrime
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_descent_endomorphism_quotient_group_scheme : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ f : A ⟶ A, IsMonHom f → (∀ h ∈ H, h ≫ f ∈ H) → ∃ f' : A' ⟶ A', IsMonHom f' ∧ ψ ≫ f' = f ≫ ψ := by
  first | exact @GlobalTheory.UPel.HT.Hecke.exists_desc_endo | exact GlobalTheory.UPel.HT.Hecke.exists_desc_endo | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_desc_endo; all_goals assumption)
end
