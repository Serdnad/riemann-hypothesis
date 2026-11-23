module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle005
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem ιMulti_ne_zero {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b : Fin r → E}
    (hb : LinearIndependent Ω b) : exteriorPower.ιMulti Ω r b ≠ 0 := by
  apply GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent <;> assumption

theorem ιMulti_mem_span {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (R : Subring Ω) {r : ℕ} (b c : Fin r → E)
    (hc : ∀ i, c i ∈ Submodule.span R (Set.range b)) :
    exteriorPower.ιMulti Ω r c ∈ Submodule.span R {exteriorPower.ιMulti Ω r b} := by
  classical
  choose m hm using fun i => (Submodule.mem_span_range_iff_exists_fun R).1 (hc i)
  have hc' : c = fun i => ∑ j, ((m i j : R) : Ω) • b j := by
    funext i
    rw [← hm i]
    rfl
  have hsum : exteriorPower.ιMulti Ω r (fun i => ∑ j, ((m i j : R) : Ω) • b j) =
      ∑ σ : Fin r → Fin r, exteriorPower.ιMulti Ω r (fun i => ((m i (σ i) : R) : Ω) • b (σ i)) :=
    (exteriorPower.ιMulti Ω r).toMultilinearMap.map_sum (fun i j => ((m i j : R) : Ω) • b j)
  rw [hc', hsum]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hsm : exteriorPower.ιMulti Ω r (fun i => ((m i (σ i) : R) : Ω) • b (σ i)) =
      (∏ i, ((m i (σ i) : R) : Ω)) • exteriorPower.ιMulti Ω r (b ∘ σ) :=
    (exteriorPower.ιMulti Ω r).toMultilinearMap.map_smul_univ _ _
  have hR : (∏ i, ((m i (σ i) : R) : Ω)) ∈ R := prod_mem fun i _ => (m i (σ i)).2
  rw [hsm]
  by_cases hσ : Function.Injective σ
  · have hperm := (exteriorPower.ιMulti Ω r).map_perm b (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ))
    have hco : b ∘ (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ)) = b ∘ σ := rfl
    rw [hco] at hperm
    rw [hperm]
    refine Submodule.smul_mem _ (⟨_, hR⟩ : R) ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ))) with h | h
    · rw [h, one_smul]
      exact Submodule.mem_span_singleton_self _
    · rw [h, Units.neg_smul, one_smul]
      exact neg_mem (Submodule.mem_span_singleton_self _)
  · have h0 : exteriorPower.ιMulti Ω r (b ∘ σ) = 0 :=
      (exteriorPower.ιMulti Ω r).map_eq_zero_of_not_injective _ fun h => hσ h.of_comp
    rw [h0, smul_zero]
    exact zero_mem _

theorem wedge_eq_span_ιMulti : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p → L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} ∧ exteriorPower.ιMulti Ω r b ≠ 0 := by
  intro X Ω _ ξ E _ _ L r b p ⟨hb, hL⟩
  refine ⟨le_antisymm ?_ ?_, ιMulti_ne_zero hb⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact ιMulti_mem_span (regAt ξ p) b c (fun i => hL ▸ hc i)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨b, fun i => by rw [hL]; exact Submodule.subset_span ⟨i, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame
end
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.regular_lattice_local_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type) (reg : Q → Subring Ω) (r : ℕ) (Λ : Q → AddSubgroup (Fin r → Ω)), (∀ q, IsLocalRing (reg q)) → (∀ q, ∀ a ∈ R, a ∈ reg q) → (∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q)) → (∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R) → (∀ q, ∃ g ∈ R, g ≠ 0 ∧ g⁻¹ ∈ reg q ∧ ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q', g⁻¹ ∈ reg q' → ∀ e, e ∈ Λ q' ↔ ∃ a : Fin r → Ω, (∀ i, a i ∈ reg q') ∧ e = ∑ i, a i • f i) → LocFree R r (⨅ q, Λ q) ∧ ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) → ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.SecAlg.locFree_and_extend | exact GlobalTheory.CompanionTheory.Ar.Num.SecAlg.locFree_and_extend | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.SecAlg.locFree_and_extend <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem dotDual_overlap : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (L : ι → AddSubgroup (Fin r → Ω)),
    (∀ c, ∀ a ∈ chartRing O x c, ∀ e ∈ L c, a • e ∈ L c) →
    (∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) →
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ L c) ∧
      ∀ e ∈ L c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ dotDual (chartRing O x i) (L i),
      ∃ m : ℕ, (x i / x j) ^ m • e ∈ dotDual (chartRing O x j) (L j) :=
  PositivityTheory.Xgn.hodge_dual_lattice_overlap

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem chartBundle_dotDual_localFrame : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)),
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing O x i) ∧ (∀ l, c l ∈ chartRing O x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, ∃ b : Fin r → Fin r → Ω, LinearIndependent Ω b ∧
        Submodule.span Ω (Set.range b) = ⊤ ∧ ∀ e : Fin r → Ω,
          ((∃ n : ℕ, f l ^ n • e ∈ dotDual (chartRing O x i) (B.lat i)) ↔
            ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O x i) ∧ e = ∑ q, a q • b q) :=
  PositivityTheory.Xgn.hodge_dual_frame_exists

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.CompanionTheory.Relay.regular_at_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ f g' ⟨U, hU, s, hs⟩
  refine ⟨F ⁻¹ᵁ U, hU, (F.app U).hom s, fun t h => ?_⟩
  have e := GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R T Γ R' Γ' F hF κ hκ t
  have h1 : ⊤ ≤ ((Γ'.pt t).left ≫ F) ⁻¹ᵁ U := h
  have h2 : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := e ▸ h1
  have h3 : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun z _ => by
    have hz : z = Spec.map (CommRingCat.ofHom κ) (IsLocalRing.closedPoint (FractionRing R')) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [hz]
    exact h2 (by trivial)
  refine (PositivityTheory.HtPt.Htat.Pull.valAt_comp _ F U h1 s).symm.trans
    ((PositivityTheory.HtPt.Htat.Pull.valAt_congr e U h1 h2 s).trans ?_)
  rw [PositivityTheory.HtPt.Htat.Pull.valAt_spec κ _ U h3, hs t h3]
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.exists_denominator_btOrder :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
      (Γ : GlobalTheory.CompanionTheory.Ar.BT.QFGroup R T),
      ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ :=
  @GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.regular_function_iff_section : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.regularAt_forall_iff_exists_section
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.section_eq_zero_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 :=
  @GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

theorem _root_.GlobalTheory.T.height_one_prime_dvr_stalk : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → IsLocallyNoetherian X → IsNormalScheme X → ∀ (p : Cpt ξ) (P : PrimeSpectrum (regAt ξ p)), P.asIdeal.height = 1 → ∃ (q : Cpt ξ) (hs : q.1 ⤳ p.1), (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) ∧ (∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q) ∧ ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne.exists_generisation_of_height_eq_one | exact GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne.exists_generisation_of_height_eq_one | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne.exists_generisation_of_height_eq_one <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.btSet_eq_of_le (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens)
    (hU : Γ.IsFinOpenSub U) (hU' : Γ.IsFinOpenSub U') (hle : U' ≤ U) :
    Γ.btSet U = Γ.btSet U' := by
  apply Set.Subset.antisymm
  · intro f hf t g hg
    exact hf t g (hle hg)
  · intro f hf s g hg
    have hcover := Transl.translates_cover R T Γ U U' hU hU' hle g hg
    obtain ⟨σ, t, hσ, hmem⟩ := hcover
    have hreg := hf (s * t⁻¹) _ hmem
    have key := QFGroup.regularAt_translate R T Γ σ t hσ
      (fun h => algebraMap R (FractionRing R) (f (s * t⁻¹ * h))) g hreg
    have heq : (fun h => algebraMap R (FractionRing R) (f (s * t⁻¹ * (t * h)))) =
        fun h => algebraMap R (FractionRing R) (f (s * h)) := by
      funext h
      congr 2
      rw [_root_.mul_assoc, inv_mul_cancel_left]
    simpa only [heq] using key

theorem QFGroup.btOrder_eq_of_le : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → Γ.btOrder U = Γ.btOrder U' := by
  intro R _ _ _ T _ _ Γ U U' hU hU' hle
  unfold QFGroup.btOrder
  rw [QFGroup.btSet_eq_of_le R T Γ U U' hU hU' hle]

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.translate_into_smaller_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → ∀ g ∈ U, ∃ (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t ∧ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g ∈ U' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Transl.translates_cover | exact GlobalTheory.CompanionTheory.Ar.BT.Transl.translates_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Transl.translates_cover <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ActBC

theorem exists_act_extends : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (O : Type) [CommRing O] (act : OAct O G) (act' : OAct O G'), (∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → Submodule.span L' (Set.range j) = ⊤ → ∀ ρ : O →+* Module.End L V, MV.IsActOf act.act ρ → ∃ ρ' : O →+* Module.End L' V', MV'.IsActOf act'.act ρ' ∧ ∀ a x, ρ' a (j x) = j (ρ a x) := by
  intro L L' _ _ e G G' _ _ φ hpb O _ act act' hcomm V V' _ _ _ _ MV MV' j hj hspan ρ hρ
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ _ _ _ _ MV' _ act'.act act'.hom act'.one
    act'.mul act'.add
  refine ⟨ρ', hρ', fun a x => ?_⟩
  apply MV'.inj
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · rw [hρ' a (j x), Over.comp_left, Category.assoc, hcomm a, ← Category.assoc, hj x, Category.assoc,
      ← Over.comp_left, ← hρ a x, hj (ρ a x)]
  · rw [Over.w, Over.w]

end GlobalTheory.CompanionTheory.Ar.ActBC
end
end
