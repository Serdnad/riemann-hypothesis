module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSquareDeterminantComparisonIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GenericSectionsMeetTransversally
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle037
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyRow

theorem comb_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (ψ : T'.left ⟶ T.left)
    (hψ : ψ ≫ T.hom = T'.hom ≫ f) {n : ℕ} (p : Fin n → (T ⟶ G)) (p' : Fin n → (T' ⟶ G'))
    (hp : ∀ c, (p' c).left ≫ φ = ψ ≫ (p c).left) (a : Fin n → ℤ) (ξ : 𝟙_ (Over S) ⟶ G) (ξ' : 𝟙_ (Over S') ⟶ G')
    (hξ : ξ'.left ≫ φ = f ≫ ξ.left) :
    ((List.ofFn fun c => p' c ^ a c).prod * (toUnit _ ≫ ξ')).left ≫ φ =
      ψ ≫ ((List.ofFn fun c => p c ^ a c).prod * (toUnit _ ≫ ξ)).left := by
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk ψ hψ
  have e₁ : ∀ c, pushHom h T' (p' c) = preHom U (p c) := fun c => Over.OverMorphism.ext (hp c)
  have t : ∀ {B : Scheme.{0}} (V : Over B), (toUnit V).left = V.hom := fun V =>
    (Category.comp_id _).symm.trans (Over.w (toUnit V))
  have e₂ : pushHom h T' (toUnit _ ≫ ξ') = preHom U (toUnit _ ≫ ξ) := Over.OverMorphism.ext (by
    show ((toUnit T').left ≫ ξ'.left) ≫ φ = ψ ≫ (toUnit T).left ≫ ξ.left
    rw [Category.assoc, hξ, t, t]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ξ.left) hψ.symm).trans (Category.assoc _ _ _)))
  have e : pushHom h T' ((List.ofFn fun c => p' c ^ a c).prod * (toUnit _ ≫ ξ')) =
      preHom U ((List.ofFn fun c => p c ^ a c).prod * (toUnit _ ≫ ξ)) := by
    rw [map_mul, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, e₂]
    congr 3
    funext c
    simp only [Function.comp_apply, map_zpow, e₁]
  exact congrArg (fun z => z.left) e

theorem cancel_units {A K κ : Type} [CommRing A] [Fintype K] [Fintype κ] [DecidableEq κ] {N m : ℕ} (s : K → Aˣ)
    (t : κ → Aˣ) (v : Aˣ) (x : K → A) (c : (κ → Fin N) → A) (y : κ → Fin N → A)
    (h : ∏ r, (s r ^ 1).val * x r = (((∏ r, s r ^ (1 : ℤ)) * ∏ k, t k ^ (-(m : ℤ))) * v).val *
      ∑ I, c I * ∏ k, (t k ^ m).val * y k (I k)) :
    ∏ r, x r = v.val * ∑ I, c I * ∏ k, y k (I k) := by
  simp only [pow_one, zpow_one, zpow_neg, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    ← Units.coe_prod, mul_left_comm _ (∏ k, t k ^ m).val, ← Finset.mul_sum] at h
  refine (Units.mul_right_inj (∏ r, s r)).1 (h.trans ?_)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [mul_comm (∏ k, t k ^ m), mul_right_comm, inv_mul_cancel_right]

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ u (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (b' : Fin N → RR x' m) (ξ : Fin 4 → Pt x) (ξ' : Fin 4 → Pt x') (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (q : (Fin 4 → Fin N) → R), KeyVia x' x f φ u → (∀ k, SecVia x' x φ u (b' k) (b k)) → (∀ r, (ξ' r).left ≫ φ = spMap f ≫ (ξ r).left) → w.IsGen → (∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ r)).left))) = (val w ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (q I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left)))) → ∃ w' : LB.Gen (LB.LinComb x'.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x'.P.A 4).left) (z : Z) J, Good x'.P.L z J → ∏ r, gs (ρ ≫ (alMap x' al r (ξ' r)).left) z (x'.P.L.U (J (ρ ≫ (alMap x' al r (ξ' r)).left))) (x'.th.f (J (ρ ≫ (alMap x' al r (ξ' r)).left))) = (val w' ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f (q I'))) * ∏ c, gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J (ρ ≫ (Out.powPr x'.P.A c).left))) ((b' (I' c)).f (J (ρ ≫ (Out.powPr x'.P.A c).left))) := by
  rintro R R' _ _ x x' f φ u m N al b b' ξ ξ' w q ⟨he, hg, F, hφ, hu, -, hth, -⟩ hb hξ hw H
  obtain ⟨ψ, hψ, hc⟩ := KeyPow.exists_isGrpPullback_pow hφ (Out.powIsPowGrp x.P.A 4) (Out.powIsPowGrp x'.P.A 4)
  have hc' : ∀ c : Fin 4, (Out.powPr x'.P.A c).left ≫ φ = ψ ≫ (Out.powPr x.P.A c).left := hc
  have ha : ∀ r, (alMap x' al r (ξ' r)).left ≫ φ = ψ ≫ (alMap x al r (ξ r)).left := fun r =>
    comb_push hφ ψ hψ.1.w _ _ hc' (al r) (ξ r) (ξ' r) (hξ r)
  obtain ⟨w', hw', P⟩ := H1.exists_gen_move x.P.isLB x'.P.isLB u ((isGen_iff u).1 hu) _
    (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) _ ψ
    (by rintro (r | c); exacts [ha r, hc' c]) w hw
  refine ⟨w', hw', fun Z ρ z J' hJ' => ?_⟩
  choose J hJ using fun χ : Z ⟶ x.P.A.left => exists_chart x.P.isLB (χ z)
  have ha' : ∀ r, (ρ ≫ ψ) ≫ (alMap x al r (ξ r)).left = (ρ ≫ (alMap x' al r (ξ' r)).left) ≫ φ := fun r => by
    rw [Category.assoc, Category.assoc, ha]
  have hc'' : ∀ c : Fin 4, (ρ ≫ ψ) ≫ (Out.powPr x.P.A c).left = (ρ ≫ (Out.powPr x'.P.A c).left) ≫ φ := fun r => by
    rw [Category.assoc, Category.assoc, hc']
  have E := H Z (ρ ≫ ψ) z J hJ
  have hv := (val_of w (ρ ≫ ψ) z J (fun k => J ((ρ ≫ Sum.elim (fun r => (alMap x' al r (ξ' r)).left)
    (fun c => (Out.powPr x'.P.A c).left) k) ≫ φ)) (by rintro (r | c); exacts [congrArg J (ha' r), congrArg J (hc'' c)])).trans
    (P Z ρ z _ (fun k => J' (ρ ≫ Sum.elim (fun r => (alMap x' al r (ξ' r)).left)
    (fun c => (Out.powPr x'.P.A c).left) k)) (fun k => hJ _) (fun k => hJ' _))
  rw [Fintype.prod_sum_type] at hv
  have hth' : KeyVia.Via u 1 x'.th.f x.th.f := fun j i h => (hth j i h).trans (by rw [pow_one])
  have hq : ∀ a : R, gs (ρ ≫ ψ) z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ a) =
      gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f a)) := fun a =>
    (gs_appLE ψ ⊤ ⊤ le_top ρ z trivial _).symm.trans
      (congrArg (gs ρ z ⊤) (KeyVia.appLE_cst f _ _ hψ.1.w le_top a))
  rw [hv] at E
  refine cancel_units (m := m)
    (fun r => gw u (ρ ≫ (alMap x' al r (ξ' r)).left) z (J ((ρ ≫ (alMap x' al r (ξ' r)).left) ≫ φ))
      (J' (ρ ≫ (alMap x' al r (ξ' r)).left)))
    (fun c => gw u (ρ ≫ (Out.powPr x'.P.A c).left) z (J ((ρ ≫ (Out.powPr x'.P.A c).left) ≫ φ))
      (J' (ρ ≫ (Out.powPr x'.P.A c).left))) _ _ _
    (fun c k => gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J' (ρ ≫ (Out.powPr x'.P.A c).left)))
      ((b' k).f (J' (ρ ≫ (Out.powPr x'.P.A c).left)))) ?_
  refine Eq.trans (Finset.prod_congr rfl fun r _ => ?_) (E.trans (congrArg₂ (· * ·) rfl
    (Finset.sum_congr rfl fun I _ => congrArg₂ (· * ·) (hq _) (Finset.prod_congr rfl fun c _ => ?_))))
  · rw [ha']
    exact (KeyBasis.via_val hth' _ z (hJ _) (hJ' _)).symm
  · rw [hc'']
    exact KeyBasis.via_val (w := u) (hb (I c)) _ z (hJ _) (hJ' _)

end GlobalTheory.KeyRow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.exists_squareDeterminantComparison_isAlgClosed : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (m ^ x.P.g) → RR x m), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → ∃ lam, IsSquareDeterminantComparison x m al b lam := by
  first | exact @GlobalTheory.SimilDet.exists_l2Val | exact GlobalTheory.SimilDet.exists_l2Val | (intros; apply GlobalTheory.SimilDet.exists_l2Val <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.generic_sections_meet_transversally : Out.Laws → ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n : ℕ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (T : Fin x'.P.g × Fin (n ^ x.P.g) → K) (s : Fin x'.P.g → RR x' n), 4 ≤ n → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → AlgebraicIndependent k T → (∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) → ∃ (d : ℕ) (z : Fin d → Pt x') (ch : Fin d → x'.P.L.ι), EtZ x' s z ch := by
  first | exact @GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent | exact GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent | (intros; apply GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyGenInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

theorem value_mem_valuationSubring (κ : Rule) (hU : UnitSp κ) (S K : Type) [CommRing S] [Field K] [CharZero K] [Algebra S K]
    (y : KeyIn S) (x : KeyIn K) (h : KeyPB x y (algebraMap S K)) (V : ValuationSubring K) (hV : IsDiscreteValuationRing V)
    (hS : ∀ s : S, algebraMap S K s ∈ V) : (κ K x : K) ∈ V ∧ (κ K x : K)⁻¹ ∈ V := by
  let j : S →+* V := (algebraMap S K).codRestrict V.toSubring hS
  obtain ⟨yV, hyV⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y j
  have hc : (algebraMap V K).comp j = algebraMap S K := RingHom.ext fun _ => rfl
  have hx : KeyPB x yV (algebraMap V K) :=
    GlobalTheory.KeyCancel.keyPB_cancel S V K y yV x j (algebraMap V K) hyV (by rw [hc]; exact h)
  obtain ⟨u, hu, -⟩ := hU V K yV x hx
  refine ⟨?_, ?_⟩
  · rw [hu]; exact (u : V).2
  · have : (κ K x : K)⁻¹ = algebraMap V K (u⁻¹ : Vˣ) := by
      rw [hu]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, Units.mul_inv, map_one]
    rw [this]; exact ((u⁻¹ : Vˣ) : V).2

theorem isIntegral_value : ∀ κ : Rule, UnitSp κ → ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K]
    [CharZero K] [Algebra S K] [IsFractionRing S K] (y : KeyIn S) (x : KeyIn K), KeyPB x y (algebraMap S K) →
    IsIntegral S (κ K x : K) ∧ IsIntegral S ((κ K x : K)⁻¹) := by
  intro κ hU S K _ _ _ _ _ _ _ y x h
  exact ⟨GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring S K _ fun V hV hS => (value_mem_valuationSubring κ hU S K y x h V hV hS).1,
    GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring S K _ fun V hV hS => (value_mem_valuationSubring κ hU S K y x h V hV hS).2⟩

end GlobalTheory.KeyGenInt
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.KeyKa

namespace GlobalTheory.KeyLine

section Via

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem gs_unit_pow {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)ˣ) (n : ℕ) :
    gs r z U (a.val ^ n) = (gm r z U a).val ^ n := by
  rw [← gs_unit r z U h, gs_eq r z U h, gs_eq r z U h, map_pow, map_pow]

theorem via_iff_stalk (w : LB.Iso L' (L.pull F)) (l : ℕ) (a' : ∀ i, Γ(X', L'.U i)) (a : ∀ j, Γ(X, L.U j)) :
    KeyVia.Via w l a' a ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (a j) = (gw w r z j k).val ^ l * gs r z _ (a' k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun y hy => mem_pull.1 hy.1
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit_pow _ z _ hy _ l)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit_pow _ y _ hy _ l).symm

variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))} {l : ℕ}
  {a : ∀ j, Γ(X, L.U j)} {a' : ∀ i, Γ(X', L'.U i)} {a'' : ∀ i, Γ(X'', L''.U i)}

theorem via_comp (T : Tri w w' w'') (hL' : L'.IsLB) (h : KeyVia.Via w l a' a) (h' : KeyVia.Via w' l a'' a') :
    KeyVia.Via w'' l a'' a := by
  refine (via_iff_stalk _ _ _ _).2 fun Z q z j k hj hk => ?_
  obtain ⟨i, hi⟩ := exists_chart hL' (F' (q z))
  have e := (via_iff_stalk _ _ _ _).1 h Z (q ≫ F') z j i hj hi
  have e' := (via_iff_stalk _ _ _ _).1 h' Z q z i k hi hk
  rw [T Z q z j i k hj hi hk, ← Category.assoc, e, e', Units.val_mul, mul_pow, _root_.mul_assoc]

theorem via_cancel (T : Tri w w' w'') (hL : L.IsLB) (h : KeyVia.Via w l a' a) (h'' : KeyVia.Via w'' l a'' a) :
    KeyVia.Via w' l a'' a' := by
  refine (via_iff_stalk _ _ _ _).2 fun Z q z i k hi hk => ?_
  obtain ⟨j, hj⟩ := exists_chart hL (F (F' (q z)))
  have e := (via_iff_stalk _ _ _ _).1 h Z (q ≫ F') z j i hj hi
  have e' := (via_iff_stalk _ _ _ _).1 h'' Z q z j k hj hk
  rw [T Z q z j i k hj hi hk, ← Category.assoc, e, Units.val_mul, mul_pow, _root_.mul_assoc] at e'
  exact ((Units.isUnit _).pow l).mul_left_cancel e'

end Via

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'} {x'' : KeyIn R''}
  {f : R →+* R'} {f' : R' →+* R''}

theorem keyVia_g {φ w} (h : KeyVia x' x f φ w) : x'.P.g = x.P.g := by
  obtain ⟨_, hg, _⟩ := h
  exact hg

theorem keyVia_isPullback {φ w} (h : KeyVia x' x f φ w) : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f) := by
  obtain ⟨_, _, _, h, _⟩ := h
  exact h.1

theorem keyVia_trans {φ w φ' w'} (H : KeyVia x' x f φ w) (H' : KeyVia x'' x' f' φ' w') :
    ∃ w'', KeyVia x'' x (f'.comp f) (φ' ≫ φ) w'' ∧ ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l),
      SecVia x' x φ w s' s → SecVia x'' x' φ' w' s'' s' → SecVia x'' x (φ' ≫ φ) w'' s'' s := by
  obtain ⟨he, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨he', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨w'', ⟨he'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩,
    fun l s s' s'' h h' => via_comp (L := x.P.L) (L' := x'.P.L) (L'' := x''.P.L) (l := l) (a := s.f) (a' := s'.f) (a'' := s''.f) T x'.P.isLB h h'⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂
  · refine KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' z)
    have a := KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

theorem keyVia_cancel {φ w φ'' w''} (H : KeyVia x' x f φ w) (H'' : KeyVia x'' x (f'.comp f) φ'' w'') :
    ∃ φ' w', KeyVia x'' x' f' φ' w' ∧ φ' ≫ φ = φ'' ∧ ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l),
      SecVia x' x φ w s' s → SecVia x'' x φ'' w'' s'' s → SecVia x'' x' φ' w' s'' s' := by
  obtain ⟨he, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := H
  obtain ⟨he'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := H''
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp f f'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel x.P.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp F = F'' := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', w', ⟨he', hg''.trans hg.symm, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel x.P.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel x.P.isLB (fun _ => he') r r''),
    (KeyCancel.appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩, rfl,
    fun l s s' s'' h h'' => via_cancel (L := x.P.L) (L' := x'.P.L) (L'' := x''.P.L) (l := l) (a := s.f) (a' := s'.f) (a'' := s''.f) T x.P.isLB h h''⟩
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (KeyCancel.appLE_eq_iff_stalk w'' x.th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, ← hFF, ← Category.assoc]
      congr 1
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyLine
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyPow

theorem keyFormulaPow_of_keyRule :
    ThetaUnifAV → ∀ N : ℕ → ℕ, (∀ g, 1 ≤ N g) → GlobalTheory.KeyPow.KeyRule N 1 GlobalTheory.KeyPow.charHalf → GlobalTheory.KeyFormulaPow := by
  rintro hT N hN ⟨κ, hH, hF, hU, hK⟩
  refine ⟨N, hN, κ, fun K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M =>
      hH K P hg rig hr th hth v hv th' hth' v' hv' a M hg,
    fun K K' _ _ _ _ f x x' => hF K K' f x x' x.g_pos,
    fun R K _ _ _ _ _ _ _ x xK => hU R K x xK x.g_pos,
    fun x u τ a b h₁ h₂ ha hb h₃ h₄ h₅ h₆ =>
      hK x τ a b x.g_pos ⟨ha, hb⟩ ((normalAt_one_iff x τ a b).2 ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩), ?_⟩
  intro x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  obtain ⟨u', τ, M, a, b, c, k₁, k₂, ha, hb, k₃, k₄, hc, k₅, hM, k₆, hn⟩ :=
    keyIn_normal_form_and_archimedean_constant hT x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hv := value_at_normalForm N 1 (κ ℂ) x.P.g a b x.g_pos (hH ℂ)
    (fun y h τ' hy => hK y τ' _ _ y.g_pos ⟨fun i => ha _, fun i => hb _⟩ hy) x rfl τ M c hc hM
    ⟨u', k₁, k₂, k₃, k₄, k₅, k₆⟩
  rw [hv, norm_pow, pow_mul nth, pow_mul nη, ← mul_pow, ← mul_pow, hn, ← pow_mul]

end GlobalTheory.KeyPow
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.thetaFrame_value_independent_normalForm : ThetaUnifAV → Key.Chi.InversionStatement → ∀ (x : KeyIn ℂ) (t t' : ℂ), (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8) → (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t' = M.det ^ 4 / c ^ 8) → t = t' := by
  first | exact @GlobalTheory.NormalUnique.thetaFrame_value_unique | exact GlobalTheory.NormalUnique.thetaFrame_value_unique | (intros; apply GlobalTheory.NormalUnique.thetaFrame_value_unique <;> assumption)
end
