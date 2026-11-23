module

import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle005

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PowLevelCompat

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem box_gen_val_along {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y₀ : Scheme.{0}}
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε))
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (r : Z ⟶ Y) (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (r ≫ φ' a) y (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r y J' =
      ∏ i, val (t i) (r ≫ ρ i) y J := by
  apply GlobalTheory.PowTorus.box_gen_val_along <;> assumption

end PowLevelCompat

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem exists_twist_iff {S : Scheme.{0}} {A T : Over S} [GrpObj A] (L : LB A.left) (ψ : T ⊗ A ⟶ T ⊗ A)
    (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (n : ℤ) {W : Type} (g : W → Prop)
    (P : W → (LB.Sec (LPow A L n T) → LB.Sec (LPow A L n T) → Prop) → Prop) :
    (∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n])) (w : W),
      α.IsGen ∧ g w ∧ P w (IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α)) ↔
    ∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![n, -n])) (w : W),
      α.IsGen ∧ g w ∧ P w (IsTwistPull A L ψ m hm n n α) := by
  subst hm
  rfl

theorem exists_smul_of_pt_eq (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℤ)
    (x : TFK (R := R) F ⟶ A.A) (α β : LB.Gen (thetaLB A.A A.L n x)) (hα : α.IsGen) (hβ : β.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ (t : LB.Sec (LPow A.A A.L n (TFK (R := R) F)))
      (u u' : FieldBaseChange.SecOver (FieldBaseChange.abelianBase A F) (LPow A.A A.L n (TFK (R := R) F))),
      IsActOf A.A A.L n ⟨x, α, hα⟩ t u → IsActOf A.A A.L n ⟨x, β, hβ⟩ t u' → u' = c • u := by
  obtain ⟨a, ha⟩ := H1.exists_const A.L A.isLB (fst (TFK (R := R) F) A.A).left (BoxTheta.surj_fst hG A.isAb _)
    (LB.mulGen A.L ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x).left] ![n, -n] _ _ β
      (LB.invGen A.L ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x).left] ![n, -n] α))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.invGen_isGen _ _ _ _ hα)) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun t u u' hu hu' => ?_⟩
  · rintro rfl
    let z : (TFK (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TFK (R := R) F).left ⟶ A.A.left => exists_chart A.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (lift (𝟙 _) x).left z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (FieldBaseChange.gs_zero' _ z ⊤ trivial)
  · refine FieldBaseChange.SecOver.ext _ _ fun j => sec_ext_val A.isLB (fun y J hJ => ?_) j
    have e := (congrArg Units.val ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _)))).symm.trans
      (ha _ (𝟙 _) y J hJ)
    refine (BoxTheta.act_val _ t u' hu' (𝟙 _) y hJ).trans (Eq.trans ?_
      (FieldBaseChange.sval_smul' hJ (𝟙 _) c u).symm)
    refine Eq.trans ?_ (congrArg₂ (· * ·) e (BoxTheta.act_val _ t u hu (𝟙 _) y hJ).symm)
    exact (congrArg (fun v : ((TFK (R := R) F ⊗ A.A).left.presheaf.stalk y)ˣ => v.val * _)
      (inv_mul_cancel_right _ _).symm).trans ((congrArg (· * _) (Units.val_mul _ _)).trans (_root_.mul_assoc _ _ _))

theorem indAt_translT_iff : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A), IndAt U.toUnifPre F N p (translT A.A x) ↔ QkToAkU U.toUnifPre F N p x := by
  intro hL R _ _ _ I _ D A G _ _ _ U F _ _ _ N hN p x
  have hG := hL.1.globalFns
  have key := fun w₀ : W0 U.toUnifPre => exists_twist_iff A.L (translT A.A x) (translPt A.A x) (lift_snd _ _) (N : ℤ)
    (W := Frm D.toPre F N p.g.b) (fun w => w.IsGen) (fun w Q => ∀ (t t' : SecA A F N) s s',
      U.toUnifPre.ExpandsF F N w₀ t s → U.toUnifPre.ExpandsF F N w₀ t' s' → Q t t' → PhiRel D.toPre F N p w s s')
  constructor
  · rintro ⟨-, H⟩ w₀ hw₀
    obtain ⟨α, w, hα, hw, h⟩ := (key w₀).1 (H w₀ hw₀)
    refine ⟨(hL.1.kerPow _ A N hN _ x).1 fun _ => ⟨⊤, trivial, exists_isGen_pull _ α hα _⟩, ?_⟩
    rintro ⟨y, β, hβ⟩ rfl
    obtain ⟨c, hc, hcs⟩ := exists_smul_of_pt_eq hG A F (N : ℤ) _ α β hα hβ
    obtain ⟨w', hw', hΦ⟩ := ProdTorsion.exists_phiRel_smul hG p w hw c hc
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨w', hw', fun t t' s s' hs hs' ht => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := (lift_snd _ _ : translT A.A y ≫ _ = _)) A.isLB hα t
    have e₁ := hΦ _ _ (h t u s _ hs ((he u _).2 rfl) hu)
    have e₂ : s' = c • e u := ((he _ _).1 hs').symm.trans ((congrArg e (hcs t u t' hu ht)).trans (e.map_smul c u))
    exact e₂ ▸ e₁
  · intro H
    refine ⟨lift_fst _ _, fun w₀ hw₀ => (key w₀).2 ?_⟩
    haveI : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    haveI : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
    obtain ⟨θ, rfl⟩ := BoxTheta.exists_theta hL.1.kerPow A hN x (H w₀ hw₀).1
    obtain ⟨w, hw, h⟩ := (H w₀ hw₀).2 θ rfl
    exact ⟨θ.φ, w, θ.isGen, hw, h⟩

end GlobalTheory.UT
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem weilQkIs_iff_of_comm (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (D : DegData R I) {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
    (p p' : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b) (w' : Frm D.toPre F k p'.g.b)
    (hw : w.IsGen) (hw' : w'.IsGen) (z : F)
    (H : ∀ s s₁ s₂ s₃ s₄ : Fam D.toPre F k, PhiRel D.toPre F k p' w' s s₁ → PhiRel D.toPre F k p w s₁ s₂ →
      PhiRel D.toPre F k p w s s₃ → PhiRel D.toPre F k p' w' s₃ s₄ → s₂ = z • s₄)
    (hne : ∃ s s₃ s₄ : Fam D.toPre F k, PhiRel D.toPre F k p w s s₃ ∧ PhiRel D.toPre F k p' w' s₃ s₄ ∧ s₄ ≠ 0)
    (hk : 1 ≤ k) (ζ : F) : WeilQkIs D.toPre F k p p' ζ ↔ ζ = z := by
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R I D F k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG R I D F k hk p' w' hw'
  have r : ∀ s, PhiRel D.toPre F k p w s (Φ s) := fun s => (hΦ _ _).2 rfl
  have r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ' s) := fun s => (hΦ' _ _).2 rfl
  constructor
  · intro h
    obtain ⟨s, s₃, s₄, h₃, h₄, h0⟩ := hne
    have a := (isSmul_iff _ _ _).1 (h w w' hw hw' s _ _ s₃ s₄ (r' s) (r _) h₃ h₄)
    have b := H s _ _ s₃ s₄ (r' s) (r _) h₃ h₄
    exact smul_left_injective F h0 (a.symm.trans b)
  · rintro rfl v v' hv hv' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
    obtain ⟨c, -, hc⟩ := TorsionImage.exists_smul_of_phiVal p w v hw hv
    obtain ⟨c', -, hc'⟩ := TorsionImage.exists_smul_of_phiVal p' w' v' hw' hv'
    have q : ∀ s t, PhiRel D.toPre F k p v s t → t = c • Φ s := fun s t h =>
      hc s _ t ((phiRel_iff hG p w hw _ _).1 (r s)) ((phiRel_iff hG p v hv _ _).1 h)
    have q' : ∀ s t, PhiRel D.toPre F k p' v' s t → t = c' • Φ' s := fun s t h =>
      hc' s _ t ((phiRel_iff hG p' w' hw' _ _).1 (r' s)) ((phiRel_iff hG p' v' hv' _ _).1 h)
    rw [isSmul_iff, q _ _ h₂, q' _ _ h₁, q' _ _ h₄, q _ _ h₃, map_smul, map_smul,
      H s _ _ _ _ (r' s) (r _) (r s) (r' _), smul_comm c' ζ, smul_comm c ζ, smul_comm c c']

theorem weilQkIs_iff_weilIs : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ) := by
  intro hL R _ _ _ I _ D A G _ _ _ U F _ _ _ k hk p p' x x' hx hx' ζ
  have hG := hL.1.globalFns
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  obtain ⟨ρ, hρ, hcomm, -⟩ := thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_commIsOf hG A.isAb A.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, Units.ext (by simp [unitOn])⟩
  let E : SecM A.A A.L (k : ℤ) (TFK (R := R) F) → Fam D.toPre F k := fun v => e (SecM.toSec A.A v)
  have hE : ∀ s, ∃ v, E v = s := fun s => ⟨SecM.ofSec A.A (e.symm s), e.apply_symm_apply s⟩
  have a : ∀ v, PhiRel D.toPre F k p w (E v) (E (ρ θ v)) := fun v =>
    h _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have a' : ∀ v, PhiRel D.toPre F k p' w' (E v) (E (ρ θ' v)) := fun v =>
    h' _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have b : ∀ v t, PhiRel D.toPre F k p w (E v) t → t = E (ρ θ v) := fun v t H =>
    phi_unique p w ((phiRel_iff hG p w hw _ _).1 H) ((phiRel_iff hG p w hw _ _).1 (a v))
  have b' : ∀ v t, PhiRel D.toPre F k p' w' (E v) t → t = E (ρ θ' v) := fun v t H =>
    phi_unique p' w' ((phiRel_iff hG p' w' hw' _ _).1 H) ((phiRel_iff hG p' w' hw' _ _).1 (a' v))
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' (z : F) (fun s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ => by
    obtain ⟨v, rfl⟩ := hE s
    obtain rfl := b' _ _ h₁
    obtain rfl := b _ _ h₂
    obtain rfl := b _ _ h₃
    obtain rfl := b' _ _ h₄
    rw [hcomm θ θ' _ hc v]
    exact e.map_smul (z : F) (SecM.toSec A.A (ρ θ' (ρ θ v)))) (by
    obtain ⟨B, hB, -⟩ := BoxSpan.exists_basis hL.1.secBaseChange A k hk F (jFK (R := R) F)
    have : Nontrivial Γ((TFK (R := R) F).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    have hne := hB.ne_zero ⟨0, pow_pos hk _⟩
    refine ⟨_, _, _, a (B ⟨0, pow_pos hk _⟩), a' _, fun h0 => hne ?_⟩
    have h1 : SecM.toSec A.A (ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩))) = _ := e.map_eq_zero_iff.1 h0
    have h2 : ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩)) = 0 := congrArg (SecM.ofSec A.A) h1
    exact (ρ θ).map_eq_zero_iff.1 ((ρ θ').map_eq_zero_iff.1 h2)) hk (ζ : F)
  have hz := GlobalLift.weilIs_of_commIsOf hG A.isAb A.isLB hc
  rw [key]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective (CommutatorPairing.weilIs_unique hG A.isAb A.isLB H hz))

end GlobalTheory.UT
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompletedPoint

theorem adicLevelMap_surjective {B : Type} [CommRing B] (J : Ideal B) (n : ℕ) :
    Function.Surjective (adicLevelMap J (Nat.succ_le_succ (Nat.zero_le n))) := by
  intro p
  have : Set.range (PrimeSpectrum.comap (Ideal.Quotient.factorPow J (Nat.succ_le_succ (Nat.zero_le n)))) = _ :=
    range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective _)
  refine this.ge ?_
  refine (PrimeSpectrum.mem_zeroLocus _ _).2 fun a ha => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hb : b ∈ J := by
    have h : Ideal.Quotient.mk (J ^ (0 + 1)) b = 0 := ha
    rwa [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at h
  refine p.isPrime.mem_of_pow_mem (n + 1) ?_
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hb _)]
  exact zero_mem _

theorem hom_ext_spec {B : Type} [CommRing B] (J : Ideal B) [IsHausdorff J B] {S : CommRingCat.{0}}
    {g g' : Spec (CommRingCat.of B) ⟶ Spec S}
    (h : ∀ n, adicLevelι J (n + 1) ≫ g = adicLevelι J (n + 1) ≫ g') : g = g' := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨φ', rfl⟩ := Spec.map_surjective g'
  congr 1
  ext1
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' J (a := fun n => n + 1) (strictMono_id.add_const 1)
  intro n a
  have h1 := h n
  rw [← Spec.map_comp, ← Spec.map_comp] at h1
  exact congr($(Spec.map_injective h1).hom a)

theorem exists_of_isAdicFamily {B : Type} [CommRing B] (J : Ideal B) [IsAdicComplete J B] {X : Scheme.{0}}
    {V : X.Opens} (hV : IsAffineOpen V) {f : ∀ n : ℕ, Spec (CommRingCat.of (B ⧸ J ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily J f) (h₀ : ∀ p, f 0 p ∈ V) :
    ∃ g : Spec (CommRingCat.of B) ⟶ X, (∀ p, g p ∈ V) ∧ ∀ n, adicLevelι J (n + 1) ≫ g = f n := by
  have hr : ∀ n, Set.range (f n) ⊆ Set.range hV.fromSpec := fun n => by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := adicLevelMap_surjective J n p
    rw [hV.range_fromSpec, ← Scheme.Hom.comp_apply, hf.of_le (Nat.zero_le n)]
    exact h₀ q
  have hφ : ∀ n, ∃ φ : Γ(X, V) ⟶ CommRingCat.of (B ⧸ J ^ (n + 1)), Spec.map φ ≫ hV.fromSpec = f n := fun n => by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec (f n) (hr n))
    exact ⟨φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩
  choose φ hφ using hφ
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp
      (φ (m + 1)).hom = (φ m).hom := by
    intro m
    have h1 : adicLevelMap J (Nat.le_succ (m + 1)) ≫ Spec.map (φ (m + 1)) = Spec.map (φ m) := by
      rw [← cancel_mono hV.fromSpec, Category.assoc, hφ, hφ, hf m]
    rw [← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom)
  refine ⟨Spec.map (CommRingCat.ofHom
    (IsAdicComplete.StrictMono.liftRingHom J ha (fun n => (φ n).hom) hc)) ≫ hV.fromSpec, fun p => ?_,
    fun n => ?_⟩
  · exact hV.range_fromSpec.le ⟨_, rfl⟩
  · rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      IsAdicComplete.StrictMono.mk_comp_liftRingHom J ha (fun n => (φ n).hom) hc (n := n)]
    exact hφ n

theorem exists_completion {A : Type} [CommRing A] [IsNoetherianRing A] (J : Ideal A) :
    ∃ (B : Type) (_ : CommRing B) (ψ : A →+* B), IsAdicComplete (J.map ψ) B ∧ ψ.Flat ∧
      ∀ p : PrimeSpectrum A, J ≤ p.asIdeal → p ∈ Set.range (PrimeSpectrum.comap ψ) := by
  refine ⟨AdicCompletion J A, inferInstance, algebraMap _ _, ?_, ?_, fun p hp => ?_⟩
  · rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete J.fg_of_isNoetherianRing
  · exact RingHom.flat_algebraMap_iff.2 inferInstance
  · have h : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (J ^ 1))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, PrimeSpectrum.mem_zeroLocus,
        Ideal.mk_ker, pow_one]
      exact hp
    obtain ⟨q, rfl⟩ := h
    refine ⟨PrimeSpectrum.comap (AdicCompletion.evalₐ J 1).toRingHom q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]
    congr 2


open GlobalTheory.FormalPoint in
theorem exists_completed_point {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (G G' : Over (Spec (CommRingCat.of R))) [Flat G'.hom] [LocallyOfFiniteType G'.hom]
    (j : ∀ e : ℕ, thickObj R I e G' ⟶ thickObj R I e G)
    (hj : ∀ e, thickMap R I e G' ≫ (j (e + 1)).left = (j e).left ≫ thickMap R I e G)
    (x : (thickObj R I 0 G').left) (W : G.left.Opens) (W' : G'.left.Opens)
    (hW : (fstG I 0 G).left ((j 0).left x) ∈ W) (hW' : (fstG I 0 G').left x ∈ W') :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (g' : Spec (CommRingCat.of B) ⟶ G'.left)
      (g : Spec (CommRingCat.of B) ⟶ G.left), IsAdicComplete (I.map (algebraMap R B)) B ∧ Module.Flat R B ∧
      Flat g' ∧ (fstG I 0 G').left x ∈ Set.range g' ∧
      g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧
      g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ W' ∧ ⊤ ≤ g ⁻¹ᵁ W ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
        r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).left ≫ (fstG I e G).left = ρ ≫ g := by
  have tf : ∀ (e : ℕ) (H : Over (Spec (CommRingCat.of R))),
      thickMap R I e H ≫ (fstG I (e + 1) H).left = (fstG I e H).left := fun e H =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have fh : ∀ (e : ℕ) (H : Over (Spec (CommRingCat.of R))),
      (fstG I e H).left ≫ H.hom = (thickObj R I e H).hom ≫ thick R I e := fun e H => pullback.condition
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open hW W.isOpen
  have hci : IsClosedImmersion (thick R I 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hci' : IsClosedImmersion (fstG I 0 G').left :=
    inferInstanceAs (IsClosedImmersion (pullback.fst G'.hom (thick R I 0)))
  obtain ⟨O, hO, hO'⟩ := (fstG I 0 G').left.isClosedEmbedding.isInducing.isOpen_iff.1
    (((j 0).left ≫ (fstG I 0 G).left) ⁻¹ᵁ V).isOpen
  have hxO : (fstG I 0 G').left x ∈ O := hO'.ge hxV
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hVO⟩ := G'.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show (fstG I 0 G').left x ∈ O ∩ W' from ⟨hxO, hW'⟩) (hO.inter W'.isOpen)
  replace hV' : IsAffineOpen V' := hV'
  have hln : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have hN : IsNoetherianRing Γ(G'.left, V') := IsLocallyNoetherian.component_noetherian ⟨V', hV'⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV'.fromSpec ≫ G'.hom)
  have hφf : φ.hom.Flat := by
    have : Flat (Spec.map φ) := by rw [hφ]; exact Flat.comp _ _
    exact Flat.SpecMap_iff.1 this
  obtain ⟨B, _, ψ, hB, hψ, hs⟩ := exists_completion (I.map φ.hom)
  letI : Algebra R B := (ψ.comp φ.hom).toAlgebra
  have hBc : IsAdicComplete (I.map (algebraMap R B)) B := by
    rw [Ideal.map_map] at hB; exact hB
  let g' : Spec (CommRingCat.of B) ⟶ G'.left := Spec.map (CommRingCat.ofHom ψ) ≫ hV'.fromSpec
  have hg' : g' ≫ G'.hom = spMap (algebraMap R B) := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]; rfl
  have hg'V : ∀ p, g' p ∈ V' := fun p => hV'.range_fromSpec.le ⟨_, rfl⟩
  let y : Over.mk (spMap (algebraMap R B)) ⟶ G' := Over.homMk g' hg'
  have hy : ∀ e, reduction I y e ≫ (fstG I e G').left = adicLevelι (I.map (algebraMap R B)) (e + 1) ≫ g' :=
    fun e => reduction_fstG I y e
  have hf : IsAdicFamily (I.map (algebraMap R B)) fun e => reduction I y e ≫ (j e).left ≫ (fstG I e G).left := by
    intro e
    have h₁ : adicLevelMap (I.map (algebraMap R B)) (Nat.le_succ (e + 1)) ≫ reduction I y (e + 1) =
        reduction I y e ≫ thickMap R I e G' := by
      rw [← cancel_mono (fstG I (e + 1) G').left, Category.assoc, Category.assoc, hy, tf, hy, adicLevelMap_ι_assoc]
    show _ ≫ _ ≫ _ = _
    rw [reassoc_of% h₁, reassoc_of% (hj e), tf]
  obtain ⟨g, hgV, hg⟩ := exists_of_isAdicFamily _ hV hf fun p => by
    have h₁ : (fstG I 0 G').left (reduction I y 0 p) ∈ O := by
      have : (reduction I y 0 ≫ (fstG I 0 G').left) p ∈ V' := by rw [hy]; exact hg'V _
      exact (hVO this).1
    exact hO'.le h₁
  refine ⟨B, inferInstance, inferInstance, g', g, hBc, RingHom.Flat.comp hφf hψ, ?_, ?_, hg', ?_, fun p _ => (hVO (hg'V p)).2,
    fun p _ => hVW (hgV p), fun e Z ρ r h => ?_⟩
  · have : Flat (Spec.map (CommRingCat.ofHom ψ)) := Flat.SpecMap_iff.2 hψ
    exact Flat.comp _ _
  · obtain ⟨p, hp⟩ := hV'.range_fromSpec.ge hxV'
    obtain ⟨q, hq⟩ := hs p (by
      rw [Ideal.map_le_iff_le_comap]
      have h₁ : Spec.map φ p = thick R I 0 ((thickObj R I 0 G').hom x) := by
        rw [hφ, Scheme.Hom.comp_apply, hp, ← Scheme.Hom.comp_apply, fh]; rfl
      have h₂ : p.asIdeal.comap φ.hom = _ := congrArg PrimeSpectrum.asIdeal h₁
      rw [h₂]
      intro a ha
      show Ideal.Quotient.mk (I ^ (0 + 1)) a ∈ PrimeSpectrum.asIdeal _
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [zero_add, pow_one])]
      exact zero_mem _)
    exact ⟨q, (congrArg hV'.fromSpec hq).trans hp⟩
  · refine hom_ext_spec (I.map (algebraMap R B)) fun e => ?_
    rw [reassoc_of% (hg e), fh, ← Category.assoc (j e).left, Over.w, ← Category.assoc, reduction_hom,
      levelMap_thick]
  · have w : ρ ≫ spMap (algebraMap R B) = (r ≫ (thickObj R I e G').hom) ≫ thick R I e := by
      rw [← hg', ← Category.assoc, ← h, Category.assoc, fh, Category.assoc]
    obtain ⟨l, rfl⟩ := exists_factor_level I (algebraMap R B) ρ _ w
    obtain rfl : r = l ≫ reduction I y e := by
      rw [← cancel_mono (fstG I e G').left, Category.assoc, hy]
      exact h.trans (Category.assoc _ _ _)
    rw [Category.assoc, Category.assoc, hg]

end GlobalTheory.CompletedPoint

theorem GlobalTheory.exists_completed_point_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ x : (thickObj R I 0 G').left, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B ∧ Module.Flat R B ∧ Flat g' ∧ (fstG I 0 G').left x ∈ Set.range g' ∧ g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' ∧ ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g := by
  intro R _ _ _ I _ _ D D' A A' G G' _ _ _ _ _ hG' U U' hD j hj x
  have := hG'.smooth
  obtain ⟨jL, h⟩ : ∃ i, (fstG I 0 G).left ((j 0).hom.left x) ∈ U.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U.LG.isLB.cover.ge trivial)
  obtain ⟨jL', h'⟩ : ∃ i, (fstG I 0 G').left x ∈ U'.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U'.LG.isLB.cover.ge trivial)
  obtain ⟨B, _, _, g', g, H⟩ := GlobalTheory.CompletedPoint.exists_completed_point I G G' (fun e => (j e).hom)
    (fun e => (hj e).2.1) x _ _ h h'
  exact ⟨B, _, _, g', g, jL, jL', H⟩
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange

namespace GlobalTheory

theorem sval_eq_zero_of_indep_comb :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (X Y Y' : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of R)) [Flat π] (π' : Y' ⟶ Spec (CommRingCat.of R')) (p : Y' ⟶ Y), IsPullback p π' π (Spec.map (CommRingCat.ofHom f)) → ∀ (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (M : Type) [Fintype M] (β : M → R'), (∀ c : M → R, ∑ m, f (c m) * β m = 0 → ∀ m, c m = 0) → ∀ d : M → LB.Sec (LB.LinComb L φ ε), (∀ (y : Y') (J), Good L y J → ∑ m, constVal π' y (β m) * sval (d m) p y J = 0) → ∀ (m : M) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval (d m) r z J = 0 := by
  intro R R' _ _ f X Y Y' π _ π' p H L hL K _ φ ε M _ β hβ d hd m Z r z J hJ
  let e := (Fintype.equivFin M).symm
  have key := ThetaSpecialise.sec_indep H ε (φ := φ) (φ' := fun k => p ≫ φ k) (fun _ => rfl) (fun i => β (e i))
    (fun a ha i => by
      have := hβ (fun m => a (e.symm m)) (by
        rw [← ha, ← e.sum_comp]
        simp only [Equiv.symm_apply_apply]) (e i)
      simpa only [Equiv.symm_apply_apply] using this)
    (fun i => d (e i)) (sec_ext' hL fun y J hJ => by
      rw [sval_sum' hJ, sval_zero' hJ, ← hd y J hJ, ← e.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sval_smul' hJ]
      exact congrArg₂ (· * ·) (by rw [Category.id_comp])
        ((sval_pullOver H.w _ _ _ hJ).trans (by rw [Category.id_comp]))) (e.symm m)
  rw [Equiv.apply_symm_apply] at key
  exact (congrArg (fun s => sval s r z J) key).trans (sval_zero' (π := π) hJ r)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.genMaps_linCombIso_of_semiAbelian : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → (Geo.Tor.PMaps wL (thφ G (x3 G)) (thφ G (x3 G)) thε U'.cubG.t U.cubG.t (𝟙 _) ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] U'.symG U.symG (𝟙 G.left)) → ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom → (U'.gt e).q ≫ β.hom = (U.gt e).q → ∀ u : LB.Iso (D'.toPre.P.L.pull (U'.gt e).pG.left) (D.toPre.P.L.pull (U.gt e).pG.left), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw u r z jM (fun _ => jM') * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL') → ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.toPre.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι), (U.gt e).pG.left (y.left z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.toPre.P.L.U jM' → Geo.Tor.gw u ((τ ≫ (U.gt e).i) * y).left z jM (fun _ => jM') = Geo.Tor.gw u y.left z jM (fun _ => jM') := by
  first | exact @GlobalTheory.comparison_torus_invariant | exact GlobalTheory.comparison_torus_invariant | (intros; apply GlobalTheory.comparison_torus_invariant <;> assumption)
end
