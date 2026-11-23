module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.UniformizationBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle034

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionImage

open FieldBaseChange

theorem translT_translPt {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x y : T ⟶ A) :
    translT A x ≫ translPt A y = translPt A (y * x) := by
  show lift (fst T A) ((fst T A ≫ x) * snd T A) ≫ ((fst T A ≫ y) * snd T A) = (fst T A ≫ (y * x)) * snd T A
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd, _root_.mul_assoc]

theorem translPt_one {S : Scheme.{0}} {A : Over S} [GrpObj A] (T : Over S) :
    translPt A (1 : T ⟶ A) = snd T A := by
  show (fst T A ≫ 1) * snd T A = _
  rw [MonObj.comp_one, _root_.one_mul]

theorem translT_inv {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x : T ⟶ A) :
    translT A x⁻¹ ≫ translT A x = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, Category.id_comp]
    exact (congrArg (_ ≫ ·) (lift_snd _ _)).trans
      ((translT_translPt _ _).trans (by rw [mul_inv_cancel, translPt_one]))

theorem eq_of_gen {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F] (q : Spec (CommRingCat.of F) ⟶ S)
    (x x' : Over.mk q ⟶ P.A)
    (r : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(translPt P.A x).left, (translPt P.A x').left] ![1, -1]))
    (hr : r.IsGen) : x = x' := by
  refine mul_inv_eq_one.1 (P.ktriv F q (x * x'⁻¹) fun p => ⟨⊤, trivial, ?_⟩)
  obtain ⟨w, hw, -⟩ := VVRank.exists_gen_pullTo
    (φ' := ![(translPt P.A (x * x'⁻¹)).left, (snd (Over.mk q) P.A).left]) r hr (translT P.A x'⁻¹).left (fun i => by
      fin_cases i
      · exact congrArg (fun q => q.left) (translT_translPt x'⁻¹ x)
      · exact congrArg (fun q => q.left) ((translT_translPt x'⁻¹ x').trans
          (by rw [mul_inv_cancel, translPt_one])))
  exact exists_isGen_pull (translDiff P.A P.L (x * x'⁻¹)) w hw _

theorem exists_smul_of_phiVal {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k)
    (w w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ s t t' : Fam D F k, DVR.PhiVal p w s.s t.s → DVR.PhiVal p w' s.s t'.s → t' = c • t := by
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (fun a => ⟨a, rfl⟩)
    (LB.mulGen D.P.L _ _ _ _ w' (LB.invGen D.P.L _ _ w))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw' (DVR.invGen_isGen _ _ _ _ hw)) (fun U _ h => by
      refine (DVR.prod_sum₂ _ (c := ∏ i, h (DegPre.lineφ D F p.g.b i) ^ DegPre.lineε k i) rfl
        (DVR.prod_neg _ _ rfl)).trans ?_
      exact mul_inv_cancel _)
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun s t t' h h' => DVR.phi_unique p w' h' fun α β e' T ρ z J hJ => ?_⟩
  · rintro rfl
    let z : (TF (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (𝟙 _) z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (gs_zero' _ z ⊤ trivial)
  · have e := ha _ (ρ ≫ fst _ _).left z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id] at e
    refine (DVR.sval_smul c t β ρ.left z hJ).trans ?_
    rw [h α β e' T ρ z J hJ, val_mul hJ, val_mul hJ]
    refine (congrArg (· * _) e.symm).trans ?_
    rw [mul_left_comm, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem pt_eq_of_proportional (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K)))
    {F : Type} [Field F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K)) {n : ℕ} (hn : 1 ≤ n)
    (θ θ' : ThetaGrp P.A P.L (n : ℤ) (Over.mk q)) (c : Γ((Over.mk q).left, ⊤)ˣ)
    (H : ∀ t u u', IsActOf P.A P.L (n : ℤ) θ t u → IsActOf P.A P.L (n : ℤ) θ' t u' → ∀ y J, Good P.L y J →
      VVRank.sv P.A u' (𝟙 _) y J =
        (gm (𝟙 _ ≫ (fst (Over.mk q) P.A).left) y ⊤ c).val * VVRank.sv P.A u (𝟙 _) y J) : θ.pt = θ'.pt := by
  have hL := P.isLB
  let T := Over.mk q
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ P.A
  have : IsIntegral (T ⊗ P.A).left :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F _
  have hN : ∀ y : (T ⊗ P.A).left, IsIntegrallyClosed ((T ⊗ P.A).left.presheaf.stalk y) := fun y =>
    ((isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ (fst T P.A).left
      (inferInstanceAs (Smooth (pullback.fst q P.A.hom)))).2.1 y).2
  obtain ⟨b, hb, -⟩ := BoxSpan.exists_basis hS P 1 le_rfl F q
  have : Nontrivial Γ(T.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := hb.ne_zero ⟨0, by simp⟩
  let th : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => (snd T P.A).left) (fun _ => ((1 : ℕ) : ℤ))) :=
    SecM.toSec P.A (b ⟨0, by simp⟩)
  have tr : ∀ x : T ⟶ P.A, ∃ s : LB.Sec (LB.LinComb P.L (K := PUnit) (fun _ => (translPt P.A x).left) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ P.A).left) (z : Z) (J), Good P.L z J →
        sval s r z J = sval th (r ≫ (translT P.A x).left) z J := fun x => by
    have e : (translT P.A x).left ≫ (snd T P.A).left = (translPt P.A x).left :=
      congrArg (fun q => q.left) (lift_snd _ _ : translT P.A x ≫ snd T P.A = _)
    obtain ⟨s, hs⟩ := exists_sec hL (φ' := fun _ : PUnit => (translPt P.A x).left) (ε' := fun _ => 1)
      (fun U _ h => by simp only [e, Fintype.prod_unique, Nat.cast_one]) (H1.SectionArithmetic.pullSec th (translT P.A x).left)
    exact ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ r z hJ)⟩
  obtain ⟨s, hs⟩ := tr θ.pt
  obtain ⟨s', hs'⟩ := tr θ'.pt
  obtain ⟨t, ht⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T P.A).left) (ε' := fun _ => (n : ℤ))
    (fun U _ h => by simp) (H1.SectionArithmetic.powSec fun _ : Fin n => th)
  have ht' : ∀ (r : (T ⊗ P.A).left ⟶ (T ⊗ P.A).left) y J, Good P.L y J → sval t r y J = sval th r y J ^ n :=
    fun r y J hJ => by
      rw [ht _ r y J hJ, H1.SectionArithmetic.sval_powSec _ r y hJ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨u, hu⟩ : ∃ u, IsActOf P.A P.L (n : ℤ) θ t u := VVRank.exists_isTwistPull P.A hL θ.isGen t
  obtain ⟨u', hu'⟩ : ∃ u, IsActOf P.A P.L (n : ℤ) θ' t u := VVRank.exists_isTwistPull P.A hL θ'.isGen t
  have hc : (constGen P.A P.L c).IsGen := isGen_of_gm _ fun y j j' _ _ => by
    obtain rfl : j = j' := Subsingleton.elim _ _
    rw [trF, Fintype.prod_empty, _root_.one_mul]
  obtain ⟨v, hv, hv'⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(translPt P.A θ'.pt).left, (translPt P.A θ.pt).left])
    (ε' := ![(n : ℤ), -(n : ℤ)]) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
    (LB.mulGen P.L _ _ _ _ (LB.invGen P.L ![(snd T P.A).left, (translPt P.A θ'.pt).left] ![(n : ℤ), -(n : ℤ)] θ'.φ)
      (LB.mulGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n : ℤ), -(n : ℤ)] _ _ θ.φ
        (constGen P.A P.L c)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ θ'.isGen)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ θ.isGen hc))
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow _ _ hN P.L hL _ _ n hn s' s v hv (by
    by_contra h0
    have h0' : ∀ j, s.f j = 0 := fun j => by_contra fun hj => h0 ⟨j, hj⟩
    refine hne (Subtype.ext (funext fun j => sec_ext_val (s := th) (s' := H1.SectionArithmetic.secZero _) hL
      (fun y J hJ => ?_) j))
    have e := hs _ (translT P.A θ.pt⁻¹).left y J hJ
    rw [← Over.comp_left, translT_inv, Over.id_left] at e
    refine e.symm.trans (Eq.trans ?_ (gs_zero' _ y _ (hJ.mem _ _)).symm)
    exact (congrArg (gs _ y _) (h0' _)).trans (gs_zero' _ y _ (hJ.mem _ _))) (fun y J hJ => by
    have e := H t u u' hu hu' y J hJ
    rw [VVRank.sv_of_isTwistPull P.A hu _ y hJ, VVRank.sv_of_isTwistPull P.A hu' _ y hJ] at e
    have e₁ := (ht' _ y J hJ).trans (congrArg (· ^ n) (hs _ (𝟙 _) y J hJ).symm)
    have e₂ := (ht' _ y J hJ).trans (congrArg (· ^ n) (hs' _ (𝟙 _) y J hJ).symm)
    have e₃ := (congrArg _ e₂).symm.trans (e.trans (congrArg _ (congrArg _ e₁)))
    have e₄ := (hv' _ (𝟙 _) y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (H1.val_constGen _ c _ y J)))))
    rw [e₄, Units.val_mul, _root_.mul_assoc, Units.eq_inv_mul_iff_mul_eq, Units.val_mul, _root_.mul_assoc]
    exact e₃.trans (mul_left_comm _ _ _))
  exact (eq_of_gen P q _ _ r hr).symm

theorem qkToAkU_unique : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) (x x' : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F n p x → QkToAkU U.toUnifPre F n p x' → x = x' := by
  intro hL _ R _ _ I _ D A G _ _ _ U F _ _ n hn p x x' hx hx'
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hL.globalFns U F hn w₀ hw₀
  obtain ⟨c, hc, hcs⟩ := exists_smul_of_phiVal p w w' hw hw'
  refine pt_eq_of_proportional hL.secBaseChange A _ hn θ θ'
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))
    fun t u u' hu hu' y J hJ => ?_
  have a := hcs _ _ _
    ((DVR.phiRel_iff hL.globalFns p w hw _ _).1 (h t u _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu))
    ((DVR.phiRel_iff hL.globalFns p w' hw' _ _).1 (h' t u' _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu'))
  obtain rfl := e.injective (a.trans (e.map_smul c u).symm)
  exact (sval_smul' hJ _ c _).trans (congrArg (· * _) (gs_unit _ y ⊤ trivial
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))))

end GlobalTheory.TorsionImage
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiSpread

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_finite_cube_induction (X : Type) [AddCommGroup X] [Module.Finite ℤ X] :
    ∃ S : Set X, S.Finite ∧ ∀ E : X → Prop, (∀ x ∈ S, E x) →
      (∀ a a' b, E a → E a' → E b → E (a + a') → E (a + b) → E (a' + b) → E (a + a' + b)) → ∀ x, E x := by
  have h : AddMonoid.FG X := AddGroup.fg_iff_addMonoid_fg.1 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  obtain ⟨G, hG, hGfin⟩ := AddMonoid.fg_iff.mp h
  refine ⟨insert 0 (G ∪ Set.image2 (· + ·) G G),
    (hGfin.union (hGfin.image2 _ hGfin)).insert _, fun E hS hE x => ?_⟩
  have h₁ : ∀ g ∈ G, E g := fun g hg => hS g (Or.inr (Or.inl hg))
  have key : E x ∧ ∀ g ∈ G, E (g + x) := by
    refine AddSubmonoid.induction_of_closure_eq_top_left (motive := fun x => E x ∧ ∀ g ∈ G, E (g + x))
      hG x ⟨hS 0 (Or.inl rfl), fun g hg => by rw [add_zero]; exact h₁ g hg⟩ fun g hg y hy => ⟨hy.2 g hg, fun g' hg' => ?_⟩
    rw [← add_assoc]
    exact hE g' g y (h₁ _ hg') (h₁ _ hg) hy.1 (hS _ (Or.inr (Or.inr ⟨g', hg', g, hg, rfl⟩))) (hy.2 _ hg') (hy.2 _ hg)
  exact key.1

theorem exists_gen_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (j : K → L.ι) (hj : ∀ y, y ∈ LB.wchart L φ j) (V : Y.Opens) (hV : ∀ y, y ∈ V) (u : Γ(Y, V)ˣ) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j' : K → L.ι),
      r z ∈ LB.wchart L φ j' → gm r z (LB.wchart L φ j') (t.s j') = trF φ ε r z j' j * gm r z V u := by
  let t : LB.Gen (LB.LinComb L φ ε) := ⟨fun j' =>
    res (le_inf le_rfl (fun y _ => hj y) : LB.wchart L φ j' ≤ LB.wchart L φ j' ⊓ LB.wchart L φ j)
      ((LB.LinComb L φ ε).g j' j) * res (fun y _ => hV y : LB.wchart L φ j' ≤ V) u⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j' : K → L.ι),
      r z ∈ LB.wchart L φ j' → gm r z (LB.wchart L φ j') (t.s j') = trF φ ε r z j' j * gm r z V u :=
    fun Z r z j' h => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ h _).trans (gm_linComb L φ ε r z j' j h (hj _))) (gm_res r z _ h _))
  refine ⟨t, fun (i i' : K → L.ι) => unit_ext fun y hy => ?_, key⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i hy.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y i i' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i' hy.2))).trans ?_)
  rw [← trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hj _), _root_.mul_assoc]
  rfl

theorem exists_unit_near {X Y : Scheme.{0}} (f : Y ⟶ X) [IsPreimmersion f] (y : Y) (a : (Y.presheaf.stalk y)ˣ) :
    ∃ (U : X.Opens) (u : Γ(X, U)ˣ), f y ∈ U ∧ gm f y U u = a := by
  obtain ⟨s, hs⟩ := f.stalkMap_surjective y a.val
  obtain ⟨U, hU, g, rfl⟩ := X.presheaf.exists_germ_eq s
  have hu : IsUnit ((X.presheaf.germ U (f y) hU).hom g) :=
    (isUnit_map_iff (f.stalkMap y).hom _).1 (hs ▸ a.isUnit)
  have hm : f y ∈ X.basicOpen g := (X.mem_basicOpen g (f y) hU).2 hu
  refine ⟨X.basicOpen g, (X.toRingedSpace.isUnit_res_basicOpen g).unit, hm, Units.ext ?_⟩
  refine (gs_unit f y _ hm _).symm.trans ((gs_res f y (X.basicOpen_le g) hm g).trans ((gs_eq f y U hU g).trans ?_))
  exact (Scheme.Hom.germ_stalkMap_apply f U y hU g).symm.trans hs

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def Extends {T : Over (Spec (CommRingCat.of R))} (κ : TK R ⟶ T) (χ : D.X) : Prop :=
  ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (cP D T χ).left) (fun _ => -1)), t.IsGen ∧
    ∀ z J, Good D.P.L z J → val t κ.left z J = val (D.psi χ) (𝟙 _) z J

theorem exists_extends (χ : D.X) (z : (TK R).left) : ∃ V : (Spec (CommRingCat.of R)).Opens, jK R z ∈ V ∧
    ∀ W : (Spec (CommRingCat.of R)).Opens, W ≤ V → ∀ κ : TK R ⟶ TW W, Extends D κ χ := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R) (S := FractionRing R)
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  obtain ⟨j, hj⟩ := exists_chart D.P.isLB (D.xK χ z)
  obtain ⟨U, u, hU, e⟩ := exists_unit_near (jK R) z
    (gm (𝟙 (TK R).left) z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => j)) ((D.psi χ).s (fun _ => j)))
  refine ⟨U ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U j, ⟨hU, hj⟩, fun W hW κ => ?_⟩
  have hκ : κ.left ≫ W.ι = jK R := Over.w κ
  obtain ⟨t, ht, vt⟩ := exists_gen_of_chart D.P.isLB (K := PUnit) (fun _ => (cP D (TW W) χ).left) (fun _ => -1)
    (fun _ => j) (fun y => Set.mem_iInter.2 fun _ => (hW y.2).2) (W.ι ⁻¹ᵁ U) (fun y => (hW y.2).1) (pullU W.ι U u)
  refine ⟨t, ht, fun z' J hJ => ?_⟩
  obtain rfl : z = z' := Subsingleton.elim _ _
  have q : κ.left ≫ (cP D (TW W) χ).left = 𝟙 _ ≫ D.xK χ :=
    (congrArg (fun q => q.left) (comp_cP D κ χ)).trans (Category.id_comp _).symm
  refine (vt _ κ.left z _ (hJ.mem _ _)).trans (Eq.trans ?_
    (gen_trans (D.psi_gen χ) (𝟙 _) z (j' := fun _ => j) (hJ.mem _ _) (Set.mem_iInter.2 fun _ => hj)).symm)
  refine congrArg₂ (· * ·) ?_ ((gm_pull κ.left W.ι z U (hW (κ.left z).2).1 u).trans (by rw [hκ]; exact e))
  exact congrArg (fun ψ => ∏ _k : PUnit.{1}, gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U j) (D.P.L.g (J ψ) j) ^ (-1 : ℤ)) q

theorem prod_elim {A U K K' : Type} [CommGroup U] [Fintype K] [Fintype K'] (h : A → U) {φ : K → A} {ε : K → ℤ}
    {φ' : K' → A} {ε' : K' → ℤ} {c c' : U} (e : ∏ k, h (φ k) ^ ε k = c) (e' : ∏ k, h (φ' k) ^ ε' k = c') :
    ∏ k, h (Sum.elim φ φ' k) ^ Sum.elim ε ε' k = c * c' := by
  rw [Fintype.prod_sum_type, ← e, ← e']; rfl

theorem prod_punit {A U : Type} [CommGroup U] (h : A → U) (a : A) (n : ℤ) :
    ∏ k : PUnit.{1}, h ((fun _ => a) k) ^ (fun _ => n) k = h a ^ n := Fintype.prod_unique _

theorem Extends.cube (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (κ : TK R ⟶ T) (a a' b : D.X)
    (h₁ : Extends D κ a) (h₂ : Extends D κ a') (h₃ : Extends D κ b) (h₄ : Extends D κ (a + a'))
    (h₅ : Extends D κ (a + b)) (h₆ : Extends D κ (a' + b)) : Extends D κ (a + a' + b) := by
  obtain ⟨t₁, g₁, v₁⟩ := h₁
  obtain ⟨t₂, g₂, v₂⟩ := h₂
  obtain ⟨t₃, g₃, v₃⟩ := h₃
  obtain ⟨t₄, g₄, v₄⟩ := h₄
  obtain ⟨t₅, g₅, v₅⟩ := h₅
  obtain ⟨t₆, g₆, v₆⟩ := h₆
  obtain ⟨t, gt, vt⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => (cP D T (a + a' + b)).left) (ε' := fun _ => -1)
    (fun U _ h => by
      have p := prod_cub (cP D T a) (cP D T a') (cP D T b) h
      have q : (toUnit T).left ≫ eSec D.P.A = (1 : T ⟶ D.P.A).left := rfl
      refine (prod_elim h (prod_elim h (prod_elim h (prod_punit h _ _) (prod_punit h _ _)) (prod_punit h _ _))
        (prod_neg _ _ (prod_elim h (prod_elim h (prod_elim h (prod_punit h _ _) (prod_punit h _ _)) (prod_punit h _ _))
          (prod_elim h (prod_punit h _ _) p)))).trans (Eq.trans ?_ (prod_punit h _ _).symm)
      rw [q]
      simp only [cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₄ t₅) t₆)
      (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₁ t₂) t₃)
        (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit T).left)
          (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (cP D T a) (lift (cP D T a') (cP D T b))).left)))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₄ g₅) g₆)
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₁ g₂) g₃)
        (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) (pullGen_isGen _ _ _ _ D.cub.isGen _)))))
  refine ⟨t, gt, fun z J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      th D z J (cP D _ a) (cP D _ a') (cP D _ b) :=
    (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).trans (by simp only [comp_cP])
  have vρ : val (LB.pullGen D.P.L _ _ D.rig (toUnit T).left) κ.left z J = val D.rigK (𝟙 _) z J := by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp]
    exact congrArg (fun q => val D.rig q z J) (Over.w κ)
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (cP D T a) (lift (cP D T a') (cP D T b))).left) κ.left z J = th D z J (cP D _ a) (cP D _ a') (cP D _ b) :=
    (val_cub D.cub κ hJ _ _ _).trans (by simp only [comp_cP])
  rw [c, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ] at e
  refine (vt _ _ z J hJ).trans (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (v₄ z J hJ) (v₅ z J hJ))) (v₆ z J hJ)))
    ((val_inv _ _).trans (congrArg (·⁻¹) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (v₁ z J hJ) (v₂ z J hJ))) (v₃ z J hJ)))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) vρ vc)))))))).trans ?_)
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) -e'

theorem nonempty_psiOn {W : (Spec (CommRingCat.of R)).Opens} (κ : TK R ⟶ TW W) (h : ∀ χ, Extends D κ χ) :
    Nonempty (PsiOn D W) := by
  choose t gt vt using h
  refine ⟨⟨t, gt, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  have c : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (t χ) κ.left) (D.psi χ) :=
    corr_of_val D.P.isLB fun z J hJ => (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; exact vt χ z J hJ)
  have q : (jK R ⁻¹ᵁ W).ι ≫ κ.left = jK R ∣_ W := by
    have hκ : κ.left ≫ W.ι = jK R := Over.w κ
    rw [← cancel_mono W.ι, morphismRestrict_ι, Category.assoc, hκ]
  have e := (val_pull hJ _ _ _).symm.trans (val_corr hJ c (jK R ⁻¹ᵁ W).ι)
  rw [q] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  rw [Category.id_comp, Category.id_comp]
  exact e

theorem exists_psiOn (hB : D.TauBimult) : ∃ W : (Spec (CommRingCat.of R)).Opens,
    genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W) := by
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨S, hS, ind⟩ := exists_finite_cube_induction D.X
  choose V hV ext using fun χ => exists_extends D χ z
  let W : (Spec (CommRingCat.of R)).Opens := ⟨⋂ χ ∈ S, V χ, hS.isOpen_biInter fun χ _ => (V χ).isOpen⟩
  have hz : jK R z ∈ W := Set.mem_iInter₂.2 fun χ _ => hV χ
  let κ : TK R ⟶ TW W := Over.homMk (IsOpenImmersion.lift W.ι (jK R) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact TauPull.jK_mem y W ⟨_, hz⟩)) (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨W, ?_, nonempty_psiOn D κ (ind _ (fun χ hχ => ext χ W (fun x hx => Set.mem_iInter₂.1 hx χ hχ) κ)
    (Extends.cube D hB κ))⟩
  exact ((genericPoint_spec (Spec (CommRingCat.of R))).mem_open_set_iff W.isOpen).2 ⟨_, trivial, hz⟩

end PsiSpread

theorem psiOnExists : PsiOnExistsSt := fun _ _ _ _ _ D => PsiSpread.exists_psiOn D.toPre D.tau_bimult

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifPullCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange (CarriesFam GrpPull RigPull UnifPull GenericInPsiLocus UnifBaseChange)
open GlobalTheory.PullDegCompare
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Bundle

end Bundle

section Main

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']

omit [IsDomain R] [IsDomain R'] in
theorem isGrpPullback_of_bc (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom) :
    IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
  ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl


variable [IsCommMonObj G] [IsCommMonObj G']

variable {I : Ideal R} {I' : Ideal R'}

variable {D : DegData R I} {D' : DegData R' I'} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}

end Main

end GlobalTheory.UnifPullCompare
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.exists_degData_isPullDeg : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolBaseChangeSt → _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R'), I.map φ ≤ I' → ∀ (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Out.PsiOn D.toPre W) → (_root_.ReciprocityTheory.ChartRestriction.G.Out.specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R' I') (hD : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPullDeg φ D.toPre D'.toPre), hD.W = W ∧ D'.toPre.P.g = D.toPre.P.g := by
  intro hP hG R R' _ _ _ _ I I' φ hle D W hψ hgen
  obtain ⟨D₀, hE, hT, hI, hF⟩ := D
  obtain ⟨D', hD, hW, hg⟩ :=
    _root_.GlobalTheory.DegPull.exists_isPullDeg hP R R' φ D₀ W hψ hgen
  refine ⟨⟨D', _root_.GlobalTheory.PsiEvenPull.psiEven_pull hG R R' φ D₀ D' hD hE,
    _root_.GlobalTheory.tauBimult_of_isPullDeg hG R R' φ D₀ D' hD hT, ?_, ?_⟩, hD, hW, hg⟩
  · intro χ hχ
    exact _root_.GlobalTheory.psiIn_of_isPullDeg R R' φ D₀ D' hD χ I I' hle
      (hI _ fun h => hχ (hD.xe.map_eq_zero_iff.mp h))
  · intro n
    refine ((hF n).preimage hD.xe.injective.injOn).subset ?_
    intro χ hχ h
    exact hχ (_root_.GlobalTheory.psiIn_of_isPullDeg R R' φ D₀ D' hD χ (I ^ n) (I' ^ n)
      (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hle n) h)

end GlobalTheory
end
