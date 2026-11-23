module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionEndomorphismExpansion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTorusExtensionPointOfGroupPoint
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.pullback_section_endomorphism_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U), Function.Injective E.h → ∀ (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), κ.IsGen → (∀ (e : ℕ) (Z : Scheme.{0}) (x o : Z ⟶ (thickObj R I e G).left) (z : Z) (JG) (J), Good U.LG.L z JG → Good D.toPre.P.L z J → o = x ≫ (1 : thickObj R I e G ⟶ thickObj R I e G).left → ∀ W : (Z ⟶ (thickObj R I e G).left) → (Z.presheaf.stalk z)ˣ, (∀ y, W y = gw (U.w e) y z (J (y ≫ (U.gt e).pG.left)) (fun _ => JG (y ≫ (fstG I e G).left))) → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z JG * W x ^ (k' : ℤ) * W (x ≫ ((Over.pullback (thick R I e)).map E.aG).left) ^ (-(k : ℤ)) * W o ^ ((k : ℤ) - k')) → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → ∃ (σ' : H0 U.LG.L k') (f' : ∀ α : D.toPre.X, D.toPre.SecB k' α), (∀ e, U.ExpandsAt e k' σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J → sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val) ∧ (∀ (χ : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f' (E.h χ)) r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J * rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧ ∀ b, b ∉ Set.range E.h → ∀ j, (f' b).f j = 0 := by
  first | exact @GlobalTheory.PullInt.main | exact GlobalTheory.PullInt.main | (intros; apply GlobalTheory.PullInt.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.uniformizationEndomorphism_calculus : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ E E' E'' : EndU U.toUnifPre, (∀ g : GtPtF D.toPre F, ∃! g', E.Act g g') ∧ (∀ g₁ g₂ g₃ g₁' g₂' g₃' : GtPtF D.toPre F, g₁.IsAdd g₂ g₃ → E.Act g₁ g₁' → E.Act g₂ g₂' → E.Act g₃ g₃' → g₁'.IsAdd g₂' g₃') ∧ (∀ t (g g' : GtPtF D.toPre F), IsTor t g → E.Act g g' → IsTor (t.comp (AddMonoidHom.toMultiplicative E.h)) g') ∧ (E.aG = E'.aG → E.aB = E'.aB ∧ E.h = E'.h ∧ ∀ g g' : GtPtF D.toPre F, E.Act g g' ↔ E'.Act g g') ∧ (E''.aG = E.aG * E'.aG → E''.aB = E.aB * E'.aB ∧ E''.h = E.h + E'.h ∧ ∀ g g₁ g₂ g₃ : GtPtF D.toPre F, E.Act g g₁ → E'.Act g g₂ → g₁.IsAdd g₂ g₃ → E''.Act g g₃) ∧ (E''.aG = E.aG ≫ E'.aG → E''.aB = E.aB ≫ E'.aB ∧ E''.h = E.h.comp E'.h ∧ ∀ g g₁ g₂ : GtPtF D.toPre F, E.Act g g₁ → E'.Act g₁ g₂ → E''.Act g g₂) := by
  first | exact @GlobalTheory.EndCalc.end_calculus | exact GlobalTheory.EndCalc.end_calculus | (intros; apply GlobalTheory.EndCalc.end_calculus <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CoordAdd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusCoord

theorem corr_of_thick {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤)
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of R) ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen)
    (hv : ∀ e z J, Good L z J → val u (thick R I e) z J = val u' (thick R I e) z J) :
    LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := exists_ratio hL h u hu u' hu'
  have h2 : a = 1 := by
    refine Units.ext (AbelianPartIso.fn_eq_of_thickenings hI ⊤ rfl _ _ fun e z => ?_)
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := ha _ (thick R I e) z J hJ
    rw [hv e z J hJ] at this
    rw [gs_unit _ z ⊤ trivial, gs_unit _ z ⊤ trivial, map_one, mul_eq_right.1 this.symm]
  exact corr_of_val hL fun y J hJ => by rw [ha _ _ y J hJ, h2, map_one, _root_.one_mul]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]


variable (I) in
abbrev lev (e : ℕ) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (𝟙 _)


variable (I) in
abbrev levι (e : ℕ) : (Over.map (thick R I e)).obj (lev I e) ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))) := toUnit _

omit [IsDomain R] in
theorem levι_left (e : ℕ) : (levι I e).left = thick R I e :=
  (Category.comp_id _).symm.trans ((Over.w (levι I e)).trans (Category.id_comp _))

omit [IsDomain R] in
theorem toUnit_left (e : ℕ) : (toUnit (Over.mk (thick R I e))).left = thick R I e :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (thick R I e))))

def Lifts {e : ℕ} (g : GtCoord I D e G) (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G)
    (gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) (a : lev I e ⟶ thickObj R I e G) : Prop :=
  pushHom (isGrpPullback_pullback G (thick R I e)) (lev I e) a = levι I e ≫ x ∧ im g a = levι I e ≫ gp.b ∧
    ∀ χ z J, Good D.P.L z J → val (g.t χ) a.left z J = val (gp.s χ) (levι I e).left z J

theorem exists_lifts {e : ℕ} (g : GtCoord I D e G) {x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G}
    {gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G),
      xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ g.pG = toUnit _ ≫ gp.b ∧
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) xe.left)
        (LB.pullGen D.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) :
    ∃ a, Lifts g x gp a := by
  obtain ⟨xe, h₁, h₂, h₃⟩ := h
  have hw : xe.left ≫ (thickObj R I e G).hom = 𝟙 _ := by
    rw [← cancel_mono (thick R I e), Category.assoc]
    exact (Over.w xe).trans (Category.id_comp _).symm
  have hu : (toUnit (Over.mk (thick R I e))).left = (levι I e).left := (toUnit_left e).trans (levι_left e).symm
  refine ⟨Over.homMk xe.left hw, Over.OverMorphism.ext ?_, Over.OverMorphism.ext ?_, fun χ z J hJ => ?_⟩
  · exact (congrArg (·.left) h₁).trans (congrArg (· ≫ x.left) hu)
  · exact (congrArg (·.left) h₂).trans (congrArg (· ≫ gp.b.left) hu)
  · have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h₃ χ) (𝟙 _)).trans (val_pull hJ _ _ _))
    rw [Category.id_comp, Category.id_comp, hu] at this
    exact this

omit [IsDomain R] [IsCommMonObj G] in
theorem push_injective {e : ℕ} {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    Function.Injective (pushHom (isGrpPullback_pullback G (thick R I e)) T) := fun a b h =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (·.left) h) ((Over.w a).trans (Over.w b).symm))


omit [IsDomain R] in
theorem pt_ext [IsLocalRing R] [IsHausdorff I R] {B : Over (Spec (CommRingCat.of R))}
    {b b' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B} (h : ∀ e, levι I e ≫ b = levι I e ≫ b') : b = b' :=
  Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e =>
    (congrArg (· ≫ b.left) (levι_left e)).symm.trans
      ((congrArg (·.left) (h e)).trans (congrArg (· ≫ b'.left) (levι_left e))))

theorem prod_gtφT {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h (DegPre.cT D T χ * b).left)⁻¹ * h (DegPre.cT D T χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h _ ^ (-1 : ℤ) * h _ ^ (1 : ℤ) * h _ ^ (1 : ℤ) * h _ ^ (-1 : ℤ) = _
  rw [zpow_neg_one, zpow_neg_one, zpow_one, zpow_one]
  rfl

variable [IsLocalRing R] [IsNoetherianRing R] [IsHausdorff I R]

theorem isAdd_of_lifts (hGF : GlobalFnsSt) (hI : I ≠ ⊤) (g : ∀ e, GtCoord I D e G)
    {x x' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G} {gp gp' gp'' : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∀ e, ∃ a, Lifts (g e) x gp a) (h' : ∀ e, ∃ a, Lifts (g e) x' gp' a)
    (h'' : ∀ e, ∃ a, Lifts (g e) (x * x') gp'' a) : GtPt.IsAdd gp gp' gp'' := by
  choose a ha using h
  choose a' ha' using h'
  choose a'' ha'' using h''
  have hm : ∀ e, a'' e = a e * a' e := fun e => push_injective (by
    rw [map_mul, (ha e).1, (ha' e).1, (ha'' e).1]
    exact MonObj.comp_mul _ _ _)
  have hb : gp''.b = gp.b * gp'.b := pt_ext (I := I) fun e => by
    rw [MonObj.comp_mul, ← (ha e).2.1, ← (ha' e).2.1, ← (ha'' e).2.1, hm, im_mul]
  refine ⟨hb, fun χ => corr_of_thick hI D.P.isLB (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gp''.isGen χ) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gp.isGen χ) (gp'.isGen χ)) fun e z J hJ => ?_⟩
  · refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
    refine (congrArg₂ (· * ·) (prod_gtφT gp''.b χ h) (prod_cub (DegPre.cT D _ χ) gp.b gp'.b h)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (prod_gtφT gp.b χ h) (prod_gtφT gp'.b χ h)).symm)
    rw [hb, _root_.mul_assoc (DegPre.cT D _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have k := val_t_mul_points (g e) hGF χ (a e) (a' e) z J hJ
    have c : cubeVal (g e) χ z J (a e) (a' e) =
        cubV D.cub z J (levι I e ≫ DegPre.cT D _ χ) (levι I e ≫ gp.b) (levι I e ≫ gp'.b) := by
      unfold cubeVal
      rw [(ha e).2.1, (ha' e).2.1, comp_toUnit_assoc]
    rw [← hm, (ha e).2.2 χ z J hJ, (ha' e).2.2 χ z J hJ, (ha'' e).2.2 χ z J hJ, c] at k
    have := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (levι I e) hJ _ _ _))).trans
      (k.trans (val_mul hJ _ _ _).symm)
    rw [levι_left] at this
    exact this

theorem isZero_of_lifts (hI : I ≠ ⊤) (g : ∀ e, GtCoord I D e G)
    {gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∀ e, ∃ a, Lifts (g e) 1 gp a) : gp.IsZero := by
  choose a ha using h
  have hm : ∀ e, a e = 1 := fun e => push_injective (by
    rw [map_one, (ha e).1]
    exact MonObj.comp_one _)
  have hb : gp.b = 1 := pt_ext (I := I) fun e => by
    rw [MonObj.comp_one, ← (ha e).2.1, hm, im_one]
  refine ⟨hb, fun χ => corr_of_thick hI D.P.isLB (fun U _ h => ?_) (gp.isGen χ)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm) fun e z J hJ => ?_⟩
  · refine (prod_gtφT gp.b χ h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
  · have k := (ha e).2.2 χ z J hJ
    rw [hm, val_unit (g e) χ hJ, levι_left] at k
    exact k.symm.trans (val_one _).symm

end GlobalTheory.CoordAdd

namespace GlobalTheory


open CoordAdd in
theorem gtCoord_additive : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), (∀ (x x' : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp gp' gp'' : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x' ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp'.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp'.s χ) (toUnit (Over.mk (thick R I e))).left)) → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ (x * x') ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp''.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp''.s χ) (toUnit (Over.mk (thick R I e))).left)) → GtPt.IsAdd gp gp' gp'') ∧ ∀ gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ (1 : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → gp.IsZero := by
  intro hGF R _ _ _ I hR hI D A G _ _ U
  obtain ⟨_, -, -, _⟩ := hR
  exact ⟨fun x x' gp gp' gp'' h h' h'' => isAdd_of_lifts hGF hI U.gt (fun e => exists_lifts _ (h e))
    (fun e => exists_lifts _ (h' e)) (fun e => exists_lifts _ (h'' e)),
    fun gp h => isZero_of_lifts hI U.gt fun e => exists_lifts _ (h e)⟩

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

section Algebra

variable {S F F' N V V' : Type} [CommRing S] [IsDomain S] [ValuationRing S] [Field F] [Field F']
  [AddCommGroup N] [Module S N] [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F' V']

theorem exists_ratio {fS : S →+* F} {π : S →+* F'} (hf : Function.Injective fS) (mv : N →ₛₗ[fS] V) (mv' : N →ₛₗ[π] V')
    (ind : ∀ (n : ℕ) (c : Fin n → F), (∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) →
      ∀ a : Fin n → N, ∑ i, c i • mv (a i) = 0 → ∀ i, a i = 0)
    {I : Type} (a b : I → N) (l : F) (h : ∀ i, mv (a i) = l • mv (b i)) (ha : ∃ i, mv' (a i) ≠ 0)
    (hb : ∃ i, mv' (b i) ≠ 0) : ∃ l' : F', l' ≠ 0 ∧ ∀ i, mv' (a i) = l' • mv' (b i) := by
  have inj : ∀ x y, mv x = mv y → x = y := fun x y e => sub_eq_zero.1 (ind 1 (fun _ => 1) (fun a ha i => by
    rw [Fin.sum_univ_one, _root_.mul_one] at ha
    rw [Subsingleton.elim i 0]; exact hf (ha.trans (map_zero _).symm)) (fun _ => x - y)
    (by rw [Fin.sum_univ_one, one_smul, map_sub, e, sub_self]) 0)
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  by_cases H : ∀ a : Fin 2 → S, ∑ i, fS (a i) * ![1, -l] i = 0 → ∀ i, a i = 0
  · refine absurd ?_ hi
    have e : a i = 0 := ind 2 _ H ![a i, b i] (by simp [Fin.sum_univ_two, h]) 0
    rw [e, map_zero]
  · push_neg at H
    obtain ⟨u, hu, m, hm⟩ := H
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, mul_neg] at hu
    have inj' : ∀ x, fS x = 0 → x = 0 := fun x e => hf (e.trans (map_zero _).symm)
    have h1 : u 1 ≠ 0 := fun e => by
      rw [e, map_zero, zero_mul, neg_zero, add_zero] at hu
      fin_cases m
      exacts [hm (inj' _ hu), hm e]
    have h1' : fS (u 1) ≠ 0 := fun e => h1 (inj' _ e)
    obtain ⟨t, ht | ht⟩ := ValuationRing.cond (u 0) (u 1)
    · have h0 : fS (u 0) ≠ 0 := fun e => h1' (by rw [← ht, map_mul, e, zero_mul])
      have e : fS t * l = 1 := mul_left_cancel₀ h0 (by rw [← ht, map_mul] at hu; linear_combination -hu)
      have k : ∀ i, mv' (b i) = π t • mv' (a i) := fun i => by
        rw [← map_smulₛₗ]
        exact congrArg mv' (inj _ _ (by rw [map_smulₛₗ, h, smul_smul, e, one_smul]))
      have p : π t ≠ 0 := fun e => hj (by rw [k, e, zero_smul])
      exact ⟨(π t)⁻¹, inv_ne_zero p, fun i => by rw [k, smul_smul, inv_mul_cancel₀ p, one_smul]⟩
    · have e : fS t = l := mul_left_cancel₀ h1' (by rw [← ht, map_mul] at hu; linear_combination hu)
      have k : ∀ i, mv' (a i) = π t • mv' (b i) := fun i => by
        rw [← map_smulₛₗ]
        exact congrArg mv' (inj _ _ (by rw [map_smulₛₗ, h, e]))
      exact ⟨π t, fun e => hi (by rw [k, e, zero_smul]), k⟩

end Algebra

section Flat

variable {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F} {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]

theorem fn_indep {U : Y.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → FnOver π U)
    (h : ∑ i, c i • pullFn H.w (le_refl (p ⁻¹ᵁ U)) (a i) = 0) (i : Fin n) : a i = 0 := by
  let : Algebra S F := fS.toAlgebra
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := p ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (CommRingCat.ofHom (constHom π U)) (CommRingCat.ofHom fS) (p.app U)
      (CommRingCat.ofHom (constHom π' (p ⁻¹ᵁ U))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of S)) (Iso.refl _) (Scheme.ΓSpecIso (.of F)) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
  let : Algebra (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) := (p.app U).hom.toAlgebra
  let : Algebra S (FnOver π' (p ⁻¹ᵁ U)) := ((constHom π' (p ⁻¹ᵁ U)).comp fS).toAlgebra
  have : IsScalarTower S F (FnOver π' (p ⁻¹ᵁ U)) := .of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower S (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (congrArg (fun q => q.hom r) po'.w).symm
  have hpo : Algebra.IsPushout S (FnOver π U) F (FnOver π' (p ⁻¹ᵁ U)) :=
    CommRingCat.isPushout_iff_isPushout.mp po'
  have fl : Module.Flat S (FnOver π U) := by
    have f₁ : RingHom.Flat (π.appLE ⊤ U le_top).hom :=
      HasRingHomProperty.appLE (P := @Flat) π inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    have f₂ : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact f₂.comp f₁
  have li : LinearIndependent S c := Fintype.linearIndependent_iff.2 fun g hg => hc g hg
  have li' := Fintype.linearIndependent_iff.1 (Module.Flat.linearIndependent_one_tmul (S := FnOver π U) li)
  refine li' a (hpo.out.equiv.injective ?_) i

  rw [map_zero, ← h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hpo.out.equiv_tmul, one_smul, Algebra.smul_def, Algebra.smul_def, mul_comm]
  congr 1
  show _ = (Y'.presheaf.map (𝟙 _)).hom _
  rw [CategoryTheory.Functor.map_id]; rfl

theorem sec_indep {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} (ε : K → ℤ) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → SecOver π (LB.LinComb L φ ε))
    (h : ∑ i, c i • pullOver L ε H.w hφ (a i) = 0) (i : Fin n) : a i = 0 := by
  refine SecOver.ext _ _ fun (j : K → L.ι) => fn_ext fun y hy => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy (LB.wchart L φ j).isOpen
  have hle : U ≤ LB.wchart L φ j := hle
  have hle' : p ⁻¹ᵁ U ≤ LB.wchart L φ' j := fun z hz => (wchart_eq hφ j).ge (hle hz)
  have e := fn_indep H hU c hc (fun i => resFn π hle (chartLin π (LB.LinComb L φ ε) j (a i))) (by
    have := congrArg (resFn π' hle' ∘ₗ chartLin π' (LB.LinComb L φ' ε) j) h

    rw [map_zero, map_sum] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    rw [map_smul]
    refine congrArg (c i • ·) (fn_ext fun z hz => ?_)
    exact ((gs_pullFn H.w _ _ _ z hz).trans (gs_res (𝟙 Y' ≫ p) z hle hz _)).trans
      ((gs_res _ z hle' hz _).trans (gs_pullFn H.w _ _ _ z (hle' hz))).symm) i
  exact ((gs_res (𝟙 Y) y hle hyU _).symm.trans ((congrArg (gs (𝟙 Y) y U) e).trans (gs_zero' _ y U hyU))).trans
    (gs_zero' _ y _ hy).symm

end Flat

section Move

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

def PSec (w : LB.Iso L' (L.pull Φ)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (s' : LB.Sec (LB.LinComb L' φ' ε)) (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
    (∀ κ, Φ (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
    gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
      (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (s'.f q)

variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
  {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)}

theorem exists_moveMap (hL : L.IsLB) (hL' : L'.IsLB) (hw : w.IsGen) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom fS)) :
    ∃ mv : SecOver π (LB.LinComb L φ ε) →ₛₗ[fS] SecOver π' (LB.LinComb L' φ' ε),
      ∀ s s', PSec w φ' φ ε h s' s ↔ mv s = s' := by
  have ex := SecPull.existsUnique_secPull _ _ _ _ _ _ _ hL hL' w hw K φ' φ ε h hc
  choose mv hmv using fun s : SecOver π (LB.LinComb L φ ε) => (ex s).exists
  have m : ∀ {Z : Scheme.{0}} {r : Z ⟶ Y'} {z : Z} {p : K → L.ι}, (∀ κ, Φ (φ' κ (r z)) ∈ L.U (p κ)) →
      (r ≫ h) z ∈ LB.wchart L φ p := fun hp => SecPull.mem_wchart_comp hc (Set.mem_iInter.2 hp)
  refine ⟨{ toFun := mv
            map_add' := fun a b => (ex _).unique (hmv _) fun Z r z p q hp hq => ?_
            map_smul' := fun c a => (ex _).unique (hmv _) fun Z r z p q hp₁ hq => ?_ },
    fun s s' => ⟨fun H => (ex s).unique (hmv s) H, fun H => H ▸ hmv s⟩⟩
  · refine (gs_add _ z _ (m hp) _ _).trans (Eq.trans ?_ (congrArg _ (gs_add r z _ (mem_wchart.2 hq) _ _)).symm)
    rw [mul_add]
    exact congrArg₂ (· + ·) (hmv a Z r z p q hp hq) (hmv b Z r z p q hp hq)
  · refine (gs_smul π _ z _ (m hp₁) _ _).trans
      (Eq.trans ?_ (congrArg _ (gs_smul π' r z _ (mem_wchart.2 hq) _ _)).symm)
    rw [mul_left_comm, Category.assoc, hp, ← Category.assoc, constVal_specMap]
    exact congrArg _ (hmv a Z r z p q hp₁ hq)

theorem move_indep (hL : L.IsLB) (hL' : L'.IsLB) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]
    (mv : SecOver π (LB.LinComb L φ ε) → SecOver π' (LB.LinComb L' φ' ε)) (hmv : ∀ s, PSec w φ' φ ε h (mv s) s)
    (n : ℕ) (c : Fin n → F) (hi : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0)
    (a : Fin n → SecOver π (LB.LinComb L φ ε)) (e : ∑ i, c i • mv (a i) = 0) (i : Fin n) : a i = 0 := by
  refine sec_indep H ε (φ' := fun κ => h ≫ φ κ) (fun _ => rfl) c hi a (sec_ext' hL fun y J hJ => ?_) i
  choose J' hJ' using fun ψ : Y' ⟶ X' => exists_chart hL' (ψ y)
  have hJ' : Good L' y J' := hJ'
  have e' := congrArg (fun t => sval t (𝟙 _) y J') e
  beta_reduce at e'
  rw [sval_sum' hJ', sval_zero' hJ'] at e'
  rw [sval_sum' hJ, sval_zero' hJ, ← mul_zero (∏ κ, ExpTrans.om w y J J' (𝟙 _ ≫ φ' κ) ^ ε κ).val, ← e',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval_smul' hJ, sval_smul' hJ', sval_pullOver _ _ _ _ hJ,
    ExpTrans.sec_val w φ' φ ε h hc _ _ (𝟙 _) y (hmv (a i) _ (𝟙 _) y) hJ hJ', mul_left_comm]

end Move

end GlobalTheory.ThetaSpecialise
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauBalElem

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.TauBalBox

theorem tau_zero_left {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {y : (TK R).left} {J}
    (hJ : Good D.P.L y J) (b : D.X) : val (D.tau 0 b) (𝟙 _) y J = 1 := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  have t := tauK_mul hJ hB 0 0 b
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact mul_eq_left.1 t.symm

end GlobalTheory.TauBalElem
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusCoord

theorem val_torus_point_and_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Geo.Tor.Good D.P.L z J → ∀ χ : D.X, Geo.Tor.val (g.t χ) (τ ≫ g.i).left z J = Geo.Tor.gm τ.left z ⊤ (charUnit _ D.X χ) ∧ Geo.Tor.val (g.t χ) ((τ ≫ g.i) * y).left z J = Geo.Tor.gm τ.left z ⊤ (charUnit _ D.X χ) * Geo.Tor.val (g.t χ) y.left z J := by
  intro R _ _ I D e G _ _ g Z τ y z J hJ χ
  refine ⟨?_, GlobalTheory.TorusCoord.val_torus g χ hJ τ y⟩
  rw [GlobalTheory.TorusCoord.val_congr g χ (_root_.mul_one (τ ≫ g.i)).symm z J, GlobalTheory.TorusCoord.val_torus g χ hJ τ 1,
    GlobalTheory.TorusCoord.val_unit g χ hJ, _root_.mul_one]

end GlobalTheory.TorusCoord
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.existsUnique_torusExtensionPoint_of_groupPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G), ∃! gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) := by
  first | exact @GlobalTheory.existsUnique_gtPt_of_point | exact GlobalTheory.existsUnique_gtPt_of_point | (intros; apply GlobalTheory.existsUnique_gtPt_of_point <;> assumption)
end
