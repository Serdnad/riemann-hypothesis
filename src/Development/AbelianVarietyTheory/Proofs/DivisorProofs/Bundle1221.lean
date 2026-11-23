module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import GroundTheory.AutomorphicForms.LocallyProfinite

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.GtVec

open ReciprocityTheory.ChartRestriction.G.DVR

section Local

variable {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} {M : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_cpt (hM : M.IsLB) {φ : K → (Sp S ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp S ⟶ X)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {t : LB.Gen (LB.LinComb M φ ε)} {t' : LB.Gen (LB.LinComb M φ' ε')} (ht : t.IsGen)
    (ht' : t'.IsGen) {J} (hJ : Good M (cpt S) J) (e : val t (𝟙 _) (cpt S) J = val t' (𝟙 _) (cpt S) J) :
    LB.Gen.Corr M _ _ _ _ t t' := by
  obtain ⟨u, hu, vu⟩ := exists_gen hM hF t' ht'
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio hM rfl t u ht hu
  have h1 : Geo.Tor.gm (𝟙 (Sp S)) (cpt S) ⊤ ρ = 1 :=
    mul_eq_right.1 ((hρ _ _ _ J hJ).symm.trans (e.trans (vu _ _ _ J hJ).symm))
  have h2 : ρ = 1 := by
    apply Units.ext
    obtain ⟨a, ha⟩ := (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.surjective ρ.val
    have h3 : toStkA (cpt S) a = toStkA (cpt S) 1 := by
      rw [map_one]
      refine Eq.trans ?_ (congrArg Units.val h1)
      rw [gm_val (𝟙 (Sp S)) (cpt S) ⊤ trivial, ← ha]
      rfl
    rw [← ha, toStkA_injective h3, map_one]; rfl
  refine corr_of_val hM fun y I hI => (hρ _ _ y I hI).trans ?_
  rw [h2, map_one, _root_.one_mul]
  exact vu _ _ y I hI

theorem exists_gen_cpt (hM : M.IsLB) (φ : K → (Sp S ⟶ X)) (ε : K → ℤ) {J} (hJ : Good M (cpt S) J)
    (u : ((Sp S).presheaf.stalk (cpt S))ˣ) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ val t (𝟙 _) (cpt S) J = u := by
  have all : ∀ w : Sp S, w ∈ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) := fun w =>
    (top_le_iff_cpt (𝟙 (Sp S)) _).2 (hJ.mem φ (𝟙 _)) trivial
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) :=
    fun j w hw => ⟨hw, all w⟩
  obtain ⟨c, hc⟩ : ∃ c : Γ(Sp S, ⊤)ˣ, Geo.Tor.gm (𝟙 (Sp S)) (cpt S) ⊤ c = u := by
    obtain ⟨U, hU, a, ha⟩ := (Sp S).presheaf.exists_germ_eq u.val
    obtain rfl : U = ⊤ := top_le_iff.1 ((top_le_iff_cpt (𝟙 (Sp S)) U).2 hU)
    have hb : (Sp S).basicOpen a = ⊤ := top_le_iff.1 ((top_le_iff_cpt (𝟙 (Sp S)) _).2
      (((Sp S).mem_basicOpen a _ hU).2 (ha ▸ u.isUnit)))
    have ha' : IsUnit a := (Sp S).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
      ((Sp S).mem_basicOpen a y hy).1 (hb.ge trivial)
    exact ⟨ha'.unit, Units.ext ((gm_val (𝟙 _) _ ⊤ trivial _).trans ha)⟩
  let t : LB.Gen (LB.LinComb M φ ε) :=
    ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j fun k => J (𝟙 _ ≫ φ k)) * res le_top c⟩
  have v : ∀ (w : Sp S) j, w ∈ LB.wchart M φ j → Geo.Tor.gm (𝟙 (Sp S)) w (LB.wchart M φ j) (t.s j) =
      trF φ ε (𝟙 _) w j (fun k => J (𝟙 _ ≫ φ k)) * Geo.Tor.gm (𝟙 (Sp S)) w ⊤ c := fun w j h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ w (le j) h _).trans (gm_linComb M _ ε (𝟙 _) w j _ h (all w)))
      (gm_res _ w le_top h c))
  refine ⟨t, isGen_of_gm _ fun w j j' h h' => ?_, (v _ _ (all _)).trans ?_⟩
  · refine (v w j h).trans (Eq.trans ?_ (congrArg _ (v w j' h')).symm)
    rw [← trF_trans hM _ ε (𝟙 _) w h h' (all w), _root_.mul_assoc]
  · rw [mul_eq_left.1 (trF_trans hM φ ε (𝟙 _) _ (all _) (all _) (all _)), _root_.one_mul, hc]

end Local

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

open GlobalTheory.TorusModel

theorem exists_over {S : Type} [CommRing S] [IsLocalRing S] (f : Sp S ⟶ Sp R) (b : Over.mk f ⟶ D.P.A) :
    ∃ g : GtPt D (Over.mk f), g.b = b := by
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt S)
  have C : IsCub (th D (T := Over.mk f) (cpt S) J) := isCub_cubV D.cub hJ
  obtain ⟨v, m₀, m⟩ := exists_mult C (c := cP D (Over.mk f)) (cPoint_add D _) b
  choose s hs hv using fun χ => exists_gen_cpt D.P.isLB (DegPre.gtφT D (Over.mk f) b χ) DegPre.gtε hJ (v χ)
  refine ⟨⟨b, s, hs, corr_cpt D.P.isLB (fun U _ h => Eq.symm ?_) (hs 0) (fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm) hJ
      ((hv 0).trans (m₀.trans (val_one _).symm)),
    fun χ χ' => corr_cpt D.P.isLB (fun U _ h => Eq.symm ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (pullGen_isGen _ _ _ _ D.cub.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) hJ
      (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (val_cubAtT (T := Over.mk f) hJ _ _ _))).trans
        ((m χ χ').trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (hv _))).symm))⟩, rfl⟩
  · refine (prod_pt b 0 h).trans ?_
    rw [cPoint_zero, _root_.one_mul]; simp
  · refine (prod_sum₂ (K := Fin 4) (K' := thK.{0}) (U := U) _ (prod_pt b _ h)
      (prod_cub (cP D _ χ) (cP D _ χ') b h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_pt b χ h) (prod_pt b χ' h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem isZero_of_isAdd {T : Over (Sp R)} {g : GtPt D T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := mul_eq_left.1 hb.symm
  refine ⟨hb1, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e := hv χ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  rw [hb1, C.face₃, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm).trans (val_one _).symm

theorem isZero_unique {T : Over (Sp R)} {g g' : GtPt D T} (h : g.IsZero) (h' : g'.IsZero) : g = g' :=
  pt_ext (h.1.trans h'.1.symm) fun χ _ _ hJ => (val_corr hJ (h.2 χ) _).trans (val_corr hJ (h'.2 χ) _).symm

omit [IsDomain R] in
theorem red_comp : redE R ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), (∀ b : epsR R ⟶ D.P.A, IsTangent b → ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = b) ∧ (∀ gm gm' : GtPt D (epsR R), ∃ gm'', GtPt.IsAdd gm gm' gm'' ∧ (GtTan gm → GtTan gm' → GtTan gm'')) ∧ (∀ (T T' : Over (Sp R)) (h : T' ⟶ T) (gm : GtPt D T), ∃ gm' : GtPt D T', GtPt.IsPull h.left gm gm') ∧ ∀ gm gm' : GtPt D (epsR R), gm.b = gm'.b → (∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (gm.s χ) (gm'.s χ)) → gm = gm' := by
  intro R _ _ _ D
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨G, _, _, hH⟩ := exists_isGt hG (splitExt D)
  obtain ⟨Φ, hp, ha⟩ := exists_points hG hH
  have hz : ∀ T, (Φ T 1).IsZero := fun T => isZero_of_isAdd (by simpa using ha T 1 1)
  let r : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) red_comp
  let a : epsR R ⟶ baseOver (Sp R) := Over.homMk (spMap (algebraMap R (DualNumber R))) (Category.comp_id _)
  have hra : r ≫ a = 𝟙 _ := Over.OverMorphism.ext red_comp
  have tan : ∀ x : epsR R ⟶ G, GtTan (Φ _ x) ↔ r ≫ x = 1 := fun x =>
    ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((isPull_unique (hp _ _ r x) h).trans (isZero_unique ho (hz _))),
      fun h => ⟨Φ _ 1, hz _, h ▸ hp _ _ r x⟩⟩
  refine ⟨fun b hb => ?_, fun g g' => ?_, fun T T' h g => ?_, fun g g' hb hs =>
    pt_ext hb fun χ _ _ hJ => val_corr hJ (hs χ) _⟩
  · have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
      simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using
        IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
    obtain ⟨g, hg⟩ := exists_over (D := D) _ b
    obtain ⟨x, rfl⟩ := (Φ (epsR R)).surjective g
    refine ⟨Φ _ (((a ≫ r) ≫ x)⁻¹ * x), (tan _).2 ?_, ?_⟩
    · rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, hra, Category.id_comp,
        inv_mul_cancel]
    · have h₁ := ((TorusModel.isAdd_iff _ _ _).1 (ha _ ((a ≫ r) ≫ x) (((a ≫ r) ≫ x)⁻¹ * x))).1
      have h₂ := ((TorusModel.isPull_iff _ _ _).1 (hp _ _ (a ≫ r) x)).1
      have h₃ : r ≫ b = 1 := Over.OverMorphism.ext (hb.trans (Category.id_comp _).symm)
      rw [mul_inv_cancel_left, h₂, hg, Category.assoc, h₃, MonObj.comp_one, _root_.one_mul] at h₁
      exact h₁.symm
  · obtain ⟨x, rfl⟩ := (Φ (epsR R)).surjective g
    obtain ⟨x', rfl⟩ := (Φ (epsR R)).surjective g'
    refine ⟨_, ha _ x x', fun h h' => (tan _).2 ?_⟩
    rw [MonObj.comp_mul, (tan _).1 h, (tan _).1 h', _root_.mul_one]
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    exact ⟨_, hp _ _ h x⟩

end GlobalTheory.MBLow.GtVec

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.GtTanClass

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem exists_unit {T : Over (Sp R)} (g : GtPt D T) (hb : g.b = 1) (χ : D.X) :
    ∃ ρ : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ T.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val (g.s χ) q z J = Geo.Tor.gm q z ⊤ ρ := by
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T g.b χ) (ε' := DegPre.gtε)
    (fun U _ h => Eq.symm (by
      refine (prod_pt g.b χ h).trans ?_
      rw [hb, _root_.mul_one]; simp)) (LB.oneGen D.P.L (Y := T.left))
    (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio D.P.isLB rfl (g.s χ) u (g.isGen χ) hu
  exact ⟨ρ, fun Z q z J hJ => by rw [hρ Z q z J hJ, vu Z q z J hJ, val_one, _root_.mul_one]⟩

omit [IsDomain R] in
theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Sp B) (a : A) :
    gs (spMap f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = toStkA z (f a) := by
  rw [gs_eq _ _ ⊤ trivial]
  have e := congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact congrArg ((Sp B).presheaf.germ ⊤ z trivial).hom e.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (gm : GtPt D (epsR R)), GtTan gm → gm.b = DegPre.zeroT D (epsR R) → ∃ l : D.X →+ R, ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ _ D gm ⟨o, ho, hp⟩ hb
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using
      IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hb1 : gm.b = 1 := hb
  choose ρ hρ using exists_unit gm hb1
  choose u hu using fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).commRingCatIsoToRingEquiv.symm.surjective (ρ χ).val
  have hv : ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → (val (gm.s χ) q z J).val =
        gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (u χ)) := fun χ Z q z J hJ =>
    (congrArg Units.val (hρ χ Z q z J hJ)).trans ((gs_unit q z ⊤ trivial _).symm.trans
      (congrArg (gs q z ⊤) (hu χ).symm))
  have h1 : ∀ χ, TrivSqZeroExt.fst (u χ : DualNumber R) = 1 := fun χ => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt R)
    have e : val (gm.s χ) (redE R) (cpt R) J = 1 := by
      have e₁ := (val_corr hJ (hp.2 χ) (𝟙 (Sp R))).trans (val_pull hJ _ _ _)
      have e₂ := (val_corr hJ (ho.2 χ) (𝟙 (Sp R))).trans (val_one _)
      rw [← e₂, e₁]
      congr 1
    have e' := hv χ _ (redE R) (cpt R) J hJ
    rw [e] at e'
    refine toStkA_injective (A := R) ?_
    rw [map_one]
    exact (gs_spMap (TrivSqZeroExt.fstHom R R R).toRingHom (cpt R) (u χ)).symm.trans e'.symm
  have hm : ∀ χ χ', (u (χ + χ') : DualNumber R) = u χ * u χ' := fun χ χ' => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt (DualNumber R))
    have C : IsCub (th D (T := epsR R) (cpt (DualNumber R)) J) := isCub_cubV D.cub hJ
    have e := cv_add gm hJ χ χ'
    rw [hb1, C.face₃, _root_.mul_one] at e
    have k : ∀ χ, (cv gm χ (cpt (DualNumber R)) J).val = toStkA (cpt (DualNumber R)) (u χ) := fun χ =>
      (hv χ _ (𝟙 _) _ J hJ).trans (gs_eq _ _ ⊤ trivial _)
    refine toStkA_injective (A := DualNumber R) ?_
    rw [map_mul]
    exact (k _).symm.trans ((congrArg Units.val e).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (k _) (k _))))
  refine ⟨AddMonoidHom.mk' (fun χ => TrivSqZeroExt.snd (u χ : DualNumber R)) fun χ χ' => ?_, fun χ Z q z J hJ => ?_⟩
  · rw [hm, DualNumber.snd_mul, h1, h1]; ring
  · refine (hv χ Z q z J hJ).trans (congrArg (fun x => gs q z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom x)) ?_)
    exact TrivSqZeroExt.ext (by simp [h1]) (by simp)

end GlobalTheory.MBLow.GtTanClass

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HenQ.DetDParts

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def wD (w : List E) (g : E → ℂ) : E → ℂ :=
  List.foldr (fun (u : E) (f : E → ℂ) (x : E) => fderiv ℝ f x u) g w

theorem top_add_one_le : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := le_of_eq rfl

theorem fderiv_fderiv_comm {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    {x : E} (hx : x ∈ U) (u v : E) :
    fderiv ℝ (fun y => fderiv ℝ g y u) x v = fderiv ℝ (fun y => fderiv ℝ g y v) x u := by
  have hgx : ContDiffAt ℝ (⊤ : ℕ∞) g x := hg.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hgx.fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero
  have key : ∀ a b : E, fderiv ℝ (fun y => fderiv ℝ g y a) x b = fderiv ℝ (fderiv ℝ g) x b a := by
    intro a b
    rw [fderiv_clm_apply hd (differentiableAt_const a)]
    simp
  rw [key, key]
  exact (hgx.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)).eq v u

variable {μ : Measure E} [μ.IsAddHaarMeasure]

theorem continuous_mul_of_tsupport {U : Set E} (hU : IsOpen U) {u χ : E → ℂ}
    (hu : ContinuousOn u U) (hχ : Continuous χ) (hs : tsupport χ ⊆ U) :
    Continuous fun x => χ x * u x :=
  (hχ.continuousOn.mul hu).continuous_of_tsupport_subset hU (tsupport_mul_subset_left.trans hs)

theorem integrable_mul_of_tsupport {U : Set E} (hU : IsOpen U) {u χ : E → ℂ}
    (hu : ContinuousOn u U) (hχ : Continuous χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U) :
    Integrable (fun x => χ x * u x) μ :=
  (continuous_mul_of_tsupport hU hu hχ hs).integrable_of_hasCompactSupport hc.mul_right

theorem integral_partial_mul {U : Set E} (hU : IsOpen U) {Ψ g : E → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hc : HasCompactSupport Ψ) (hs : tsupport Ψ ⊆ U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (u : E) :
    ∫ x, fderiv ℝ Ψ x u * g x ∂μ = -∫ x, Ψ x * fderiv ℝ g x u ∂μ := by
  have h1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by exact_mod_cast le_top)
  have hg1 : ContDiffOn ℝ 1 g U := hg.of_le (by exact_mod_cast le_top)
  have hg' : ContDiffOn ℝ 0 (fun x => fderiv ℝ g x u) U :=
    (hg1.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  rw [eq_neg_iff_add_eq_zero, add_comm, ← eq_neg_iff_add_eq_zero]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_tsupport hU hg1.continuousOn
      ((h1.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ _)
      ((tsupport_fderiv_apply_subset ℝ _).trans hs))
    (integrable_mul_of_tsupport hU hg'.continuousOn h1.continuous hc hs)
    (integrable_mul_of_tsupport hU hg1.continuousOn h1.continuous hc hs)
    (fun x _ => h1.differentiable one_ne_zero x)
    (fun x hx => (hg1.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt one_ne_zero)

end General

section Specific

variable {K : Type} [Field K] [NumberField K] {n : ℕ}


open Classical in
def wordOf (v : InfinitePlace K) (p : Equiv.Perm (Fin n)) (l : List (Fin n)) : List (Lie K n) :=
  l.map fun j => toL (Matrix.single (p j) j (Pi.single v 1))

theorem foldr_pdL_eq (v : InfinitePlace K) (p : Equiv.Perm (Fin n)) (F : Lie K n → ℂ) (l : List (Fin n)) :
    l.foldr (fun j G => pdL v (p j) j G) F = wD (wordOf v p l) F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons, wordOf, List.map_cons]
    rw [ih]
    rfl

theorem detD_eq (v : InfinitePlace K) (G : Lie K n → ℂ) :
    detD v G = fun x => ∑ p : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * wD (wordOf v p (List.finRange n)) G x := by
  funext x
  simp only [detD, foldr_pdL_eq]

end Specific

end GlobalTheory.HenQ.DetDParts
end
end

section

set_option autoImplicit false

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

set_option autoImplicit false in
open Filter Topology in
private lemma isBallFam_mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {r r' : ℝ} (hrr' : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.2 hrr'))
  simpa using this

set_option autoImplicit false in
open Filter Topology in
private lemma encard_mul_encard_le_isBallFam {G : Type} [AddCommGroup G] {Λ : AddSubgroup G}
    {B : ℝ → Set G} (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (hbm : b + b ≤ m) (hfa : (B a).Finite) (hfb : (B b).Finite) (hf1 : (B 1).Finite) :
    (B a).encard * (B b).encard ≤ (B 1).encard * (B (m * a + b)).encard := by
  classical
  set S := hfa.toFinset ×ˢ hfb.toFinset with hS
  let f : G × G → G := fun p ↦ m • p.1 + p.2
  have hmem : ∀ p ∈ S, f p ∈ B (m * a + b) := by
    intro p hp
    rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    have h1 : m • p.1 ∈ B (m * a) :=
      (hB.nsmul_iff m a p.1 hm (hB.subset a hp.1)).2 hp.1
    have h2 : -p.2 ∈ B (0 + b) := by
      simpa using hB.sub_mem 0 b 0 p.2 (hB.zero_mem 0 le_rfl) hp.2
    have := hB.sub_mem _ _ _ _ h1 h2
    simpa [f, sub_neg_eq_add] using this
  have hcard : S.card ≤ hf1.toFinset.card * (S.image f).card := by
    refine Finset.card_le_mul_card_image S _ fun w hw ↦ ?_
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.1 hw
    refine Finset.card_le_card_of_injOn (fun p ↦ p₀.1 - p.1) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hp
      obtain ⟨hpS, hfp⟩ := hp
      have hp₀' := hp₀
      rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hpS hp₀'
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      have hd : m • (p₀.1 - p.1) = p.2 - p₀.2 := by
        simp only [f] at hfp
        rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← hfp]
        abel
      have hΛ : p₀.1 - p.1 ∈ Λ := Λ.sub_mem (hB.subset a hp₀'.1) (hB.subset a hpS.1)
      have h2 : p.2 - p₀.2 ∈ B ((m : ℝ) * 1) :=
        isBallFam_mono hB (by simpa using hbm) (hB.sub_mem _ _ _ _ hpS.2 hp₀'.2)
      exact (hB.nsmul_iff m 1 _ hm hΛ).1 (hd ▸ h2)
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : p.1 = q.1 := by simpa using hpq
      have h2 : p.2 = q.2 := by
        have := hp.2.trans hq.2.symm
        simp only [f, h1] at this
        exact add_left_cancel this
      exact Prod.ext h1 h2
  have himg : ((S.image f).card : ℕ∞) ≤ (B (m * a + b)).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    refine Set.encard_le_encard fun w hw ↦ ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
    exact hmem p hp
  rw [hfa.encard_eq_coe_toFinset_card, hfb.encard_eq_coe_toFinset_card,
    hf1.encard_eq_coe_toFinset_card, ← Nat.cast_mul, ← Finset.card_product]
  calc ((S.card : ℕ) : ℕ∞) ≤ ((hf1.toFinset.card * (S.image f).card : ℕ) : ℕ∞) := by
        exact_mod_cast hcard
    _ ≤ (hf1.toFinset.card : ℕ∞) * (B (m * a + b)).encard := by
        push_cast
        gcongr


set_option autoImplicit false in
open Filter Topology in
theorem _root_.GlobalTheory.VolBr.isBallFam_encard_mul_le : ∀ (G : Type) [AddCommGroup G]
    (Λ : AddSubgroup G) (B : ℝ → Set G), _root_.GlobalTheory.VolBr.IsBallFam Λ B → ∀ n : ℕ, 0 < n →
    (B n).Finite →
    (B n).encard * (B (n / 2)).encard ≤ (B 1).encard * (B (n ^ 2 + n / 2)).encard := by
  intro G _ Λ B hB n hn hfin
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (B 1).Finite := hfin.subset (isBallFam_mono hB hn1)
  have h2 : (B (n / 2)).Finite := hfin.subset (isBallFam_mono hB (by linarith))
  have := encard_mul_encard_le_isBallFam hB (a := n) (b := n / 2) hn (by linarith) hfin h2 h1
  rw [sq]
  exact this

end GlobalTheory.VolBr
end

section

alias GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue :=
  GlobalTheory.PtExt.Dat.lift_coc
end
