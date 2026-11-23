module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle032
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle108
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OrigVan

theorem stalkMap_gs {X Y Z : Scheme.{0}} (t : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (t z) ∈ U)
    (a : Γ(X, U)) : (t.stalkMap z).hom (gs r (t z) U a) = gs (t ≫ r) z U a := by
  rw [gs_eq r (t z) U h, gs_eq (t ≫ r) z U h]
  exact Scheme.Hom.germ_stalkMap_apply t (r ⁻¹ᵁ U) z h _

theorem stalkMap_stalkOf {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (z : Sp S) (v : R) :
    ((Spec.map (CommRingCat.ofHom φ)).stalkMap z).hom (stalkOf ((Spec.map (CommRingCat.ofHom φ)) z) v) =
      stalkOf z (φ v) := by
  have e := congrArg (fun q => q.hom v) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  refine (Scheme.Hom.germ_stalkMap_apply (Spec.map (CommRingCat.ofHom φ)) ⊤ z trivial _).trans ?_
  exact congrArg ((Sp S).presheaf.germ ⊤ z trivial).hom e.symm

theorem eq_zero_of_stalkOf {S : Type} [CommRing S] (w : S) (h : ∀ z : Sp S, stalkOf z w = 0) : w = 0 := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom w = 0 := by
    apply TopCat.Presheaf.section_ext (Sp S).sheaf ⊤
    intro x hx
    exact (h x).trans (map_zero _).symm
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom h1
  simpa using h2

end GlobalTheory.Mum.OrigVan

namespace GlobalTheory.Mum
open OrigVan

theorem origVal_mem_of_vanMod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (α : D.X)
    (b : D.SecB k α) (v : R) (e : ℕ), OrigVal D b v → VanMod I b e → v ∈ I ^ (e + 1) := by
  intro R _ _ I D k α b v e hO hV
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine eq_zero_of_stalkOf _ fun z => ?_
  choose J hJ using fun χ : Sp R ⟶ D.P.A.left => exists_chart D.P.isLB (χ (thick R I e z))
  have hG : Good D.P.L (thick R I e z) J := hJ
  have h1 := congrArg ((thick R I e).stalkMap z).hom (hO (thick R I e z) J hG)
  have hm := hG.mem (D.famφB α) (unitW D.P.A)
  have hu : unitW D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w (η[D.P.A])
  let s : Sp (R ⧸ I ^ (e + 1)) ⟶ pullback D.P.A.hom (thick R I e) :=
    pullback.lift (thick R I e ≫ unitW D.P.A) (𝟙 _) (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp])
  have hs : s ≫ pullback.fst D.P.A.hom (thick R I e) = thick R I e ≫ unitW D.P.A := pullback.lift_fst _ _ _
  have hm' : (s ≫ pullback.fst D.P.A.hom (thick R I e)) z ∈
      LB.wchart D.P.L (D.famφB α) (fun k => J (unitW D.P.A ≫ D.famφB α k)) := by
    rw [hs]; exact hm
  have h0 : ((thick R I e).stalkMap z).hom (sval b (unitW D.P.A) (thick R I e z) J) = 0 := by
    refine (stalkMap_gs (thick R I e) (unitW D.P.A) z _ hm _).trans ?_
    rw [← hs]
    refine (gs_pull s _ z _ hm' _).symm.trans ?_
    refine (congrArg (gs s z _) (hV _)).trans ?_
    refine (gs_eq s z _ hm' _).trans ?_
    rw [map_zero, map_zero]
  rw [h0, map_mul, map_pow, stalkMap_stalkOf] at h1
  exact (((Units.isUnit _).map _).pow k).mul_left_eq_zero.1 h1.symm

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OrigValPull

theorem gs_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)) :
    gs (f ≫ g) z U a = (f.stalkMap z).hom (gs g (f z) U a) := by
  rw [← gs_pull f g z U h, gs_eq f z (g ⁻¹ᵁ U) h, gs_eq g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h _).symm

theorem gm_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    (gm (f ≫ g) z U a).val = (f.stalkMap z).hom (gm g (f z) U a).val := by
  rw [← gs_unit (f ≫ g) z U h, ← gs_unit g (f z) U h, gs_comp f g z U h]

theorem stalkMap_stalkOf {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (z : Sp R') (v : R) :
    ((spMap φ).stalkMap z).hom (stalkOf (spMap φ z) v) = stalkOf z (φ v) := by
  have h := congrArg (fun q => q.hom v) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  refine (Scheme.Hom.germ_stalkMap_apply (spMap φ) ⊤ z trivial _).trans ?_
  exact congrArg ((Sp R').presheaf.germ ⊤ z trivial).hom h.symm

theorem unit_fam {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (α : D.X) (κ : Fin 4) :
    unitW D.P.A ≫ D.famφB α κ = ![unitW D.P.A, (D.c α).left, (D.c α).left, unitW D.P.A] κ := by
  have u : η[D.P.A] ≫ toUnit D.P.A = 𝟙 _ := Subsingleton.elim _ _
  fin_cases κ
  · exact Category.comp_id _
  · show (η[D.P.A] ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (D.c α).left
    congr 1
    show η[D.P.A] ≫ (lift (𝟙 D.P.A) (toUnit _ ≫ D.c α) ≫ μ[D.P.A]) = _
    rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, u, Category.id_comp]
    have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Sp R)))) (D.c α)
    simpa using this
  · show (η[D.P.A] ≫ toUnit _ ≫ D.c α).left = (D.c α).left
    rw [← Category.assoc, u, Category.id_comp]
  · show (η[D.P.A] ≫ toUnit _ ≫ η[D.P.A]).left = η[D.P.A].left
    rw [← Category.assoc, u, Category.id_comp]

theorem origVal_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (k : ℕ) (x : D'.X) (b : D.SecB k (hD.xe x)) (b' : D'.SecB k x) (v : R), PullB hD x b b' → OrigVal D b v → OrigVal D' b' (φ v) := by
  intro R R' _ _ _ _ φ D D' hD k x b b' v hP hO z J' hJ'
  choose J hJ using fun χ : Sp R ⟶ D.P.A.left => exists_chart D.P.isLB (χ (spMap φ z))
  have hJ : Good D.P.L (spMap φ z) J := hJ
  have he : unitW D'.P.A ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = spMap φ ≫ unitW D.P.A := hD.he
  have hc : ∀ κ, (unitW D'.P.A ≫ D'.famφB x κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
      spMap φ ≫ unitW D.P.A ≫ D.famφB (hD.xe x) κ := fun κ => by
    rw [unit_fam, unit_fam]
    fin_cases κ
    exacts [he, hD.c_pr x, hD.c_pr x, he]
  have h₁ := hP (Sp R') (unitW D'.P.A) z (fun κ => J (unitW D.P.A ≫ D.famφB (hD.xe x) κ))
    (fun κ => J' (unitW D'.P.A ≫ D'.famφB x κ))
    (fun κ => (congrArg (fun q : Sp R' ⟶ D.P.A.left => q z ∈ D.P.L.U (J (unitW D.P.A ≫ D.famφB (hD.xe x) κ))) (hc κ)).mpr
      (hJ _)) (fun κ => hJ' _)
  have hprod : (∏ κ, gw hD.w (unitW D'.P.A ≫ D'.famφB x κ) z (J (unitW D.P.A ≫ D.famφB (hD.xe x) κ))
      (J' (unitW D'.P.A ≫ D'.famφB x κ)) ^ (DegPre.famε k) κ) =
      gw hD.w (unitW D'.P.A) z (J (unitW D.P.A)) (J' (unitW D'.P.A)) ^ k := by
    simp only [unit_fam, Fin.prod_univ_four, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [_root_.mul_assoc (_ ^ _), ← zpow_add, add_neg_cancel, zpow_zero, _root_.mul_one, ← zpow_add, sub_add_cancel,
      zpow_natCast]
  have h₂ := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
    (rigPull_le _ _ hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig (Sp R') (idW R') z
    (fun _ => J (idW R ≫ eSec D.P.A)) (fun _ => J' (idW R' ≫ eSec D'.P.A))
    (fun _ => (congrArg (fun q : Sp R' ⟶ D.P.A.left => q z ∈ D.P.L.U (J (idW R ≫ eSec D.P.A))) he).mpr
      (hJ _)) (fun _ => hJ' _)
  have h₃ : ((spMap φ).stalkMap z).hom (val D.rig (idW R) (spMap φ z) J).val =
      (gw hD.w (unitW D'.P.A) z (J (unitW D.P.A)) (J' (unitW D'.P.A))).val * (val D'.rig (idW R') z J').val := by
    have i : idW R ≫ eSec D.P.A = unitW D.P.A := Category.id_comp _
    have i' : idW R' ≫ eSec D'.P.A = unitW D'.P.A := Category.id_comp _
    have c : spMap φ ≫ idW R = idW R' ≫ specOf φ := (Category.comp_id _).trans (Category.id_comp _).symm
    refine (gm_comp (spMap φ) (idW R) z _ (hJ.mem (fun _ : PUnit => eSec D.P.A) (idW R)) _).symm.trans ?_
    rw [c, ← Units.val_mul]
    refine congrArg Units.val (h₂.trans (congrArg₂ (· * ·) ?_ rfl))
    rw [Fintype.prod_unique, zpow_one, i, i']
  have h₄ := congrArg ((spMap φ).stalkMap z).hom (hO (spMap φ z) J hJ)
  rw [map_mul, map_pow, stalkMap_stalkOf, h₃] at h₄
  have h₅ := (gs_comp (spMap φ) (unitW D.P.A) z _ (hJ.mem (D.famφB (hD.xe x)) (unitW D.P.A)) _).trans h₄
  rw [he, hprod] at h₁
  have h₆ := h₁.symm.trans h₅
  rw [mul_pow, _root_.mul_left_comm, ← Units.val_pow_eq_pow_val] at h₆
  exact (Units.mul_right_inj _).1 h₆

end GlobalTheory.Mum.OrigValPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FormalModel

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstLin

section Thru

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R}
  {D' : DegPre R'} {F : D'.P.A.left ⟶ D.P.A.left} {w : LB.Iso D'.P.L (D.P.L.pull F)} {ε : D'.X → D.X}

theorem thru_pull_iff {T T₀ : Over (Sp R)} {T' : Over (Sp R')} (k : T₀ ⟶ T) {g : GtPt D T} {g₀ : GtPt D T₀}
    (hk : GtPt.IsPull k.left g g₀) (h : T'.left ⟶ T₀.left) (ξ : GtPt D' T') :
    Thru w ε h g₀ ξ ↔ Thru w ε (h ≫ k.left) g ξ := by
  have hb : k ≫ g.b = g₀.b := Over.OverMorphism.ext hk.1.symm
  refine forall_congr' fun y => and_congr (forall_congr' fun j => ?_) (forall_congr' fun Z => forall_congr' fun r =>
    forall_congr' fun z => forall_congr' fun J => forall_congr' fun J' => forall_congr' fun hJ => ?_)
  · rw [Category.assoc, ConstTanRed.comp_gtφT D k g.b g₀.b hb]
  · rw [(val_corr hJ (hk.2 (ε y)) (r ≫ h)).trans (val_pull hJ _ _ _), Category.assoc]

theorem eq_of_thru {Y : Over (Sp R)} [GrpObj Y] {Φ : ∀ T, (T ⟶ Y) ≃ GtPt D T} (hΦ : Represents Φ)
    (hε : Function.Surjective ε) {T' : Over (Sp R')} {r r' : T'.left ⟶ Y.left} {ξ : GtPt D' T'}
    (h : Thru w ε r (Φ Y (𝟙 Y)) ξ) (h' : Thru w ε r' (Φ Y (𝟙 Y)) ξ) : r = r' := by
  refine hom_ext hΦ (((h 0).1 2).symm.trans ((h' 0).1 2)) fun χ z J hJ => ?_
  obtain ⟨χ, rfl⟩ := hε χ
  obtain ⟨J', hJ'⟩ := TorusCoord.exists_good' D'.P.isLB z
  have a := ((h χ).2 _ (𝟙 _) z J J' hJ hJ').trans ((h' χ).2 _ (𝟙 _) z J J' hJ hJ').symm
  rwa [Category.id_comp, Category.id_comp] at a

end Thru

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R}
  {I : Ideal R'} {E : DegData R' I} {hE : IsPullDeg ρ D E.toPre} {A' : PolAV (Sp (FractionRing R'))}
  {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {Y : Over (Sp R)}

theorem Carries.thru {e : ℕ} {c : GtCoord I E.toPre e G'} {g : GtPt D Y} {φ} (h : Carries hE c g φ)
    {T : Over (Sp (R' ⧸ I ^ (e + 1)))} (x : T ⟶ thickObj R' I e G') :
    Thru hE.w hE.xe (T' := (Over.map (thick R' I e)).obj T) (x.left ≫ φ) g (TorusCoord.toGtPt c x) := by
  have hx := TorusCoord.isPointOf_toGtPt c x
  intro y
  refine ⟨fun k => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [TorusCoord.gtφT_eq, TorusCoord.gtφT_eq]
    refine TorusCoordPull.Oφ_pull hE g.b (TorusCoord.toGtPt c x).b (x.left ≫ φ) ?_ y k
    rw [hx.1, Category.assoc, h.1, Category.assoc]
  · have o := (TorusCoord.comp_eq_of_left (TorusCoord.toGtPt c x).b c.pG r (r ≫ x.left)
      (by rw [hx.1, Category.assoc])).1 y
    refine (congrArg (fun q => val (g.s (hE.xe y)) q z J) (Category.assoc _ _ _).symm).trans
      ((h.2 y Z (r ≫ x.left) z J J' hJ hJ').trans (congrArg₂ (· * ·)
        (Finset.prod_congr rfl fun k _ => congrArg (fun q => TorusCoordPull.om hE.w z J J' q ^ Oinvε k) (o k).symm) ?_))
    exact ((val_corr hJ' (hx.2 y) r).trans (val_pull hJ' _ _ _)).symm

theorem Carries.isGrpPullback' [GrpObj Y] {Φ : ∀ T, (T ⟶ Y) ≃ GtPt D T} (hΦ : Represents Φ) (U : UnifPre I E A' G')
    {e : ℕ} {φ} (h : Carries hE (U.gt e) (Φ Y (𝟙 Y)) φ) :
    IsGrpPullback (thickObj R' I e G') Y (thick R' I e ≫ spMap ρ) φ := by
  refine ⟨h.isPullback hΦ U, fun T x y x₀ y₀ hx hy => ?_⟩
  let Tw := (Over.map (thick R' I e)).obj T
  let T₀ : Over (Sp R) := Over.mk (T.hom ≫ thick R' I e ≫ spMap ρ)
  let i : Tw.left ⟶ T₀.left := 𝟙 T.left
  have hi : i ≫ T₀.hom = Tw.hom ≫ spMap ρ := (Category.id_comp _).trans (Category.assoc _ _ _).symm
  have pl : ∀ k : T₀ ⟶ Y, GtPt.IsPull k.left (Φ Y (𝟙 Y)) (Φ T₀ k) := fun k => by
    have := hΦ.1 _ _ k (𝟙 Y)
    rwa [Category.comp_id] at this
  have key : ∀ (x : T ⟶ thickObj R' I e G') (x₀ : T₀ ⟶ Y), x₀.left = x.left ≫ φ →
      Thru hE.w hE.xe i (Φ T₀ x₀) (TorusCoord.toGtPt (U.gt e) x) := fun x x₀ hx => by
    refine (thru_pull_iff x₀ (pl x₀) i _).2 ?_
    have e₁ : i ≫ x₀.left = x.left ≫ φ := (Category.id_comp _).trans hx
    rw [e₁]
    exact h.thru x
  obtain ⟨ξ, hξ⟩ := ConstPoint.exists_gtPt_through globalFns_holds (pull_grp hE) hE.w_gen hE.xe.toAddMonoidHom hE.c_pr
    (T := T₀) (T' := Tw) i hi (Φ T₀ (x₀ * y₀))
  have hξ' : Thru hE.w hE.xe i (Φ T₀ (x₀ * y₀)) ξ := hξ
  have ad := Thru.isAdd (pull_grp hE) globalFns_holds hE.w_gen hi (key x x₀ hx) (key y y₀ hy) hξ' (hΦ.2 T₀ x₀ y₀)
  obtain rfl : ξ = TorusCoord.toGtPt (U.gt e) (x * y) :=
    isAdd_unique ad (TorusCoord.isAdd_pointsEquiv (U.gt e) globalFns_holds x y)
  exact (Category.id_comp _).symm.trans
    (eq_of_thru hΦ hE.xe.surjective ((thru_pull_iff _ (pl _) i _).1 hξ') (h.thru (x * y)))

theorem isGrpPullback_of_carries : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → IsGrpPullback (thickObj R' I e G') Y.H (thick R' I e ≫ spMap ρ) φ :=
  fun _ _ _ _ _ U Y _ _ h => h.isGrpPullback' Y.rep U

end GlobalTheory.FormalModel
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Ext

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre GlobalTheory.RayEv Formalism.L2.Pj

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (Y : Ext D)

theorem Φ_b {T : Over (Sp R)} (x : T ⟶ Y.H) : (Y.Φ T x).b = x ≫ Y.q := by
  have h := ((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).1
  rwa [Category.comp_id] at h

theorem isMonHom_q : IsMonHom Y.q :=
  isMonHom_of_mul _ fun T x x' => by
    rw [← Φ_b, ← Φ_b, ← Φ_b]; exact ((TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x x')).1

theorem exists_q_eq (c : GtCoord (⊥ : Ideal R) D 0 Y.H) : ∃ a : Y.H.left ⟶ (thickObj R ⊥ 0 Y.H).left, IsIso a ∧
    Y.q.left = a ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  refine ⟨a ≫ j, inferInstance, ?_⟩
  rw [haj, ← GlobalTheory.TorusCoord.pG_left]
  exact hx.1

theorem q_props : Smooth Y.q.left ∧ IsAffineHom Y.q.left ∧ Surjective Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := smooth_gtCoord_q c
  have := c.q_surj
  have := c.q_affine
  obtain ⟨a, _, h⟩ := Y.exists_q_eq c
  rw [h]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem formEq_term (k : ℕ) (α : D.X) :
    FormEq (Sum.elim (fun i => Y.q.left ≫ DegPre.famφB D α i) (DegPre.gtφT D Y.H Y.q α))
      (Sum.elim (DegPre.famε k) DegPre.gtε) (K' := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ)) := by
  have e1 : Y.q ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α) = padd D.P.A (DegPre.cT D Y.H α) Y.q := by
    simp only [padd, comp_lift_assoc, Category.comp_id]
    rw [← Hom.mul_def, ← Hom.mul_def, mul_comm, comp_toUnit_assoc]
  have e2 : Y.q.left ≫ (toUnit D.P.A ≫ D.c α).left = (DegPre.cT D Y.H α).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e3 : Y.q.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (DegPre.zeroT D Y.H).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e0 : Y.q.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (DegPre.cT D Y.H α) Y.q).left := by
    rw [← Over.comp_left, e1]
  intro U _ h
  rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp only [DegPre.famφB, DegPre.famε, DegPre.gtφT, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e0, e2, e3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem exists_isTermOf (k : ℕ) (α : D.X) (σ : D.SecB k α) : ∃ τ : SecK D.P.L Y.q.left k, IsTermOf Y σ τ := by
  obtain ⟨τ, hτ⟩ := exists_sec D.P.isLB (Y.formEq_term k α)
    (pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α))
  refine ⟨τ, fun T x y J hJ => ?_⟩
  refine (hτ _ _ y J hJ).trans ((sval_pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α)
    x.left y hJ).trans ?_)
  obtain ⟨-, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))
  have e := h₂ α y J hJ
  rw [Category.comp_id] at e
  rw [Over.comp_left]
  exact congrArg _ (congrArg Units.val e.symm)

end GlobalTheory.Mum.Ext

namespace GlobalTheory.Mum

theorem ext_smooth_affine_surj_terms (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) :
    Smooth Y.H.hom ∧ IsAffineHom Y.q.left ∧ Surjective Y.q.left ∧ IsMonHom Y.q ∧
      ∀ (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ τ : SecK D.P.L Y.q.left k, IsTermOf Y b τ := by
  obtain ⟨h1, h2, h3⟩ := Y.q_props
  refine ⟨?_, h2, h3, Y.isMonHom_q, Y.exists_isTermOf⟩
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  rw [← Over.w Y.q]
  infer_instance

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FibrePull

theorem fibre_isPull : ∀ (S T : Scheme.{0}) (A₀ : Over T) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S), P₀.IsLB → P.IsLB → SameFib A₀ P₀ (𝟙 _) A P f → ∃ (φ : A₀.left ⟶ A.left) (φ₂ : (G2 A₀).left ⟶ (G2 A).left), IsGrpPullback A₀ A f φ ∧ IsSquare φ φ₂ ∧ LBIso P₀ (P.pull φ₂) ∧ LBIso (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  intro S T A₀ _ _ P₀ A _ _ P f hP₀ hP hS
  obtain ⟨H, _, _, a, a₂, a', a₂', h₁, s₁, h₂, s₂, w⟩ := hS
  have : IsMonHom (Iso.refl A₀).hom := inferInstanceAs (IsMonHom (𝟙 A₀))
  obtain ⟨e, he, hea⟩ := grpPullback_iso h₁ (isGrpPullback_of_iso (Iso.refl A₀))
  have hea' : e.hom.left = a := by simpa using hea
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hinv : e.inv.left ≫ a = 𝟙 _ := by rw [← hea', ← Over.comp_left, e.inv_hom_id, Over.id_left]
  let ψ : G2 A₀ ⟶ G2 H := lift (fst A₀ A₀ ≫ e.inv) (snd A₀ A₀ ≫ e.inv)
  have ext2 : ∀ {G : Over T} {X : Scheme.{0}} (u v : X ⟶ (G2 G).left), u ≫ (fst G G).left = v ≫ (fst G G).left →
      u ≫ (snd G G).left = v ≫ (snd G G).left → u = v := fun u v h1 h2 => Over.tensorObj_ext _ _ h1 h2
  have ext2' : ∀ {X : Scheme.{0}} (u v : X ⟶ (G2 A).left), u ≫ (fst A A).left = v ≫ (fst A A).left →
      u ≫ (snd A A).left = v ≫ (snd A A).left → u = v := fun u v h1 h2 => Over.tensorObj_ext _ _ h1 h2
  have k1 : ψ.left ≫ (fst H H).left = (fst A₀ A₀).left ≫ e.inv.left := by rw [← Over.comp_left, lift_fst, Over.comp_left]
  have k2 : ψ.left ≫ (snd H H).left = (snd A₀ A₀).left ≫ e.inv.left := by rw [← Over.comp_left, lift_snd, Over.comp_left]
  have d1 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (fst A₀ A₀).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
  have d2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (snd A₀ A₀).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have d1' : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
  have d2' : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have hψ : ψ.left ≫ a₂ = 𝟙 _ := by
    apply ext2
    · rw [Category.assoc, s₁.1, Category.id_comp, ← Category.assoc, k1, Category.assoc, hinv, Category.comp_id]
    · rw [Category.assoc, s₁.2, Category.id_comp, ← Category.assoc, k2, Category.assoc, hinv, Category.comp_id]
  have hψ₀ : LBIso P₀ ((P₀.pull a₂).pull ψ.left) :=
    GlobalTheory.ThetaAffineGlue.lbIso_cancel hP₀ (pull_isLB hP₀ _) hP₀
      (by rw [hψ]; exact GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP₀)
      (LBIso.trans (pull_isLB hP₀ _) (pull_isLB hP _) (pull_isLB hP₀ _) w w.symm)
  have hP₀₂ : LBIso P₀ (P.pull (ψ.left ≫ a₂')) :=
    hψ₀.trans hP₀ (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP _) (GlobalTheory.ThetaAffineGlue.lbIso_pull w ψ.left)
  have hd : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (ψ.left ≫ a₂') = (e.inv.left ≫ a') ≫ (lift (𝟙 A) (𝟙 A)).left := by
    apply ext2'
    · simp only [Category.assoc]
      rw [s₂.1, d1', Category.comp_id, ← Category.assoc ψ.left, k1, ← Category.assoc, ← Category.assoc, d1, Category.id_comp]
    · simp only [Category.assoc]
      rw [s₂.2, d2', Category.comp_id, ← Category.assoc ψ.left, k2, ← Category.assoc, ← Category.assoc, d2, Category.id_comp]
  refine ⟨e.inv.left ≫ a', ψ.left ≫ a₂', ?_, ?_, hP₀₂, ?_⟩
  · exact ((isGrpPullback_of_iso e.symm).comp h₂).congr (Category.id_comp _) rfl
  · constructor
    · rw [Category.assoc, s₂.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
    · rw [Category.assoc, s₂.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · have h3 := GlobalTheory.ThetaAffineGlue.lbIso_pull hP₀₂ (lift (𝟙 A₀) (𝟙 A₀)).left
    rw [hd] at h3
    have hΔ := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
    exact h3.trans (pull_isLB hP₀ _) (pull_isLB hP _) (pull_isLB hΔ _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull
        (show LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P.pull (lift (𝟙 A) (𝟙 A)).left) from
          LBIso.trans hΔ (pull_isLB hΔ _) hΔ (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ) (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ))) (e.inv.left ≫ a')).symm

end GlobalTheory.FibrePull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unitaryTrait_pullback_thetaSystem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (T : UTrait Xo cf) (yK : ratHull S.R →+* FractionRing T.V), spMap yK ≫ u' = T.y → ∃ φ : T.P.A.A.left ⟶ ρ.P.A.left, IsGrpPullback T.P.A.A ρ.P.A (spMap (yK.comp (toRat S.R))) φ ∧ LBIso T.P.A.L (ρ.P.L.pull φ) ∧ ∀ (Y : Over (Sp (FractionRing T.V))) (x x' : Y ⟶ T.P.A.A) (w w' : Y.left ⟶ G.left) (a : 𝓞 E), w ≫ α = x.left ≫ φ → w' ≫ α = x'.left ≫ φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → x' = x ≫ T.P.oA.act a := by
  first | exact @GlobalTheory.UPoinc.TraitPullAct.exists_pull_act | exact GlobalTheory.UPoinc.TraitPullAct.exists_pull_act | (intros; apply GlobalTheory.UPoinc.TraitPullAct.exists_pull_act <;> assumption)
end
