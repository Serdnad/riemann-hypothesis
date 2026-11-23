module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsPrincipalPolarisationEqOne
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle107
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveOverValuationRing
open GlobalTheory.CechPic

theorem pull_eq_zero_of_mem {Y Z : Scheme.{0}} (W : Y.Opens) (r : Z ⟶ Y) (hr : ∀ z, r z ∈ W) {c : CechPic.Pic Y}
    (h : CechPic.pull W.ι c = 0) : CechPic.pull r c = 0 := by
  have e := IsOpenImmersion.lift_fac W.ι r (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hr z)
  rw [← e, pull_comp, h, map_zero]

theorem cls_pair {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a b : Y ⟶ X)
    (h : (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]).IsLB) :
    cls _ h = CechPic.pull a (cls L hL) - CechPic.pull b (cls L hL) := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

section Points

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L O : LB B.left}

theorem triv_iff (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x : T ⟶ B) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ B).left) :
    Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull r) ↔
      CechPic.pull r (CechPic.pull ((fst T B ≫ x) * snd T B).left (cls L hL) - CechPic.pull (snd T B).left (cls L hL) -
        CechPic.pull (snd T B).left (cls O hO)) = 0 := by
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  have hM := LB.isLB_div h₁ h₂
  refine (cls_eq_zero_iff (pull_isLB hM r)).symm.trans ?_
  rw [cls_pull hM, cls_div h₁ h₂, cls_pull hO]
  exact Iff.of_eq (congrArg (fun q => CechPic.pull r (q - _) = 0) (cls_pair hL _ _ h₁))

theorem inK_mul_inv (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x y : T ⟶ B)
    (hx : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι))
    (hy : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L y) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) :
    InK B L (x * y⁻¹) := by
  intro p
  obtain ⟨U, hU, h₁⟩ := hx p
  obtain ⟨U', hU', h₂⟩ := hy p
  refine ⟨U ⊓ U', ⟨hU, hU'⟩, ?_⟩
  have hD : (translDiff B L (x * y⁻¹)).IsLB := LB.isLB_linComb hL _ _
  let τ : T ⊗ B ⟶ T ⊗ B := lift (fst T B) ((fst T B ≫ y⁻¹) * snd T B)
  have k₁ : τ ≫ fst T B = fst T B := lift_fst _ _
  have k₂ : ∀ z : T ⟶ B, τ ≫ ((fst T B ≫ z) * snd T B) = (fst T B ≫ (z * y⁻¹)) * snd T B := fun z => by
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, k₁, MonObj.comp_mul, _root_.mul_assoc]
  have m : ∀ z, (fst T B).left ((((fst T B).left ⁻¹ᵁ (U ⊓ U')).ι ≫ τ.left) z) ∈ U ⊓ U' := fun z => by
    have e := congrArg (fun q : T ⊗ B ⟶ T => q.left z.1) k₁
    exact (congrArg (· ∈ U ⊓ U') e).mpr z.2
  have a₁ := pull_eq_zero_of_mem _ _ (fun z => (m z).1) ((triv_iff hL hO x _).1 h₁)
  have a₂ := pull_eq_zero_of_mem _ _ (fun z => (m z).2) ((triv_iff hL hO y _).1 h₂)
  have a := congrArg₂ (· - ·) a₁ a₂
  simp only [← map_sub, sub_sub_sub_cancel_right, sub_zero] at a
  rw [pull_comp, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, k₂, k₂, mul_inv_cancel,
    MonObj.comp_one, _root_.one_mul] at a
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  exact (congrArg _ (cls_pair hL _ _ hD)).trans a

end Points

theorem exists_geometric_point (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {O : LB P.A.left} (hO : O.IsLB)
    (hu : ∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) :
    ∃ x : Over.mk f ⟶ P.A, Triv (LB.div (translDiff P.A P.L x) (O.pull (snd (Over.mk f) P.A).left)) := by
  obtain ⟨P', g, hg, -, hm, ht⟩ := hL.polBaseChange S _ f P
  have hc : CechPic.pull g (cls P.L P.isLB) = cls P'.L P'.isLB := (cls_eq_iff (pull_isLB P.isLB g) P'.isLB).2 ht
  have hO' := pull_isLB hO g
  have one : ∀ T : Over (Spec (CommRingCat.of K)), toBase hg.w (1 : T ⟶ P'.A) = 1 := fun T => by
    have := hm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have lamO : lam (cls O hO) (fst P.A P.A) (snd P.A P.A) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  have lamO' : lam (cls _ hO') (fst P'.A P'.A) (snd P'.A P'.A) = 0 := by
    have e := congrArg (CechPic.pull (lift (toBase hg.w (fst P'.A P'.A)) (toBase hg.w (snd P'.A P'.A))).left) lamO
    rw [pull_lam, lift_fst, lift_snd, map_zero, lam, ← hm, ← one] at e
    rw [cls_pull hO, lam, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]
    exact e
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_point_primitiveBundle_eq_translate_ppav hL K P' (O.pull g) hO'
    ((cls_eq_zero_iff (LB.isLB_linComb hO' _ _)).1 ((cls_cube_two hO' _ _ (LB.isLB_linComb hO' _ _)).trans lamO'))
  have e := ((cls_eq_iff hO' (LB.isLB_linComb P'.isLB _ _)).2 hx').trans (cls_pair P'.isLB _ _ _)
  let T : Over S := Over.mk f
  have wx : x'.left ≫ P'.A.hom = 𝟙 _ := Over.w x'
  let x : T ⟶ P.A := Over.homMk (x'.left ≫ g) (by
    show (x'.left ≫ g) ≫ P.A.hom = f
    rw [Category.assoc, hg.w, ← Category.assoc, wx]
    exact Category.id_comp _)
  have w : (snd T P.A).left ≫ P.A.hom = (fst T P.A).left ≫ f := (Over.w (snd T P.A)).trans (Over.w (fst T P.A)).symm
  let T' : Over (Spec (CommRingCat.of K)) := Over.mk (Y := (T ⊗ P.A).left) (fst T P.A).left
  let h : T' ⟶ P'.A := Over.homMk (hg.lift (snd T P.A).left (fst T P.A).left w) (hg.lift_snd _ _ _)
  have hh : h.left ≫ g = (snd T P.A).left := hg.lift_fst _ _ _
  let u : Over.mk (T'.hom ≫ f) ⟶ T ⊗ P.A := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Over.w (fst T P.A)).symm)
  have b₁ : u ≫ snd T P.A = toBase hg.w h := Over.OverMorphism.ext ((Category.id_comp _).trans hh.symm)
  have b₂ : u ≫ fst T P.A ≫ x = toBase hg.w (toUnit T' ≫ x') := by
    refine Over.OverMorphism.ext ((Category.id_comp _).trans ?_)
    have : (toUnit T').left = (fst T P.A).left := (Category.comp_id _).symm.trans (Over.w (toUnit T'))
    show (fst T P.A).left ≫ x'.left ≫ g = ((toUnit T').left ≫ x'.left) ≫ g
    rw [this]
    exact (Category.assoc _ _ _).symm
  have b : h.left ≫ ((toUnit P'.A ≫ x') * 𝟙 P'.A).left ≫ g = ((fst T P.A ≫ x) * snd T P.A).left := by
    have b₃ : toBase hg.w (h ≫ ((toUnit P'.A ≫ x') * 𝟙 P'.A)) = u ≫ ((fst T P.A ≫ x) * snd T P.A) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, b₁, b₂, ← hm, Category.comp_id, ← Category.assoc, comp_toUnit]
    exact (Category.assoc _ _ _).symm.trans ((congrArg CommaMorphism.left b₃).trans (Category.id_comp _))
  have e' := congrArg (CechPic.pull h.left) e
  rw [cls_pull hO, ← hc, pull_id, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, Category.assoc, b, hh] at e'
  have h₁ : (translDiff P.A P.L x).IsLB := LB.isLB_linComb P.isLB _ _
  have h₂ := pull_isLB hO (snd T P.A).left
  refine ⟨x, (cls_eq_zero_iff (LB.isLB_div h₁ h₂)).1 ?_⟩
  rw [cls_div h₁ h₂, sub_eq_zero]
  exact (cls_pair P.isLB _ _ h₁).trans e'.symm

theorem isIso_of_flat_of_closedPoint {V : Type} [CommRing V] [IsLocalRing V] [_root_.IsReduced V] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of V)) [IsClosedImmersion q] [Flat q] (h : X) (hh : q h = IsLocalRing.closedPoint V) :
    IsIso q := by
  have : Surjective q := ⟨fun s => by
    obtain ⟨y, -, hy⟩ := Flat.generalizingMap q (a := h) (b := s) (by
      rw [hh]; exact IsLocalRing.specializes_closedPoint s)
    exact ⟨y, hy⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective q

theorem exists_section_translate : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P : PolAV (Spec (CommRingCat.of V))) (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1]) := by
  intro hL V _ _ _ P O hO hu
  have proj : IsProjBy P.A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V P.A P.L P.isLB).1 P.ample
    exact ⟨_, isLB_pw P.isLB _, n, s, hs⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns V P.A P.isAb proj P.L O P.isLB hO
  have fin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns V P.A P.isAb P.L O P.isLB hO
    P.ample H j hj hH
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨c⟩ := (hL.cube _ P ⟨P.L, r, P.isLB, hr⟩ rfl).1
  have flat : Flat H.hom := GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR hL.globalFns V P.A P.isAb proj ⟨P.L, r, P.isLB, hr⟩ c O hO hu H j hj hH fin
  have mono : Mono H.hom := ⟨fun {Z} a b e => by
    let a' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk a e
    let b' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk b rfl
    have := (inK_mul_inv P.isLB hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one P.ktriv
    rw [mul_inv_eq_one] at this
    exact (cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩
  have : IsClosedImmersion H.hom := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩
  let K : Type := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* K := (algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨x₀, hx₀⟩ := exists_geometric_point hL P hO hu K (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨y, -⟩ := (hH _ x₀).1 fun p => ⟨⊤, trivial, by
    have hM := LB.isLB_div (show (translDiff P.A P.L x₀).IsLB from LB.isLB_linComb P.isLB _ _)
      (pull_isLB hO (snd _ P.A).left)
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩
  have : IsIso H.hom := isIso_of_flat_of_closedPoint H.hom (y.left (IsLocalRing.closedPoint K))
    ((congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ))
  let σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H := Over.homMk (inv H.hom) (IsIso.inv_hom_id _)
  obtain ⟨U, hU, ht⟩ := (hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have e := pull_eq_zero_of_mem ((fst _ P.A).left ⁻¹ᵁ ⊤) (lift (toUnit P.A) (𝟙 P.A)).left (fun _ => trivial)
    ((triv_iff P.isLB hO (σ ≫ j) _).1 ht)
  rw [map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)] at e
  exact ⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).1 (e.symm.trans (cls_pair P.isLB _ _ _).symm)⟩

end GlobalTheory.PrimitiveOverValuationRing
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.thetaConstant_eq_sum_thetaTerms_odd_multiple : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → ∀ w, TXFrame (m ^ 2) p w → ∀ (g' : GtPtF D.toPre F), GtPtF.IsNsmul m p.g g' → ∀ (κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ m) (m ^ 2) 1)), Normd κ → ∀ w' : Frm D.toPre F 1 g'.b, w'.IsGen → (∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J * val κ p.g.b.left z J = val w' (𝟙 _) z J) → SumF I F (coef ϑ g' w') c ∧ ∀ s, U.ExpandsF F (m ^ 2) w₀ t s → ∀ (o : GtPtF D.toPre F) (w₁ : Frm D.toPre F (m ^ 2) o.b), o.IsZero → FrmOne w₁ → (∀ χ, coef s o w₁ (m • χ + p.y) = coef ϑ g' w' χ) ∧ ∀ β, (∀ χ, β ≠ m • χ + p.y) → coef s o w₁ β = 0 := by
  first | exact @GlobalTheory.UT.ThetaSum.theta_const_sum | exact GlobalTheory.UT.ThetaSum.theta_const_sum | (intros; apply GlobalTheory.UT.ThetaSum.theta_const_sum <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ThetaAverage
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

section Sums
variable {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)}

end Sums

section Frames
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_translate {t : Multiplicative D.X →* Fˣ} {g g₀ g' : GtPtF D F} (ht : IsTor t g₀) (hadd : g.IsAdd g₀ g') :
    g'.b = g.b ∧ ∀ χ z J, Good D.P.L z J → (val (g'.s χ) (𝟙 _) z J).val =
      cstH z (t (Multiplicative.ofAdd χ)).val * (val (g.s χ) (𝟙 _) z J).val := by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  rw [ht.1, _root_.mul_one] at hb
  refine ⟨hb, fun χ z J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have e := hs χ z J hJ
  have e₀ : th D z J (cP D _ χ) g.b g₀.b = 1 := by rw [ht.1, C.face₃]
  rw [e₀, _root_.mul_one] at e
  rw [e, Units.val_mul, ht.2 χ z J hJ, cst_eq, mul_comm]

theorem coef_translate {k : ℕ} {t : Multiplicative D.X →* Fˣ} {g g₀ g' : GtPtF D F} (ht : IsTor t g₀)
    (hadd : g.IsAdd g₀ g') {w : Frm D F k g.b} (hw : w.IsGen) {w' : Frm D F k g'.b} {c : F}
    (hv : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cstH z c * (val w (𝟙 _) z J).val) (s : Fam D F k) (χ : D.X) :
    coef s g' w' χ = c * (t (Multiplicative.ofAdd χ)).val * coef s g w χ := by
  obtain ⟨hb, hs⟩ := val_translate ht hadd
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  have e₁ : lift (𝟙 (TF (R := R) F)) g'.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
  rw [hv z J hJ, hs χ z J hJ, e₁]
  simp only [cst_eq, map_mul] at a ⊢
  linear_combination cstH z c * cstH z (t (Multiplicative.ofAdd χ)).val * a

end Frames

attribute [local instance] gtGroup

end GlobalTheory.UT.ThetaAverage
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
theorem _root_.GlobalTheory.twistBaseChange : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBaseChangeStatement :=
  _root_.GlobalTheory.twistBaseChange_of_finrank_sections_one _root_.GlobalTheory.AbLaw.finrank_sections_principal_polarisation_eq_one

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.KeyIota
open GlobalTheory.TorusExt

theorem eq_of_torsion_chars {X F : Type} [AddCommGroup X] [Module.Free ℤ X] [Field F] [IsAlgClosed F] [CharZero F]
    {a b : X} (h : ∀ k : ℕ, 1 ≤ k → ∀ t : Multiplicative X →* Fˣ, t ^ k = 1 →
      t (Multiplicative.ofAdd a) = t (Multiplicative.ofAdd b)) : a = b := by
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℤ hd
  let k : ℕ := (φ (a - b)).natAbs + 1
  haveI : NeZero k := ⟨Nat.succ_ne_zero _⟩
  haveI : NeZero (k : F) := ⟨Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  let u : Fˣ := (hζ.isUnit (NeZero.ne k)).unit
  have hu : IsPrimitiveRoot u k := hζ.isUnit_unit (NeZero.ne k)
  let t : Multiplicative X →* Fˣ := (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative φ.toAddMonoidHom)
  have ht : ∀ x, t (Multiplicative.ofAdd x) = u ^ φ x := fun _ => rfl
  have h1 := h k (Nat.succ_le_succ (Nat.zero_le _)) t (MonoidHom.ext fun x => by
    show t (Multiplicative.ofAdd x.toAdd) ^ k = 1
    rw [ht, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu.pow_eq_one, one_zpow])
  rw [ht, ht] at h1
  have h2 : u ^ φ (a - b) = 1 := by rw [map_sub, zpow_sub, h1, mul_inv_cancel]
  have h3 := Int.natCast_dvd.1 ((hu.zpow_eq_one_iff_dvd _).1 h2)
  have h4 := Nat.le_of_dvd (Int.natAbs_pos.2 hφ) h3
  omega

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem weilQkIs_swap {k : ℕ} {p p' : QkPt D F k} {z : Fˣ} (h : WeilQkIs D F k p p' z) :
    WeilQkIs D F k p' p (z⁻¹ : Fˣ) := by
  intro w' w hw' hw s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ α j
  have e := h w w' hw hw' s s₃ s₄ s₁ s₂ h₃ h₄ h₁ h₂ α j
  rw [e, ← _root_.mul_assoc]
  have : ∀ W, DegPre.constBF D F ((z⁻¹ : Fˣ) : F) W * DegPre.constBF D F (z : F) W = 1 := fun W => by
    unfold DegPre.constBF
    rw [← map_mul, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, map_one]
  rw [this, _root_.one_mul]

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ E E' : EndU U.toUnifPre, Function.Injective E.h → Function.Injective E'.h → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g' := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U E E' hE hE' hadj y g g' hg hgg'
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  haveI : CharZero (FractionRing V) := charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing V) F).injective
  letI := gtGroup D.toPre F
  have hB := D.tau_bimult
  have inj := GlobalTheory.IotaInj.main hL V _ hA D F
  have dv := (gt_onto_divisible_kernel hL V _ hA D F).2.1
  have ec := GlobalTheory.T.uniformizationEndomorphism_calculus hL V _ hA D A G hG U F
  have key := GlobalTheory.T.torsionPoint_endomorphism_image_eq_moved_gtPoint hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U
  have ros := (GlobalTheory.T.rosatiAdjoint_abelianPart_and_classifying_map_linear hL V _ hA D A G hG U E E' hadj).1

  have act : ∀ e : EndU U.toUnifPre, ∃ a : GtPtF D.toPre F →+ GtPtF D.toPre F, ∀ x x', e.Act x x' ↔ x' = a x := by
    intro e
    obtain ⟨ex, ad, -⟩ := ec e e e
    choose a ha hu using ex
    exact ⟨AddMonoidHom.mk' a fun x x' => (isAdd_iff_eq _ _ _).1
      (ad x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (ha x) (ha x') (ha _)),
      fun x x' => ⟨hu x x', fun h => h ▸ ha x⟩⟩
  obtain ⟨a, ha⟩ := act E
  obtain ⟨a', ha'⟩ := act E'
  have hy : g = iota hB F y := (isIota_iff_eq hB _ _).1 hg
  have hg' : g' = a g := (ha _ _).1 hgg'

  have div : ∀ k : ℕ, 1 ≤ k → ∀ f, Tors U.toUnifPre F k f → ∃ p p' : QkPt D.toPre F k, p.y = y ∧
      f p' = f p ≫ E.aA ∧ GtPtF.IsIota p'.y g' := by
    intro k hk f hf
    obtain ⟨gk, hgk⟩ := dv k hk g
    let p : QkPt D.toPre F k := ⟨y, gk, g, hgk, hg⟩
    obtain ⟨p', e₁, e₂⟩ := key E hE k hk p (f p) ((hf.1 _ _).2 rfl) (a gk) ((ha _ _).2 rfl)
    refine ⟨p, p', rfl, ((hf.1 _ _).1 e₂).symm, (isIota_iff_eq hB _ _).2 ?_⟩
    rw [← qk_nsmul hB p', e₁, ← map_nsmul, hg', (isNsmul_iff_eq _ _ _).1 hgk]
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F 1 le_rfl
  obtain ⟨-, p₁, -, -, hp₁⟩ := div 1 le_rfl f₁ hf₁
  suffices hs : p₁.y = E'.h y from hs ▸ hp₁
  refine eq_of_torsion_chars (F := F) fun k hk t ht => ?_
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F k hk
  obtain ⟨p, p', hp, hpp', hp'⟩ := div k hk f hf
  have wp := GlobalTheory.T.weilQk_pairing_existsUnique_torus hL V _ hA D F k hk
  rw [inj _ _ _ hp₁ hp', ← hp]
  have tor : ∀ p : QkPt D.toPre F k, f p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U.toUnifPre.ext
    exact ((hf.1 p _).2 rfl w hw).1
  have h0 : k • torusPt D.toPre F (Additive.ofMul t) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, ht, ofMul_one, map_zero]
  let q : QkPt D.toPre F k := qkMk hB 0 (torusPt D.toPre F (Additive.ofMul t)) (h0.trans (map_zero _).symm)
  have hq : IsTor t q.g := by
    apply (isTor_iff _ _).2
    simpa [q] using (isTorusPtF_torusPt t)
  obtain ⟨q', e₁, e₂⟩ := key E' hE' k hk q (f q) ((hf.1 _ _).2 rfl) (a' q.g) ((ha' _ _).2 rfl)
  have hq' : IsTor (t.comp (AddMonoidHom.toMultiplicative E'.h)) q'.g :=
    (ec E' E' E').2.2.1 t q.g q'.g hq ((ha' _ _).2 e₁)
  have hq0 : q'.y = 0 := by
    refine inj _ _ (0 : GtPtF D.toPre F) ((isIota_iff_eq hB _ _).2 ?_) ((isIota_iff_eq hB _ _).2 (map_zero _).symm)
    rw [← qk_nsmul hB q', e₁, ← map_nsmul]
    simpa [q] using ((congrArg a' h0).trans (map_zero _)).symm
  have w₁ := (hf.2.2.2.2 _ _ _).1 (weilQkIs_swap ((wp q p').2 t (by simp [q]) hq))
  rw [hpp', weilIs_comp_iff_of_rosatiAdj hL _ A E.aA E'.aA E.homA E'.homA ros F _ k _ _ (tor p) (tor q),
    (hf.1 _ _).1 e₂] at w₁
  have w₂ := weilQkIs_swap ((hf.2.2.2.2 _ _ _).2 w₁)
  rw [inv_inv] at w₂
  exact (wp q' p).1.unique w₂ ((wp q' p).2 _ hq0 hq')

end GlobalTheory.KeyIota
end
end
