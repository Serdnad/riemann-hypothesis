module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.PullAction

section
open MonObj

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_lift_end (h : IsGrpPullback G' G f φ) (u : G ⟶ G) [IsMonHom u] :
    ∃ v : G' ⟶ G', IsMonHom v ∧ v.left ≫ φ = φ ≫ u.left := by
  let v : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ u.left) G'.hom (by rw [Category.assoc, Over.w u, h.1.w]))
    (h.1.lift_snd _ _ _)
  have hv : v.left ≫ φ = φ ≫ u.left := h.1.lift_fst _ _ _
  have inj : ∀ (T : Over S') (x y : T ⟶ G'), pushPt h.1.w x = pushPt h.1.w y → x = y := fun T x y e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w x, Over.w y]))
  have pa : ∀ (T : Over S') (x : T ⟶ G'), pushPt h.1.w (x ≫ v) = pushPt h.1.w x ≫ u := fun T x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hv, Category.assoc])
  have pm : ∀ (T : Over S') (x y : T ⟶ G'), pushPt h.1.w (x * y) = pushPt h.1.w x * pushPt h.1.w y := fun T x y =>
    Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have p1 : ∀ (T : Over S'), pushPt h.1.w (1 : T ⟶ G') = 1 := fun T => by
    have := pm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hm : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ v = (x ≫ v) * (y ≫ v) := fun T x y => inj T _ _ (by
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp])
  have h1 : ∀ (T : Over S'), (1 : T ⟶ G') ≫ v = 1 := fun T => inj T _ _ (by
    rw [pa, p1, MonObj.one_comp])
  refine ⟨v, ⟨?_, ?_⟩, hv⟩
  · have := h1 (𝟙_ _)
    simpa [Hom.one_def] using this
  · have := hm (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this]
    congr 1

end

theorem exists_action_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (W : Scheme.{0}) (w : W ⟶ Xo.XF c) (G₀ : Over W) [GrpObj G₀] (β₀ : G₀.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) β₀ → ∃ f₀ : 𝓞 E → (G₀ ⟶ G₀), (∀ a, IsMonHom (f₀ a) ∧ (f₀ a).left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ W) (tT : SAB H T) (mm : SABMap tT Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _)), ∃ γ : tT.G.left ⟶ G₀.left, IsGrpPullback tT.G G₀ x γ ∧ γ ≫ β₀ = mm.φ ∧ LBIso tT.PP.L ((Xo.univ.t.PP.L.pull β₀).pull γ) ∧ ∀ a, (tT.act.act a).left ≫ γ = γ ≫ (f₀ a).left := by
  intro E _ _ _ H Dw l Xo c W w G₀ _ β₀ hβ
  have key : ∀ a : 𝓞 E, ∃ v : G₀ ⟶ G₀, IsMonHom v ∧ v.left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left := fun a =>
    haveI := Xo.univ.t.act.hom a
    exists_lift_end hβ _
  choose f₀ hf₀ using key
  refine ⟨f₀, hf₀, fun T x tT mm => ?_⟩
  have hp := hβ.1
  let γ : tT.G.left ⟶ G₀.left := hp.lift mm.φ (tT.G.hom ≫ x)
    (mm.cart.1.w.trans (by simp only [Category.assoc]))
  have hγ : γ ≫ β₀ = mm.φ := hp.lift_fst _ _ _
  have hw : γ ≫ G₀.hom = tT.G.hom ≫ x := hp.lift_snd _ _ _
  have hL : LBIso tT.PP.L (Xo.univ.t.PP.L.pull mm.φ) := mm.lin.imp fun _ h => h.1
  have hU := Xo.univ.t.PP.isLB
  refine ⟨γ, hβ.cancel (by rw [hγ, ← Category.assoc]; exact mm.cart) hw, hγ,
    LBIso.trans tT.PP.isLB (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) hL
      (GlobalTheory.GenSpread.lbIso_pull_pull hU γ hγ.symm), fun a => ?_⟩
  apply hp.hom_ext
  · rw [Category.assoc, hγ, mm.act, Category.assoc γ, (hf₀ a).2, ← Category.assoc γ, hγ]
  · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

end GlobalTheory.PullAction
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison


theorem _root_.GlobalTheory.T.exists_finiteType_subring_model_abelian_lineBundle : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (F : Finset R), IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (_ : IsCommMonObj B) (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P₀ : LB (G2 B).left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) := by
  first | exact @GlobalTheory.SiegApproxModel.model_exists | exact GlobalTheory.SiegApproxModel.model_exists | (intros; apply GlobalTheory.SiegApproxModel.model_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem lift_left_comp {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left}
    {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (hsq : IsSquare χ χ₂)
    (x y : B ⟶ C) (x' y' : B' ⟶ C') (hx : x'.left ≫ χ = φB ≫ x.left) (hy : y'.left ≫ χ = φB ≫ y.left) :
    (lift x' y').left ≫ χ₂ = φB ≫ (lift x y).left := by
  have f1 : (lift x y).left ≫ (fst C C).left = x.left := congrArg (fun q => q.left) (lift_fst x y)
  have f2 : (lift x y).left ≫ (snd C C).left = y.left := congrArg (fun q => q.left) (lift_snd x y)
  have f1' : (lift x' y').left ≫ (fst C' C').left = x'.left := congrArg (fun q => q.left) (lift_fst x' y')
  have f2' : (lift x' y').left ≫ (snd C' C').left = y'.left := congrArg (fun q => q.left) (lift_snd x' y')
  apply pullback.hom_ext
  · show (_ ≫ _) ≫ (fst C C).left = (_ ≫ _) ≫ (fst C C).left
    rw [Category.assoc, hsq.1, ← Category.assoc, f1', hx, Category.assoc, f1]
  · show (_ ≫ _) ≫ (snd C C).left = (_ ≫ _) ≫ (snd C C).left
    rw [Category.assoc, hsq.2, ← Category.assoc, f2', hy, Category.assoc, f2]

theorem lbIso_eighth_pull : ∀ {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (Q : LB (C ⊗ C).left) (Q' : LB (C' ⊗ C').left) (L : LB B.left) (L' : LB B'.left) (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (W : Matrix (Fin 8) (Fin 8) ℤ), Q.IsLB → Q'.IsLB → L.IsLB → L'.IsLB → IsSquare χ χ₂ → LBIso Q' (Q.pull χ₂) → (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) → LBIso L' (L.pull φB) → LBIso L (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → LBIso L' (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) := by
  intro T T' B C B' C' φB χ χ₂ Q Q' L L' pr pr' W hQ hQ' hL hL' hsq HQ hpr h1 hLL
  have h3 := GlobalTheory.ShapePull.iso_linComb_pull HQ (K := Fin 8 × Fin 8)
    (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2) φB (fun ab => lift_left_comp hsq _ _ _ _ (hpr ab.1) (hpr ab.2))
  have h2 := GlobalTheory.SiegelPullComp.iso_pull φB hLL
  have lc : (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
      (fun ab => W ab.1 ab.2)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hQ _ _
  have lc' : (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left)
      (fun ab => W ab.1 ab.2)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hQ' _ _
  exact LBIso.trans hL' (pull_isLB hL φB) lc' h1
    (LBIso.trans (pull_isLB hL φB) (pull_isLB lc φB) lc' h2 h3.symm)

end GlobalTheory.Poinc.Eq8
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.torsion_commutatorPairing_const_holomorphicFamily_anyLineBundle : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), LocallyOfFiniteType s → IsAbelianScheme G → L.IsLB → ∀ (m k : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (c : ℂˣ) (b₀ : Fin m → ℂ), 0 < k → IsOpen B → IsPreconnected B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ = x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs G L k (x b₀) (x' b₀) (unitOn c) → ∀ b ∈ B, Out.WeilIs G L k (x b) (x' b) (unitOn c))) := by
  first | exact @GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB | exact GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB | (intros; apply GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PowCart

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {β : G'.left ⟶ G.left}

theorem square_over_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G2 G).left}
    (h : ∀ i, a ≫ (x2 G i).left = b ≫ (x2 G i).left) : a = b :=
  pullback.hom_ext (h 0) (h 1)

theorem isPullback_two (hp : IsPullback β G'.hom G.hom f) :
    IsPullback (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left (G2 G').hom (G2 G).hom f := by
  set F2 := (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left with hF2
  have f2 : ∀ i, F2 ≫ (x2 G i).left = (x2 G' i).left ≫ β := fun i => by
    fin_cases i
    · exact congrArg (fun z => z.left) (lift_fst (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
    · exact congrArg (fun z => z.left) (lift_snd (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
  have w : F2 ≫ (G2 G).hom = (G2 G').hom ≫ f := Over.w (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
  have ex : ∀ s : PullbackCone (G2 G).hom f, ∃ l : s.pt ⟶ (G2 G').left,
      l ≫ F2 = s.fst ∧ l ≫ (G2 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 2 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x2 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x2 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G2 G' := lift (x 0) (x 1)
    have lx : ∀ i, l ≫ x2 G' i = x i := fun i => by fin_cases i <;> simp [l, x2]
    refine ⟨l.left, square_over_hom_ext _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f2, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => square_over_hom_ext _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f2, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem fourth_power_over_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G4 G).left}
    (h : ∀ i, a ≫ (x4 G i).left = b ≫ (x4 G i).left) : a = b := by
  apply pullback.hom_ext
  · exact h 0
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]; exact h 1
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]; exact h 2
      · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]; exact h 3

theorem isPullback_four (hp : IsPullback β G'.hom G.hom f) :
    IsPullback (lift (pushPt hp.w (x4 G' 0)) (lift (pushPt hp.w (x4 G' 1))
      (lift (pushPt hp.w (x4 G' 2)) (pushPt hp.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f := by
  set L4 := lift (pushPt hp.w (x4 G' 0)) (lift (pushPt hp.w (x4 G' 1))
      (lift (pushPt hp.w (x4 G' 2)) (pushPt hp.w (x4 G' 3)))) with hL4
  have f4 : ∀ i, L4.left ≫ (x4 G i).left = (x4 G' i).left ≫ β := fun i => by
    rw [← Over.comp_left]
    have : L4 ≫ x4 G i = pushPt hp.w (x4 G' i) := by fin_cases i <;> simp [L4, x4]
    rw [this]; rfl
  have w : L4.left ≫ (G4 G).hom = (G4 G').hom ≫ f := Over.w L4
  have ex : ∀ s : PullbackCone (G4 G).hom f, ∃ l : s.pt ⟶ (G4 G').left,
      l ≫ L4.left = s.fst ∧ l ≫ (G4 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 4 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x4 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x4 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G4 G' := lift (x 0) (lift (x 1) (lift (x 2) (x 3)))
    have lx : ∀ i, l ≫ x4 G' i = x i := fun i => by fin_cases i <;> simp [l, x4]
    refine ⟨l.left, fourth_power_over_hom_ext _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f4, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => fourth_power_over_hom_ext _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f4, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem isPullback_three [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (gp : IsGrpPullback G' G f β) :
    IsPullback (cubeMapOf gp).F3 (G3 G').hom (G3 G).hom f := by
  have hp := gp.1
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 G' i).left ≫ β := cubeMap_comp_proj_three (cubeMapOf gp)
  have w : (cubeMapOf gp).F3 ≫ (G3 G).hom = (G3 G').hom ≫ f :=
    Over.w (lift (pushPt hp.w (x3 G' 0)) (lift (pushPt hp.w (x3 G' 1)) (pushPt hp.w (x3 G' 2))))
  have ex : ∀ s : PullbackCone (G3 G).hom f, ∃ l : s.pt ⟶ (G3 G').left,
      l ≫ (cubeMapOf gp).F3 = s.fst ∧ l ≫ (G3 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 3 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 G' := lift (x 0) (lift (x 1) (x 2))
    have lx : ∀ i, l ≫ x3 G' i = x i := fun i => by fin_cases i <;> simp [l, x3]
    refine ⟨l.left, hom_ext_triple _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f3, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => hom_ext_triple _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f3, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem isPullback_pow {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β) :
    IsPullback (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left (G2 G').hom (G2 G).hom f ∧
    IsPullback (cubeMapOf h).F3 (G3 G').hom (G3 G).hom f ∧
    IsPullback (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
      (pushPt h.1.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f :=
  ⟨isPullback_two h.1, isPullback_three h, isPullback_four h.1⟩

end GlobalTheory.Mum.PowCart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenTransport

theorem exists_unflat {X X' Y : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (ε : J → ℤ) (ψ : K → (Y ⟶ X')) (δ : K → ℤ)
    (T : LB.Gen (LB.LinComb (LB.LinComb L F ε) ψ δ)) (hT : T.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι), Good L z I →
        val t r z I = val T r z (fun χ j => I (χ ≫ F j)) := by
  have le : ∀ p : K × J → L.ι, LB.wchart L (K := K × J) (fun p => ψ p.1 ≫ F p.2) p ≤
      LB.wchart (LB.LinComb L F ε) ψ (fun k j => p (k, j)) := fun p y hy =>
    Set.mem_iInter.2 fun k => by
      have h1 : ψ k y ∈ LB.wchart L F (fun j => p (k, j)) :=
        Set.mem_iInter.2 fun j => Set.mem_iInter.1 hy (k, j)
      exact h1
  let t : LB.Gen (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2)) :=
    ⟨fun p => res (le p) (T.s fun k j => p (k, j))⟩
  refine ⟨t, isGen_of_gm _ fun y p q hp hq => ?_, fun Z r z I hI => ?_⟩
  · refine (gm_res _ y (le p) hp _).trans (Eq.trans ?_ (congrArg _ (gm_res _ y (le q) hq _)).symm)
    refine (gen_trans hT (𝟙 Y) y (le p hp) (le q hq)).trans (congrArg (· * _) ?_)
    refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ δ k)
      (gm_linComb L F ε (𝟙 Y ≫ ψ k) y (fun j => p (k, j)) (fun j => q (k, j)) (Set.mem_iInter.1 (le p hp) k)
        (Set.mem_iInter.1 (le q hq) k))).trans ?_
    simp only [trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, mul_comm]
  · refine (gm_res r z (le _) (hI.mem (fun p : K × J => ψ p.1 ≫ F p.2) r) _).trans ?_
    exact (val_of T r z (fun χ j => I (χ ≫ F j)) _ fun k => funext fun j => congrArg I (Category.assoc _ _ _)).symm

theorem exists_transport : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {J K : Type} [Fintype J] [Fintype K], L.IsLB → L'.IsLB → ∀ (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)), w.IsGen → ∀ (φ' : K → (Y ⟶ X')) (δ : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' δ)), a.IsGen → ∃ t : LB.Gen (LB.LinComb L (fun p : K × J => φ' p.1 ≫ pr p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι) (I' : (Z ⟶ X') → L'.ι), Good L z I → Good L' z I' → val t r z I = (∏ k, gv w (r ≫ φ' k) z (fun j => I ((r ≫ φ' k) ≫ pr j)) (I' (r ≫ φ' k)) ^ δ k) * val a r z I' := by
  intro X X' Y L L' J K _ _ hL hL' pr ε w hw φ' δ a ha
  obtain ⟨T, hT, hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_linComb hL' φ' δ)
    (LB.isLB_linComb (LB.isLB_linComb hL pr ε) φ' δ) (LB.linCombIso w φ' δ) (DVR.linCombIso_isGen w hw _ _) a ha
  obtain ⟨t, ht, hv'⟩ := exists_unflat pr ε φ' δ T hT
  refine ⟨t, ht, fun Z r z I I' hI hI' => (hv' Z r z I hI).trans ?_⟩
  have hI'' : Good (LB.LinComb L pr ε) z (fun χ j => I (χ ≫ pr j)) := fun χ => hI.mem pr χ
  refine (hv Z r z _ (fun k => I' (r ≫ φ' k)) (hI''.mem φ' r) (hI'.mem φ' r)).trans (congrArg₂ (· * ·) ?_ rfl)
  exact GlobalTheory.WtTower.gm_linCombIso w φ' δ (fun k j => I ((r ≫ φ' k) ≫ pr j), fun k => I' (r ≫ φ' k)) r z
    ⟨hI''.mem φ' r, hI'.mem φ' r⟩

end GlobalTheory.Mum.GenTransport

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CubeSymDescent

theorem of_push : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → ∀ x y u : T ⟶ G', cubV c z I (pushHom h T x⁻¹) (pushHom h T y⁻¹) (pushHom h T u⁻¹) * val s (pushHom h T (x * y)).left z I * val s (pushHom h T (x * u)).left z I * val s (pushHom h T (y * u)).left z I = cubV c z I (pushHom h T x) (pushHom h T y) (pushHom h T u) * val s (pushHom h T (x * y * u)).left z I * val s (pushHom h T x).left z I * val s (pushHom h T y).left z I * val s (pushHom h T u).left z I) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J = cubV c z J x y u * val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J := by
  intro S S' G G' _ _ _ _ f β h L c s hs i₃ c₃ hup T x y u z J hJ
  let φs : Fin 2 → (G.left ⟶ G.left) := ![(ι[G]).left, 𝟙 G.left]
  let εs : Fin 2 → ℤ := ![1, -1]
  let a := x3 G 0
  let b := x3 G 1
  let d := x3 G 2
  let A := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
    (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left))
    (LB.pullGen L.L φs εs s (b * d).left)
  have vA : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      val A V.left z J = cubV c z J (V ≫ a)⁻¹ (V ≫ b)⁻¹ (V ≫ d)⁻¹ * val s ((V ≫ a) * (V ≫ b)).left z J *
        val s ((V ≫ a) * (V ≫ d)).left z J * val s ((V ≫ b) * (V ≫ d)).left z J := by
    intro T V z J hJ
    have m1 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left))
      (LB.pullGen L.L φs εs s (b * d).left) V.left
    have m2 := val_mul hJ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left) V.left
    have m3 := val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left) V.left
    refine m1.trans ?_
    rw [m2, m3, val_pull hJ, val_pull hJ, val_pull hJ, val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]
    simp only [← Over.comp_left, comp_lift, GrpObj.comp_inv, MonObj.comp_mul]
    rfl
  let B := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
    (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
    (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d.left)
  have vB : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      val B V.left z J = cubV c z J (V ≫ a) (V ≫ b) (V ≫ d) * val s ((V ≫ a) * (V ≫ b) * (V ≫ d)).left z J *
        val s (V ≫ a).left z J * val s (V ≫ b).left z J * val s (V ≫ d).left z J := by
    intro T V z J hJ
    have m1 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
      (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d.left) V.left
    have m2 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
      (LB.pullGen L.L φs εs s b.left) V.left
    have m3 := val_mul hJ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left) V.left
    have m4 := val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left) V.left
    refine m1.trans ?_
    rw [m2, m3, m4, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ,
      val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]
    simp only [← Over.comp_left, comp_lift, MonObj.comp_mul]
    rfl
  have hcorr : LB.Gen.Corr L.L _ _ _ _ A B := by
    refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB (cubeMapOf h).F3 i₃ (fun a b e => c₃ a b e) fun z J hJ => ?_
    let P : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G :=
      lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))
    have hP : (cubeMapOf h).F3 = P.left := rfl
    have ha : P ≫ a = pushHom h (G3 G') (x3 G' 0) := by simp [P, a, x3]; rfl
    have hb : P ≫ b = pushHom h (G3 G') (x3 G' 1) := by simp [P, b, x3]; rfl
    have hd : P ≫ d = pushHom h (G3 G') (x3 G' 2) := by simp [P, d, x3]; rfl
    rw [hP, vA _ P z J hJ, vB _ P z J hJ, ha, hb, hd]
    have e := hup (G3 G') z J hJ (x3 G' 0) (x3 G' 1) (x3 G' 2)
    simp only [map_inv, map_mul] at e ⊢
    exact e
  have e := val_corr hJ hcorr (lift x (lift y u)).left
  have ha : lift x (lift y u) ≫ a = x := by simp [a, x3]
  have hb : lift x (lift y u) ≫ b = y := by simp [b, x3]
  have hd : lift x (lift y u) ≫ d = u := by simp [d, x3]
  rw [vA _ _ z J hJ, vB _ _ z J hJ, ha, hb, hd] at e
  exact e

end GlobalTheory.CubeSymDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.symmetry_cubicalBundle_of_dense_abelian_normal_base : ∀ {S U : Scheme.{0}} [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (j : U ⟶ S) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (F : A.left ⟶ G.left), IsGrpPullback A G j F → GlobalFnsSt → IsAbelianScheme A → ∀ (L : RigLB G) (c : CubicalStr G L) (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), sym.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J = cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J * val sym u.left z J := by
  first | exact @GlobalTheory.SymCubDense.sym_cub_of_dense_abelian | exact GlobalTheory.SymCubDense.sym_cub_of_dense_abelian | (intros; apply GlobalTheory.SymCubDense.sym_cub_of_dense_abelian <;> assumption)
end
