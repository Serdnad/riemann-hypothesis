module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfMemClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.MatchBundle

open GlobalTheory.CechPic

variable {R : Type} [CommRing R] [IsDomain R]

theorem pull_one (D : DegPre R) (T : Over (Sp R)) : CechPic.pull (1 : T ⟶ D.P.A).left (cls D.P.L D.P.isLB) = 0 := by
  have h : CechPic.pull (eSec D.P.A) (cls D.P.L D.P.isLB) = 0 :=
    (cls_pull D.P.isLB _ (pull_isLB D.P.isLB _)).symm.trans
      ((cls_eq_zero_iff (pull_isLB D.P.isLB _)).2 ⟨D.rig, D.rig_gen⟩)
  have e : (1 : T ⟶ D.P.A).left = (toUnit T).left ≫ eSec D.P.A := rfl
  rw [e, pull_comp, h, map_zero]

theorem cls_eq_lam (D : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O)
    (h : TraceFormTwistIso D oa w0) : cls D.P.L D.P.isLB = lam (cls D.P.L D.P.isLB) (𝟙 _) (oa.onB.act w0) := by
  obtain ⟨u, hu, -⟩ := h
  have h₀ := (cls_eq_zero_iff (LB.isLB_linComb D.P.isLB _ _)).2 ⟨u, hu⟩
  rw [cls_linComb D.P.isLB, Fin.sum_univ_four] at h₀
  have h₁ : (1 : ℤ) • CechPic.pull (𝟙 D.P.A * oa.onB.act w0).left (cls D.P.L D.P.isLB) +
      (-2 : ℤ) • CechPic.pull (𝟙 D.P.A.left) (cls D.P.L D.P.isLB) +
      (-1 : ℤ) • CechPic.pull (oa.onB.act w0).left (cls D.P.L D.P.isLB) +
      (2 : ℤ) • CechPic.pull (1 : D.P.A ⟶ D.P.A).left (cls D.P.L D.P.isLB) = 0 := h₀
  rw [lam, Over.id_left]
  rw [pull_one] at h₁ ⊢
  rw [pull_id] at h₁ ⊢
  linear_combination (norm := abel) -h₁

theorem cls_eq_lam_pull {V : Type} [CommRing V] [IsDomain V] {f : R →+* V} {D : DegPre R} {D' : DegPre V}
    (hD : IsPullDeg f D D') (a : D.P.A ⟶ D.P.A) (a' : D'.P.A ⟶ D'.P.A)
    (ha : a' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf f)).map a)
    (h : cls D.P.L D.P.isLB = lam (cls D.P.L D.P.isLB) (𝟙 _) a) :
    cls D'.P.L D'.P.isLB = lam (cls D'.P.L D'.P.isLB) (𝟙 _) a' := by
  have gp := pull_grp hD
  have e : cls D'.P.L D'.P.isLB =
      CechPic.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf f)) (cls D.P.L D.P.isLB) :=
    ((cls_eq_iff D'.P.isLB (pull_isLB D.P.isLB _)).2 ⟨hD.w, hD.w_gen⟩).trans (cls_pull D.P.isLB _ _)
  have p1 : (pushHom gp _ (𝟙 D'.P.A)).left = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf f) := Category.id_comp _
  have q : pushHom gp _ a' = pushHom gp _ (𝟙 D'.P.A) ≫ a := Over.OverMorphism.ext (by
    rw [Over.comp_left, p1]
    have a₂ : ((Over.pullback (specOf f)).map a).left ≫ pullback.fst D.P.A.hom (specOf f) =
        pullback.fst _ _ ≫ a.left := pullback.lift_fst _ _ _
    show a'.left ≫ hD.e.hom.left ≫ _ = (hD.e.hom.left ≫ _) ≫ _
    rw [← Category.assoc, ← Over.comp_left, ha, Over.comp_left, Category.assoc, a₂, Category.assoc])
  have k := congrArg (CechPic.pull (pushHom gp _ (𝟙 D'.P.A)).left) h
  rw [pull_lam, Category.comp_id, ← q, p1] at k
  rw [e, lam_pull_of_isGrpPullback gp]
  exact k

theorem lbIso_of_match : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → LBIso D₁.toPre.P.L (D₂.toPre.P.L.pull b.left) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ _ C _ V _ _ _ _ _ f₁ f₂ _ _ _ _ D₁ D₂ hD₁ hD₂ _ _ b φ' _ _ hM hact
  letI := H.starRing
  obtain ⟨a₁, a₂, h₁, h₂, hb⟩ := hact H.w0
  have k := cls_eq_lam C.P.D.toPre C.P.oD H.w0 C.P.w0
  have k₁ := cls_eq_lam_pull hD₁ _ a₁ h₁ k
  have k₂ := cls_eq_lam_pull hD₂ _ a₂ h₂ k
  have hL₁ := D₁.toPre.P.isLB
  have hL₂ := D₂.toPre.P.isLB
  have i₁ : (abelian₂ D₁.toPre.P.A D₁.toPre.P.L).IsLB := LB.isLB_linComb hL₁ _ _
  have i₂ : (abelian₂ D₂.toPre.P.A D₂.toPre.P.L).IsLB := LB.isLB_linComb hL₂ _ _
  have m := ((cls_eq_iff i₁ (pull_isLB i₂ _)).2 hM.2.2.1).trans (cls_pull i₂ _ _)
  have c₁ : cls _ i₁ = lam (cls _ hL₁) (fst _ _) (snd _ _) := cls_cube_two hL₁ _ _ _
  have c₂ : cls _ i₂ = lam (cls _ hL₂) (fst _ _) (snd _ _) := cls_cube_two hL₂ _ _ _
  rw [c₁, c₂] at m
  have m' := congrArg (CechPic.pull (lift (𝟙 D₁.toPre.P.A) a₁).left) m
  simp only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.id_comp] at m'
  refine (cls_eq_iff hL₁ (pull_isLB hL₂ _)).1 ?_
  rw [cls_pull hL₂, k₁, m', hb]
  conv_rhs => rw [k₂, pull_lam, Category.comp_id]

end GlobalTheory.UCanon.MatchBundle
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.exists_iso_uniformisedGroups_same_siegelFibre : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing R) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (a : G₁ ≅ G₂) (cA : A₁.A ≅ A₂.A), IsMonHom a.hom ∧ IsMonHom cA.hom ∧ Gen₀ U₁ U₂ a.hom cA.hom ∧ cA.hom.left ≫ α₂ = α₁ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left) := by
  first | exact @GlobalTheory.TInj.exists_iso_of_overPt | exact GlobalTheory.TInj.exists_iso_of_overPt | (intros; apply GlobalTheory.TInj.exists_iso_of_overPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.comesFromBase_of_pullback_injective_domains : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D), Function.Injective f → From T ω s ε n D₀.toPre e β ββ w → ∃ ββ' w', From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' := by
  first | exact @GlobalTheory.TInj.from_pull | exact GlobalTheory.TInj.from_pull | (intros; apply GlobalTheory.TInj.from_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.mumfordBundleIso_generic_origin_one_tautologicalBase : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (z : (TK V).left) (J : ((TK V).left ⟶ T.B.left) → T.M.L.ι) (J' : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι), Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : TK V ⟶ D.P.A) (1 : TK V ⟶ D.P.A)).left z J J' = 1 := by
  first | exact @GlobalTheory.TInj.lamVal_origin_of_from | exact GlobalTheory.TInj.lamVal_origin_of_from | (intros; apply GlobalTheory.TInj.lamVal_origin_of_from <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.torsionPairImage_latticePart_eq_of_match : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (J : Ideal V), AdmBase V J → ∀ (D₁ D₂ : DegData V J) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], Match D₁.toPre D₂.toPre b φ F → ∀ (k : ℕ) (p : QkPt D₁.toPre F k) (p' : QkPt D₂.toPre F k), Act D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom p.g p'.g → p'.y = φ p.y := by
  first | exact @GlobalTheory.TInj.qImg_lattice | exact GlobalTheory.TInj.qImg_lattice | (intros; apply GlobalTheory.TInj.qImg_lattice <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.uniformisation_genericFibre_eq_siegelFibre_pullback : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀) (f : R →+* V) (D : DegData V J') (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif J' D A ((Over.pullback (specOf f)).obj G₀)), IsPullUnif f hD (Iso.refl _) U₀ U → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ κ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ ≫ jK R = jK V ≫ spMap f → ∃ α : A.A.left ⟶ c.A.left, OverPt c A (κ ≫ y₀) α ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ A.A.left) (x₀ : Z ⟶ A₀.A.left), x ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = x₀ ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) → x ≫ α = x₀ ≫ α₀ := by
  first | exact @GlobalTheory.TInj.overPt_genPull | exact GlobalTheory.TInj.overPt_genPull | (intros; apply GlobalTheory.TInj.overPt_genPull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.FactorPeriod



theorem factor_period : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (W : (Sp R).Opens) (ψW : PsiOn D₀ W) (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (a b : Q.X) (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)) (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), u.IsGen → θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good Q.M.L z J → val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) → ∀ z J J', Good D₀.P.L z J → Good Q.M.L z J' → gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val u ((TK V).hom ≫ spMap θ) z J' = lamVal F.w (((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left) z J J' * val (ψW.tau (F.xi a) (F.f • F.xi b)) g z J := by
  intro R V _ _ _ _ θ Q D₀ F W ψW g hg a b u x y k k' hu hy hk hk' hτ z J J' hJ hJ'
  letI := D₀.P.isAb.comm
  obtain ⟨t, ht, tv, tl⟩ := GlobalTheory.T.exists_period_generator_on_open R D₀ W ψW (F.xi a) (F.f • F.xi b)
  have hQ : ∀ T : Over (Sp R), (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left ≫
      (lift (fst Q.B Q.B ≫ F.inc) (snd Q.B Q.B ≫ F.inc ≫ F.o.onB.act F.f) : G2 Q.B ⟶ G2 D₀.P.A).left =
      𝟙 _ ≫ (lift (toUnit T ≫ D₀.c (F.xi a)) (toUnit T ≫ D₀.c (F.f • F.xi b))).left := fun T => by
    rw [Category.id_comp, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, F.o.c_lin, F.c_xi, F.c_xi]
    simp only [Category.assoc]
  obtain ⟨t₁, ht₁, v₁⟩ := GlobalTheory.T.exists_generator_transport_mumfordBundleIso _ _ Q.B D₀.P.A Q.M.L D₀.P.L Q.M.isLB D₀.P.isLB _ F.w F.w_gen (TW W) (TW W)
    (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b) _ _ (𝟙 _) (hQ (TW W)) t ht
  obtain ⟨lam, hlam⟩ : ∃ lam : (TK R).left ⟶ W.toScheme, lam ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact GlobalTheory.TauPull.jK_mem p _ ⟨(g z).1, (g z).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have hl : ∀ T : Over (Sp R), (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left =
      T.hom ≫ (lift (Q.c a) (Q.c b)).left := fun T => by
    rw [← comp_lift]; rfl
  have H := GlobalTheory.T.generator_proportionality_spreads_from_generic R V θ W Q.B.left Q.M.L Q.M.isLB (Fin 4) (Fin 4)
    (lamPts (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)) negε
    (fun i => W.ι ≫ lamPts (Q.c a) (Q.c b) i) negε (fun U _ h => Finset.prod_congr rfl fun i _ => by
      congr 2
      fin_cases i
      · exact congrArg (fun q : TW W ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TW W)) (Q.c a) (Q.c b)).symm
      · rfl
      · rfl
      · exact congrArg (fun q : TW W ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TW W))).symm)
    t₁ (LB.pullGen Q.M.L _ _ u W.ι) ht₁ (DVR.pullGen_isGen _ _ _ _ hu _) lam hlam g hg x y k k' hy hk hk'
    (fun p I' hI' => by
      obtain ⟨I, hI⟩ := DegPull.exists_good' D₀.P.isLB p
      have e₁ := v₁ _ lam p I I' hI hI'
      have e₂ : lam ≫ (lift (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)).left =
          (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left := by
        rw [hl, hl, ← Category.assoc]
        exact congrArg (· ≫ _) hlam
      rw [e₂] at e₁
      erw [Category.comp_id] at e₁
      refine e₁.trans ((congrArg (_ * ·) (tl lam hlam p I hI)).trans ((F.tau a b p I I' hI hI').symm.trans
        ((hτ p I' hI').trans (congrArg (_ * ·) ?_))))
      rw [val_pull hI', hlam]
      rfl) z J' hJ'
  have e₁ := v₁ _ g z J J' hJ hJ'
  have e₂ : g ≫ (lift (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)).left =
      ((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left := by
    rw [hl, ← Category.assoc]
    exact congrArg (· ≫ _) hg
  rw [e₂] at e₁
  erw [Category.comp_id] at e₁
  rw [val_pull hJ', hg] at H
  exact H.symm.trans (e₁.trans (congrArg (_ * ·) (tv _ g z J hJ)))

end GlobalTheory.FactorPeriod
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EFix

theorem exists_equiv_act_of_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (n : ℕ), 1 ≤ n → IsUnit (n : R) → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A), a ^ n = 1 → a ≫ oA.act F.e = a → ∀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing R)) n p a → ∃ p₁ : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, p₁.y = F.e • p.y ∧ GtPtAct F.o F.e p.g p₁.g ∧ QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p₁ p := by
  intro R _ _ _ hR n hn _ Q D' F A' G' _ _ U' oA oG hS hl a _ hae p hp
  have hAdm : AdmBase R (maximalIdeal R) := ⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩
  haveI : CharZero R := hR.2.2.2
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨q, hqy, hqg⟩ := exists_gtPtAct (F := AlgebraicClosure (FractionRing R)) hL.1.globalFns F.o F.e p
  obtain ⟨E, eG, eA, -, -, eact⟩ := endU_of_oLinear hL R (maximalIdeal R) hAdm D' A' G' hS U' F.O F.o oA oG hl F.e
  obtain ⟨E', eG', -, -, eh', -⟩ := endU_of_oLinear hL R (maximalIdeal R) hAdm D' A' G' hS U' F.O F.o oA oG hl (star F.e)
  have hcube := GlobalTheory.Mum.EFixCube.cube_adj_of_oLinear R hAdm D' A' G' U'.toUnifPre hS F.O F.o oA oG hl F.e
  have hfun := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hAdm D' A' G' hS U'
  have h2 := (hfun.2 E E' (by rw [eG, eG']; exact hcube)).2 (AlgebraicClosure (FractionRing R))
  have hq := h2.2.2 n hn p q a (by rw [eh', star_star]; exact hqy)
    ((eact (AlgebraicClosure (FractionRing R)) _ _).2 hqg) hp
  rw [eA, hae] at hq
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hAdm D' A' G' hS U'
    (AlgebraicClosure (FractionRing R)) n hn
  exact ⟨q, hqy, hqg, (hf.2.2.1 q p).1 (((hf.1 q a).1 hq).symm.trans ((hf.1 p a).1 hp))⟩

end GlobalTheory.Mum.EFix
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FactorPull

section PFactorPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [GrpObj C]
  [GrpObj B₁] [GrpObj C₁] [IsCommMonObj C] [IsCommMonObj C₁] {β : B₁.left ⟶ B.left} {δ : C₁.left ⟶ C.left}

theorem lift_sq_of (β₂ : (G2 B₁).left ⟶ (G2 B).left) (hsq : IsSquare β β₂) (gC : IsGrpPullback C₁ C f δ)
    {u v : B ⟶ C} {u₁ v₁ : B₁ ⟶ C₁} (hu : u₁.left ≫ δ = β ≫ u.left) (hv : v₁.left ≫ δ = β ≫ v.left) :
    (lift (fst B₁ B₁ ≫ u₁) (snd B₁ B₁ ≫ v₁) : G2 B₁ ⟶ G2 C₁).left ≫ sqOf gC =
      β₂ ≫ (lift (fst B B ≫ u) (snd B B ≫ v) : G2 B ⟶ G2 C).left := by
  apply pullback.hom_ext
  · show _ ≫ (fst C C).left = _ ≫ (fst C C).left
    rw [Category.assoc, (isSquare_sqOf gC).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hu, ← Category.assoc β₂,
      hsq.1, Category.assoc]
  · show _ ≫ (snd C C).left = _ ≫ (snd C C).left
    rw [Category.assoc, (isSquare_sqOf gC).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hv, ← Category.assoc β₂,
      hsq.2, Category.assoc]

end PFactorPull



theorem pfactor_pull : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
  ∀ (Q : Data R) (D' : DegPre R) (F : PFactor Q D') (D : DegPre R') (ε : D.X ≃+ Q.X), Refines Q ρ D ε →
  ∀ (D₁' : DegPre R') (hD' : IsPullDeg ρ D' D₁') [Module F.O D₁'.X] (o₁ : D₁'.OAct F.O),
    (∀ (a : F.O) (y : D₁'.X), hD'.xe (a • y) = a • hD'.xe y) →
    (∀ a, (o₁.onB.act a).left ≫ proj hD' = proj hD' ≫ (F.o.onB.act a).left) →
    ∃ (inc : D.P.A ⟶ D₁'.P.A) (pr : D₁'.P.A ⟶ D.P.A) (xi : D.X →+ D₁'.X) (xp : D₁'.X →+ D.X)
      (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₁'.P.A D₁'.P.L).pull
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left)),
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧
      (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁'.c (xi y) = D.c y ≫ inc) ∧
      (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁'.X, ∃ y, star F.e • z = star F.e • F.f • xi y) ∧
      w.IsGen ∧ ∀ a b z J J', Good D₁'.P.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' =
          lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' *
            val (D₁'.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  intro R R' _ _ _ _ ρ hρ Q D' F D ε hR D₁' hD' _ o₁ hx ho
  obtain ⟨β, β₂, wR, gB, hsq, hwR, hcR, htR⟩ := hR
  have gC := pull_grp hD'
  obtain ⟨inc, mi, hi⟩ := hom_pull gB gC F.inc F.inc_hom
  obtain ⟨pr, mp, hp⟩ := hom_pull gC gB F.pr F.pr_hom
  obtain ⟨xi, hxi⟩ : ∃ xi : D.X →+ D₁'.X, ∀ y, hD'.xe (xi y) = F.xi (ε y) :=
    ⟨hD'.xe.symm.toAddMonoidHom.comp (F.xi.comp ε.toAddMonoidHom), fun y => hD'.xe.apply_symm_apply _⟩
  obtain ⟨xp, hxp⟩ : ∃ xp : D₁'.X →+ D.X, ∀ y, ε (xp y) = F.xp (hD'.xe y) :=
    ⟨ε.symm.toAddMonoidHom.comp (F.xp.comp hD'.xe.toAddMonoidHom), fun y => ε.apply_symm_apply _⟩
  have hf : (inc ≫ o₁.onB.act F.f).left ≫ proj hD' = β ≫ (F.inc ≫ F.o.onB.act F.f).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ho, ← Category.assoc, hi, Category.assoc]
  have hm := lift_sq_of β₂ hsq gC hi hf
  obtain ⟨w, hw, vw⟩ := GlobalTheory.T.mumfordBundleIso_square_passes_second_iso gC Q.M.isLB D'.P.isLB D.P.isLB D₁'.P.isLB β₂ wR hwR hD'.w hD'.w_gen hm F.w F.w_gen
  have hc : ∀ y, D₁'.c (xi y) = D.c y ≫ inc := fun y => ext_pull gC (by
    rw [hD'.c_pr, hxi, F.c_xi, Over.comp_left, Over.comp_left, Category.assoc, hi, ← Category.assoc (D.c y).left,
      hcR, Category.assoc])
  refine ⟨inc, pr, xi, xp, w, mi, mp, ext_pull gB ?_, ext_pull gC ?_, fun y => ε.injective ?_,
    fun y => hD'.xe.injective ?_, hc, fun y y' h => ?_, fun z => ?_, hw, fun a b z I₁ J₁ hI₁ hJ₁ => ?_⟩
  · rw [Over.comp_left, Category.assoc, hp, ← Category.assoc, hi, Category.assoc, ← Over.comp_left, F.inc_pr,
      Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
  · rw [Over.comp_left, Category.assoc, hi, ← Category.assoc, hp, Category.assoc, ← Over.comp_left, F.pr_inc, ho]
  · rw [hxp, hxi, F.xp_xi]
  · rw [hxi, hxp, F.xi_xp, hx]
  · have h' := congrArg hD'.xe h
    simp only [hx, hxi] at h'
    exact ε.injective (F.inj h')
  · obtain ⟨y, hy⟩ := F.onto (hD'.xe z)
    refine ⟨ε.symm y, hD'.xe.injective ?_⟩
    rw [hx, hx, hx, hxi, ε.apply_symm_apply, hy]
  · obtain ⟨J, hJ⟩ := GlobalTheory.DegPull.exists_good' Q.M.isLB z
    obtain ⟨I, hI⟩ := GlobalTheory.DegPull.exists_good' D'.P.isLB z
    let g₀ := genMap hρ
    have sq : (TK R').hom ≫ spMap ρ = g₀ ≫ (TK R).hom := (Category.id_comp _).symm.trans (fracMap_sq hρ)
    have hκ : g₀ ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hρ).symm.trans (Category.id_comp _)
    have cQ : ∀ y, (toUnit (TK R') ≫ D.c y).left ≫ β = g₀ ≫ (toUnit (TK R) ≫ Q.c (ε y)).left := fun y => by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hcR, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ (Q.c (ε y)).left) sq
    have hP : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ≫ β₂ =
        g₀ ≫ (lift (toUnit (TK R) ≫ Q.c (ε a)) (toUnit (TK R) ≫ Q.c (ε b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst Q.B Q.B).left = _ ≫ (fst Q.B Q.B).left
        rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
          ← Over.comp_left, lift_fst]
        exact cQ a
      · show _ ≫ (snd Q.B Q.B).left = _ ≫ (snd Q.B Q.B).left
        rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
          ← Over.comp_left, lift_snd]
        exact cQ b
    have hQ : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ≫
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left =
        (lift (toUnit (TK R') ≫ D₁'.c (xi a)) (toUnit (TK R') ≫ D₁'.c (F.f • xi b))).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, o₁.c_lin, hc, hc]
      simp only [Category.assoc]
    have R₁ := htR g₀ hκ a b z J J₁ hJ hJ₁
    have t₁ := F.tau (ε a) (ε b) (g₀ z) (fun ψ => I (g₀ ≫ ψ)) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => hI (g₀ ≫ ψ))
      (fun ψ => hJ (g₀ ≫ ψ))
    have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans (map_mul _ _ _)
    have n₁ : val (Q.tau (ε a) (ε b)) (g₀ ≫ 𝟙 _) z J = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (Q.tau (ε a) (ε b)) (𝟙 _) (g₀ z) (fun ψ => J (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z J hJ).2.2.1 _)
    have n₂ : val (D'.tau (F.xi (ε a)) (F.f • F.xi (ε b))) (g₀ ≫ 𝟙 _) z I =
        Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D'.tau (F.xi (ε a)) (F.f • F.xi (ε b))) (𝟙 _) (g₀ z) (fun ψ => I (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z I hI).2.2.1 _)
    rw [Category.comp_id] at n₁ n₂
    have E := n₁.trans (t₂.trans (congrArg₂ (· * ·) (lamVal_comp F.w g₀ _ z I J hI hJ).symm n₂.symm))
    have K := vw _ (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z I J I₁ J₁ hI hJ hI₁ hJ₁
    rw [hP, hQ] at K
    have a₂ := tau_lam hD' hρ (xi a) (F.f • xi b) hI hI₁
    rw [hx, hxi, hxi] at a₂
    rw [R₁, ← a₂, E, ← _root_.mul_assoc, ← _root_.mul_assoc, mul_comm (lamVal w _ z I₁ J₁), K,
      mul_comm (lamVal F.w _ z I J)]

end GlobalTheory.FactorPull

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.polarisedFactor_algebraic_part_pullback : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X) (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B (spMap θ) β → (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) → ∃ (inc : Q'.B ⟶ D₁.P.A) (pr : D₁.P.A ⟶ Q'.B) (xi : Q'.X →+ D₁.X) (xp : D₁.X →+ Q'.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left ∧ (∀ y, hD.xe (xi y) = F.xi (ex y)) ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧ (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) ∧ (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁.X, ∃ y, star F.e • z = star F.e • F.f • xi y) := by
  first | exact @GlobalTheory.PFactorPull.algebraic_pull | exact GlobalTheory.PFactorPull.algebraic_pull | (intros; apply GlobalTheory.PFactorPull.algebraic_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem quasiFinite_of_tautB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p = ξ (closedPoint _) → p = closedPoint _) ∧ ((residue (ChartRing k m e)).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU hS k _ m e C hC ξ hξ
  obtain ⟨⟨_, _, _, _, ⟨_, _, hft⟩, _⟩, ⟨n, s, ε, τ₀, h1, h2, h3, h4, hP⟩⟩ := hC
  have hb : ξ ≫ π ≫ zs = spMap C.b := by
    refine GlobalTheory.ChartQF.eq_spMap_of_injective (algebraMap _ (FractionRing (ChartRing k m e)))
      (IsFractionRing.injective _ _) _ _ ?_
    have e1 : i ≫ zs = pullback.snd _ _ := hU.1.2.2.2.2.1
    have e2 : j ≫ π = i := hU.2.2.2.2.1.2.2.2.2.1
    show jK _ ≫ _ = jK _ ≫ _
    rw [← Category.assoc, ← hξ, Category.assoc, reassoc_of% e2, e1, C.y_over]
  exact GlobalTheory.ChartQF.quasiFinite_of_pointRigid ξ (π ≫ zs) C.b hb hft fun K _ _ ev k₀ hk hemb hq hd =>
    hP K ev k₀ hk hemb (hS _ C (GlobalTheory.ChartQF.base_chartRing C.toFam) ξ hξ n s ε τ₀ h1 h2 h3 h4 K ev k₀ hk hq hd)

end GlobalTheory.UCanon
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_hom_to_dual_of_mumfordClass : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P), A'.dim = A.dim → ∀ c : Pic A.X.left, ∃ φ : A ⟶ A', AbVar.lam c (fst A.X A.X) (snd A.X A.X) = AbDual.evc hP.isLB (fst A.X A.X) (snd A.X A.X ≫ φ.hom) ∧ (IsAmpleCls c → IsIsogeny φ) := by
  first | (exact @GlobalTheory.AV.AbVar.exists_phi) | (exact GlobalTheory.AV.AbVar.exists_phi) | (intros; apply GlobalTheory.AV.AbVar.exists_phi  <;> assumption)
end
