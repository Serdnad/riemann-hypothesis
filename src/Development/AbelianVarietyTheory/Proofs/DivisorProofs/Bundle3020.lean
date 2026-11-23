module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.FactorAdj

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}

theorem c_xp (F : Factor D D') (y : D'.X) : D.c (F.xp y) = D'.c y ≫ F.pr := by
  have h : D.c (F.xp y) ≫ F.inc = D'.c y ≫ F.pr ≫ F.inc := by
    rw [← F.c_xi, F.xi_xp, F.o.c_lin, F.pr_inc]
  have h2 := congrArg (· ≫ F.pr) h
  simp only [Category.assoc, F.inc_pr, Category.comp_id] at h2
  exact h2

theorem c_fxi (F : Factor D D') (y : D.X) : D'.c (F.f • F.xi y) = D.c y ≫ F.inc ≫ F.o.onB.act F.f := by
  rw [F.o.c_lin, F.c_xi, Category.assoc]

end GlobalTheory.MumFam.FactorAdj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lift_after_field_extension : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (E : Emb π G') (Ω : Type) [Field Ω] (ν : Sp Ω ⟶ PSpace R E.N) (s : Sp Ω ⟶ S), ν ≫ PSpace.str R E.N = s ≫ π → (∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) → ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (q : Sp Ω' ⟶ E.H.toScheme), q ≫ E.f = spMap io ≫ ν ∧ q ≫ E.H.ι ≫ G'.hom = spMap io ≫ s := by
  first | exact @GlobalTheory.Mum.Emb.exists_lift_fieldExt | exact GlobalTheory.Mum.Emb.exists_lift_fieldExt | (intros; apply GlobalTheory.Mum.Emb.exists_lift_fieldExt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galois_fixes_quotientPoints_of_rational : ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (D₂ : DegData R₂ (maximalIdeal R₂)) (n : ℕ), (∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p) → ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, ∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p' := by
  first | exact @GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational | exact GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational | (intros; apply GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.pull_generator_factor_pairing_generic_mumfordBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (inc : G ⟶ G'), IsMonHom inc → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → ∃ t : LB.Gen (letI := A'.isAb.comm; (abelian₂ A'.A A'.L).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.f) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 A'.A).left), t.IsGen := by
  first | exact @GlobalTheory.Mum.pull_gen_lam_generic | exact GlobalTheory.Mum.pull_gen_lam_generic | (intros; apply GlobalTheory.Mum.pull_gen_lam_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  first | exact @GlobalTheory.Mum.UpExt.torsion_from_closure | exact GlobalTheory.Mum.UpExt.torsion_from_closure | (intros; apply GlobalTheory.Mum.UpExt.torsion_from_closure <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.idempotentFactor_uniformised_groups_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → IsLocalHom ρ → ∃ (D₁ D₁' : DegData R' (maximalIdeal R')) (F₁ : Factor D₁.toPre D₁'.toPre) (A₁' : PolAV (Sp (FractionRing R'))) (G₁' : Over (Sp R')) (_ : GrpObj G₁') (_ : IsCommMonObj G₁') (U₁' : Unif (maximalIdeal R') D₁' A₁' G₁') (oA₁ : A₁'.OAct F₁.O) (oG₁ : RingAct G₁' F₁.O) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (inc₁ : G₁ ⟶ G₁') (pr₁ : G₁' ⟶ G₁), Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsSemiAbelian G₁' ∧ U₁'.toUnifPre.OLinear F₁.O F₁.o oA₁ oG₁ ∧ IsSemiAbelian G₁ ∧ IsMonHom inc₁ ∧ IsMonHom pr₁ ∧ inc₁ ≫ pr₁ = 𝟙 G₁ ∧ pr₁ ≫ inc₁ = oG₁.act F₁.e ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso ((abelian₂ G₁' U₁'.LG.L).pull (lift (fst G₁ G₁ ≫ inc₁) (snd G₁ G₁ ≫ inc₁ ≫ oG₁.act F₁.f) : G2 G₁ ⟶ G2 G₁').left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  first | exact @GlobalTheory.FactorPull.factor_baseChange | exact GlobalTheory.FactorPull.factor_baseChange | (intros; apply GlobalTheory.FactorPull.factor_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BdStalkExt

theorem exists_extension_test {S X Y : Scheme.{0}} (g : X ⟶ S) [Smooth g] [QuasiCompact g] (e : Y ⟶ X)
    [IsOpenImmersion e] (x : S) [IsRegularLocalRing (S.presheaf.stalk x)] (L : LB Y) (hL : L.IsLB) :
    ∃ N : LB (pullback g (S.fromSpecStalk x)), N.IsLB ∧
      ∀ (T : Scheme.{0}) (a : T ⟶ pullback g (S.fromSpecStalk x)) (b : T ⟶ Y),
        a ≫ pullback.fst g (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b) := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.BdLocalExt.exists_extension_stalk g e x L hL
  refine ⟨N, hN, fun T a b hab => ?_⟩
  let t : T ⟶ pullback (e ≫ g) (S.fromSpecStalk x) :=
    pullback.lift b (a ≫ pullback.snd g (S.fromSpecStalk x)) (by
      rw [← Category.assoc, ← hab, Category.assoc, Category.assoc, pullback.condition])
  have ha : a = t ≫ pullback.map (e ≫ g) (S.fromSpecStalk x) g (S.fromSpecStalk x) e (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · rw [hab, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hb : b = t ≫ pullback.fst (e ≫ g) (S.fromSpecStalk x) := (pullback.lift_fst _ _ _).symm
  exact LBIso.chartPull (chartPullSame N _ _ _ t fun _ => ha) (chartPullSame L _ _ _ t fun _ => hb) h

theorem exists_extension_at_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ x : S, x ∉ Set.range j → ∃ N : LB (pullback G.hom (S.fromSpecStalk x)), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ pullback G.hom (S.fromSpecStalk x)) (b : T ⟶ tF.G.left), a ≫ pullback.fst G.hom (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (tF.PP.L.pull b) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU hpre tF _ G _ _ e hsa he _ x hx
  obtain ⟨-, -, -, -, ⟨-, hproj, -⟩, -⟩ := hU
  haveI := hsa.smooth
  haveI := hsa.quasiCompact
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  obtain ⟨k, _, m, n, C, ξ, a, -, -, rfl, het, -⟩ := hpre x hx
  haveI : IsRegularLocalRing (ChartRing k m n) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
  haveI : IsRegularLocalRing (S.presheaf.stalk (ξ (closedPoint _))) :=
    (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion _ het).1
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback (P := @IsOpenImmersion) he.1.flip inferInstance
  exact exists_extension_test G.hom e _ tF.PP.L tF.PP.isLB

end GlobalTheory.BdStalkExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.closedPoint_notMem_abelianLocus_tautologicalBoundaryChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → 1 ≤ C.m → closedPoint (ChartRing k m e) ∉ abLocus C.t.G := by
  first | exact @GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut | exact GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut | (intros; apply GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (ψ : R →+* W), Function.Injective ψ → IsLocalHom ψ → ∀ (ϖ : W), Irreducible ϖ → ∀ (w : Fin C.m → ℕ), (∀ i, Associated (ψ (C.s i)) (ϖ ^ w i)) → ∀ κ : Sp (FractionRing W) ⟶ Sp (FractionRing R), κ ≫ jK R = jK W ≫ spMap ψ → ∃ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))) (P : PELUnif (maximalIdeal W) t), Nonempty (SABMap tK t (jK W)) ∧ Nonempty (SABMap tK Xo.univ.t ((κ ≫ C.y) ≫ pullback.fst _ _)) ∧ ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] ∧ φ.evalZ be = ∑ i, (w i : ℝ) * φ.evalZ ((l.M' : ℤ) • C.δ i) := by
  first | exact @GlobalTheory.UChart.pull_trait | exact GlobalTheory.UChart.pull_trait | (intros; apply GlobalTheory.UChart.pull_trait <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GenCmp

theorem diagEnd_unique_comm {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (u' : T' ⟶ F.X) (h : T ⟶ T') (hu : h ≫ u' = u)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A))
    (hS : IsDiagEnd F W P u ε) (hS' : IsDiagEnd F W P' u' ε') :
    ∃ α : P.A.left ⟶ P'.A.left, IsGrpPullback P.A P'.A h α ∧ LBIso P.L (P'.L.pull α) ∧
      ∀ E, (ε E).left ≫ α = α ≫ (ε' E).left := by
  subst hu
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hdiag⟩ := hS
  obtain ⟨c', hc', pr', hpr', huniv', hbun', hdiag'⟩ := hS'
  obtain ⟨κ, κ₂, hκ, hsq, hw, -⟩ := GlobalTheory.SiegelPullComp.pb_cancel hc' hc
  have hκw : κ ≫ c'.A.hom = c.A.hom ≫ h := hκ.1.w
  obtain ⟨x₀, hx₀, -⟩ := huniv' (Over.mk (P.A.hom ≫ h)) (fun a => pushPt hκw (pr a))
  let α : P.A.left ⟶ P'.A.left := x₀.left
  have hα : ∀ a, α ≫ (pr' a).left = (pr a).left ≫ κ := fun a => congrArg (fun q => q.left) (hx₀ a)
  have hαw : α ≫ P'.A.hom = P.A.hom ≫ h := Over.w x₀
  have ext' : ∀ {T₁ : Over T'} (v w : T₁ ⟶ P'.A), (∀ a, (v ≫ pr' a).left = (w ≫ pr' a).left) → v = w := by
    intro T₁ v w e
    obtain ⟨_, -, hu⟩ := huniv' T₁ (fun a => w ≫ pr' a)
    exact (hu v fun a => Over.OverMorphism.ext (e a)).trans (hu w fun _ => rfl).symm
  have key : ∀ {Z : Scheme.{0}} (z₁ : Z ⟶ P'.A.left) (z₂ : Z ⟶ T), z₁ ≫ P'.A.hom = z₂ ≫ h →
      ∃! m : Z ⟶ P.A.left, m ≫ α = z₁ ∧ m ≫ P.A.hom = z₂ := by
    intro Z z₁ z₂ e
    have ea : ∀ a, (z₁ ≫ (pr' a).left) ≫ c'.A.hom = z₂ ≫ h := fun a => by
      rw [Category.assoc, Over.w (pr' a), e]
    let ya : Fin 8 → (Over.mk z₂ ⟶ c.A) := fun a =>
      Over.homMk (hκ.1.lift (z₁ ≫ (pr' a).left) z₂ (ea a)) (hκ.1.lift_snd _ _ _)
    have hya : ∀ a, (ya a).left ≫ κ = z₁ ≫ (pr' a).left := fun a => hκ.1.lift_fst _ _ _
    obtain ⟨x, hx, hxu⟩ := huniv (Over.mk z₂) ya
    have hxw : x.left ≫ P.A.hom = z₂ := Over.w x
    refine ⟨x.left, ⟨?_, hxw⟩, fun m ⟨hm₁, hm₂⟩ => ?_⟩
    · have w₁ : (x.left ≫ α) ≫ P'.A.hom = z₂ ≫ h := by rw [Category.assoc, hαw, ← Category.assoc, hxw]
      have := ext' (T₁ := Over.mk (z₂ ≫ h)) (Over.homMk (x.left ≫ α) w₁) (Over.homMk z₁ e) fun a => by
        show (x.left ≫ α) ≫ (pr' a).left = z₁ ≫ (pr' a).left
        rw [Category.assoc, hα, ← Category.assoc, ← hya a, ← hx a]; rfl
      exact congrArg (fun q => q.left) this
    · have := hxu (Over.homMk m hm₂) fun a => Over.OverMorphism.ext (hκ.1.hom_ext (by
        show (m ≫ (pr a).left) ≫ κ = (ya a).left ≫ κ
        rw [Category.assoc, ← hα, ← Category.assoc, hm₁, hya]) (by
        show (m ≫ (pr a).left) ≫ c.A.hom = (ya a).left ≫ c.A.hom
        rw [Category.assoc, Over.w (pr a), hm₂]; exact (Over.w (ya a)).symm))
      exact congrArg (fun q => q.left) this
  have hpb : IsPullback α P.A.hom P'.A.hom h := by
    refine ⟨⟨hαw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (key s.fst s.snd s.condition).exists.choose)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.1)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.2)
      (fun s m h₁ h₂ => (key s.fst s.snd s.condition).unique ⟨h₁, h₂⟩
        (key s.fst s.snd s.condition).exists.choose_spec)⟩⟩
  have hmul : ∀ (T₀ : Over T) (x y : T₀ ⟶ P.A) (x₁ y₁ : Over.mk (T₀.hom ≫ h) ⟶ P'.A),
      x₁.left = x.left ≫ α → y₁.left = y.left ≫ α → (x₁ * y₁).left = (x * y).left ≫ α := by
    intro T₀ x y x₁ y₁ hx hy
    have wz : ((x * y).left ≫ α) ≫ P'.A.hom = (Over.mk (T₀.hom ≫ h)).hom := by
      rw [Category.assoc, hαw, ← Category.assoc, Over.w (x * y)]; rfl
    have := ext' (x₁ * y₁) (Over.homMk ((x * y).left ≫ α) wz) fun a => by
      haveI := hpr a
      haveI := hpr' a
      rw [MonObj.mul_comp]
      have e := hκ.2 T₀ (x ≫ pr a) (y ≫ pr a) (x₁ ≫ pr' a) (y₁ ≫ pr' a)
        (by show x₁.left ≫ (pr' a).left = x.left ≫ (pr a).left ≫ κ; rw [hx, Category.assoc, hα])
        (by show y₁.left ≫ (pr' a).left = y.left ≫ (pr a).left ≫ κ; rw [hy, Category.assoc, hα])
      rw [e, ← MonObj.mul_comp]
      show ((x * y).left ≫ (pr a).left) ≫ κ = ((x * y).left ≫ α) ≫ (pr' a).left
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hα a).symm).trans (Category.assoc _ _ _).symm)
    exact congrArg (fun q => q.left) this
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr ab.1) (pr ab.2)).left ≫ κ₂ = α ≫ (lift (pr' ab.1) (pr' ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (α ≫ P'.A.hom)) (T' := P.A)
      (𝟙 P.A.left) (pr ab.1) (pr ab.2) (Z := P'.A) α (pr' ab.1) (pr' ab.2)
      ((Category.id_comp _).trans (hα ab.1).symm) ((Category.id_comp _).trans (hα ab.2).symm))
  let wt : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
  let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
  let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
  have l0 : (LB.LinComb c'.P q' wt).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' wt
  have l1 : (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB _ wt
  have l2 : (LB.LinComb (c'.P.pull κ₂) q wt).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c'.P.pull κ₂) (pull_isLB c'.isLB κ₂) q wt
  have l3 : (LB.LinComb c.P q wt).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q wt
  have refl1 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) :=
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
  have i2 : LBIso (P'.L.pull α) ((LB.LinComb c'.P q' wt).pull α) := GlobalTheory.SiegelPullComp.iso_pull α hbun'
  have i3 : LBIso ((LB.LinComb c'.P q' wt).pull α) (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) :=
    LBIso.chartPull (chartPullOut c'.P q' wt α _ fun _ => rfl) (chartPullId _) refl1
  have i4 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) (LB.LinComb (c'.P.pull κ₂) q wt) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb c'.P κ₂ q (fun ab => α ≫ q' ab) wt (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
  have i5 : LBIso (LB.LinComb (c'.P.pull κ₂) q wt) (LB.LinComb c.P q wt) :=
    GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q wt
  have h1 := pull_isLB P'.isLB α
  have h2 := pull_isLB l0 α
  have chain : LBIso (P'.L.pull α) (LB.LinComb c.P q wt) :=
    LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5))
  refine ⟨α, ⟨hpb, hmul⟩, LBIso.trans P.isLB l3 h1 hbun chain.symm, fun E => ?_⟩

  have w1 : ((ε E).left ≫ α) ≫ P'.A.hom = P.A.hom ≫ h := by
    rw [Category.assoc, hαw, ← Category.assoc, Over.w (ε E)]
  let v : Over.mk (P.A.hom ≫ h) ⟶ P'.A := Over.homMk ((ε E).left ≫ α) w1
  have hvl : v.left = (ε E).left ≫ α := rfl
  have hpl : ∀ x : P.A ⟶ c.A, (pushPt hκw x).left = x.left ≫ κ := fun _ => rfl
  have e : v = x₀ ≫ ε' E := ext' v (x₀ ≫ ε' E) fun a => by
    have l : v ≫ pr' a = pushPt hκw (ε E ≫ pr a) := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hvl, hpl, Over.comp_left, Category.assoc, hα]
      exact (Category.assoc _ _ _).symm
    rw [l, Category.assoc x₀, hdiag E a, hdiag' E a]
    have r1 : pushPt hκw (((List.finRange 8).map fun b => pr b ^ E a b).prod) =
        pushHom hκ P.A (((List.finRange 8).map fun b => pr b ^ E a b).prod) := rfl
    have r2 : x₀ ≫ ((List.finRange 8).map fun b => pr' b ^ E a b).prod =
        diagPrecomp (M := c'.A) x₀ (((List.finRange 8).map fun b => pr' b ^ E a b).prod) := rfl
    rw [r1, r2, map_list_prod, map_list_prod, List.map_map, List.map_map]
    congr 2
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, map_zpow]
    congr 1
    exact (hx₀ b).symm
  exact congrArg (fun q => q.left) e

end GlobalTheory.Poinc.GenCmp

namespace GlobalTheory.Poinc

theorem exists_common_fibre_diagEnd : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R R' K : Type) [CommRing R] [CommRing R'] [Field K] (f : R →+* K) (f' : R' →+* K) (P : PolAV (Sp R)) (u : Sp R ⟶ F.X) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (P' : PolAV (Sp R')) (u' : Sp R' ⟶ F.X), IsDiagEnd F W P u ε → SharpOver F W P' u' → spMap f ≫ u = spMap f' ≫ u' → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A), IsDiagEnd F W P' u' ε' ∧ ∃ (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left) (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap f) a ∧ IsGrpPullback P₀.A P'.A (spMap f') a' ∧ LBIso P₀.L (P.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') ∧ ∀ E, (ε₀ E).left ≫ a = a ≫ (ε E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left := by
  intro g n F W R R' K _ _ _ f f' P u ε P' u' hD hS' he
  obtain ⟨P₀, a, -, ha, hLa⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f) P
  obtain ⟨ε₀, hD₀, hc₀⟩ := isDiagEnd_pullback F W P P₀ u (spMap f) a ε hD ha hLa
  obtain ⟨ε', hD', -⟩ := exists_diagEnd_isMonHom g n F W _ P' u' hS'
  obtain ⟨a', ha', hLa', hc'⟩ :=
    GenCmp.diagEnd_unique_comm F W P₀ P' (spMap f ≫ u) u' (spMap f') he.symm ε₀ ε' hD₀ hD'
  exact ⟨ε', hD', P₀, a, a', ε₀, ha, ha', hLa, hLa', fun E => ⟨hc₀ E, hc' E⟩⟩

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.tensPsi_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)) (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A') (y : Fin r → D.X), (∀ i, x ≫ pr i = D.c (y i)) → ∃ ψ : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => ptK x) (fun _ => -1)), ψ.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val ψ (𝟙 _) z J' = gm (ptK x) z _ (w.s (fun k => J (ptK x ≫ tensφ pr k), J' (ptK x))) * ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  intro R _ _ D r W A' _ L' hL pr w hw x y hx
  exact GlobalTheory.Mum.TraitWit.exists_psi D W hL pr hw (toUnit (TK R) ≫ x) y (fun i => by rw [Category.assoc, hx])
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.thetaSetup_extends_normal_affineChart_after_rescaling : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (fg : (X₁.M.ringOn U).FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ (X₁.M.ringOn U), ∃ b ∈ (X₁.M.ringOn U), x = a / b) (u' : Sp (X₁.M.ringOn U) ⟶ F.X) (P' : PolAV (Sp (X₁.M.ringOn U))) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A)) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left) (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)) (pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A)) (th : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp (X₁.M.ringOn U))))) (b : Fin (X₁.S.N ^ P'.g) → SecM P'.A P'.L (X₁.S.N : ℕ) (baseOver (Sp (X₁.M.ringOn U)))), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → IsDiagEnd F W P' u' ε' → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → (∀ E, (ε₀ E).left ≫ a = a ≫ (ε₁ E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left) → P'.g = X₁.S.g → HypS P'.A P'.L → (∀ x y, pt' (x + y) = pt' x * pt' y) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) → (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) → (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) → GlobalTheory.ThetaReal.UnivBasis P' 1 (fun _ : Fin 1 => SecM.ofSec P'.A th) → GlobalTheory.ThetaReal.UnivBasis P' (X₁.S.N : ℕ) b → ∃ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (hth : ∀ x, c₀ * X₁.S.th x ∈ (X₁.M.ringOn U)) (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ (X₁.M.ringOn U)) (ρ' : (X₁.S.rechart c₀ hc (X₁.M.ringOn U) fg frac hth hev).Real) (ε'' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X₁.ρ ε₁ ρ' ε'' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ IsDiagEnd F W ρ'.P u' ε'' := by
  first | exact @GlobalTheory.Poinc.exists_real_rechart_of_univBasis | exact GlobalTheory.Poinc.exists_real_rechart_of_univBasis | (intros; apply GlobalTheory.Poinc.exists_real_rechart_of_univBasis <;> assumption)
end
