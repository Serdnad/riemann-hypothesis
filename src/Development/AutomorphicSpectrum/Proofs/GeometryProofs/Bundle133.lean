module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle123
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle122
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationCompact
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle115
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestLiftExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyReindexed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.hodge_gram_pullback_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (k : ℕ) (v' : Fin k → (epsAt x' ⟶ t'.G)) (v : Fin k → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x = x' ≫ f → (∀ a, (v' a).left ≫ m.φ = (v a).left) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_of_sabMap | exact GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_of_sabMap | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_of_sabMap <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.KapEquiv

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_kap_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → ∃ ψ : kap Z ≃+* Or.𝔐.Ω₀, spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ ∧ ∀ a : c.F, Or.𝔐.fn (ψ (algebraMap c.F (kap Z) a)) = Or.𝔐.cst a := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or Z hgen
  have hb₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have hb₂ : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    have hf : Module.Flat (𝓞 c.F) c.F := IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F))
    exact RingHom.flat_algebraMap_iff.2 hf
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance
  have hg : IsGenericPoint (Formalism.L2.Pj.genPt Z) (Z : Set (Xo.XF c)) :=
    Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
  have hC : IsCptGen (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z ≫ Y.j) :=
    GlobalTheory.CompanionTheory.Ar.Flat.isCptGen_comp_of_flat_preimmersion Y.j (fun x => (Y.normal x).1) (Formalism.L2.Pj.genPt Z)
      (GlobalTheory.CompanionTheory.Ar.Flat.eq_genericPoint_of_specializes Z.2 hg)
  have e₁ : GlobalTheory.CompanionTheory.Ar.genPt (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z ≫ Y.j) = Y.j (Formalism.L2.Pj.genPt Z) :=
    congrArg Y.j ((Xo.XF c).fromSpecResidueField_apply (Formalism.L2.Pj.genPt Z) _)
  have e₂ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf := RegAtDom.map_genPt Or.g_over
  have e₃ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ₀ := RegAtDom.map_genPt Or.𝔐.fn_over
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.Ar.FlagPull.exists_iso hC Or.𝔐.gen₀ (e₁.trans (hgen.symm.trans (e₂.symm.trans e₃)))
  refine ⟨ψ, hψ, ?_⟩
  have hsY : Y.j ≫ Y.s = Formalism.L2.Pj.strK ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
    (Spec.map_preimage _).symm
  have hfn : Or.𝔐.ξ ≫ Or.𝔐.f = spMap Or.𝔐.fn ≫ Or.𝔐.ξ₀ := Or.𝔐.fn_over
  let i : c.F →+* RM.Ω := (Or.𝔐.fn.comp ψ.toRingHom).comp (algebraMap c.F (Formalism.L2.Pj.kap Z))
  have e0 : i.comp (algebraMap (𝓞 c.F) c.F) = Or.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hS : spMap (i.comp (algebraMap (𝓞 c.F) c.F)) = spMap (Or.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      refine Eq.trans ?_ Or.𝔐.cst_over
      have h3 : Or.𝔐.ξ ≫ Or.𝔐.f ≫ Y.s = spMap Or.𝔐.fn ≫ spMap ψ.toRingHom ≫
          (Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK) ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
        rw [← Category.assoc, hfn, ← hψ]
        simp only [Category.assoc]
        rw [hsY]
      rw [h3, h1]
      simp only [i, spMap_comp_eq, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hS)
  have e4 : i = Or.𝔐.cst := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  intro a
  exact congrArg (fun φ : c.F →+* RM.Ω => φ a) e4

end GlobalTheory.CompanionTheory.Ar.KapEquiv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem exists_fieldMap_of_surjective {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (h : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) (z : X) (hz : ξ (IsLocalRing.closedPoint Ω) = z) :
    ∃ i : Ω →+* X.residueField z, spMap i ≫ ξ = X.fromSpecResidueField z := by
  subst hz
  let g := X.descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ)
  have hsurj : Function.Surjective g.hom := by
    intro a
    obtain ⟨b, hb⟩ := h a
    refine ⟨(X.residue _).hom b, ?_⟩
    have e := congrArg CommRingCat.Hom.hom
      (X.residue_descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ))
    exact (congrArg (fun φ => φ b) e).trans hb
  let e : X.residueField (ξ (IsLocalRing.closedPoint Ω)) ≃+* Ω :=
    RingEquiv.ofBijective g.hom ⟨g.hom.injective, hsurj⟩
  refine ⟨e.symm.toRingHom, ?_⟩
  have h1 : Spec.map g ≫ X.fromSpecResidueField (ξ (IsLocalRing.closedPoint Ω)) = ξ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X ξ
  have h2 : spMap e.symm.toRingHom ≫ Spec.map g = 𝟙 _ := by
    have h3 : g ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
      ext a
      exact e.symm_apply_apply a
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h3).trans (Spec.map_id _))
  refine (congrArg (spMap e.symm.toRingHom ≫ ·) h1).symm.trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.fromSpecResidueField _) h2).trans (Category.id_comp _))

theorem isGeom_of_fnAlgClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))), FracBase β → Formalism.L2.Pj.FnAlgClosed (Xo := Xo) (c := c) → Z'.IsGeom := by
  intro E _ _ _ H D l Xo c O _ β Y Z Z' _ hc x ⟨f, hf0, hf⟩
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo Z'.ξ₀).hom := by
    have h := Z'.gen.bij.2
    rw [Scheme.stalkClosedPointTo_comp] at h
    intro a
    obtain ⟨b, hb⟩ := h a
    exact ⟨_, hb⟩
  have hgp : genPt Z'.ξ₀ = Formalism.L2.Pj.genPt Z := by
    have hg := Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
    have h2 : Formalism.L2.Pj.genPt Z ⤳ genPt Z'.ξ₀ := hg.specializes Z'.genPt_mem
    have h3 : genPt Z'.ξ₀ ⤳ Formalism.L2.Pj.genPt Z := (Z'.closure _).1 hg.mem
    exact (h3.antisymm h2).eq
  obtain ⟨i, hi⟩ := exists_fieldMap_of_surjective Z'.ξ₀ hsurj _ hgp
  have hcomp : i.comp Z'.inc = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (i.comp Z'.inc) = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) := by
      rw [← h1]
      have e : spMap (i.comp Z'.inc) = spMap i ≫ spMap Z'.inc := by
        rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
      rw [e, ← Z'.over_inc, ← Category.assoc, hi]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i x)) := by
    refine ⟨f, hf0, ?_⟩
    have h3 := Polynomial.hom_eval₂ f Z'.inc ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) x
    rw [hf, map_zero] at h3
    rw [Polynomial.aeval_def]
    refine Eq.trans ?_ h3.symm
    have e : algebraMap c.F (Formalism.L2.Pj.Om Z) =
        ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i).comp Z'.inc := by
      rw [RingHom.comp_assoc, hcomp]
      exact IsScalarTower.algebraMap_eq _ _ _
    rw [e]
    rfl
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i x := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.Br
end
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

theorem _root_.GlobalTheory.T.prime_divisors_of_omega_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → AlgOver (Or.Re.comap some) → ∃ T : HodgeTie Y S (Module.finrank ℚ c.F) RM, T.A = Or.𝔐 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin | exact GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin | (intros; apply GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrbitBlock

theorem aeval_smul_of_homog {σ A : Type} [Fintype σ] [CommRing A] [Algebra ℤ A] {n : ℕ}
    {F : MvPolynomial σ ℤ} (hF : F.IsHomogeneous n) (t : A) (b : σ → A) :
    MvPolynomial.aeval (fun i => t * b i) F = t ^ n * MvPolynomial.aeval b F := by
  classical
  simp only [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hd)
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem mConeMap_rename_block {n : ℕ} (y : (Σ k, J k) → Ω) (k₀ : K)
    {F : MvPolynomial (J k₀) ℤ} (hF : F.IsHomogeneous n) :
    mConeMap y (MvPolynomial.rename (Sigma.mk k₀) F) =
      MvPolynomial.X k₀ ^ n *
        MvPolynomial.C (MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) F) := by
  have h1 : mConeMap y (MvPolynomial.rename (Sigma.mk k₀) F) =
      MvPolynomial.aeval (fun i : J k₀ => (MvPolynomial.X k₀ : MvPolynomial K Ω) *
        MvPolynomial.C (y ⟨k₀, i⟩)) F := by
    rw [mConeMap, MvPolynomial.aeval_rename]
    congr 2
    funext i
    simp [mul_comm]
  rw [h1, aeval_smul_of_homog hF]
  congr 1
  exact (MvPolynomial.comp_aeval_apply (fun i : J k₀ => y ⟨k₀, i⟩)
    (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω)) F).symm

theorem relation_at {n : ℕ} (y : (Σ k, J k) → Ω) (k₀ k : K) (c j : J k)
    {Fj Fc : MvPolynomial (J k₀) ℤ} (hj : Fj.IsHomogeneous n) (hc : Fc.IsHomogeneous n)
    (h : MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) Fj * y ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) Fc * y ⟨k, j⟩)
    {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) :
    MvPolynomial.aeval (fun i : J k₀ => w ⟨k₀, i⟩) Fj * w ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => w ⟨k₀, i⟩) Fc * w ⟨k, j⟩ := by
  set G : MRing J := MvPolynomial.rename (Sigma.mk k₀) Fj * MvPolynomial.X ⟨k, c⟩ -
    MvPolynomial.rename (Sigma.mk k₀) Fc * MvPolynomial.X ⟨k, j⟩ with hG
  have hmem : G ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, hG, map_sub, map_mul, map_mul,
      mConeMap_rename_block y k₀ hj, mConeMap_rename_block y k₀ hc]
    have hx : ∀ p : Σ k, J k, mConeMap y (MvPolynomial.X p) =
        MvPolynomial.C (y p) * MvPolynomial.X p.1 := fun p => by
      simp [mConeMap]
    rw [hx, hx]
    have h' := congrArg (MvPolynomial.C : Ω →+* MvPolynomial K Ω) h
    simp only [map_mul] at h'
    linear_combination (MvPolynomial.X k₀ ^ n * MvPolynomial.X k) * h'
  have hv := hw.2 G hmem
  have hv' : MvPolynomial.aeval w G = 0 := by
    rw [← hv, MvPolynomial.eval_map]
    rfl
  rw [hG, map_sub, map_mul, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename,
    MvPolynomial.aeval_X, MvPolynomial.aeval_X] at hv'
  exact sub_eq_zero.1 hv'

theorem sameOrbit_of_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ w ∈ mcPts (mCoordIdeal y), ∀ w' ∈ mcPts (mCoordIdeal y), ∀ u : ℂ, (∀ i : J k₀, w ⟨k₀, i⟩ = u * w' ⟨k₀, i⟩) → SameOrbit w w' := by
  intro X Ω _ _ ξ K _ J _ y k₀ hT hE w hw w' hw' u hu
  have hpts : w ∈ Small.ptsOver ℂ (mCoordIdeal y) := by
    refine ⟨hw.1, fun f hf => ?_⟩
    rw [← hw.2 f hf, MvPolynomial.eval_map]
    rfl
  obtain ⟨i, hi⟩ := hw.1 k₀
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hi (by rw [hu i, zero_mul])
  have key : ∀ k, ∃ s : ℂ, s ≠ 0 ∧ ∀ j, w ⟨k, j⟩ = s * w' ⟨k, j⟩ := by
    intro k
    obtain ⟨c, hc⟩ := hw.1 k
    obtain ⟨n, F, hF, hrel, hne⟩ :=
      GlobalTheory.T.small_points_coord_ratio_bound X Ω ξ K J y k₀ hT hE ℂ w hpts i k c hi hc
    have hscale : ∀ t, MvPolynomial.aeval (fun i' : J k₀ => w ⟨k₀, i'⟩) (F t) =
        u ^ n * MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F t) := by
      intro t
      rw [← aeval_smul_of_homog (hF t)]
      congr 2
      funext i'
      exact hu i'
    have hne' : MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F c) ≠ 0 := by
      intro h0
      exact hne (by rw [hscale, h0, mul_zero])
    have r := fun j => relation_at y k₀ k c j (hF j) (hF c) (hrel j) hw
    have r' := fun j => relation_at y k₀ k c j (hF j) (hF c) (hrel j) hw'
    have hc' : w' ⟨k, c⟩ ≠ 0 := by
      intro h0
      obtain ⟨j, hj⟩ := hw'.1 k
      have := r' j
      rw [h0, mul_zero] at this
      exact (mul_ne_zero hne' hj) this.symm
    refine ⟨w ⟨k, c⟩ / w' ⟨k, c⟩, div_ne_zero hc hc', fun j => ?_⟩
    have e1 := r j
    have e2 := r' j
    rw [hscale, hscale] at e1
    have hun : u ^ n ≠ 0 := pow_ne_zero n hu0
    have e3 : MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F j) * w ⟨k, c⟩ =
        MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F c) * w ⟨k, j⟩ :=
      mul_left_cancel₀ hun (by linear_combination e1)
    apply mul_left_cancel₀ hne'
    have e4 : w ⟨k, c⟩ / w' ⟨k, c⟩ * w' ⟨k, c⟩ = w ⟨k, c⟩ := div_mul_cancel₀ _ hc'
    linear_combination (-1 : ℂ) * e3 + (w ⟨k, c⟩ / w' ⟨k, c⟩) * e2 -
      MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F j) * e4
  choose s hs0 hs using key
  exact ⟨s, hs0, funext fun p => by
    obtain ⟨k, j⟩ := p
    exact hs k j⟩

end GlobalTheory.CompanionTheory.Ar.OrbitBlock
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open CategoryTheory.Limits

theorem genFibre_pullback_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (y : FrPt Xo c F) (t' : SAB H (Spec (CommRingCat.of F))) (m1 : SABMap t' Xo.univ.t y.x) (g : Spec (CommRingCat.of F) ⟶ X), Small.ptY Y y = g ≫ f → ∃ b : t'.G.left ⟶ tX.G.left, IsGrpPullback t'.G tX.G g b ∧ (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (u' : Spec (CommRingCat.of (DualNumber F)) ⟶ t'.G.left), u' ≫ m1.φ = y.u τ i → u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) → u' ≫ b ≫ m.φ = Small.tanY Y y τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ y t' m1 g hg
  have wa : m1.φ ≫ Xo.univ.t.G.hom = (t'.G.hom ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [m1.cart.1.w, Category.assoc, Small.ptF_fst]
  let a : t'.G.left ⟶ Y.oF.t.G.left := Y.m0.cart.1.lift m1.φ (t'.G.hom ≫ Small.ptF y) wa
  have ha1 : a ≫ Y.m0.toSABMap.φ = m1.φ := IsPullback.lift_fst _ _ _ _
  have ha2 : a ≫ Y.oF.t.G.hom = t'.G.hom ≫ Small.ptF y := IsPullback.lift_snd _ _ _ _
  have gpa : IsGrpPullback t'.G Y.oF.t.G (Small.ptF y) a :=
    IsGrpPullback.cancel Y.m0.cart (m1.cart.congr (Small.ptF_fst y).symm ha1.symm) ha2
  have gpY : IsGrpPullback t'.G Y.t.G (g ≫ f) (a ≫ Y.m.φ) := (gpa.comp Y.m.cart).congr hg rfl
  have wb : (a ≫ Y.m.φ) ≫ Y.t.G.hom = (t'.G.hom ≫ g) ≫ f := by
    rw [gpY.1.w, Category.assoc]
  let b : t'.G.left ⟶ tX.G.left := m.cart.1.lift (a ≫ Y.m.φ) (t'.G.hom ≫ g) wb
  have hb1 : b ≫ m.φ = a ≫ Y.m.φ := IsPullback.lift_fst _ _ _ _
  have hb2 : b ≫ tX.G.hom = t'.G.hom ≫ g := IsPullback.lift_snd _ _ _ _
  have acta : ∀ r, (t'.act.act r).left ≫ a = a ≫ (Y.oF.t.act.act r).left := by
    intro r
    apply Y.m0.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha1, Y.m0.act r, ← Category.assoc, ha1, m1.act r]
    · rw [Category.assoc, Category.assoc, ha2, Over.w (Y.oF.t.act.act r), ha2, ← Category.assoc,
        Over.w (t'.act.act r)]
  refine ⟨b, IsGrpPullback.cancel m.cart (gpY.congr rfl hb1.symm) hb2, fun r => ?_, fun τ i u' h1 h2 => ?_⟩
  · apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hb1, m.act r, ← Category.assoc b, hb1, Category.assoc, ← Y.m.act r,
        ← Category.assoc, acta r, Category.assoc]
    · rw [Category.assoc, Category.assoc, hb2, Over.w (tX.act.act r), hb2, ← Category.assoc,
        Over.w (t'.act.act r)]
  · have e : u' ≫ a = Small.tanF Y y τ i := by
      apply Small.eq_tanF
      · rw [Category.assoc, ha1, h1]
      · rw [Category.assoc, ha2, ← Category.assoc, h2]
    rw [hb1, ← Category.assoc, e]
    rfl

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

open AlgebraicGeometry CategoryTheory

abbrev gen {X : Scheme.{0}} (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) : Spec (CommRingCat.of T.Fr) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ zV

def ReadsPt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (A : Subring Ω) (T : CDVR)
    (evT : A →+* T.Fr) (zV : Spec (CommRingCat.of T.V) ⟶ X) : Prop :=
  ∀ a : A, ValAt ξ (gen T zV) (a : Ω) (evT a)

def TriIn {F EC : Type} [Field F] [AddCommGroup EC] [Module F EC] {r : ℕ} (u : Fin r → EC) (d : Fin r → F)
    (v : Fin r → EC) : Prop :=
  ∀ i, ∃ cf : Fin r → F, cf i = d i ∧ (∀ j, i < j → cf j = 0) ∧ v i = ∑ j, cf j • u j

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

def IsFrameVec (Or : RootOrigin Y SS RM Fx) {T : CDVR} (io : c.F →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr)
    {zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X} {EC : Type} [AddCommGroup EC] [Module T.Fr EC]
    (MC : LieModel Or.𝔐.t.G (gen T zV) EC) (w : EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)) : Prop :=
  letI := io.toAlgebra
  (MC.pt w).left ≫ Or.𝔐.m.φ = Small.tanY Y zT (Small.labelC s) (Small.labelFin Dw s i)

def lieEig (Or : RootOrigin Y SS RM Fx) {T : CDVR} {zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X} {EC : Type}
    [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] (MC : LieModel Or.𝔐.t.G (gen T zV) EC)
    [IsScalarTower T.V T.Fr EC] (ρC : 𝓞 E →+* Module.End T.Fr EC) (σ : 𝓞 E →+* T.V) : Submodule T.V EC :=
  Or.𝔐.M.fibAt Or.𝔐.M.lat zV MC ⊓ (eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem compact_of_finite_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (Z' : Scheme.{0}) (f : Z' ⟶ XQ X), IsFinite f →
    @CompactSpace (Sp ℂ ⟶ Z') (anTop Z') :=
  @PositivityTheory.Xgn.torus_uniformization_compact

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.htLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ τ, ∃ hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C)), Function.Injective hb ∧ LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) ∧ (stdLat RC _).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).omHT τ ∧ (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ ∧ (∀ b' c'', (b', c'') ∈ ((chartD e b pq sc w P i).bc RC).Del τ ↔ (algebraMap O C w) • b' ∈ stdLat RC _ ∧ c'' - (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) b' ∈ ((chartD e b pq sc w P i).bc RC).omHT τ) ∧ (∀ a b', (a, b') ∈ ((chartD e b pq sc w P i).bc RC).Gam τ ↔ (algebraMap O C w) • a ∈ ((chartD e b pq sc w P i).bc RC).W τ ∧ b' - hb a ∈ stdLat RC _) ∧ ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _) :=
  @PositivityTheory.Xgn.test_lift_exists
end

section

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

theorem _root_.GlobalTheory.T.arith_variety_reindexed : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ (Gf : GenFibre (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (mCoordIdeal y)) (ch : ∀ k : FibreBlock bk, J k.1), (∀ k : FibreBlock bk, Gf.x' ⟨k.1, ch k⟩ ≠ 0) ∧ Module.finrank Gf.Φ (IntermediateField.adjoin Gf.Φ (Set.range fun q : Σ k : FibreBlock bk, J k.1 => Gf.x' ⟨q.1.1, q.2⟩ / Gf.x' ⟨q.1.1, ch q.1⟩)) = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree | exact GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree <;> assumption)
end
