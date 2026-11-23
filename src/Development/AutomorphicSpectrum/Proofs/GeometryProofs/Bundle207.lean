module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PicardClassTrivialBySeesaw
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompat
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle205
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle195
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapComp
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle203
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle177
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle204
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.complex_section_finite_combination : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ), LocallyOfFiniteType p → ∀ (B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y), B.IsLB → ∀ (O : Y.Opens) (x : GlobalTheory.SecC p σ B), (∀ i y, y ∉ GlobalTheory.CxPts.ptsIn p σ O → GlobalTheory.SecC.val x i y = 0) → ∃ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → B.Sec), (∀ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (ss j) ≤ O) ∧ GlobalTheory.SecC.val x = ∑ j, as j • GlobalTheory.CxPts.secVal p σ (ss j) := by
  first | exact @GlobalTheory.CompanionTheory.VanDescent.vanish_descent | exact GlobalTheory.CompanionTheory.VanDescent.vanish_descent | (intros; apply GlobalTheory.CompanionTheory.VanDescent.vanish_descent <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def tanW (Y : Model Xo c β) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (w : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left)
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x) :
    Spec (CommRingCat.of (DualNumber S)) ⟶ Y.t.G.left :=
  Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ GlobalTheory.AllWt.ptF y) (by
    rw [hw, Category.assoc, GlobalTheory.AllWt.ptF, Limits.pullback.lift_fst]) ≫ Y.m.φ

theorem isComb_cast {V : Type} [CommRing V] {G : CategoryTheory.Over (Spec (CommRingCat.of V))} [GrpObj G] {r m : ℕ} (h : r = m)
    (v : Fin m → (epsOver V V ⟶ G)) (cf : Fin m → V) (w : epsOver V V ⟶ G) (hc : IsComb v cf w) :
    IsComb (fun i => v (Fin.cast h i)) (fun i => cf (Fin.cast h i)) w := by
  subst h
  exact hc

theorem spec_frac_ext (T : CDVR) {B : Type} [CommRing B]
    {p q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of T.Fr)}
    (h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) : p = q := by
  rw [← Spec.map_preimage p, ← Spec.map_preimage q] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  congr 1
  ext1
  refine IsLocalization.ringHom_ext (nonZeroDivisors T.V) ?_
  exact congrArg CommRingCat.Hom.hom h2

theorem base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (T : CDVR)
    (G : SAB H (Spec (CommRingCat.of T.V))) (t' : SAB H (Spec (CommRingCat.of T.Fr)))
    (m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))) (v : epsOver T.V T.V ⟶ G.G)
    (u' : Spec (CommRingCat.of (DualNumber T.Fr)) ⟶ t'.G.left)
    (h : u' ≫ m2.φ = Spec.map (CommRingCat.ofHom (dualMap (algebraMap T.V T.Fr))) ≫ v.left) :
    u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) := by
  apply spec_frac_ext T
  have e1 := m2.cart.1.w
  rw [Category.assoc, ← e1, ← Category.assoc, h, Category.assoc, Over.w v]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.picard_class_trivial_by_seesaw : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (T : TorusExtension G) (Y : Over (Sp k)), Smooth Y.hom → GeometricallyConnected Y.hom → ∀ (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (c : Pic (T.B ⊗ Y).left), pull (lift (fst G Y ≫ T.q) (snd G Y)).left c = 0 → pull (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left c = 0 → c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TorusPic.pic_inj | exact GlobalTheory.CompanionTheory.TorusPic.pic_inj | (intros; apply GlobalTheory.CompanionTheory.TorusPic.pic_inj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.omega_lattice_dominant_compat : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → Smooth G.hom → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → ∀ (jd : Module.Dual Ω V →+ Module.Dual Ω' V'), (∀ w e, jd w (j e) = i (w e)) → ∀ (N : ℕ), 0 < N → ∀ (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), IsIntegrallyClosed (X.presheaf.stalk (f p'.1)) → IsNoetherianRing (X.presheaf.stalk (f p'.1)) → (∃ ζ : Ω, IsPrimitiveRoot ζ N) → M.IsHTFormAt N ⟨f p'.1, h⟩ 0 → M'.htLat N p' = (M.htLat N).pull ξ' f jd p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HTPull.main | exact GlobalTheory.CompanionTheory.Ar.HTPull.main | (intros; apply GlobalTheory.CompanionTheory.Ar.HTPull.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameDual

theorem exists_frame_dual_sq : ∀ (S X : Scheme.{0}) (G : Over S) [GrpObj G] (Gx : Over X) [GrpObj Gx] [IsCommMonObj Gx] [Smooth Gx.hom] (φ : Gx.left ⟶ G.left) (Ω₁ : Type) [Field Ω₁] (ξ : Spec (CommRingCat.of Ω₁) ⟶ X), IsCptGen ξ → ∀ (Li : Type) [AddCommGroup Li] [Module Ω₁ Li] (M : LieModel Gx ξ Li) (F : Type) [Field F] (θ : Ω₁ →+* F) (A : Subring F) [IsLocalRing A] (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), (∀ s : X.presheaf.stalk (centre z), (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) → ∀ (ER : Type) [AddCommGroup ER] [Module A ER] (MR : LieModel Gx z ER) (xF : Spec (CommRingCat.of F) ⟶ S) (V : Type) [AddCommGroup V] [Module F V] (MV : LieModel G xF V) (io : ER → V) (Lm : Li → V), (∀ x, (MV.pt (io x)).left = Spec.map (CommRingCat.ofHom (dualMap A.subtype)) ≫ (MR.pt x).left ≫ φ) → (∀ e, (MV.pt (Lm e)).left = Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (M.pt e).left ≫ φ) → ∀ (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω₁ Li) (m : ℕ), (∀ i, (m : Ω₁) • b i ∈ M.lat ⟨centre z, h⟩) → (∀ i j, π i (b j) = if i = j then 1 else 0) → (∀ i, ∀ e ∈ M.lat ⟨centre z, h⟩, (m : Ω₁) * π i e ∈ regAt ξ ⟨centre z, h⟩) → ∃ (β : Fin r → ER) (g : Fin r → ER →ₗ[A] A), (∀ k, io (β k) = Lm ((m : Ω₁) • b k)) ∧ ∀ i k, ((g i (β k) : A) : F) = if k = i then (m : F) ^ 2 else 0 := by
  intro S X G _ Gx _ _ _ φ Ω₁ _ ξ hξ Li _ _ M F _ θ A _ z h hs ER _ _ MR xF V _ _ MV io Lm hio hLm r b π m hm hπ hreg
  obtain ⟨ev, hev, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X Gx Ω₁ ξ Li M A z h ER MR hξ inferInstance
  let β : Fin r → ER := fun k => ev ⟨(m : Ω₁) • b k, hm k⟩
  have hval : ∀ k, M.ValAt z ((m : Ω₁) • b k) (MR.pt (β k)) := fun k => (hev _ _).2 ⟨hm k, rfl⟩
  have hcomp : A.subtype.comp (Scheme.stalkClosedPointTo z).hom = θ.comp (genMap ξ ⟨centre z, h⟩) :=
    RingHom.ext fun s => hs s
  have hg : ∀ i, ∃ g : ER →ₗ[A] A, ∀ (e : Li) (x : ER) (u : A), M.ValAt z e (MR.pt x) →
      ValAt ξ z (((m : Ω₁) • π i) e) u → g x = u := fun i =>
    GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional X Gx Ω₁ ξ Li M A z h ER MR ((m : Ω₁) • π i) hξ
      (fun e he => by simpa [smul_eq_mul] using hreg i e he)
  choose g hg using hg
  refine ⟨β, g, fun k => ?_, fun i k => ?_⟩
  · obtain ⟨h', v, hext, hw⟩ := hval k
    have e1 := GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.spec_dual_comp (Scheme.stalkClosedPointTo z).hom A.subtype
    have e2 := GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.spec_dual_comp (genMap ξ ⟨centre z, h⟩) θ
    apply MV.inj
    apply Over.OverMorphism.ext
    rw [hio, hLm, hext.2, hw]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map (CommRingCat.ofHom (dualMap A.subtype))),
      ← Category.assoc (Spec.map (CommRingCat.ofHom (dualMap θ))), e1, e2, hcomp]
  · have hnat : ∀ n : ℕ, ValAt ξ z (n : Ω₁) (n : A) := fun n =>
      ⟨h, (n : X.presheaf.stalk (centre z)), map_natCast _ n, map_natCast _ n⟩
    have hv : ((m : Ω₁) • π i) ((m : Ω₁) • b k) = ((if k = i then m ^ 2 else 0 : ℕ) : Ω₁) := by
      by_cases e : k = i
      · subst e
        simp [hπ, smul_eq_mul, pow_two]
      · have e' : ¬ i = k := fun q => e q.symm
        simp [hπ, e, e']
    have h1 := hg i _ (β k) _ (hval k) (hv ▸ hnat _)
    rw [h1]
    by_cases e : k = i <;> simp [e]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameDual
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.lattice_tangent_vectors_affine_open : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (q : Cpt ξ) (N : ℕ) (b : Fin N → Li), IsCptGen ξ → (∀ k, b k ∈ M.lat q) → ∃ (W : X.Opens) (hW : IsAffineOpen W) (v : Fin N → (epsAt (R := Γ(X, W)) hW.fromSpec ⟶ G)), q.1 ∈ W ∧ (∀ k, IsTanAt G hW.fromSpec (v k)) ∧ ∀ (ψ : Γ(X, W) →+* ℂ) (z : Sp ℂ ⟶ X), spMap ψ ≫ hW.fromSpec = z → genPt ξ ⤳ centre z → ∀ k, ∃ w : epsAt z ⟶ G, M.ValAt z (b k) w ∧ w.left = spMap (dualMap ψ) ≫ (v k).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.exists_affine_frame | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.exists_affine_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.exists_affine_frame <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem finrank_lieModel_of_algebra (X : Scheme.{0}) (G : Over X) [GrpObj G] [Smooth G.hom] (A : Type) [CommRing A]
    [IsLocalRing A] (x : Sp A ⟶ X) (E₀ : Type) [AddCommGroup E₀] [Module A E₀] (M₀ : LieModel G x E₀) (K : Type)
    [Field K] [Algebra A K] (V : Type) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (MV : LieModel G (spMap (algebraMap A K) ≫ x) V) : Module.finrank K V = Module.finrank A E₀ := by
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x = spMap (algebraMap A K) ≫ x := rfl
  have hsm : ∀ (a : A) (t : V), a • t = algebraMap A K a • t := fun a t => by
    rw [algebraMap_smul]
  have halg : (dualMap (algebraMap A K)).comp (algebraMap A (DualNumber A)) =
      (algebraMap K (DualNumber K)).comp (algebraMap A K) := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let b : epsAt (spMap (algebraMap A K) ≫ x) ⟶ epsAt x :=
    Over.homMk (spMap (dualMap (algebraMap A K))) (by
      change spMap (dualMap (algebraMap A K)) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap (algebraMap A K) ≫ x
      simp only [spMap]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, halg])
  have htan (e : E₀) : IsTanAt G (spMap (algebraMap A K) ≫ x) (b ≫ M₀.pt e) := by
    have h1 : (Over.homMk (spMap (algebraMap A K)) rfl : Over.mk (spMap (algebraMap A K) ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) = 1 := MonObj.comp_one _
    have h2 : spMap (algebraMap A K) ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (spMap (algebraMap A K) ≫ x) ⟶ G).left := by rw [← h1]; rfl
    have hv := M₀.tan e
    unfold IsTanAt at hv ⊢
    rw [← h2, ← hv]
    change Spec.map _ ≫ spMap (dualMap (algebraMap A K)) ≫ (M₀.pt e).left = spMap (algebraMap A K) ≫ Spec.map _ ≫ (M₀.pt e).left
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    congr 1
    exact RingHom.ext fun a => by simp [dualMap]
  have ex : ∀ e, ∃ t, MV.pt t = b ≫ M₀.pt e :=
    fun e => MV.onto _ (htan e)
  choose f hf using ex
  let j : E₀ →ₗ[A] V :=
    { toFun := f
      map_add' := fun a b => MV.inj (by rw [MV.add, hf, hf, hf, M₀.add, comp_mul])
      map_smul' := fun c e => MV.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc]
        have hb : b ≫ LieTangent.epsScale x c =
            LieTangent.epsScale (spMap (algebraMap A K) ≫ x) (algebraMap A K c) ≫ b := by
          apply Over.OverMorphism.ext
          change spMap (dualMap (algebraMap A K)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) =
            Spec.map (CommRingCat.ofHom (epsMul (algebraMap A K c))) ≫ spMap (dualMap (algebraMap A K))
          simp only [spMap]
          rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
          congr 1
          congr 1
          refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_smul]
        rw [hb, Category.assoc]) }

  have hl : ∀ e, ((MV.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A K)) ≫ (M₀.pt e).left) := fun e => by
    change (MV.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf, Category.comp_id]
    rfl
  have hbc : IsBaseChange K j := GlobalTheory.T.lie_model_isBaseChange X G A K x E₀ V M₀ MV j hl
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.lie_model_finite_projective X G A x E₀ M₀
  haveI : Module.Free A E₀ := Module.free_of_flat_of_isLocalRing
  rw [← LinearEquiv.finrank_eq hbc.equiv, Module.finrank_baseChange]

theorem finrank_lieModel_eq (X : Scheme.{0}) (G : Over X) [GrpObj G] [Smooth G.hom] (A : Type) [CommRing A]
    [IsLocalRing A] (x : Sp A ⟶ X) (E₀ : Type) [AddCommGroup E₀] [Module A E₀] (M₀ : LieModel G x E₀) (K : Type)
    [Field K] (c : A →+* K) (y : Sp K ⟶ X) (hy : Spec.map (CommRingCat.ofHom c) ≫ x = y) (V : Type) [AddCommGroup V]
    [Module K V] (MV : LieModel G y V) : Module.finrank K V = Module.finrank A E₀ := by
  subst hy
  letI : Algebra A K := c.toAlgebra
  letI mR : Module A V := Module.compHom V c
  haveI tower : IsScalarTower A K V := ⟨fun a b t => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  exact finrank_lieModel_of_algebra X G A x E₀ M₀ K V MV

theorem lieModel_transport {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X} {Li : Type}
    [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) {L : Type} [Field L] {z z' : Sp L ⟶ X} (hz : z' = z)
    {T : Type} [AddCommGroup T] [Module L T] (TL : LieModel G z T) :
    ∃ MC : LieModel G z' T,
      (∀ t, (MC.pt t).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap L L))) ≫ (TL.pt t).left) ∧
      ∀ e t, M.ValAt z' e (MC.pt t) → M.ValAt z e (TL.pt t) := by
  subst hz
  have hd : dualMap (algebraMap L L) = RingHom.id _ := RingHom.ext fun a =>
    by ext <;> simp [dualMap]
  exact ⟨TL, fun t => by rw [hd, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp], fun _ _ h => h⟩

theorem lieModel_valFrame : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] (zL : Sp L ⟶ X) (T : Type) [AddCommGroup T] [Module L T] (TL : LieModel G zL T) (h : genPt ξ ⤳ centre zL) (Ix : Type) [Fintype Ix] (f : Ix → Li), IsCptGen ξ → LinearIndependent Ω f → Submodule.span Ω (Set.range f) = ⊤ → M.lat ⟨centre zL, h⟩ = Submodule.span (regAt ξ ⟨centre zL, h⟩) (Set.range f) → ∃ w : Ix → T, (∀ i, M.ValAt zL (f i) (TL.pt (w i))) ∧ LinearIndependent L w ∧ Submodule.span L (Set.range w) = ⊤ ∧ ∀ (A : Set Ix) (e : Li) (u : T), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) → M.ValAt zL e (TL.pt u) → u ∈ Submodule.span L (w '' A) := by
  intro X G _ _ _ Ω _ ξ Li _ _ M L _ zL T _ _ TL h Ix _ f hξ hli hsp hlat
  have ex : ∀ i, ∃ w, M.ValAt zL (f i) (TL.pt w) := fun i => by
    have hm : f i ∈ M.lat ⟨centre zL, h⟩ := by
      rw [hlat]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := (M.exists_valAt_iff zL (f i)).2 ⟨h, hm⟩
    obtain ⟨t, rfl⟩ := TL.onto v hv.isTanAt
    exact ⟨t, hv⟩
  choose w hw using ex
  have key : ∀ (A : Set Ix) (e : Li), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) →
      ∃ u ∈ Submodule.span L (w '' A), M.ValAt zL e (TL.pt u) := by
    intro A e he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨i, hi, rfl⟩ := he
      exact ⟨w i, Submodule.subset_span ⟨i, hi, rfl⟩, hw i⟩
    | zero => exact ⟨0, zero_mem _, by rw [TL.pt_zero]; exact M.valAt_zero h⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, hv⟩ := ha
      obtain ⟨u', hu', hv'⟩ := hb
      exact ⟨u + u', add_mem hu hu', by rw [TL.add]; exact hv.add hv'⟩
    | smul c a _ ha =>
      obtain ⟨u, hu, hv⟩ := ha
      obtain ⟨_, s, rfl⟩ := c
      refine ⟨(Scheme.stalkClosedPointTo zL).hom s • u, Submodule.smul_mem _ _ hu, ?_⟩
      rw [TL.pt_smul]
      exact hv.smul h s
  have hz : Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ zL = zL := by
    have e : CommRingCat.ofHom (algebraMap L L) = 𝟙 (CommRingCat.of L) := rfl
    rw [e, Spec.map_id, Category.id_comp]
  obtain ⟨MC, h1, h2⟩ := lieModel_transport M hz TL
  have hc : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ zL) :=
    (congrArg centre hz).symm ▸ h
  have hspan : ⊤ ≤ Submodule.span L (Set.range w) := by
    intro t _
    have ht : t ∈ M.fibAt M.lat zL MC :=
      (GlobalTheory.T.lie_lattice_eval_fraction_field X G Ω ξ Li M L zL L T MC hξ inferInstance h hc t).2 ⟨TL.pt t, TL.tan t, h1 t⟩
    refine (Submodule.span_le.2 ?_ : M.fibAt M.lat zL MC ≤ _) ht
    rintro w' ⟨h', e, he, hv⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' Set.univ) := by
      rw [Set.image_univ, ← hlat]
      exact he
    obtain ⟨u, hu, hv'⟩ := key _ _ he'
    have := TL.inj ((h2 _ _ hv).unique hξ hv')
    rw [this]
    rwa [Set.image_univ] at hu
  obtain ⟨E₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre zL)) (X.fromSpecStalk (centre zL))
  have c1 := finrank_lieModel_eq X G _ _ E₀ M₀ Ω (genMap ξ ⟨centre zL, h⟩) ξ (LieTangent.spec_genMap ξ ⟨centre zL, h⟩) Li M
  have c2 := finrank_lieModel_eq X G _ _ E₀ M₀ L (Scheme.stalkClosedPointTo zL).hom zL (LieTangent.spec_centre zL) T TL
  have card : Fintype.card Ix = Module.finrank L T := by
    rw [c2, ← c1, Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge)]
  refine ⟨w, hw, linearIndependent_of_top_le_span_of_card_eq_finrank hspan card, top_le_iff.1 hspan, ?_⟩
  intro A e u he hv
  obtain ⟨u', hu', hv'⟩ := key A e he
  rw [TL.inj (hv.unique hξ hv')]
  exact hu'

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.codim_one_gram_twist_agree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (t t' : SAB H X) (tp : SAB H (Spec (X.presheaf.stalk p.1))) (m : SABMap tp t (X.fromSpecStalk p.1)) (m' : SABMap (twistSAB tp g) t' (X.fromSpecStalk p.1)) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V), (∀ e, ∃ v : Sp (DualNumber Ω) ⟶ tp.G.left, v ≫ m.φ = (M.pt e).left ∧ v ≫ m'.φ = (M'.pt e).left) → ∀ (z : Sp ℂ ⟶ X), centre z = p.1 → ∀ (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ), M.GramAt t.PP.L z b Γ ↔ M'.GramAt t'.PP.L z b Γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.codim_one_gram_twist_eq | exact GlobalTheory.CompanionTheory.Ar.codim_one_gram_twist_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.codim_one_gram_twist_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_uniform_height_constant_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o₀ : RootOrigin Y ∅ R Fx), ∃ C₀ : ℝ, ∀ (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y S M Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich o.𝔐 p κ) → ∀ r, Ht.VertBound (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (o₀.e r) / o.e r) (C₀ + ∑ p ∈ S, ((if p = 2 then 2 else 1 / ((p : ℝ) - 1)) + 2 * padicValInt p (discr E)) * Real.log p) := by
  exact @GlobalTheory.CompanionTheory.Ar.OrVert.or_vert
end

section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.RootSum

theorem mono_smooth {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (t : ℝ)
    (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (j : Fin d) : IsSmoothHerm (monoLines (M.line t) m d j) := by
  unfold monoLines
  split_ifs
  · rename_i h
    generalize (Finsupp.toMultiset m).toList.get ⟨j, h⟩ = o
    cases o with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  · unfold IsSmoothHerm
    simp only [trivLine]
    exact contDiffOn_const

theorem PP_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem)
    (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.PP II (monomial m 1) = limUnder (𝓝[>] 0) fun t => M.arMono II t m := by
  exact Module.Basis.constr_basis (basisMonomials (Option (Ψ × Fin N)) ℝ) ℝ _ m

theorem geoFun_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)
    (m : Option (Ψ × Fin N) →₀ ℕ) : M.geoFun (monomial m 1) = M.geoMono m := by
  exact Module.Basis.constr_basis (basisMonomials (Option (Ψ × Fin N)) ℝ) ℝ _ m

theorem toA_pk_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (τ : Ψ) (m : Ψ × Fin N →₀ ℕ) :
    toA (pk τ 1 * monomial m (1 : ℝ) : RP Ψ N) =
      ∑ i : Fin N, monomial ((m + Finsupp.single (τ, i) 1).mapDomain some) (1 : ℝ) := by

  rw [toA, pk, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_one, X, monomial_mul, rename_monomial, add_comm, mul_one]

theorem sum_arMono (hP : PtsIntegrableStatement) (hM : MetricLocalStatement) (hD : DegreeStatement)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ)
    (R : RootFlat M τ) (hII : IsIntersectionSystem II) (m : Ψ × Fin N →₀ ℕ) (hm : m.degree = dimFl Ψ N)
    (t : ℝ) (ht : 0 < t) :
    ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some) =
      R.ht * M.geoMono (m.mapDomain some) -
        ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (R.v t) / (M.δ : ℝ) := by
  have h1 := GlobalTheory.T.intersection_family_multilinear hP hM M.K M.ι M.Ω R.F M.y R.φ (II M.K M.ι) M.P (dimFl Ψ N)
    (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) R.A R.S (dimFl Ψ N + 1) N
    (fun i => M.x t (τ, i)) (R.v t) (hII M.K M.ι) M.arith R.overInt le_rfl M.arith
    (mono_smooth M t _ _) R.A_smooth (fun i => M.x_smooth t _) (R.v_inv t) (R.v_smooth t)
    (by simp only [M.x_deg]; exact R.deg) (R.prod t ht)
  rw [Finset.sum_congr rfl fun i _ => arMono_add_single Ψ N M II t m (τ, i) hII hm, ← Finset.sum_div, h1,
    ← geoMono_eq hD Ψ N M t m hm, RootFlat.ht]
  ring

theorem PP_mono (hP : PtsIntegrableStatement) (hM : MetricLocalStatement) (hD : DegreeStatement)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ)
    (R : RootFlat M τ) (hII : IsIntersectionSystem II) (hC : M.Converges II) (m : Ψ × Fin N →₀ ℕ)
    (hm : m.degree = dimFl Ψ N) :
    M.PP II (toA (pk τ 1 * monomial m 1)) = R.ht * M.geoFun (toA (monomial m 1)) := by

  rw [toA_pk_monomial, map_sum, toA, rename_monomial, geoFun_monomial]
  simp only [PP_monomial]
  have h1 : Tendsto (fun t => ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))
      (𝓝[>] 0) (𝓝 (∑ i : Fin N, limUnder (𝓝[>] 0) fun t =>
        M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))) :=
    tendsto_finsetSum _ fun i _ => tendsto_nhds_limUnder (hC _)
  have h2 : Tendsto (fun t => ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))
      (𝓝[>] 0) (𝓝 (R.ht * M.geoMono (m.mapDomain some) - 0 / (M.δ : ℝ))) := by
    refine (tendsto_const_nhds.sub ((R.small m hm).div_const _)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (sum_arMono hP hM hD M II τ R hII m hm t ht).symm
  rw [tendsto_nhds_unique h1 h2, zero_div, sub_zero]

end GlobalTheory.CompanionTheory.Ar.Flat.RootSum

open GlobalTheory.CompanionTheory.Ar.Flat.RootSum in
theorem GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq : PtsIntegrableStatement → MetricLocalStatement → DegreeStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ) (R : RootFlat M τ) (Q : RP Ψ N), IsIntersectionSystem II → M.Converges II → Q.IsHomogeneous (dimFl Ψ N) → M.PP II (toA (pk τ 1 * Q)) = R.ht * M.geoFun (toA Q) := by
  intro hP hM hD Ψ _ _ N M II τ R Q hII hC hQ
  have hQ' : Q = ∑ m ∈ Q.support, Q.coeff m • monomial m (1 : ℝ) := by
    conv_lhs => rw [Q.as_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have hA : ∀ (c : ℝ) (F : RP Ψ N), toA (c • F) = c • toA F := fun c F => map_smul (rename some) c F
  have hS : ∀ (s : Finset (Ψ × Fin N →₀ ℕ)) (F : _ → RP Ψ N), toA (∑ m ∈ s, F m) = ∑ m ∈ s, toA (F m) :=
    fun s F => map_sum (rename some) F s

  rw [hQ', Finset.mul_sum, hS, hS, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : m.degree = dimFl Ψ N := by
    rw [Finsupp.degree_eq_weight_one]
    exact hQ (mem_support_iff.mp hm)
  rw [mul_smul_comm, hA, hA, map_smul, map_smul, PP_mono hP hM hD M II τ R hII hC m hd, smul_eq_mul, smul_eq_mul]
  ring
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.framed_point_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (F : Type) [Field F] (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ β y v w → ∃ (k : Type) (_ : Field k) (β₀ : c.F →+* k) (y₀ : Sp k ⟶ Xo.XF c) (v₀ : Vecs y₀ D.p) (w₀ : Vecs y₀ D.q) (f : k →+* F) (j : k →+* ℂ), IsFramed U τ β₀ y₀ v₀ w₀ ∧ f.comp β₀ = β ∧ j.comp β₀ = algebraMap c.F ℂ ∧ y = spMap f ≫ y₀ ∧ ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p) (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧ (∀ a, (v' a).left = spMap (dualMap f') ≫ (v₀ a).left) ∧ ∀ b, (w' b).left = spMap (dualMap f') ≫ (w₀ b).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_framed_residue | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_framed_residue | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_framed_residue <;> assumption)
end
