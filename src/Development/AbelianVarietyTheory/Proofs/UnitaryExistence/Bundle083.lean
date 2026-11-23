module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle046
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram : ∀ (D : D7) (V : HSp D), latHat V = GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) ∧ (∀ v, finVec V v = GlobalTheory.AdLat.fv D.host.F v) ∧ (latC V).FG ∧ Submodule.span D.host.E (latC V : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (∀ x, cF D (cF D x) = x) ∧ (∀ x, cF D x = cc x) ∧ cF D ≠ 1 ∧ (∀ a b, cF D (V.gramᵀ a b) = V.gramᵀ b a) ∧ V.gramᵀ.det ≠ 0 ∧ (∀ x y, V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) = -herm (-V.gramᵀ) y x) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latC V, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ latC V := by
  first | exact @GlobalTheory.Member.latHat_eq_hat_and_gram | exact GlobalTheory.Member.latHat_eq_hat_and_gram | (intros; apply GlobalTheory.Member.latHat_eq_hat_and_gram <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.universalFrame_classifies_unique_openChart : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (A : Type) [CommRing A] [Algebra c.F A] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R) (π : R →ₐ[c.F] A) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)) (s : Aˣ) (u : FrPt Xo c A), OpenChart j y₀ → UnivFrame y₀ π X s u → ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A →ₐ[c.F] T) (z : FrPt Xo c T), FrMap a u z → FrMap a' u z → a = a' := by
  first | exact @GlobalTheory.Frames.univFrame_classifies_unique | exact GlobalTheory.Frames.univFrame_classifies_unique | (intros; apply GlobalTheory.Frames.univFrame_classifies_unique <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ParAtCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

theorem isHalf_of_level (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.IsHalf D l.Mb :=
  ⟨l.fromK, hl.1 ▸ l.prod, l.coprime⟩

theorem levelAt_spec (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : HalfLevelCoefficients.IsHalf D Mb) :
    (HalfLevelCoefficients.levelAt D Mb h).M = D.host.g 0 * D.host.g 1 ∧ (HalfLevelCoefficients.levelAt D Mb h).A = 1 :=
  ⟨rfl, rfl⟩

theorem levelPb_iff (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) :
    LevelPb D pb ↔ HalfLevelCoefficients.IsHalf D (HalfLevelCoefficients.halfOf D pb) := by
  constructor
  · rintro ⟨l, hl, hb⟩
    have h := isHalf_of_level D l hl
    rw [hb] at h
    exact h
  · intro h
    exact ⟨HalfLevelCoefficients.levelAt D _ h, levelAt_spec D _ h, rfl⟩

end GlobalTheory.ParAtCompare
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.realAdeles_cmField_equiv_complex_cmType : ∀ (D : D7), (∃ θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ))) ∧ ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧ Function.Bijective (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD}) => θ τ.1 z) := by
  first | exact @GlobalTheory.Member.infiniteAdele_bijective | exact GlobalTheory.Member.infiniteAdele_bijective | (intros; apply GlobalTheory.Member.infiniteAdele_bijective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.finite_points_abelianVariety_of_no_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 2 ≤ n → (n : k) ≠ 0 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ^ n = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  first | exact @GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion | exact GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion | (intros; apply GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
theorem _root_.GlobalTheory.intFrames_of_laws : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt → _root_.ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
      (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.Formalism.L2.Pj.IntFramesSt Xo c :=
  fun hBase hTwist E _ _ _ H Dw l Xo c =>
    _root_.Formalism.L2.Pj.intFrames Xo c _root_.ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (_root_.Formalism.L2.Pj.lieFree Xo c) (_root_.Formalism.L2.Pj.thetaFrame_of Xo c hTwist)
      (_root_.GlobalTheory.Frames.framedPoint_field_fromTest hBase E H Dw l Xo c)

end GlobalTheory
end
