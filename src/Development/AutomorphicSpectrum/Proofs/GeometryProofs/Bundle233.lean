module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle231
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientDifferentialMatrix
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem spMap_dualMap_comp_alg (V K : Type) [CommRing V] [Field K] [Algebra V K] :
    spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) =
      spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) := by
  have e : (dualMap (algebraMap V K)).comp (algebraMap V (DualNumber V)) =
      (algebraMap K (DualNumber K)).comp (algebraMap V K) := by
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem tan_iff_of_generic : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (X : Scheme.{0}) (Gx : Over X) [GrpObj Gx] [IsCommMonObj Gx] (T : Over (Sp V)) [GrpObj T] [IsCommMonObj T]
    (GK : Over (Sp K)) [GrpObj GK] (z : Sp V ⟶ X) (φ₀ : GK.left ⟶ T.left) (φ₁ : GK.left ⟶ Gx.left),
    IsSemiAbelian Gx → IsSemiAbelian T → IsGrpPullback GK T (spMap (algebraMap V K)) φ₀ →
    IsGrpPullback GK Gx (spMap (algebraMap V K) ≫ z) φ₁ → ∀ u : epsAt (𝟙 (Sp K)) ⟶ GK, IsTanAt GK (𝟙 _) u →
    ((∃ a : epsAt (𝟙 (Sp V)) ⟶ T, IsTanAt T (𝟙 _) a ∧ u.left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ a.left) ↔
      ∃ a : epsAt z ⟶ Gx, IsTanAt Gx z a ∧ u.left ≫ φ₁ = spMap (dualMap (algebraMap V K)) ≫ a.left) := by
  intro V K _ _ _ _ _ _ X Gx _ _ T _ _ GK _ z φ₀ φ₁ hG hT h₀ h₁ u hu
  have hp := isGrpPullback_pullback Gx z
  have hS : IsSemiAbelian ((Over.pullback z).obj Gx) := IsSemiAbelian.pullback z Gx hG
  have wφ : φ₁ ≫ Gx.hom = (GK.hom ≫ spMap (algebraMap V K)) ≫ z := by
    rw [h₁.1.w, Category.assoc]
  let φ' : GK.left ⟶ ((Over.pullback z).obj Gx).left := hp.1.lift φ₁ (GK.hom ≫ spMap (algebraMap V K)) wφ
  have eφ : φ' ≫ pullback.fst Gx.hom z = φ₁ := hp.1.lift_fst _ _ _
  have eσ : φ' ≫ ((Over.pullback z).obj Gx).hom = GK.hom ≫ spMap (algebraMap V K) := hp.1.lift_snd _ _ _
  have hn : IsGrpPullback GK ((Over.pullback z).obj Gx) (spMap (algebraMap V K)) φ' :=
    IsGrpPullback.cancel hp (h₁.congr rfl eφ.symm) eσ
  obtain ⟨ET, _, _, ⟨MT⟩⟩ := GlobalTheory.T.exists_lie_model (Sp V) T V (𝟙 _)
  obtain ⟨EG, _, _, ⟨MG⟩⟩ := GlobalTheory.T.exists_lie_model X Gx V z
  obtain ⟨M₀, hM₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main V X z Gx ((Over.pullback z).obj Gx) _ EG hp).1 MG
  obtain ⟨f, hf⟩ := GlobalTheory.T.semiabelian_hom_lie_extends V K T ((Over.pullback z).obj Gx) GK GK φ₀ φ' hT hS h₀ hn (𝟙 GK) ET EG MT M₀
  obtain ⟨g, hg⟩ := GlobalTheory.T.semiabelian_hom_lie_extends V K ((Over.pullback z).obj Gx) T GK GK φ' φ₀ hS hT hn h₀ (𝟙 GK) EG ET M₀ MT
  constructor
  · rintro ⟨a, ha, e⟩
    obtain ⟨x, rfl⟩ := MT.onto a ha
    have l := hf x u e
    refine ⟨MG.pt (f x), MG.tan _, ?_⟩
    have l' : u.left ≫ φ' = spMap (dualMap (algebraMap V K)) ≫ (M₀.pt (f x)).left := by
      simpa using l
    rw [← eφ, ← Category.assoc, l', Category.assoc, hM₀]
  · rintro ⟨a, ha, e⟩
    obtain ⟨x, rfl⟩ := MG.onto a ha
    have l : u.left ≫ φ' = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap V K)) ≫ (M₀.pt x).left := by
      refine hp.1.hom_ext ?_ ?_
      · rw [Category.assoc, eφ, e, Category.assoc, hM₀]
      · rw [Category.assoc, eσ, ← Category.assoc, Over.w u, Category.assoc, Over.w (M₀.pt x)]
        show (spMap (algebraMap K (DualNumber K)) ≫ 𝟙 _) ≫ spMap (algebraMap V K) =
          spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) ≫ 𝟙 _
        rw [Category.comp_id, Category.comp_id, spMap_dualMap_comp_alg]
    have l₂ := hg x u l
    refine ⟨MT.pt (g x), MT.tan _, ?_⟩
    simpa using l₂

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

theorem _root_.GlobalTheory.T.abelian_part_integral_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (lab : CMType H → CMType H ⊕ CMType H) (r k m : ℕ) (h : r + k = m) (v : Fin r → V) (q : CMType H → Fin k → A.Λ) (b : CMType H → Fin m → 𝔐.Li) (bL : CMType H → Fin m → V) (T : CMType H → Matrix (Fin m) (Fin m) L), 𝔐.IsLinPtOf z P MV A → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ)) → (∀ τ, IsValues 𝔐 z P MV (b τ) (bL τ)) → (∀ τ i, A.fam (lab τ) v (q τ) i = ∑ j, T τ j (Fin.cast h i) • bL τ j) → (∀ τ, (T τ).det ≠ 0) → ∀ e : L →+* ℂ, (∀ τ, 0 < A.gramDet e (q τ)) ∧ ∃ ν : ℝ, 𝔐.GeoPhi lab (spMap e ≫ spMap (algebraMap (𝓞 L) L) ≫ z) b ν ∧ 0 < ν ∧ ν = (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) * ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.geo_height_arch | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.geo_height_arch | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.geo_height_arch <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_differential_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (P : Matrix (Fin d') (Fin d) k), Q.IsDiff g gB P → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → linQ Qs = P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.linQ_eq_diff | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.linQ_eq_diff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.linQ_eq_diff <;> assumption)
end
