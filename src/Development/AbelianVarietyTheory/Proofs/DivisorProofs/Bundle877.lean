module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle847
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Mathlib.Algebra.WithConv
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem exists_mulEquiv_points_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {X : Scheme.{0}} (t : X ⟶ S') (g : X ⟶ S)
    (hg : t ≫ f = g) :
    ∃ e : (Over.mk t ⟶ G') ≃* (Over.mk g ⟶ G), ∀ z, (e z).left = z.left ≫ F := by
  subst hg
  let m : (Over.mk t ⟶ G') → (Over.mk (t ≫ f) ⟶ G) := fun z => Over.homMk (z.left ≫ F) (by
    have h : z.left ≫ G'.hom = t := Over.w z
    show (z.left ≫ F) ≫ G.hom = t ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, h])
  have hm : ∀ z, (m z).left = z.left ≫ F := fun _ => rfl
  have hmul : ∀ x y, m (x * y) = m x * m y := fun x y =>
    Over.OverMorphism.ext ((hm _).trans (hF.2 (Over.mk t) x y (m x) (m y) (hm x) (hm y)).symm)
  have hinj : Function.Injective m := fun x y h => by
    refine Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    rw [← hm, ← hm, h]
  have hsurj : Function.Surjective m := fun z =>
    ⟨Over.homMk (hF.1.lift z.left t (Over.w z)) (hF.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hm _).trans (hF.1.lift_fst _ _ _))⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' m hmul) ⟨hinj, hsurj⟩, hm⟩

end GlobalTheory.GroupBplus.Aff
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_finset_isGrpPullback_comp_of_subring_le : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → IsGrpPullback e.A d₀.A (spMap R₀.subtype) j → IsGrpPullback e.A u.A (spMap R₀.subtype ≫ h₀) (j ≫ ψ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ₁ : A₁.left ⟶ d₀.A.left), IsGrpPullback A₁ d₀.A (spMap (Subring.inclusion hle)) φ₁ → IsGrpPullback A₁ u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) := by
  first | exact @GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring | exact GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring | (intros; apply GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UPel.LocSim

theorem exists_open_eq_of_torsion_point : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (σ σ' : 𝟙_ (Over S) ⟶ A), σ ^ n = 1 → σ' ^ n = 1 → ∀ (k : Type) [Field k] (y : Sp k ⟶ S), toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ σ' → ∃ V : S.Opens, Set.range y ⊆ (V : Set S) ∧ V.ι ≫ σ.left = V.ι ≫ σ'.left := by
  intro S A _ _ hA n hn σ σ' hσ hσ' k _ y hy
  haveI := hA.smooth
  haveI : FormallyUnramified (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left := GlobalTheory.formallyUnramified_mulA S A n hn
  haveI : LocallyOfFiniteType (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left := by
    have : LocallyOfFiniteType ((ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left ≫ A.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp _ A.hom
  have hab : σ.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left = σ'.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    show σ ≫ 𝟙 A ^ n = σ' ≫ 𝟙 A ^ n
    rw [MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, hσ, hσ']
  haveI := GlobalTheory.isOpenImmersion_equalizer_ι_of_unramified (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left hab
  refine ⟨(equalizer.ι σ.left σ'.left).opensRange, ?_, ?_⟩
  · have hy' : y ≫ σ.left = y ≫ σ'.left := by
      have h := congrArg CommaMorphism.left hy
      simp only [Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at h
      exact h
    exact GlobalTheory.range_subset_range_equalizer_ι y hy'
  · rw [← cancel_epi (equalizer.ι σ.left σ'.left).isoOpensRange.hom, ← Category.assoc, ← Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι, equalizer.condition]

section
variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : GlobalTheory.UPel.Datum F} {p N : ℕ} {S : Scheme.{0}}
  {s : S ⟶ Sp (D.OEp p)} {o : GlobalTheory.UPel.Obj D p N s}

end

end GlobalTheory.UPel.LocSim
end
end
