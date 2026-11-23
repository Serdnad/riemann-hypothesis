module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle196
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle176
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle174
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle146
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle173
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle144
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle143
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
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
public import Mathlib.NumberTheory.SumFourSquares
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_etale_cover_chart_at_field_point : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := by
  first | exact @GlobalTheory.Poinc.ChartAt.exists_chart_at | exact GlobalTheory.Poinc.ChartAt.exists_chart_at | (intros; apply GlobalTheory.Poinc.ChartAt.exists_chart_at <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_symplecticLevel_after_finiteExtension_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∀ m : ℕ, 1 ≤ m → IsUnit (m : R) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (ζ : R₁ˣ) (_ : ReciprocityTheory.ChartRestriction.G.Out.Level A₁ m (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ))), FinExt ρ ∧ IsFib ρ A A₁ a ∧ A₁.g = A.g ∧ (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) := by
  first | exact @GlobalTheory.MumLevel.exists_level_finExt | exact GlobalTheory.MumLevel.exists_level_finExt | (intros; apply GlobalTheory.MumLevel.exists_level_finExt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.PullLab

open GlobalTheory.Poinc.DeepLab

theorem exists_lab_of_isGrpPullback : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left) (d : ℕ), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → S₂.r * S₂.N = S₁.r * S₁.N * d → ∃ lam : S₁.Gam →+ S₂.Gam, (∀ a, (ρ₂.pt (lam a)).left ≫ φ = spMap om ≫ (ρ₁.pt a).left) ∧ ∀ a', ∃ a, lam a = d • a' := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ om φ d hpb hd
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap (algebraMap Ω₂ K) ≫ spMap S₂.R.val.toRingHom
  let U : Over.mk ((baseOver (Sp S₂.R)).hom ≫ spMap om) ⟶ baseOver (Sp S₁.R) := Over.homMk (spMap om) (by simp)
  let V₂ : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  let p₁ : Multiplicative S₁.Gam →* (baseOver (Sp S₁.R) ⟶ ρ₁.P.A) :=
    MonoidHom.mk' (fun a => ρ₁.pt (Multiplicative.toAdd a)) fun a b => ρ₁.pt_add _ _
  let p₂ : Multiplicative S₂.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) :=
    MonoidHom.mk' (fun a => ρ₂.pt (Multiplicative.toAdd a)) fun a b => ρ₂.pt_add _ _
  have hbij : Function.Bijective (pushHom hpb (baseOver (Sp S₂.R))) :=
    ⟨pushHom_injective hpb _, pushHom_surjective hpb _⟩
  let e := MulEquiv.ofBijective (pushHom hpb (baseOver (Sp S₂.R))) hbij
  let σ : Multiplicative S₁.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) := e.symm.toMonoidHom.comp ((preHom U).comp p₁)
  have hσ : ∀ a, pushHom hpb _ (σ a) = U ≫ ρ₁.pt (Multiplicative.toAdd a) := fun a =>
    e.apply_symm_apply (U ≫ ρ₁.pt (Multiplicative.toAdd a))
  have hσl : ∀ a, (σ a).left ≫ φ = spMap om ≫ (ρ₁.pt (Multiplicative.toAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hσ a)
  have hσL : ∀ a : S₁.Gam, σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [hd, pow_mul, map_pow_self, one_pow]
  have uniq : ∀ z : baseOver (Sp S₂.R) ⟶ ρ₂.P.A, z ^ (S₂.r * S₂.N) = 1 →
      ∃! b : S₂.Gam, p₂ (Multiplicative.ofAdd b) = z := by
    intro z hz
    obtain ⟨b, hb⟩ := GlobalTheory.torsionSection_eq_labelled_of_isDomain S₂.R ρ₂.P (S₂.r * S₂.N) S₂.Gam ρ₂.pt
      (fun K _ _ x z hz => (ρ₂.pt_bij K x z hz).exists) z hz
    refine ⟨b, hb, fun b' hb' => ?_⟩
    have h2 : (V₂ ≫ z) ^ (S₂.r * S₂.N) = 1 := by
      have h3 := congrArg (preHom V₂) hz
      rwa [map_pow, map_one] at h3
    exact (ρ₂.pt_bij K x₀ (V₂ ≫ z) h2).unique (congrArg (V₂ ≫ ·) hb') (congrArg (V₂ ≫ ·) hb)
  obtain ⟨lam, hlam⟩ := exists_lab _ p₂ σ uniq hσL
  have hpt : ∀ a, (ρ₂.pt (lam a)).left ≫ φ = spMap om ≫ (ρ₁.pt a).left := fun a => by
    have h4 := hσl (Multiplicative.ofAdd a)
    rw [← hlam a] at h4
    exact h4
  refine ⟨lam, hpt, fun a' => ?_⟩
  set y := d • a' with hy
  have hyL : p₂ (Multiplicative.ofAdd y) ^ (S₁.r * S₁.N) = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, hy, smul_smul, ← hd, nsmul_self_eq_zero, ofAdd_zero, map_one]
  let T₀ : Over (Sp S₂.R) := Over.mk x₀
  let V₁ : Over.mk (x₀ ≫ spMap om) ⟶ baseOver (Sp S₁.R) := Over.homMk (x₀ ≫ spMap om) (by simp)
  let z₁ : Over.mk (x₀ ≫ spMap om) ⟶ ρ₁.P.A := pushHom hpb T₀ (V₂ ≫ ρ₂.pt y)
  have hz₁ : z₁ ^ (S₁.r * S₁.N) = 1 := by
    have h0 : (V₂ ≫ ρ₂.pt y) ^ (S₁.r * S₁.N) = 1 := by
      have h3 := congrArg (preHom V₂) hyL
      rwa [map_pow, map_one] at h3
    show (pushHom hpb T₀) _ ^ _ = 1
    rw [← map_pow, h0, map_one]
  obtain ⟨a, ha, -⟩ := ρ₁.pt_bij K (x₀ ≫ spMap om) z₁ hz₁
  refine ⟨a, ?_⟩
  have hpush : pushHom hpb T₀ (V₂ ≫ ρ₂.pt (lam a)) = V₁ ≫ ρ₁.pt a := by
    apply Over.OverMorphism.ext
    show (V₂ ≫ ρ₂.pt (lam a)).left ≫ φ = (V₁ ≫ ρ₁.pt a).left
    simp only [Over.comp_left, Category.assoc, V₂, V₁, Over.homMk_left]
    rw [hpt]
  have h1 : V₂ ≫ ρ₂.pt (lam a) = V₂ ≫ ρ₂.pt y := pushHom_injective hpb T₀ (hpush.trans ha)
  have h2 : (V₂ ≫ ρ₂.pt y) ^ (S₂.r * S₂.N) = 1 := by
    have h3 := congrArg (preHom V₂) (map_pow_self _ p₂ y)
    rwa [map_pow, map_one] at h3
  exact (ρ₂.pt_bij K x₀ _ h2).unique h1 rfl

end GlobalTheory.Poinc.PullLab
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_completeDVR_comparison_preUniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (_ : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = maximalIdeal R ∧ GlobalTheory.LN.Under U' U₀.toUnifPre := by
  first | exact @GlobalTheory.Mum.TraitCompare.exists_cmp_under | exact GlobalTheory.Mum.TraitCompare.exists_cmp_under | (intros; apply GlobalTheory.Mum.TraitCompare.exists_cmp_under <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem integral_of_sqPow_bdd (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (y : FractionRing R) (r : R) (hr : r ≠ 0)
    (h : ∀ n : ℕ, ∃ s : R, algebraMap R (FractionRing R) r * y ^ (n ^ 2) = algebraMap R _ s) :
    ∃ s : R, y = algebraMap R _ s := by
  set c : FractionRing R := algebraMap R (FractionRing R) r with hc
  have hc0 : c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  have hall : ∀ k : ℕ, ∃ s : R, c ^ 4 * y ^ k = algebraMap R _ s := by
    intro k
    obtain ⟨p, q, u, v, hk⟩ := Nat.sum_four_squares k
    obtain ⟨s1, h1⟩ := h p
    obtain ⟨s2, h2⟩ := h q
    obtain ⟨s3, h3⟩ := h u
    obtain ⟨s4, h4⟩ := h v
    refine ⟨s1 * s2 * s3 * s4, ?_⟩
    rw [← hk, map_mul, map_mul, map_mul, ← h1, ← h2, ← h3, ← h4, pow_add, pow_add, pow_add]
    ring
  let S : Subalgebra R (FractionRing R) := Algebra.adjoin R {y}
  have hle : Subalgebra.toSubmodule S ≤ Submodule.span R {(c ^ 4)⁻¹} := by
    show Subalgebra.toSubmodule (Algebra.adjoin R {y}) ≤ _
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro z hz
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hz
    obtain ⟨s, hs⟩ := hall k
    have hc4 : c ^ 4 ≠ 0 := pow_ne_zero _ hc0
    have : y ^ k = s • (c ^ 4)⁻¹ := by
      rw [Algebra.smul_def, ← hs]; field_simp
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
  have hfg : (Subalgebra.toSubmodule S).FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span_singleton (R := R) ((c ^ 4)⁻¹ : FractionRing R))
    have h1 : ((Subalgebra.toSubmodule S).comap (Submodule.span R {(c ^ 4)⁻¹}).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Submodule.span R {(c ^ 4)⁻¹}).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  have hint : IsIntegral R y := IsIntegral.of_mem_of_fg S hfg y (Algebra.self_mem_adjoin_singleton R y)
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨s, hs.symm⟩

theorem exists_coefData_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left), GlobalTheory.LN.Cmp φ U U' F → GlobalTheory.LN.CDvr V → Function.Injective φ → (maximalIdeal V).comap φ = maximalIdeal R → GlobalTheory.LN.Under U' U₀.toUnifPre → ∃ (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 ∧ U.ExpT (𝟙_ _) 1 σ f ∧ (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) ∧ GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) ∧ ∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h := by

  intro R _ _ _ hB D A G _ _ U V _ _ _ φ D' A' G' _ _ U' U₀ F C hV hφ hI hU
  obtain ⟨⟨h₁, h₂, -, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_of_laws h₁ h₂
  have hR : AdmBase R (maximalIdeal R) := hB.1
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  have hmR : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  have := hV.1
  have hV' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hm : maximalIdeal V ≠ ⊤ := (maximalIdeal.isMaximal V).ne_top
  have hIm : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hI.ge
  obtain ⟨σ, hσ0⟩ := GlobalTheory.T.exists_nonzero_section_preUniformised_completeNormal R hB D A G U
  obtain ⟨f, hf, -⟩ := GlobalTheory.CompleteBaseExpansion.main h₁ h₂ hE R _ hR hmR D A G U 1 σ
  obtain ⟨σ', f', hf', hσσ, hff⟩ := GlobalTheory.ExpCmp.expT_cmp R V _ _ φ hIm D D'.toPre A A' G G' U U' F C 1 σ f hf
  have hcmp : GlobalTheory.PsiRing.SecCmp D D'.toPre C.β C.v C.xe f f' := hff
  have hrel' := GlobalTheory.T.psiRel_of_expT' h₁ h₂ V _ hV' D' A' G' U' U₀ hU σ' f' hf'
  have hσ'0 := GlobalTheory.T.pullback_nonzero_section_injective_domain_map R hB D A G U V φ D'.toPre A' G' U' F C hV hφ σ σ' hσσ hσ0
  have hne' : ∀ α, ∃ j, (f' α).f j ≠ 0 :=
    GlobalTheory.T.forall_term_ne_zero_of_psiRelation V D'.toPre f' hrel' (GlobalTheory.T.exists_nonzero_expansionTerm_completeDVR V hV D' A' G' U' U₀ hU σ' f' hf' hσ'0)
  have hne := GlobalTheory.PsiRing.ne_zero_of_secCmp C.pbB.1.w hcmp hne'
  obtain ⟨psi, h, hrel⟩ := GlobalTheory.exists_psi_psiRel h₁ h₂ R D f hne
  let E : DegPre R := GlobalTheory.LN.withPsi D psi h
  have hrelE : GlobalTheory.UU.PsiRel E (𝟙_ _) f := hrel
  have hrig : GlobalTheory.PsiRing.RigCmp φ E D'.toPre C.β C.v := GlobalTheory.T.rigidification_comparison_uniformisation R V _ _ φ hm hIm D D'.toPre A G A' G' U U' F C
  obtain ⟨gam, hgam⟩ := GlobalTheory.PsiRing.exists_generic_map hφ
  have hpsi : GlobalTheory.PsiRing.PsiCmp E D'.toPre C.β C.v C.xe gam :=
    GlobalTheory.T.psiCmp_of_secCmp' R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig f f' hcmp hrelE hrel' (hne' 0) gam hgam
  have hev : E.PsiEven :=
    GlobalTheory.T.psiEven_descend_baseChange h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi D'.psi_even
  have hbi : E.TauBimult :=
    GlobalTheory.T.tauBimult_of_baseChange' h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi D'.tau_bimult
  obtain ⟨ga, a, hS⟩ := GlobalTheory.exists_psiScal R E
  obtain ⟨th, hth, hmul⟩ := GlobalTheory.T.exists_thetaSection_nonzeroFibres_localRing h₂.secTwist R D
  obtain ⟨q, hq⟩ := hmul (f 0)
  choose b hb using fun χ : D.X => GlobalTheory.T.exists_twistedSection_thetaTranslate_coef R D th hmul χ (ga χ) (hS χ).1 (f χ)
  have hab : ∀ χ, algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) (b χ) := fun χ =>
    GlobalTheory.T.psiScalar_eq_expansionCoef_ratio R E ga a f th hS hrelE hth χ q (b χ) hq (hb χ)
  have hq0 : q ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne 0
    apply hj
    rw [GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection R D th (f 0) 0 hq j]
    simp [scal]
  have hint : ∀ χ, ∃ c : R, ((a χ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ c := fun χ => by
    refine integral_of_sqPow_bdd R _ q hq0 fun n => ?_
    obtain ⟨u, hu⟩ := GlobalTheory.T.psiScalar_nsmul_eq_unit_mul_pow_sq R E ga a hS hev hbi χ n
    refine ⟨((u⁻¹ : Rˣ) : R) * b (n • χ), ?_⟩
    rw [map_mul, ← hab, hu]
    have hu1 : algebraMap R (FractionRing R) ((u⁻¹ : Rˣ) : R) * algebraMap R _ (u : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap R (FractionRing R) q * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2))) * hu1
  choose c hc using hint
  have hbc : ∀ χ, b χ = q * c χ := fun χ => by
    apply IsFractionRing.injective R (FractionRing R)
    exact (hab χ).symm.trans (by rw [map_mul, ← hc χ])
  have hcm : ∀ χ : D.X, χ ≠ 0 → c χ ∈ maximalIdeal R := fun χ hχ => by
    obtain ⟨x, rfl⟩ := C.xe.surjective χ
    obtain ⟨m, hm₁, hm₂⟩ := GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi ga a hS x _
      (D'.psi_pos x fun h0 => hχ (by rw [h0, map_zero])) _ q (hab _)
    have hm₃ : φ q * φ (c (C.xe x)) = φ q * m := by rw [← map_mul, ← hbc]; exact hm₂
    have hφq : φ q ≠ 0 := (map_ne_zero_iff _ hφ).2 hq0
    have e := mul_left_cancel₀ hφq hm₃
    have hmem : c (C.xe x) ∈ (maximalIdeal V).comap φ := Ideal.mem_comap.2 (by rw [e]; exact hm₁)
    exact (Set.ext_iff.1 (congrArg (fun J : Ideal R => (J : Set R)) hI) _).1 hmem
  choose G₁ hG₁ using fun χ : D.X => GlobalTheory.T.exists_translatedThetaCoefficient_section R D th χ (ga χ) (hS χ).1 (c χ)
  choose H₁ hH₁ using fun χ : D.X => GlobalTheory.T.exists_translatedThetaCoefficient_section R D th χ (ga χ) (hS χ).1 1
  classical
  let g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α := fun α => if h0 : α = 0 then h0 ▸ th else G₁ α
  refine ⟨σ, f, g, q, hq0, hf, fun α => ?_, ?_, fun α hα => ⟨c α, hcm α hα, H₁ α, ?_⟩⟩
  · by_cases h0 : α = 0
    · subst h0
      simp only [g, dif_pos rfl]
      exact GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection R D th (f 0) q hq
    · simp only [g, dif_neg h0]
      exact GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional R D α (ga α) th (f α) (G₁ α) (b α) (c α) q (hb α) (hG₁ α) (hbc α)
  · simp only [g, dif_pos rfl]
    exact hth
  · simp only [g, dif_neg hα]
    exact GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional R D α (ga α) th (G₁ α) (H₁ α) (c α) 1 (c α) (hG₁ α) (hH₁ α) (_root_.mul_one _).symm

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaSeries_values_galois_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ m : ℕ, Odd m → IsUnit (m : R) → ∀ v : QkPt D.toPre (Kb R) (m ^ 2) → Kb R, (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) (m ^ 2) → QkPt D.toPre C (m ^ 2)) (q : QkPt D.toPre (Kb R) (m ^ 2) → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i)) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) (m ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p' := by
  first | exact @GlobalTheory.Mum.values_galois_scalar | exact GlobalTheory.Mum.values_galois_scalar | (intros; apply GlobalTheory.Mum.values_galois_scalar <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem finrank_range_fderiv_lt_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (A : FinHolAtlas D (CxPts p σ)) (A' : FinHolAtlas D (CxPts q σ)), IsAlgAtlas A → IsAlgAtlas A' → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) ≠ genericPoint X → ∀ j l, ∀ y ∈ (A'.chart j).target, PtsOver.map π hπ (spMap σ) ((A'.chart j).symm y) ∈ (A.chart l).source → Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart l ∘ PtsOver.map π hπ (spMap σ) ∘ (A'.chart j).symm) y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) < D := by
  intro k _ X Y _ _ p q σ D A A' hA hA' π hπ hgen j l y hy hyl
  set m := PtsOver.map π hπ (spMap σ) with hm_def
  have hm : ∀ z : CxPts q σ, (m z).1 = z.1 ≫ π := fun _ => rfl
  have hH := hA.holoMap hA' (f := π) hm
  set W := (A'.chart j).target ∩ (A'.chart j).symm ⁻¹' (m ⁻¹' (A.chart l).source) with hW_def
  have hWo : IsOpen W := (A'.chart j).isOpen_inter_preimage_symm
    ((A.chart l).open_source.preimage hH.1)
  have han : AnalyticOnNhd ℂ (A.chart l ∘ m ∘ (A'.chart j).symm) W := hH.2 j l
  set Z : Set X := closure {π (genericPoint Y)} with hZ_def
  have hZc : IsClosed Z := isClosed_closure
  have hZg : genericPoint X ∉ Z := by
    intro h
    have h1 : π (genericPoint Y) ⤳ genericPoint X := specializes_iff_mem_closure.2 h
    have h2 : genericPoint X ⤳ π (genericPoint Y) := genericPoint_specializes _
    exact hgen (h1.antisymm h2).eq
  have hZm : ∀ z : CxPts q σ, (m z).1 (IsLocalRing.closedPoint ℂ) ∈ Z := by
    intro z
    have hs : genericPoint Y ⤳ z.1 (IsLocalRing.closedPoint ℂ) := genericPoint_specializes _
    have := hs.map π.continuous
    rw [hm]
    exact specializes_iff_mem_closure.1 this
  obtain ⟨c, hc⟩ := hA l
  have hnull := GlobalTheory.T.volume_complexPoints_properClosed_chart_field k X p σ D Z hZc hZg c
  have hsub : (A.chart l ∘ m ∘ (A'.chart j).symm) '' W ⊆
      FinChart.toV D ⁻¹' (c.e '' (c.e.source ∩ {x : CxPts p σ | x.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨m ((A'.chart j).symm z), ⟨?_, hZm _⟩, ?_⟩
    · have := hz.2
      rw [hc] at this
      exact this
    · simp only [Function.comp_apply, hc]
      rfl
  have h0 : volume ((A.chart l ∘ m ∘ (A'.chart j).symm) '' W) = 0 :=
    measure_mono_null hsub (FinChart.measurePreserving_toV.quasiMeasurePreserving.preimage_null hnull)
  exact finrank_range_fderiv_lt_of_volume_image_eq_zero D _ W hWo han h0 y ⟨hy, hyl⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.compatibleReductionSystem_gives_thickening_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (t : ℕ → W.IdealSheafData), IsSystem f I t → ∃ (q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (β : ∀ e, (t e).subscheme ⟶ (t (e + 1)).subscheme), (∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e) ∧ (∀ e, β e ≫ (t (e + 1)).subschemeι = (t e).subschemeι) ∧ ∀ e, IsPullback (β e) (q e) (q (e + 1)) (thickTrans R I e) := by
  first | exact @GlobalTheory.FormalAlg.isSystem_tower | exact GlobalTheory.FormalAlg.isSystem_tower | (intros; apply GlobalTheory.FormalAlg.isSystem_tower <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.formal_algebraisation_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), Alg f I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ j : ∀ e, (Y e).left ⟶ W, (∀ e, IsClosedImmersion (j e)) → (∀ e, j e ≫ f = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ j (e + 1) = j e) → ∃ (T : Scheme.{0}) (i : T ⟶ W) (c : ∀ e, (Y e).left ⟶ T), IsClosedImmersion i ∧ IsProper (i ≫ f) ∧ (∀ e, c e ≫ i = j e) ∧ ∀ e, IsPullback (c e) (Y e).hom (i ≫ f) (thick R I e) := by
  first | exact @GlobalTheory.FormalAlg.alg_tower | exact GlobalTheory.FormalAlg.alg_tower | (intros; apply GlobalTheory.FormalAlg.alg_tower <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.generic_uniformised_pullback_mumfordBundle_matching : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → Geo.Tor.IsSquare βW βW₂ → LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) → ∃ (ga : FractionRing R →+* FractionRing W) (α : AW.A.left ⟶ A.A.left) (α₂ : (G2 AW.A).left ⟶ (G2 A.A).left), (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧ IsGrpPullback AW.A A.A (spMap ga) α ∧ Geo.Tor.IsSquare α α₂ ∧ LBIso (abelian₂ AW.A AW.L) ((abelian₂ A.A A.L).pull α₂) ∧ UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  first | exact @GlobalTheory.Mum.genLam_pull_of_unif | exact GlobalTheory.Mum.genLam_pull_of_unif | (intros; apply GlobalTheory.Mum.genLam_pull_of_unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.uniformisationEndomorphism_carries_periodPoint_balanced : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  first | exact @GlobalTheory.Mum.KeepsIota.main | exact GlobalTheory.Mum.KeepsIota.main | (intros; apply GlobalTheory.Mum.KeepsIota.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o' : Obj b N s') (o : Obj b N s) (f : S' ⟶ S) (m m' : ObjMap o' o f), m.φ = m'.φ := by
  first | exact @GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique | exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique | (intros; apply GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique <;> assumption)
end
