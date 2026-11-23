module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle650
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle386
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle656
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle655
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle683
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix

section LinearModel

variable {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)

noncomputable def linMatEntry (a : Fin p) (b : Fin q) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => Z u a b
      map_add' := fun u v => by simp
      map_smul' := fun c u => by simp }

theorem mContDiffAt_linMat (k : WithTop ℕ∞) (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Z u) x := fun a b => by
  have : (fun u => Z u a b) = ((linMatEntry Z a b).restrictScalars ℝ : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℂ) := by
    funext u; rfl
  rw [this]
  exact ContinuousLinearMap.contDiff _ |>.contDiffAt

theorem mdel_linMat (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (fun u => Z u) x ξ = Z ξ := by
  ext a b
  have : (fun u => Z u a b) = fun u => linMatEntry Z a b u := rfl
  rw [mdel_apply, this, del_eq_fderiv (linMatEntry Z a b).differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

theorem mdbar_linMat (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (fun u => Z u) x η = 0 := by
  ext a b
  have : (fun u => Z u a b) = fun u => linMatEntry Z a b u := rfl
  rw [mdbar_apply, this, dbar_eq_zero (linMatEntry Z a b).differentiableAt]
  rfl

theorem mdel_linMat_conjTranspose (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => (Z u)ᴴ) x ξ = 0 := by
  rw [mdel_conjTranspose, mdbar_linMat, conjTranspose_zero]

theorem mdbar_linMat_conjTranspose (x η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => (Z u)ᴴ) x η = (Z η)ᴴ := by
  rw [mdbar_conjTranspose, mdel_linMat]

theorem mdel_const_sub {m l : Type*} {B : ReciprocityTheory.L2DbarEstimates.V n → Matrix m l ℂ}
    {x : ReciprocityTheory.L2DbarEstimates.V n} (C : Matrix m l ℂ) (h : MContDiffAt 1 B x) (ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => C - B u) x ξ = -mdel B x ξ := by
  ext a b
  simp only [mdel_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [del_sub (differentiableAt_const _) (h.diff a b)]
  simp

theorem mdbar_const_sub {m l : Type*} {B : ReciprocityTheory.L2DbarEstimates.V n → Matrix m l ℂ}
    {x : ReciprocityTheory.L2DbarEstimates.V n} (C : Matrix m l ℂ) (h : MContDiffAt 1 B x) (η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => C - B u) x η = -mdbar B x η := by
  ext a b
  simp only [mdbar_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [dbar_sub (differentiableAt_const _) (h.diff a b)]
  simp

theorem curv_modelGram_lie (w ξ η : ReciprocityTheory.L2DbarEstimates.V n) (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η =
      -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := by
  have hZ : ∀ x, MContDiffAt 2 (fun u => Z u) x := mContDiffAt_linMat Z 2
  have hB : ∀ x, MContDiffAt 2 (fun u => Z u * (Z u)ᴴ) x :=
    fun x => (hZ x).mul (hZ x).conjTranspose
  have hA : ∀ x, MContDiffAt 2 (fun u => 1 - Z u * (Z u)ᴴ) x :=
    fun x => (mContDiffAt_const 1).sub (hB x)
  have hAu : IsUnit (1 - Z w * (Z w)ᴴ).det := by
    rw [det_one_sub_mul_comm]; exact hw.det_pos.ne'.isUnit
  have hH : (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) =
      fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ := by
    funext u
    have e : 1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ = (1 - Z u * (Z u)ᴴ)ᵀ := by
      ext a b
      simp [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, eq_comm, mul_comm]
    rw [e, transpose_nonsing_inv]
  have hconn : ∀ x, IsUnit (1 - Z x * (Z x)ᴴ).det →
      conn (fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ) x ξ = Z ξ * (Z x)ᴴ * (1 - Z x * (Z x)ᴴ)⁻¹ := by
    intro x hx
    have h1 : MContDiffAt 1 (fun u => 1 - Z u * (Z u)ᴴ) x := (hA x).of_le one_le_two
    have hZ1 : MContDiffAt 1 (fun u => Z u) x := (hZ x).of_le one_le_two
    have hdA : mdel (fun u => 1 - Z u * (Z u)ᴴ) x ξ = -(Z ξ * (Z x)ᴴ) := by
      rw [mdel_const_sub _ ((hB x).of_le one_le_two), mdel_mul hZ1 hZ1.conjTranspose,
        mdel_linMat, mdel_linMat_conjTranspose, Matrix.mul_zero, zero_add]
    rw [conn, transpose_transpose, nonsing_inv_nonsing_inv _ hx,
      mdel_transpose (fun u => (1 - Z u * (Z u)ᴴ)⁻¹), transpose_transpose, mdel_inv h1 hx, hdA]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_left _ _ hx]
  have hev : (fun x => conn (fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ) x ξ) =ᶠ[𝓝 w]
      fun x => Z ξ * (Z x)ᴴ * (1 - Z x * (Z x)ᴴ)⁻¹ :=
    ((hA w).eventually_isUnit hAu).mono fun x hx => hconn x hx
  have h1 : MContDiffAt 1 (fun u => 1 - Z u * (Z u)ᴴ) w := (hA w).of_le one_le_two
  have hZ1 : MContDiffAt 1 (fun u => Z u) w := (hZ w).of_le one_le_two
  have hdA : mdbar (fun u => 1 - Z u * (Z u)ᴴ) w η = -(Z w * (Z η)ᴴ) := by
    rw [mdbar_const_sub _ ((hB w).of_le one_le_two), mdbar_mul hZ1 hZ1.conjTranspose,
      mdbar_linMat, mdbar_linMat_conjTranspose, Matrix.zero_mul, add_zero]
  rw [hH, curv, mdbar_congr hev,
    mdbar_mul ((mContDiffAt_const (Z ξ)).mul hZ1.conjTranspose) (h1.inv hAu), mdbar_inv h1 hAu,
    mdbar_mul (mContDiffAt_const _) hZ1.conjTranspose, mdbar_linMat_conjTranspose, mdbar_const,
    hdA]
  have hP : (1 - Z w * (Z w)ᴴ) * (1 - Z w * (Z w)ᴴ)⁻¹ = 1 := mul_nonsing_inv _ hAu
  have hQ : (1 - (Z w)ᴴ * Z w)⁻¹ = 1 + (Z w)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z w := by
    apply Matrix.inv_eq_right_inv
    have e : (1 - (Z w)ᴴ * Z w) * (1 + (Z w)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z w) =
        1 - (Z w)ᴴ * Z w + (Z w)ᴴ * ((1 - Z w * (Z w)ᴴ) * (1 - Z w * (Z w)ᴴ)⁻¹) * Z w := by
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
    rw [e, hP, Matrix.mul_one, sub_add_cancel]
  rw [hQ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, neg_neg, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc, neg_add]
  abel

end LinearModel

end GlobalTheory.PointChern
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix

section ModelCurv

variable {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)

def entryCLM (a : Fin p) (b : Fin q) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℂ ℂ a b) ∘ₗ Z)

theorem mContDiffAt_linear {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Z u) x := fun a b => by
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this]
  exact ((entryCLM Z a b).contDiff.restrict_scalars ℝ).contDiffAt

theorem mdel_linear (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (fun u => Z u) x ξ = Z ξ := by
  ext a b
  rw [mdel_apply]
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this, del_eq_fderiv (entryCLM Z a b).differentiableAt, (entryCLM Z a b).fderiv]
  rfl

theorem mdbar_linear (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (fun u => Z u) x η = 0 := by
  ext a b
  rw [mdbar_apply]
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this, dbar_eq_zero (entryCLM Z a b).differentiableAt]
  rfl

theorem mdel_one_sub_gram (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => 1 - (Z u)ᴴ * Z u) x ξ = -((Z x)ᴴ * Z ξ) := by
  have h1 : MContDiffAt 1 (fun u => Z u) x := mContDiffAt_linear Z x
  have h := mdel_mul (A := fun u => (Z u)ᴴ) h1.conjTranspose h1 ξ
  rw [mdel_linear, mdel_conjTranspose, mdbar_linear, conjTranspose_zero, Matrix.zero_mul,
    add_zero] at h
  have e : (fun u => 1 - (Z u)ᴴ * Z u) = fun u => (fun _ => (1 : Matrix (Fin q) (Fin q) ℂ)) u
      + (fun u => -((Z u)ᴴ * Z u)) u := by funext u; simp [sub_eq_add_neg]
  rw [e, mdel_add (mContDiffAt_const _) (h1.conjTranspose.mul h1).neg, mdel_const, zero_add,
    mdel_neg, h]

theorem mdbar_one_sub_gram (x η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => 1 - (Z u)ᴴ * Z u) x η = -((Z η)ᴴ * Z x) := by
  have h1 : MContDiffAt 1 (fun u => Z u) x := mContDiffAt_linear Z x
  have h := mdbar_mul (A := fun u => (Z u)ᴴ) h1.conjTranspose h1 η
  rw [mdbar_linear, mdbar_conjTranspose, mdel_linear, Matrix.mul_zero, zero_add] at h
  have e : (fun u => 1 - (Z u)ᴴ * Z u) = fun u => (fun _ => (1 : Matrix (Fin q) (Fin q) ℂ)) u
      + (fun u => -((Z u)ᴴ * Z u)) u := by funext u; simp [sub_eq_add_neg]
  rw [e, mdbar_add (mContDiffAt_const _) (h1.conjTranspose.mul h1).neg, mdbar_const, zero_add,
    mdbar_neg, h]

theorem inv_one_sub_mul_conjTranspose (z : Matrix (Fin p) (Fin q) ℂ) (hu : IsUnit (1 - zᴴ * z).det) :
    (1 - z * zᴴ)⁻¹ = 1 + z * (1 - zᴴ * z)⁻¹ * zᴴ := by
  apply Matrix.inv_eq_right_inv
  have hAQ : (1 - zᴴ * z) * (1 - zᴴ * z)⁻¹ = 1 := mul_nonsing_inv _ hu
  set Q := (1 - zᴴ * z)⁻¹
  have hQ : Q = 1 + zᴴ * (z * Q) := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at hAQ
    rw [Matrix.mul_assoc] at hAQ
    exact hAQ
  have key : z * (Q * zᴴ) = z * zᴴ + z * (zᴴ * (z * (Q * zᴴ))) := by
    nth_rewrite 1 [hQ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_assoc]
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  nth_rewrite 1 [key]
  abel

theorem curv_inv_one_sub_gram (w ξ η : ReciprocityTheory.L2DbarEstimates.V n) (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := by
  have hA : ∀ x, MContDiffAt 2 (fun u => 1 - (Z u)ᴴ * Z u) x := fun x =>
    (mContDiffAt_const 1).sub ((mContDiffAt_linear Z x).conjTranspose.mul (mContDiffAt_linear Z x))
  have hu : IsUnit (1 - (Z w)ᴴ * Z w).det := hw.det_pos.ne'.isUnit
  have hconn : ∀ x, IsUnit (1 - (Z x)ᴴ * Z x).det →
      conn (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ = ((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ := by
    intro x hx
    have h : (((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ)ᵀ * (1 - (Z x)ᴴ * Z x)⁻¹ =
        mdel (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ := by
      rw [transpose_transpose, mdel_inv ((hA x).of_le one_le_two) hx, mdel_one_sub_gram]
      simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    exact (eq_conn_of_compatible (H := fun u => (1 - (Z u)ᴴ * Z u)⁻¹) (z := x)
      (isUnit_nonsing_inv_det _ hx) h).symm
  have he : (fun x => conn (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ) =ᶠ[𝓝 w]
      fun x => ((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ :=
    ((hA w).eventually_isUnit hu).mono fun x hx => hconn x hx
  have hI : MContDiffAt 1 (fun x => (1 - (Z x)ᴴ * Z x)⁻¹) w := ((hA w).of_le one_le_two).inv hu
  have h1 : MContDiffAt 1 (fun u => Z u) w := mContDiffAt_linear Z w
  rw [curv, mdbar_congr he, mdbar_transpose (fun x => (1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ),
    mdbar_mul (A := fun x => (1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ) (B := fun _ => Z ξ)
      (hI.mul h1.conjTranspose) (mContDiffAt_const (Z ξ)), mdbar_const, Matrix.mul_zero, zero_add,
    mdbar_mul (A := fun x => (1 - (Z x)ᴴ * Z x)⁻¹) (B := fun x => (Z x)ᴴ) hI h1.conjTranspose,
    mdbar_inv ((hA w).of_le one_le_two) hu, mdbar_one_sub_gram, mdbar_conjTranspose, mdel_linear,
    inv_one_sub_mul_conjTranspose (Z w) hu]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg, Matrix.mul_assoc]

end ModelCurv

theorem curv_modelGram_tauBar : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)
    (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef →
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ :=
  fun Z w ξ η hw => curv_inv_one_sub_gram Z w ξ η hw

end GlobalTheory.PointChern
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.principalPolarization_of_mumfordBundle_siegelFibre : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (K : Type) [Field K] (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A y α → IsSquare α α₂ → ∀ L : LB B.left, L.IsLB → Rigidified B L → Out.Sym B L → LBIso (abelian₂ B L) (F.univ.P.pull α₂) → IsAbelianScheme B ∧ RelAmple B L ∧ KTriv B L := by
  first | exact @GlobalTheory.SiegFibrePol.polAV_of_lam_univ | exact GlobalTheory.SiegFibrePol.polAV_of_lam_univ | (intros; apply GlobalTheory.SiegFibrePol.polAV_of_lam_univ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameLift

open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ShFam.SecFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)
  {Tau : Type} (κ : Tau ≃ X.Ψ)

theorem analyticAt_frameAt [Fintype Tau] (τ : X.Ψ) (a b : Fin r) (v₀ : Tau × Fin j × Fin (r - j) → ℂ) :
    AnalyticAt ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ => mat (frameAt X hj κ (unflat v)) τ a b) v₀ := by
  have hM : ∀ c, AnalyticAt ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ =>
      ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b) v₀ := by
    intro c
    simp only [reindex_symm, reindex_apply, Equiv.symm_symm, submatrix_apply]
    rcases (idx hj) c with c' | c' <;> rcases (idx hj) b with b' | b' <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, unflat, of_apply] <;>
      first | exact analyticAt_const | exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Tau × Fin j × Fin (r - j) => ℂ) _).analyticAt _
  simp only [mat_frameAt, Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.fun_mul (hM c)

end GlobalTheory.FrameLift


open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ShFam.SecFrame in
theorem GlobalTheory.FrameLift.exists_analytic_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p q n : ℕ) (Xd : ReciprocityTheory.ChartRestriction.G.FD.Data E (p + q)), Xd.p0 = p + q - p → ∀ (h : Fintype.card (Xd.Ψ × Fin p × Fin (p + q - p)) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat Xd.Ψ p (p + q - p) → ∃ s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame Xd.Ψ (p + q), AnalyticAt ℂ s v ∧ (∀ (τ : Xd.Ψ) (a b : Fin p), AnalyticAt ℂ (fun w => coW Xd (Nat.le_add_right p q) (s w) τ a b) v) ∧ ∀ᶠ w in nhds v, ∃ hs : s w ∈ Xd.dom, flat (domPt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w := by
  intro E _ _ _ p q n Xd hp h v hv
  refine ⟨fun w => frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (unflat (GlobalTheory.UnifDens.flatL h w)), ?_, ?_, ?_⟩
  · rw [analyticAt_pi_iff]; intro τ
    rw [analyticAt_pi_iff]; intro a
    rw [analyticAt_pi_iff]; intro b
    have hL : AnalyticAt ℂ (GlobalTheory.UnifDens.flatL h) v := (GlobalTheory.UnifDens.flatL h).toContinuousLinearMap.analyticAt v
    exact (GlobalTheory.FrameLift.analyticAt_frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) τ a b
      (GlobalTheory.UnifDens.flatL h v)).comp hL
  · intro τ a b
    have e : (fun w => coW Xd (Nat.le_add_right p q)
        (frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (unflat (GlobalTheory.UnifDens.flatL h w))) τ a b) =
        fun _ => (1 : Matrix (Fin p) (Fin p) ℂ) a b := by
      funext w; rw [(co_frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) _ τ).1]
    rw [e]; exact analyticAt_const
  · have ho : IsOpen (DomFlat Xd.Ψ p (p + q - p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
    filter_upwards [(GlobalTheory.UnifDens.flatL h).continuous.continuousAt.preimage_mem_nhds (ho.mem_nhds hv)] with w hw
    refine ⟨frameAt_mem Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) hp hw, ?_⟩
    rw [domPt_frameAt]
    rfl
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.FlagPull

theorem frames_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z) (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → ∀ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn), Tied e C.Y C.π C.f0 E' A₁ → f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → ∀ z', ∀ A' ∈ E'.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf C.Y).O z').toSubring (A' * (A.map φ)⁻¹) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hc0 z' A' hA' A hA
  change C.Y.X at z'
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hT'.1
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  have hmapd : ∀ {B : Mat Dw.mult X.Fn}, (∀ τ, (B τ).det ≠ 0) →
      ∀ τ, (B.map φ τ).det ≠ 0 := fun {B} hB τ => by
    have := Mat.det_map B (φ : X.Fn →+* C.Y.Fn) τ
    rw [show B.map φ = B.map (φ : X.Fn →+* C.Y.Fn) from rfl, this]; exact (map_ne_zero _).2 (hB τ)
  obtain ⟨φ₁, fA, hfA⟩ := hT.2 (f z') A hA
  obtain ⟨φ', f', hf'⟩ := hT'.2 z' A' hA'
  let aY : C.Y.X.presheaf.stalk z' →+* C.Y.Fn := algebraMap (C.Y.X.presheaf.stalk z') C.Y.X.functionField
  let aB : X.X.presheaf.stalk (f z') →+* X.Fn := algebraMap (X.X.presheaf.stalk (f z')) X.X.functionField
  let σ : X.X.presheaf.stalk (f z') →+* C.Y.X.presheaf.stalk z' := (f.stalkMap z').hom
  have hinj : Function.Injective aY := IsFractionRing.injective (C.Y.X.presheaf.stalk z') C.Y.X.functionField
  have hcomp : (φ : X.Fn →+* C.Y.Fn).comp aB = aY.comp σ :=
    RingHom.ext fun a => map_algebraMap_stalk hφ z' a
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hσ : spMap σ ≫ stalkPt X (f z') = stalkPt C.Y z' ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hx' : stalkPt C.Y z' ≫ C.π ≫ genι Z = spMap σ ≫ stalkPt X (f z') ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, reassoc_of% hσ]
  have hφ' : φ' = σ.comp φ₁ := by
    have h1 : aY.comp φ' = aY.comp (σ.comp φ₁) := by
      rw [← hf'.2.1, ← RingHom.comp_assoc, ← hcomp, RingHom.comp_assoc, ← hfA.2.1, hc]
    exact RingHom.ext fun a => hinj (RingHom.congr_fun h1 a)
  have hstA : fA.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ fA inferInstance
  obtain ⟨⟨G, hG, -⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA _ φ'
    (stalkPt C.Y z' ≫ C.π ≫ genι Z) σ inferInstance hstA hx' hφ').1 f'
  have hGd := hu G hG
  have h1 := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f' _ _ _ C.f0 σ aY G (A₁ * A'⁻¹) inferInstance hG hf'
  have h2 := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₀ _ _ _ C.f0 aB (φ : X.Fn →+* C.Y.Fn) _ _
    inferInstance hfA hc0
  rw [hcomp] at h2
  have hU := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (aY.comp σ) inferInstance hstA h1.1 h1.2.1).1 C.f0).1.unique h1 h2
  have e : (A₀ * A⁻¹).map (φ : X.Fn →+* C.Y.Fn) = A₀.map φ * (A.map φ)⁻¹ := by
    rw [Mat.map_mul, Mat.map_inv]; rfl
  have key : A₁ * (A'⁻¹ * G.map aY) = A₁ * (A.map φ)⁻¹ := by
    rw [← mul_assoc, hU, e, mul_assoc A₁, ← mul_assoc (A₀.map φ)⁻¹, Mat.inv_mul (hmapd hA₀d), one_mul]
  have hGm : G.map aY = A' * (A.map φ)⁻¹ := by
    calc G.map aY = A' * (A₁⁻¹ * (A₁ * (A'⁻¹ * G.map aY))) := by
          rw [← mul_assoc A₁⁻¹, Mat.inv_mul hA₁d, one_mul, ← mul_assoc, Mat.mul_inv hA'd, one_mul]
      _ = A' * (A.map φ)⁻¹ := by
          rw [key, ← mul_assoc A₁⁻¹, Mat.inv_mul hA₁d, one_mul]
  exact (GlobalTheory.ShFam.TieBase.par_zero_iff aY hinj _ (fun x => mem_O_ratOf) _).2 ⟨G, hGd, hGm.symm⟩

end GlobalTheory.LieBase.FlagPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.exists_constant_periodMarking_universalCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (n g' r k : ℕ) (ch : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g') (lam : (Fin n → ℂ) → Fin r → Fin g' → ℂ) (ρ : Fin g' → Fin r → ℂ), IsLogChart k ch ex lam ρ → ∃ (i : Fin Fu.n) (T₀ : (Fu.Di i).La ≃+ (Fin r → ℤ)), ∀ s ∈ logDom n k, ∀ (a : CxFr Z σ) (W : Letter Dw → Fin g' → ℂ), a.1 = ch.symm (logExp k s) → Dirs a (fun w => (ex a.1 w).left) W → ∃ (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La), Per Fu a i Q ∧ IsIsom (Fu.Di i) gm ∧ ∀ v, ∑ z, Q (gm v) z • W z = ∑ m, T₀ v m • lam s m := by
  first | exact @GlobalTheory.ShFam.Hor.Mark.exists_marking_const | exact GlobalTheory.ShFam.Hor.Mark.exists_marking_const | (intros; apply GlobalTheory.ShFam.Hor.Mark.exists_marking_const <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark


theorem _root_.GlobalTheory.T.mem_closure_sum_indecomposable_face_of_additive : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (∀ x y, InFace bar ψ lab β x → InFace bar ψ lab β y → InFace bar ψ lab β (x + y) ∧ ψ.evalZ (x + y) = ψ.evalZ x + ψ.evalZ y) → (∀ x, InFace bar ψ lab β x → ∃ n : ℤ, ψ.evalZ x = n) → (∀ x, InFace bar ψ lab β x → x ≠ 0 → 0 < ψ.evalZ x) → ∀ x, InFace bar ψ lab β x → x ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y} := by
  first | exact @GlobalTheory.PolFan.Mark.mem_closure_isIndec | exact GlobalTheory.PolFan.Mark.mem_closure_isIndec | (intros; apply GlobalTheory.PolFan.Mark.mem_closure_isIndec <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark


theorem _root_.GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) (X X₁ : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (s : X₁ →ₗ[O] X), (∀ a, r (s a) = a) → ∀ β : LinearMap.BilinForm ℤ X₁, IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β := by
  first | exact @GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff | exact GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff | (intros; apply GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff <;> assumption)
end
