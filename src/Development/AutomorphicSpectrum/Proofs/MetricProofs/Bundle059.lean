module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameChangeUnitary
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle014
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodChartPotentialLeviForm
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle049
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ}

namespace LatEmb

variable (C : LatEmb F)

theorem perExt_eq_sum (R : RiemLat E g Λ) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R y = ∑ k, C.bas.repr y k • R.P (C.lam k) := by
  simp [perExt, Module.Basis.constr_apply_fintype]


omit [IsCMField E] in
theorem form_antisymm {M : Type} [AddCommGroup M] (f : M →ₗ[ℤ] M →ₗ[ℤ] ℤ) (hf : ∀ x, f x x = 0) (x y : M) :
    f x y = - f y x := by
  have h := hf (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, hf] at h
  linarith

theorem exists_dual (R : RiemLat E g Λ) (i : Fin (2 * g)) :
    ∃ z : Λ, ∀ k, R.form (C.lam k) z = if k = i then 1 else 0 := by
  obtain ⟨x, hx⟩ := R.unimod.2 (C.lam.coord i)
  refine ⟨-x, fun k => ?_⟩
  rw [map_neg, form_antisymm R.form R.alt, neg_neg, hx]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

theorem perExt_injective (R : RiemLat E g Λ) : Function.Injective (C.perExt R) := by
  apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change.perExt_injective <;> assumption

theorem perExt_bijective (R : RiemLat E g Λ) : Function.Bijective (C.perExt R) := by
  have hd : Module.finrank ℝ (Ψ → Fin (j + j') → ℂ) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_eq_card_basis C.bas]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  exact ⟨C.perExt_injective R, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 (C.perExt_injective R)⟩

def latPt (x : Λ) : Ψ → Fin (j + j') → ℂ := ∑ k, ((C.lam.repr x k : ℤ) : ℝ) • C.bas k

theorem perExt_latPt (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.latPt x) = R.P x := by
  have hb : ∀ k, C.perExt R (C.bas k) = R.P (C.lam k) := fun k => by
    simp [perExt, Module.Basis.constr_basis]

  conv_rhs => rw [← C.lam.sum_repr x, map_sum]
  unfold latPt

  rw [map_sum]
  simp only [map_smul, hb, Int.cast_smul_eq_zsmul, map_zsmul]


omit [NumberField E] in
theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply]

theorem cinv_mul {M : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (hu : Mᴴ * C.sgr τ * M = sgI j j') :
    C.cinv M τ * M = 1 := by
  unfold cinv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hu, sgI_mul_self]

theorem mul_cinv {M : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (hu : Mᴴ * C.sgr τ * M = sgI j j') :
    M * C.cinv M τ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (C.cinv_mul hu)

def aPart (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) : Fin (j + j') → ℂ :=
  A τ *ᵥ Sum.elim (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inl i)) 0

def bPart (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) : Fin (j + j') → ℂ :=
  A τ *ᵥ Sum.elim 0 (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inr i))

theorem aPart_add_bPart {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ}
    (hu : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j') (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) :
    C.aPart A y τ + C.bPart A y τ = y τ := by
  unfold aPart bPart
  rw [← mulVec_add]
  have h : (Sum.elim (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inl i)) (0 : Fin j' → ℂ) +
      Sum.elim (0 : Fin j → ℂ) (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inr i)) : Sg j j' → ℂ) =
      C.cinv (A τ) τ *ᵥ y τ := by
    ext (i | i) <;> simp
  rw [h, mulVec_mulVec, C.mul_cinv (hu τ), one_mulVec]

def cxStr (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) : Fin (j + j') → ℂ :=
  (-Complex.I) • C.aPart A y τ + Complex.I • C.bPart A y τ


open Classical in
theorem perExt_single_I_of_pPart (R : RiemLat E g Λ) (τ : Ψ) (w : Fin (j + j') → ℂ) (h : C.pPart R τ w = 0) :
    C.perExt R (Pi.single τ (Complex.I • w)) = (-Complex.I) • C.perExt R (Pi.single τ w) := by
  have h2 := (smul_eq_zero.1 h).resolve_left (by norm_num)
  rw [sub_eq_zero.1 h2, smul_smul]
  simp


open Classical in
theorem perExt_single_I_of_pBar (R : RiemLat E g Λ) (τ : Ψ) (w : Fin (j + j') → ℂ) (h : C.pBar R τ w = 0) :
    C.perExt R (Pi.single τ (Complex.I • w)) = Complex.I • C.perExt R (Pi.single τ w) := by
  have h2 := (smul_eq_zero.1 h).resolve_left (by norm_num)
  rw [eq_neg_of_add_eq_zero_left h2, smul_neg, smul_smul]
  simp


open Classical in
theorem perExt_single_cxStr {R : RiemLat E g Λ} {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A)
    (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) :
    C.perExt R (Pi.single τ (C.cxStr A y τ)) = Complex.I • C.perExt R (Pi.single τ (y τ)) := by
  have ha := C.perExt_single_I_of_pPart R τ (C.aPart A y τ) (hA.ker τ _)
  have hb := C.perExt_single_I_of_pBar R τ (C.bPart A y τ) (hA.kerBar τ _)
  have hy : C.perExt R (Pi.single τ (y τ)) =
      C.perExt R (Pi.single τ (C.aPart A y τ)) + C.perExt R (Pi.single τ (C.bPart A y τ)) := by
    rw [← map_add (f := _), ← Pi.single_add, C.aPart_add_bPart hA.unit]
  unfold cxStr
  rw [neg_smul, Pi.single_add, map_add (f := _), Pi.single_neg, map_neg, ha, hb, hy, smul_add]
  simp


open Classical in
theorem perExt_eq_sum_single (R : RiemLat E g Λ) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R y = ∑ τ, C.perExt R (Pi.single τ (y τ)) := by

  rw [← map_sum, Finset.univ_sum_single]

theorem perExt_cxStr {R : RiemLat E g Λ} {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A)
    (y : Ψ → Fin (j + j') → ℂ) : C.perExt R (C.cxStr A y) = Complex.I • C.perExt R y := by
  classical
  rw [C.perExt_eq_sum_single R (C.cxStr A y), C.perExt_eq_sum_single R y, Finset.smul_sum]
  exact Finset.sum_congr rfl fun τ _ => C.perExt_single_cxStr hA y τ

theorem eqvBy_of_adapted (R R' : RiemLat E g Λ) {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ}
    (hA : C.IsAdapted R A) (hA' : C.IsAdapted R' A) : R.EqvBy R' 1 := by
  let eL := LinearEquiv.ofBijective (C.perExt R) (C.perExt_bijective R)
  let eL' := LinearEquiv.ofBijective (C.perExt R') (C.perExt_bijective R')
  let φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := eL.symm.trans eL'
  have hφL : ∀ y, φ (C.perExt R y) = C.perExt R' y := by
    intro y
    have h : eL.symm (C.perExt R y) = y := eL.symm_apply_apply y
    show eL' (eL.symm (C.perExt R y)) = _
    rw [h]
    rfl
  have hI : ∀ z, φ (Complex.I • z) = Complex.I • φ z := by
    intro z
    obtain ⟨y, rfl⟩ := (C.perExt_bijective R).2 z
    rw [← C.perExt_cxStr hA, hφL, hφL, C.perExt_cxStr hA']
  have hz : ∀ (c : ℂ) (w : Fin g → ℂ), c • w = c.re • w + c.im • (Complex.I • w) := by
    intro c w
    ext k
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hs : ∀ (c : ℂ) z, φ (c • z) = c • φ z := by
    intro c z
    rw [hz c z, map_add (f := _), map_smul, map_smul, hI, ← hz]
  refine ⟨{ toFun := φ, invFun := φ.symm, left_inv := φ.left_inv, right_inv := φ.right_inv,
            map_add' := φ.map_add, map_smul' := hs }, fun x => ?_⟩
  show R'.P x = φ (R.P x)
  rw [← C.perExt_latPt R x, hφL, C.perExt_latPt]

end LatEmb

theorem adapted_eqvBy (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ)
    (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ)
    (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (_ : R.form = F.form) (_ : R'.form = F.form)
    (hA : C.IsAdapted R A) (hA' : C.IsAdapted R' A) : R.EqvBy R' 1 :=
  C.eqvBy_of_adapted R R' hA hA'

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem r_combine : PullbackStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (Amp : HermLine ι) (β : MRing ι) (b : K → ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : AnSys D σ) (π₁ : R.X → S₁.X) (π₂ : R.X → S₂.X) (h₁ : HoloMap R.A S₁.A π₁) (h₂ : HoloMap R.A S₂.A π₂), IsPotential R.A (potOf R Amp) → IsPosPot R.A (potOf R Amp) → IsMultiHomog β b → β ∉ P → (∀ z ∈ mcPts P, evC z β = 0 → z ∈ mcPts J) → (∀ x, π₁ x ∈ bdry S₁.s → evC (R.lift x x) β = 0) → (∀ x, π₂ x ∈ bdry S₂.s → evC (R.lift x x) β = 0) → ∃ (L : LocPot R.X) (s : R.X → R.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set R.X) (C₅ C t₀ : ℝ), IsPotential R.A L ∧ IsSection R.A L s ∧ IsSNC R.A L s m W ∧ (∀ y, logNormSec L s y ≤ 0) ∧ (∀ x, x ∈ bdry s ↔ evC (R.lift x x) β = 0) ∧ t₀ ≤ S₁.t₀ ∧ t₀ ≤ S₂.t₀ ∧ (∀ a, IsSingWeight R.A L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁) C t₀ ∧ IsRegFamilyC2 R.A s (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁)) ∧ ∀ a, IsSingWeight R.A L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) C t₀ ∧ IsRegFamilyC2 R.A s (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) :=
  PositivityTheory.UnitarySelfGeneration.r_combine

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem arInt_conj : SheetIndepStatement → PtsIndepStatement → GoodProjExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → arInt P s (conjLine A) (fun j => conjLine (L j)) = arInt P s A L :=
  PositivityTheory.UnitarySelfGeneration.c_arint

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.embedded_resolution_ample_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsEmbedded R.A P R.U R.lift → ∃ Amp : HermLine ι, IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded | exact GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

theorem _root_.GlobalTheory.T.realisation_fibre_product_compatible : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (P : Ideal (MRing ι)) (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (D : ℕ) (σ₁ σ₂ : Type) (S₁ : PB.AnSys D σ₁) (S₂ : PB.AnSys D σ₂) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) (A₁ : HermLine ι₁) (A₂ : HermLine ι₂) (A₁' A₂' : HermLine ι), IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsPullHerm κ₁ v₁ A₁ A₁' → IsPullHerm κ₂ v₂ A₂ A₂' → (Re₁.ref a₁).a = A₁.a → (Re₂.ref a₂).a = A₂.a → (∀ x, Re₁.π x ∉ ReciprocityTheory.AnForm.P.bdry S₁.s → Real.log (A₁.h (Re₁.R.lift x x)) = Real.log ((Re₁.ref a₁).h (Re₁.R.lift x x)) + S₁.ph a₁ (Re₁.π x)) → (∀ x, Re₂.π x ∉ ReciprocityTheory.AnForm.P.bdry S₂.s → Real.log (A₂.h (Re₂.R.lift x x)) = Real.log ((Re₂.ref a₂).h (Re₂.R.lift x x)) + S₂.ph a₂ (Re₂.π x)) → IsMultiProjPrime P → IsoLineOn P {z | z ∈ mcPts P ∧ evC z β ≠ 0} A₁' A₂' → SameSing Re₁ Re₂ P κ₁ v₁ κ₂ v₂ β a₁ a₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.sameSing_of_isoLine | exact GlobalTheory.CompanionTheory.Ar.Cmp.sameSing_of_isoLine | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.sameSing_of_isoLine <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Pull

theorem realis_pullback : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (P J : Ideal (MRing ι)) (D : ℕ) (σ : Type) (S : AnSys D σ) (Re : Realis S (imageZ v₁ P)) (R : AnLogRes P J D), IsBlockMap κ₁ v₁ → IsArithVar P (D + 1) → AlgOver Re → ∃ (π : R.X → S.X) (hπ : HoloMap R.A S.A π), (∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁) ∧ (∀ a (ref' : HermLine ι), IsPullHerm κ₁ v₁ (Re.ref a) ref' → SamePot R.A Set.univ (potOf R ref') ((S.th a).pullback π hπ.1)) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → ∀ x, Real.log ((Re.line a t).h fun p => R.lift x x (v₁ p)) = Real.log ((Re.ref a).h fun p => R.lift x x (v₁ p)) + S.phT a t (π x)) ∧ ∃ (β : MRing ι) (b : K → ℕ), IsMultiHomog β b ∧ β ∉ P ∧ ∀ x, π x ∈ bdry S.s → evC (R.lift x x) β = 0 :=
  @PositivityTheory.UnitarySelfGeneration.r_pull

end GlobalTheory.CompanionTheory.Ar.Pull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.period_hermitian_type_compatibility : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ty P → Hm.IsHermitian → (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) → (∀ j k, ty j ≠ ty k → Hm j k = 0) ∧ (∀ (τ : E →+* ℂ) x y, hermForm Hm (tyPart ty τ (P x)) (tyPart ty τ (P y)) - star (hermForm Hm (tyPart ty (ComplexEmbedding.conjugate τ) (P x)) (tyPart ty (ComplexEmbedding.conjugate τ) (P y))) = 2 * Complex.I * τ (sesq D x y)) ∧ ∀ (r : ℕ) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (Matrix.of fun m n => sesq D (e m) (e n)).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component | exact GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

theorem sum_neg_mul_eq_sum_fundCo {Ψ : Type} [Fintype Ψ] {N : ℕ} (f : Ψ → Fin N → ℝ) (B R : Ψ × Fin N → ℝ)
    (h : ∀ τ i, R (τ, i) = -∑ k ∈ Finset.Iic i, B (τ, k)) :
    ∑ r : Ψ × Fin N, -f r.1 r.2 * B r = ∑ r : Ψ × Fin N, fundCo (f r.1) r.2 * R r := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e := sum_fundCo_mul_sum_Iic (f τ) fun k => B (τ, k)
  simp only [h, mul_neg, Finset.sum_neg_distrib, neg_mul]
  rw [e]

theorem weight_sub_log_sing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' : Option (RootIx D) → ℤ) (s : ℝ) (x : Or.Re.R.X), (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → scale s ≤ Sys.t₀ → Or.Re.π x ∈ Sys.open' → RM.weight (scale s) (lam - s • nu) s (Or.Re.R.lift x x) - Real.log (∏ r, (Or.sing r).h (Or.Re.R.lift x x) ^ n' (some r)) = s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) - s * ∑ r : RootIx D, fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) + ∑ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 * Sys.phT (some r) (scale s) (Or.Re.π x) - ∑ r : RootIx D, fundCo (lam r.1) r.2 * Sys.ph (some r) (Or.Re.π x) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or lam nu n' s x hn ht hop
  have hw := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  have ht0 : 0 < scale s := Real.exp_pos _
  have hreg : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h (Or.Re.R.lift x x)) +
      Sys.phT (some (τ, i)) (scale s) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((RM.x (scale s) (τ, k)).h (Or.Re.R.lift x x)) := fun τ i => by
    rw [← Or.fund_reg τ i (scale s) ht0 ht _ hw, Or.Re.line_eq (some (τ, i)) (scale s) ht0 ht x]
  have hsing : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h (Or.Re.R.lift x x)) +
      Sys.ph (some (τ, i)) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((Or.sing (τ, k)).h (Or.Re.R.lift x x)) :=
    fun τ i => Or.fund_sing τ i x hop
  have e1 := sum_neg_mul_eq_sum_fundCo (lam - s • nu)
    (fun r => Real.log ((RM.x (scale s) r).h (Or.Re.R.lift x x)))
    (fun r => Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) +
      Sys.phT (some r) (scale s) (Or.Re.π x)) hreg
  have e2 := sum_neg_mul_eq_sum_fundCo lam
    (fun r => Real.log ((Or.sing r).h (Or.Re.R.lift x x)))
    (fun r => Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) +
      Sys.ph (some r) (Or.Re.π x)) hsing
  have hlog : Real.log (∏ r, (Or.sing r).h (Or.Re.R.lift x x) ^ n' (some r)) =
      ∑ r : RootIx D, -lam r.1 r.2 * Real.log ((Or.sing r).h (Or.Re.R.lift x x)) := by
    rw [Real.log_prod fun r _ => zpow_ne_zero _ ((Or.sing r).pos _ hw.1).ne']
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.log_zpow, hn (some r)]
    rfl
  have hwt : RM.weight (scale s) (lam - s • nu) s (Or.Re.R.lift x x) =
      s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) +
        ∑ r : RootIx D, -(lam - s • nu) r.1 r.2 * Real.log ((RM.x (scale s) r).h (Or.Re.R.lift x x)) := by
    unfold RootModel.weight
    rw [Fintype.sum_option]
    rfl
  rw [hwt, hlog, e1, e2]
  have hco : ∀ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 = fundCo (lam r.1) r.2 - s * fundCo (nu r.1) r.2 := by
    intro r
    have : (lam - s • nu) r.1 = lam r.1 - s • nu r.1 := rfl
    rw [this, fundCo_sub, fundCo_smul]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  have hρ : ∑ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) =
      ∑ r : RootIx D, fundCo (lam r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) -
        ∑ r : RootIx D, s * (fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hco]
    ring
  rw [hρ]
  ring

end GlobalTheory.CompanionTheory.Ar.Small.Fund
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

theorem combLine_ref_a_eq_line_a : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)) (n₀ m : Option (RootIx D) → ℤ), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → (∀ r : RootIx D, (m (some r) : ℝ) = (Fx.kA * Fx.q' : ℕ) * fundCo (nu r.1) r.2) → m none = -(Fx.q' : ℤ) → (combLine Or.Re.ref m).a = (combLine (RM.line 1) n₀).a := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or nu n₀ m hn hn₀ hn₀' hm hm'
  funext k₁
  apply Int.cast_injective (α := ℝ)
  have hL : ∀ r : RootIx D, ((m (some r) * (Or.Re.ref (some r)).a k₁ : ℤ) : ℝ) =
      -(((Fx.kA * Fx.q' : ℕ) : ℝ) * (fundCo (nu r.1) r.2 * ∑ k ∈ Finset.Iic r.2, (RM.xdeg (r.1, k) k₁ : ℝ))) := by
    rintro ⟨τ, i⟩
    rw [Or.fund_deg τ i]
    push_cast
    rw [hm (τ, i)]
    simp only [Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum, Nat.cast_mul]
    ring
  have hR : ∀ r : RootIx D, ((n₀ (some r) * (RM.line 1 (some r)).a k₁ : ℤ) : ℝ) =
      -(((Fx.kA * Fx.q' : ℕ) : ℝ) * (nu r.1 r.2 * (RM.xdeg r k₁ : ℝ))) := by
    intro r
    have h1 : (RM.line 1 (some r)).a = RM.xdeg r := RM.x_deg 1 r
    rw [h1, hn₀ r]
    push_cast
    have := hn r
    push_cast at this
    rw [this]
    ring
  have hsum : ∑ r : RootIx D, ((m (some r) * (Or.Re.ref (some r)).a k₁ : ℤ) : ℝ) =
      ∑ r : RootIx D, ((n₀ (some r) * (RM.line 1 (some r)).a k₁ : ℤ) : ℝ) := by
    simp only [hL, hR, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 2
    exact Finset.sum_congr rfl fun τ _ => sum_fundCo_mul_sum_Iic (nu τ) fun k => (RM.xdeg (τ, k) k₁ : ℝ)
  have hnone : (Or.Re.ref none).a k₁ = (RM.line 1 none).a k₁ := by
    rw [Or.ref_none.1]
    rfl
  simp only [combLine, Fintype.sum_option, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hm', hn₀', hnone]
  push_cast at hsum ⊢
  rw [hsum]

end GlobalTheory.CompanionTheory.Ar.Small.Fund
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.period_chart_potential_levi_form : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ (pot : Ψ × Fin N → LocPot X) (x : X) (V : Set X) (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ), IsPeriodChart A j pot x V g → ∀ k, x ∈ (A.chart k).source → ∃ Lm : (Fin e → ℂ) →ₗ[ℂ] (Ψ × Pairs N → ℂ), (∀ p, ContDiffAt ℝ 2 ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x)) ∧ (∀ (p : Ψ × Fin N) v, levi ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x) v = ∑ q : Pairs N, if q.1.1 ≤ p.2 ∧ p.2 < q.1.2 then (1 / 2 : ℝ) * ‖Lm v (p.1, q)‖ ^ 2 else 0) ∧ (IsFlagImmersionAt A g x → Function.Injective Lm) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.levi_diagonal_of_isPeriodChart | exact GlobalTheory.CompanionTheory.Ar.PB.levi_diagonal_of_isPeriodChart | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.levi_diagonal_of_isPeriodChart <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund


theorem _root_.GlobalTheory.T.local_multihomog_quotient_exists : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes (mCoordIdeal y) J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ ε : Ω, (∀ x : R.X, ∃ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg ∧ IsMultiHomog Hf dh ∧ (∀ k, (dg k : ℤ) = dh k + Eh.a k) ∧ aeval y G = ε * aeval y Hf ∧ aeval (R.lift x x) Hf ≠ (0 : ℂ)) → (∀ (x : R.X) (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → aeval y G = ε * aeval y Hf → aeval (R.lift x x) G ≠ (0 : ℂ) → aeval (R.lift x x) Hf ≠ (0 : ℂ) → π x ∈ S.open') → ∃ δ C : ℝ, 0 < δ ∧ ∀ x : R.X, π x ∈ S.open' → ∀ v : ℂ, HasVal y Eh.a ε (R.lift x x) v → v ≠ 0 → Real.log ‖v‖ - Real.log (Eh.h (R.lift x x)) ≤ -δ * rW S.L S.s (π x) + C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.GlobDecay.global_decay | exact GlobalTheory.CompanionTheory.Ar.Small.GlobDecay.global_decay | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.GlobDecay.global_decay <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.algebraic_square_intersection_pullback : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2), (∀ (L : Fin (d + 2) → HermLine ι) (L' : Fin (d + 2) → HermLine Q.ιW) (N : HermLine Q.ιW), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm (Q.κ 0) (Q.v 0) (L j) (L' j)) → IsSmoothHerm N → II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc L' N) = (N.a (Q.κ 1 k₀) : ℝ) * II K ι P (d + 2) L) ∧ ∀ (L : Fin (d + 3) → HermLine ι) (L' : Fin (d + 3) → HermLine Q.ιW), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm (Q.κ 1) (Q.v 1) (L j) (L' j)) → II Q.KW Q.ιW Q.PW (d + 3) L' = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.algebraic_square_intersection_pullback | exact GlobalTheory.CompanionTheory.Relay.algebraic_square_intersection_pullback | (intros; apply GlobalTheory.CompanionTheory.Relay.algebraic_square_intersection_pullback <;> assumption)
end
