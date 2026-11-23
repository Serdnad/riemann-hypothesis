module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle148
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle027
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsPreimmersionToNormalization
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusKernelTrivialSpreadsOpen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle040
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence

open ReciprocityTheory.AnForm.A (IsPsh)
open _root_.Metric

theorem isPsh_half {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℝ} (h : IsPsh U f) :
    IsPsh U (fun z => f z / 2) := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in 𝓝[U] z, f x < 2 * y := h.1 z hz (2 * y) (by simp only at hy; linarith)
    filter_upwards [h1] with x hx
    linarith
  · obtain ⟨h1, h2⟩ := h.2 z w hd
    have e : Real.circleAverage (fun ζ : ℂ => f (z + ζ • w) / 2) 0 1 =
        Real.circleAverage (fun ζ : ℂ => f (z + ζ • w)) 0 1 / 2 := by
      have := Real.circleAverage_fun_smul (c := 0) (R := 1) (a := (1 / 2 : ℝ)) (f := fun ζ : ℂ => f (z + ζ • w))
      simp only [smul_eq_mul] at this
      rw [show (fun ζ : ℂ => f (z + ζ • w) / 2) = fun ζ : ℂ => 1 / 2 * f (z + ζ • w) by
        funext ζ; ring, this]
      ring
    refine ⟨?_, ?_⟩
    · have : CircleIntegrable ((1 / 2 : ℝ) • fun ζ : ℂ => f (z + ζ • w)) 0 1 := h1.const_smul
      refine (circleIntegrable_congr (fun ζ _ => ?_)).1 this
      simp [div_eq_inv_mul]
    · rw [e]; linarith

def aff {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def affInv {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  ((ρ : ℂ)⁻¹ • (t - t₀)) ∘ π.symm

theorem aff_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    aff t₀ ρ π (affInv t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [aff, affInv, Function.comp, h]

theorem norm_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) {t : Fin n → ℂ}
    (ht : t ∈ ball t₀ ρ) : affInv t₀ ρ π t ∈ ball 0 1 := by
  rw [mem_ball, dist_eq_norm, sub_eq_add_neg] at ht
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖(t - t₀) (π.symm i)‖ < ρ := by
    have : ‖t + -t₀‖ < ρ := ht
    rw [pi_norm_lt_iff hρ] at this
    simpa [sub_eq_add_neg] using this (π.symm i)
  simp only [affInv, Function.comp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ]
  rw [inv_mul_lt_iff₀ hρ]
  simpa using h1

theorem affInv_add {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (z w : Fin n → ℂ) (ζ : ℂ) :
    affInv t₀ ρ π (z + ζ • w) = affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm) := by
  funext i
  simp [affInv, Function.comp]
  ring

theorem isPsh_comp_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n))
    {ψ : (Fin n → ℂ) → ℝ} (h : IsPsh (ball 0 1) ψ) : IsPsh (ball t₀ ρ) (fun t => ψ (affInv t₀ ρ π t)) := by
  have hc : Continuous (affInv t₀ ρ π) := by
    unfold affInv
    fun_prop
  refine ⟨h.1.comp (g := affInv t₀ ρ π) hc.continuousOn (fun t ht => norm_affInv t₀ hρ π ht), fun z w hd => ?_⟩
  have hd' : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm) ∈ ball 0 1 := by
    intro ζ hζ
    rw [← affInv_add]
    exact norm_affInv t₀ hρ π (hd ζ hζ)
  have e : (fun ζ : ℂ => ψ (affInv t₀ ρ π (z + ζ • w))) =
      fun ζ : ℂ => ψ (affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm)) := by
    funext ζ; rw [affInv_add]
  simp only [e]
  exact h.2 _ _ hd'

theorem exists_log_norm {n : ℕ} {t₀ : Fin n → ℂ} {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F t₀) (h0 : F t₀ ≠ 0) :
    ∃ r > (0 : ℝ), ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G (ball t₀ r) ∧
      ∀ t ∈ ball t₀ r, Real.log ‖F t‖ = (G t).re + Real.log ‖F t₀‖ := by
  have hH : AnalyticAt ℂ (fun t => F t / F t₀) t₀ := hF.div analyticAt_const h0
  have h1 : ∀ᶠ t in 𝓝 t₀, F t / F t₀ ∈ Complex.slitPlane := by
    have : F t₀ / F t₀ ∈ Complex.slitPlane := by rw [div_self h0]; exact Complex.one_mem_slitPlane
    exact hH.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds this)
  have h2 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ (fun t => F t / F t₀) t := hH.eventually_analyticAt
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨r, hr, fun t => Complex.log (F t / F t₀), fun t ht => ?_, fun t ht => ?_⟩
  · exact ((hb t ht).2.differentiableAt.clog (hb t ht).1).differentiableWithinAt
  · have hne : F t / F t₀ ≠ 0 := Complex.slitPlane_ne_zero (hb t ht).1
    have hFt : F t ≠ 0 := fun h => hne (by simp [h])
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hFt) (norm_ne_zero_iff.2 h0)]
    ring

theorem analyticAt_eval {A : Type} {n : ℕ} {q : (Fin n → ℂ) → A → ℂ} {t₀ : Fin n → ℂ}
    (hq : ∀ i, AnalyticAt ℂ (fun t => q t i) t₀) (p : MvPolynomial A ℤ) :
    AnalyticAt ℂ (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) t₀ := by
  apply GlobalTheory.CompanionTheory.Ar.Cusp.MuPsh.analyticAt_eval <;> assumption


open scoped ComplexOrder in
theorem gram_det_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) (hu : LinearIndependent ℂ u) :
    0 < (R.gram u).det.re := by
  apply GlobalTheory.CompanionTheory.Ar.Cusp.MuPsh.gram_det_pos <;> assumption

theorem hodgeInnerProduct_of_fibreLatticeVector {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) (tan : ∀ i, IsTanAt t.G z (v i)) (i j : A₀) :
    HodgeIP t.G t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j)) := by
  obtain ⟨A, _, φ, u, χ, h1, h2, -, -, -, h3⟩ := h
  obtain ⟨v', e', d'⟩ := h3 i
  obtain ⟨w', f', g'⟩ := h3 j
  exact ⟨t.PP.isLB, tan i, tan j, A, inferInstance, φ, g, u, R.Hm, χ, v', w', x i, x j, h1, h2, e', f', d', g', rfl⟩

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

theorem isOpen_offBd (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts) : IsOpen (offBd D a) := by
  have e : offBd D a = ball 0 1 ∩ ⋂ i : Fin (Fintype.card Ψ * D.j * (D.N - D.j)),
      {t | (i : ℕ) < (D.chart a).a → t i ≠ 0} := by
    ext t
    simp only [offBd, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    refine and_congr_right fun ht => ?_
    rw [(D.chart a).boundary t ht]
    push_neg
    rfl
  rw [e]
  refine isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : (i : ℕ) < (D.chart a).a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

end Free

end GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem torus_extension_generic : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 :=
  @PositivityTheory.Xgn.exists_split_torus_extension

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem pts_spread : ∀ (Z' S : Scheme.{0}) [IsIntegral Z'] (c : Z' ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ (m : ℕ) (P : Fin m → (Over.mk (j ≫ c) ⟶ G)), Function.Injective P → (∀ i, P i ^ 2 = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ x ⁻¹ᵁ V → ∃ Q : Fin m → (Over.mk (x ≫ c) ⟶ G), Function.Injective Q ∧ ∀ i, Q i ^ 2 = 1 := by
  exact @PositivityTheory.Xgn.two_torsion_points_spread_open

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ggeo

theorem normalisation_finite_cover :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (L : Type) [Field L] (z : Sp L ⟶ Z), GlobalTheory.IsGenericPointHom z → ∀ (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L'], ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (j : Sp L' ⟶ Z'), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap L L') ≫ z :=
  @PositivityTheory.Xgn.stratum_finite_normal_cover

end GlobalTheory.CompanionTheory.Ggeo
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.KerSpread

theorem injective_on_points_of_generic : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (G : Over Z') [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus Z' X ⟶ G) [IsMonHom u] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → (∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Z'), ⊤ ≤ a ⁻¹ᵁ V → ∀ t : Over.mk a ⟶ splitTorus Z' X, t ≫ u = 1 → t = 1 :=
  @PositivityTheory.Xgn.torus_kernel_trivial_spreads_open

end GlobalTheory.CompanionTheory.Ar.KerSpread
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

variable {X : Scheme.{0}}

structure FG (M : LB X) (Y : Scheme.{0}) where

  K : Type
  [fin : Fintype K]

  φ : K → (Y ⟶ X)

  ε : K → ℤ

  t : LB.Gen (LB.LinComb M φ ε)
  ht : t.IsGen

attribute [instance] FG.fin

namespace FG

variable {M : LB X} {Y Y' Z : Scheme.{0}}

def sum (a : FG M Y) (U : Type) [CommGroup U] (h : (Y ⟶ X) → U) : U := ∏ k, h (a.φ k) ^ a.ε k

def v (a : FG M Y) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) : (Z.presheaf.stalk z)ˣ := val a.t r z J

def one : FG M Y := ⟨PEmpty, PEmpty.elim, PEmpty.elim, LB.oneGen M, fun _ _ => (map_one _).trans
  ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm⟩

def mul (a b : FG M Y) : FG M Y :=
  ⟨a.K ⊕ b.K, Sum.elim a.φ b.φ, Sum.elim a.ε b.ε, LB.mulGen M _ _ _ _ a.t b.t,
    DVR.mulGen_isGen _ _ _ _ _ _ _ a.ht b.ht⟩

def inv (a : FG M Y) : FG M Y := ⟨a.K, a.φ, fun k => -a.ε k, LB.invGen M _ _ a.t, DVR.invGen_isGen _ _ _ _ a.ht⟩

def pull (a : FG M Y) (h : Y' ⟶ Y) : FG M Y' :=
  ⟨a.K, fun k => h ≫ a.φ k, a.ε, LB.pullGen M _ _ a.t h, DVR.pullGen_isGen _ _ _ _ a.ht h⟩

def pow (a : FG M Y) (n : ℕ) : FG M Y := Nat.rec one (fun _ b => b.mul a) n

theorem pow_zero' (a : FG M Y) : a.pow 0 = one := rfl

theorem pow_succ' (a : FG M Y) (n : ℕ) : a.pow (n + 1) = (a.pow n).mul a := rfl

variable (U : Type) [CommGroup U]

@[simp] theorem sum_one (h : (Y ⟶ X) → U) : (one : FG M Y).sum U h = 1 := by
  show ∏ k : PEmpty, _ = _
  exact Fintype.prod_empty _

@[simp] theorem sum_mul (a b : FG M Y) (h : (Y ⟶ X) → U) : (a.mul b).sum U h = a.sum U h * b.sum U h :=
  Fintype.prod_sum_type _

@[simp] theorem sum_inv (a : FG M Y) (h : (Y ⟶ X) → U) : a.inv.sum U h = (a.sum U h)⁻¹ :=
  (Finset.prod_congr rfl fun k _ => zpow_neg _ _).trans (Finset.prod_inv_distrib _)

@[simp] theorem sum_pull (a : FG M Y) (g : Y' ⟶ Y) (h : (Y' ⟶ X) → U) :
    (a.pull g).sum U h = a.sum U (fun q => h (g ≫ q)) := rfl

@[simp] theorem sum_pow (a : FG M Y) (n : ℕ) (h : (Y ⟶ X) → U) : (a.pow n).sum U h = a.sum U h ^ n := by
  induction n with
  | zero => simp [pow_zero']
  | succ n ih => simp [pow_succ', ih, pow_succ]

variable {z : Z} {J : (Z ⟶ X) → M.ι}

@[simp] theorem v_one (r : Z ⟶ Y) : (one : FG M Y).v r z J = 1 := val_one r

theorem v_mul (hJ : Good M z J) (a b : FG M Y) (r : Z ⟶ Y) : (a.mul b).v r z J = a.v r z J * b.v r z J :=
  val_mul hJ _ _ r

@[simp] theorem v_inv (a : FG M Y) (r : Z ⟶ Y) : a.inv.v r z J = (a.v r z J)⁻¹ := val_inv _ r

theorem v_pull (hJ : Good M z J) (a : FG M Y) (h : Y' ⟶ Y) (r : Z ⟶ Y') : (a.pull h).v r z J = a.v (r ≫ h) z J :=
  val_pull hJ _ h r

theorem v_pow (hJ : Good M z J) (a : FG M Y) (n : ℕ) (r : Z ⟶ Y) : (a.pow n).v r z J = a.v r z J ^ n := by
  induction n with
  | zero => simp [pow_zero']
  | succ n ih => rw [pow_succ', v_mul hJ, ih, pow_succ]

theorem exists_unit (hM : M.IsLB) (a : FG M Y) (h : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), a.sum U h = 1) :
    ∃ e : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J → a.v r z J = gm r z ⊤ e := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ := a.φ) (ε := a.ε) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ k => (h U k).trans (Fintype.prod_empty _).symm) a.t a.ht
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s (PEmpty.elim : PEmpty → M.ι)), fun Z r z J hJ => ?_⟩
  exact ((hv Z r z J hJ).symm.trans (val_of t r z J PEmpty.elim (fun k => k.elim))).trans (gm_res r z le trivial _).symm

theorem v_const (hM : M.IsLB) (a : FG M Y) (h : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), a.sum U h = 1)
    {S₀ : Scheme.{0}} (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom) {r r' : Z ⟶ Y} (e : r ≫ p = r' ≫ p)
    (hJ : Good M z J) : a.v r z J = a.v r' z J := by
  obtain ⟨c, hc⟩ := exists_unit hM a h
  obtain ⟨b, hb⟩ := hp c.val
  have key : ∀ r : Z ⟶ Y, (a.v r z J).val = gs (r ≫ p) z ⊤ b := fun r => by
    rw [hc Z r z J hJ, ← gs_unit r z ⊤ trivial, ← hb]
    exact gs_pull r p z ⊤ trivial b
  exact Units.ext ((key r).trans (by rw [e]; exact (key r').symm))

end FG

end GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

section Pts
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem left_pow {T : Over S} (a : T ⟶ G) (N : ℕ) : a.left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (a ^ N).left := by
  rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]

theorem one_left (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  have e : (1 : T ⟶ G) = toUnit T ≫ η[G] := Hom.one_def
  rw [e, Over.comp_left, eSec]
  congr 1

end Pts

def rigFG {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) : FG P.L (𝟙_ (Over S)).left :=
  ⟨PUnit, fun _ => eSec G, fun _ => 1, P.rig, P.rigGen⟩

@[simp] theorem sum_rigFG {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) (U : Type) [CommGroup U]
    (h : ((𝟙_ (Over S)).left ⟶ G.left) → U) : (rigFG P).sum U h = h (eSec G) := by
  show ∏ _k : PUnit, h (eSec G) ^ (1 : ℤ) = _
  simp

def mulFG {S : Scheme.{0}} {G : Over S} [GrpObj G] {M : LB G.left} {N : ℕ}
    (w : LB.Gen (LB.LinComb M (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)])) (hw : w.IsGen) :
    FG M G.left := ⟨Fin 2, _, _, w, hw⟩

theorem sum_mulFG {S : Scheme.{0}} {G : Over S} [GrpObj G] {M : LB G.left} {N : ℕ}
    (w : LB.Gen (LB.LinComb M (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)])) (hw : w.IsGen)
    (U : Type) [CommGroup U] (h : (G.left ⟶ G.left) → U) :
    (mulFG w hw).sum U h = h ((𝟙 G : G ⟶ G) ^ N).left * (h (𝟙 G.left) ^ (N ^ 2))⁻¹ := by
  show ∏ k : Fin 2, h ((![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) k) ^ (![1, -((N : ℤ) ^ 2)] : Fin 2 → ℤ) k = _
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]
  norm_cast

end GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl
theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap (f.comp g) = spMap f ≫ spMap g := by
  show Spec.map (CommRingCat.ofHom (f.comp g)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem gc_spMap {R : Type} [CommRing R] {F : Type} [Field F] (g : R →+* F) (z : Sp F) (t : R) :
    GlobalTheory.TwistLoc.gc (spMap g) z t = toStk z (g t) := by
  show gs (spMap g) z ⊤ _ = _
  rw [gs_eq _ z ⊤ trivial]
  show _ = ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (g t))
  exact congrArg _ (congrArg (fun φ => φ.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieProj

theorem lie_finite_projective_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), Module.Finite R L ∧ Module.Projective R L ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (L' : Type) [AddCommGroup L'] [Module R' L'] [Module R L'] [IsScalarTower R R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →ₗ[R] L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → IsBaseChange R' β :=
  @PositivityTheory.HtPt.Htat.lie_proj

end GlobalTheory.CompanionTheory.Ar.LieProj
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_embedding_open_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion (U.ι ≫ j) ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.EmbSub.openImmersion_translatesCover | exact GlobalTheory.CompanionTheory.Ar.BT.EmbSub.openImmersion_translatesCover | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.EmbSub.openImmersion_translatesCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.RegBase

theorem algebraMap_mem_regAt_of_base : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (s : X ⟶ Sp O), ξ ≫ s = spMap (algebraMap O Ω) → ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p := by
  intro X Ω _ ξ O _ _ s hs p o
  exact ⟨_, ConstReg.genMap_germ_const ξ s hs p o⟩

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.RegBase
end
