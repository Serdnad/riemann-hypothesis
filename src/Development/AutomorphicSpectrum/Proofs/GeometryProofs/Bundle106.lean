module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_open {D : ℕ} {O : Set (Fin D → ℂ)}
    (hO : IsOpen O) (hne : O.Nonempty) (p : MvPolynomial (Fin D) ℂ)
    (h : ∀ b ∈ O, MvPolynomial.eval b p = 0) : p = 0 := by
  obtain ⟨b₀, hb₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO b₀ hb₀
  refine MvPolynomial.funext_set (fun i => Metric.ball (b₀ i) ε)
    (fun i => infinite_of_mem_nhds (b₀ i) (Metric.ball_mem_nhds _ hε)) fun x hx => ?_
  rw [map_zero]
  exact h x (hball (by rw [ball_pi _ hε]; exact hx))

theorem eq_zero_of_forall_points_eq_zero :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ)) (f : Fin D → A) (a : A), IsOpen O → O.Nonempty → (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0 := by
  intro A _ _ _ D _ O Ψ f a hO hne hΨ ha
  by_contra ha0
  have key : ∀ b ∈ O, ∀ p : MvPolynomial (Fin D) ℂ,
      Ψ b (MvPolynomial.aeval f p) = MvPolynomial.eval b p := by
    intro b hb p
    let φ : A →ₐ[ℂ] ℂ :=
      { Ψ b with commutes' := fun r => DFunLike.congr_fun (hΨ b hb).1 r }
    have h1 : φ.comp (MvPolynomial.aeval f) = MvPolynomial.aeval b := by
      ext i
      simpa [φ] using (hΨ b hb).2 i
    have h2 := DFunLike.congr_fun h1 p
    exact h2.trans (DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval b) p)
  have hind : AlgebraicIndependent ℂ f := by
    rw [algebraicIndependent_iff]
    intro p hp
    refine mvPolynomial_eq_zero_of_eval_eq_zero_on_open hO hne p fun b hb => ?_
    rw [← key b hb p, hp, map_zero]
  obtain ⟨e, he⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial D ℂ A
  have htr : Algebra.trdeg ℂ A = D := GlobalTheory.AffinePoints.trdeg_eq_of_etale e he
  have hbasis : IsTranscendenceBasis ℂ f :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simp [htr])
  haveI := hbasis.isAlgebraic
  obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic
    (R := Algebra.adjoin ℂ (Set.range f)) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ha0)
  have hmem : (r : A) ∈ (MvPolynomial.aeval f : MvPolynomial (Fin D) ℂ →ₐ[ℂ] A).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact r.2
  obtain ⟨p, hp⟩ := hmem
  have hp' : MvPolynomial.aeval f p = (r : A) := hp
  have hp0 : p = 0 := by
    refine mvPolynomial_eq_zero_of_eval_eq_zero_on_open hO hne p fun b hb => ?_
    have hrc : (r : A) = a * c := hc
    rw [← key b hb p, hp', hrc, map_mul, ha b hb, zero_mul]
  apply hr
  apply Subtype.ext
  rw [← hp', hp0, map_zero]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem inner_sum_left (core : InnerProductSpace.Core ℂ V) {I : Type} (s : Finset I)
    (c : I → ℂ) (u : I → V) (y : V) :
    core.inner (∑ l ∈ s, c l • u l) y = ∑ l ∈ s, (starRingEnd ℂ) (c l) * core.inner (u l) y := by
  classical
  have h0 : core.inner (0 : V) y = 0 := by
    have h := core.smul_left (0 : V) y 0
    simpa using h
  induction s using Finset.induction_on
  · simp only [Finset.sum_empty]
    exact h0
  · rename_i a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, core.add_left, core.smul_left, ih]

theorem inner_sum_right (core : InnerProductSpace.Core ℂ V) {I : Type} (s : Finset I)
    (c : I → ℂ) (u : I → V) (y : V) :
    core.inner y (∑ l ∈ s, c l • u l) = ∑ l ∈ s, core.inner y (u l) * c l := by

  rw [← core.conj_inner_symm, GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.inner_sum_left, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, Complex.conj_conj, core.conj_inner_symm, mul_comm]

theorem gram_change (core : InnerProductSpace.Core ℂ V) {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] (u : I → V) (w : J → V) (P : Matrix J I ℂ)
    (hw : ∀ j, w j = ∑ l, P j l • u l) :
    (Matrix.of fun a b => core.inner (w a) (w b)) =
      P.map (starRingEnd ℂ) * (Matrix.of fun a b => core.inner (u a) (u b)) * P.transpose := by
  ext a b
  rw [Matrix.of_apply, hw a, hw b, GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.inner_sum_left]
  simp only [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.inner_sum_right, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem norm_det_gram (core : InnerProductSpace.Core ℂ V) {I : Type} [Fintype I]
    [DecidableEq I] (u w : I → V) (P : Matrix I I ℂ)
    (hw : ∀ j, w j = ∑ l, P j l • u l) :
    ‖(Matrix.of fun a b => core.inner (w a) (w b)).det‖ =
      ‖P.det‖ ^ 2 * ‖(Matrix.of fun a b => core.inner (u a) (u b)).det‖ := by
  have hconj : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := by
    rw [RingHom.map_det]
    rfl
  rw [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.gram_change core u w P hw, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hconj, norm_mul, norm_mul, Complex.norm_conj]
  ring

noncomputable def blockMat {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i l =>
    Fin.lastCases (motive := fun _ => ℂ)
      (Fin.lastCases (motive := fun _ => ℂ) s d l)
      (fun j => Fin.lastCases (motive := fun _ => ℂ) 0 (C j) l) i

theorem det_blockMat {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ) :
    (blockMat C d s).det = s * C.det := by
  have hsub : (GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = C := by
    ext i j
    simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat, Fin.succAbove_last]
  have hsign : ((-1 : ℂ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  rw [Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc, hsub, hsign, _root_.one_mul]
  simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat]

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot

open GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot in
theorem GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_quot : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) (n : ℕ)
    (β : Fin (n + 1) → V) (x : Fin n → V) (xe : V) (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ),
    (∀ j, x j = ∑ l, C j l • β l.castSucc) → xe = ∑ l, d l • β l.castSucc + s • β (Fin.last n) → s ≠ 0 →
    (Matrix.of fun a b => core.inner (x a) (x b)).det ≠ 0 → (Matrix.of fun a b => core.inner (β a) (β b)).det ≠ 0 →
    (1 / 2) * (Real.log ‖(Matrix.of fun a b => core.inner ((Fin.snoc x xe : Fin (n + 1) → V) a)
        ((Fin.snoc x xe : Fin (n + 1) → V) b)).det‖ - Real.log ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖) =
      Real.log ‖s‖ + (1 / 2) * (Real.log ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ -
        Real.log ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖) := by
  intro V _ _ core n β x xe C d s hx hxe hs hGx hGβ
  have hy : ∀ j, (Fin.snoc x xe : Fin (n + 1) → V) j = ∑ l, GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s j l • β l := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, hxe, Fin.sum_univ_castSucc]
      simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat]
    · rw [Fin.snoc_castSucc, hx i, Fin.sum_univ_castSucc]
      simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat]
  have h1 : ‖(Matrix.of fun a b => core.inner ((Fin.snoc x xe : Fin (n + 1) → V) a)
        ((Fin.snoc x xe : Fin (n + 1) → V) b)).det‖ =
      ‖(GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s).det‖ ^ 2 * ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ :=
    GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.norm_det_gram core β _ (GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s) hy
  have h2 : ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖ =
      ‖C.det‖ ^ 2 * ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖ :=
    GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.norm_det_gram core (fun l => β l.castSucc) x C hx
  rw [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.det_blockMat] at h1
  have hx0 : ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖ ≠ 0 := norm_ne_zero_iff.mpr hGx
  have hC : ‖C.det‖ ≠ 0 := by
    intro h
    apply hx0
    rw [h2, h]
    simp
  have hβ' : ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖ ≠ 0 := by
    intro h
    apply hx0
    rw [h2, h, mul_zero]
  have hβ : ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ ≠ 0 := norm_ne_zero_iff.mpr hGβ
  have hs' : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  rw [h1, h2, norm_mul, mul_pow,
    Real.log_mul (mul_ne_zero (pow_ne_zero 2 hs') (pow_ne_zero 2 hC)) hβ,
    Real.log_mul (pow_ne_zero 2 hs') (pow_ne_zero 2 hC), Real.log_mul (pow_ne_zero 2 hC) hβ',
    Real.log_pow, Real.log_pow]
  push_cast
  ring
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem top_le_spMap_comp_iff {X : Scheme.{0}} (σ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (U : X.Opens) :
    ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  have hsub : ∀ a b : Sp ℂ, a = b := fun a b => Subsingleton.elim (α := PrimeSpectrum ℂ) a b
  constructor
  · intro h p _
    have hq : x.base ((spMap σ).base p) ∈ U := h (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    rwa [hsub ((spMap σ).base p) p] at hq
  · intro h p _
    exact h (show (spMap σ).base p ∈ (⊤ : (Sp ℂ).Opens) from trivial)

private theorem gammaSpecIso_appLE_spMap_apply (z : Γ(Sp ℂ, ⊤)) (σ : ℂ →+* ℂ)
    (e : (⊤ : (Sp ℂ).Opens) ≤ (spMap σ) ⁻¹ᵁ ⊤) :
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)
      ((CommRingCat.Hom.hom (Scheme.Hom.appLE (spMap σ) ⊤ ⊤ e)) z) =
    σ ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) z) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)
  exact congrArg (fun φ => CommRingCat.Hom.hom φ z) h

theorem valAt'_spMap_comp {X : Scheme.{0}} (σ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (spMap σ ≫ x) U f = σ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ U
  · have hc : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := (top_le_spMap_comp_iff σ x U).2 hx
    rw [dite_eq_left hc, dite_eq_left hx]
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
    rw [← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ hx (by simp)]
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    exact gammaSpecIso_appLE_spMap_apply _ σ _
  · have hc : ¬ ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun h => hx ((top_le_spMap_comp_iff σ x U).1 h)
    rw [dite_eq_right hc, dite_eq_right hx, map_zero]

private theorem differentiableOn_conj_comp_star {m : ℕ} {g : (Fin m → ℂ) → ℂ} {S : Set (Fin m → ℂ)}
    (hg : DifferentiableOn ℂ g S) :
    DifferentiableOn ℂ (fun b => starRingEnd ℂ (g (star b))) (star ⁻¹' S) := by
  intro b hb
  obtain ⟨L, hL⟩ := hg (star b) hb
  have h1 : HasFDerivWithinAt (star : (Fin m → ℂ) → (Fin m → ℂ))
      ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) (star ⁻¹' S) b :=
    ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt g (L.restrictScalars ℝ) S (star b) := hL.restrictScalars ℝ
  have h3 := h2.comp b h1 (fun y hy => hy)
  have hR := ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasFDerivWithinAt b h3
  let L' : (Fin m → ℂ) →L[ℂ] ℂ :=
    { toFun := fun v => star (L (star v))
      map_add' := fun v w => by simp [star_add, map_add (f := _)]
      map_smul' := fun c v => by simp [star_smul, map_smul]
      cont := continuous_star.comp (L.continuous.comp continuous_star) }
  exact ⟨L', HasFDerivWithinAt.of_restrictScalars (𝕜 := ℝ) hR (by ext v; rfl)⟩

theorem isHolTo_conj (X : Scheme.{0}) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (hy : IsHolTo B y) :
    IsHolTo (star ⁻¹' B) (fun b => spMap (starRingEnd ℂ) ≫ y (star b)) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo at hy ⊢
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hset : {b | b ∈ star ⁻¹' B ∧
        ⊤ ≤ (TopologicalSpace.Opens.map (spMap (starRingEnd ℂ) ≫ y (star b)).base).obj U}
      = star ⁻¹' {b | b ∈ B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (y b).base).obj U} := by
    ext b
    exact and_congr_right fun _ => top_le_spMap_comp_iff (starRingEnd ℂ) (y (star b)) U
  rw [hset]
  refine ⟨ho.preimage continuous_star, ?_⟩
  refine (differentiableOn_conj_comp_star hd).congr ?_
  intro b _
  exact valAt'_spMap_comp (starRingEnd ℂ) (y (star b)) U f

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end
