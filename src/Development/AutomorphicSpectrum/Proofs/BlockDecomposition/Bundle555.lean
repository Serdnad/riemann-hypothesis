module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle361
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRight
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle013
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergent
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AutomorphicSpectrum.Proofs.JetProofs.ScalarOnComplement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle534
public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle510
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle535
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle528
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open PositivityTheory.Rg.Rsw.Em
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AlgStab

section Gen
variable {R : Type} [CommRing R] {a n : ℕ}

private noncomputable def twoSide [TopologicalSpace R] [IsTopologicalRing R] (h hi : Matrix (Fin a) (Fin a) R)
    (g gi : Matrix (Fin n) (Fin n) R) (h1 : h * hi = 1) (h2 : hi * h = 1) (g1 : g * gi = 1) (g2 : gi * g = 1) :
    Matrix (Fin a) (Fin n) R ≃ₜ Matrix (Fin a) (Fin n) R where
  toFun X := h * X * g
  invFun X := hi * X * gi
  left_inv X := by
    show hi * (h * X * g) * gi = X
    rw [Matrix.mul_assoc h, ← Matrix.mul_assoc hi, h2, Matrix.one_mul, Matrix.mul_assoc, g1, Matrix.mul_one]
  right_inv X := by
    show h * (hi * X * gi) * g = X
    rw [Matrix.mul_assoc hi, ← Matrix.mul_assoc h, h1, Matrix.one_mul, Matrix.mul_assoc, g2, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private theorem map_inv {S : Type} [CommRing S] (f : R →+* S) {x y : Matrix (Fin a) (Fin a) R} (h : x * y = 1) :
    x.map f * y.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

private theorem map_eq_one {S : Type} [CommRing S] (f : R →+* S) {e : R} (he : f e = 0) {x : Matrix (Fin a) (Fin a) R}
    (h : e • (x - 1) = x - 1) : x.map f = 1 := by
  have h0 : (x - 1).map f = 0 := by
    rw [← h]
    ext i j
    simp [he]
  rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)] at h0
  exact sub_eq_zero.1 h0

private noncomputable def famEquiv {T : Type} [Fintype T] (h hi : T → Matrix (Fin a) (Fin a) ℂ) (g gi : T → Matrix (Fin n) (Fin n) ℂ)
    (h1 : ∀ τ, h τ * hi τ = 1) (h2 : ∀ τ, hi τ * h τ = 1) (g1 : ∀ τ, g τ * gi τ = 1) (g2 : ∀ τ, gi τ * g τ = 1) :
    (T → Fin a → Fin n → ℂ) ≃L[ℝ] (T → Fin a → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X τ => (h τ * Matrix.of (X τ) * g τ : Matrix (Fin a) (Fin n) ℂ)
      invFun := fun X τ => (hi τ * Matrix.of (X τ) * gi τ : Matrix (Fin a) (Fin n) ℂ)
      map_add' := fun X Y => by
        funext τ
        show h τ * (Matrix.of (X τ) + Matrix.of (Y τ)) * g τ = h τ * Matrix.of (X τ) * g τ + h τ * Matrix.of (Y τ) * g τ
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        funext τ
        show h τ * (c • Matrix.of (X τ)) * g τ = c • (h τ * Matrix.of (X τ) * g τ)
        rw [Matrix.mul_smul, Matrix.smul_mul]
      left_inv := fun X => funext fun τ => (twoSide (h τ) (hi τ) (g τ) (gi τ) (h1 τ) (h2 τ) (g1 τ) (g2 τ)).left_inv (Matrix.of (X τ))
      right_inv := fun X => funext fun τ => (twoSide (h τ) (hi τ) (g τ) (gi τ) (h1 τ) (h2 τ) (g1 τ) (g2 τ)).right_inv (Matrix.of (X τ)) }

end Gen

private theorem schw {D : D7} (θ : InfFam D) {a n : ℕ} (h : GL (Fin a) (AE D)) (g : GL (Fin n) (AE D)) {Φ : Mx D a n → ℂ}
    (hΦ : Φ ∈ schwartzA θ a n) : (fun X => Φ (mm (mm h.1 X) g.1)) ∈ schwartzA θ a n := by
  induction hΦ using Submodule.span_induction with
  | zero => exact Submodule.zero_mem _
  | add f₁ f₂ _ _ i₁ i₂ => exact Submodule.add_mem _ i₁ i₂
  | smul c f _ i => exact Submodule.smul_mem _ c i
  | mem Φ hm =>
    obtain ⟨f, k, hk, rfl⟩ := hm
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := by first | infer_instance | exact GlobalTheory.AdelicU.isTopologicalRing_tens | exact isTopologicalRing_tens
    let ρ : D.what₂.Tau → (AE D →+* ℂ) := fun τ => (θ τ).comp (infPart D)
    let L := famEquiv (fun τ => h.1.map (ρ τ)) (fun τ => h.2.map (ρ τ)) (fun τ => g.1.map (ρ τ)) (fun τ => g.2.map (ρ τ))
      (fun τ => map_inv _ h.3) (fun τ => map_inv _ h.4) (fun τ => map_inv _ g.3) (fun τ => map_inv _ g.4)
    let H := twoSide (h.1.map (finPart D)) (h.2.map (finPart D)) (g.1.map (finPart D)) (g.2.map (finPart D))
      (map_inv _ h.3) (map_inv _ h.4) (map_inv _ g.3) (map_inv _ g.4)
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, fun y => k (H y),
      ⟨hk.1.comp_continuous H.continuous, hk.2.comp_homeomorph H⟩, ?_⟩
    funext X
    have e1 : (fun τ i j => compAt θ τ (mm (mm h.1 X) g.1) i j) = L (fun τ i j => compAt θ τ X i j) := by
      funext τ
      show (h.1 * X * g.1).map (ρ τ) = h.1.map (ρ τ) * X.map (ρ τ) * g.1.map (ρ τ)
      rw [Matrix.map_mul, Matrix.map_mul]
    have e2 : (fun i j => finPart D (mm (mm h.1 X) g.1 i j)) = H (fun i j => finPart D (X i j)) := by
      show (h.1 * X * g.1).map (finPart D) = h.1.map (finPart D) * X.map (finPart D) * g.1.map (finPart D)
      rw [Matrix.map_mul, Matrix.map_mul]
    show f (fun τ i j => compAt θ τ (mm (mm h.1 X) g.1) i j) * k (fun i j => finPart D (mm (mm h.1 X) g.1 i j)) = _
    rw [e1, e2]
    rfl

end GlobalTheory.CompanionTheory.AlgStab

open GlobalTheory.CompanionTheory.AlgStab in
theorem GlobalTheory.CompanionTheory.AlgStab.algStab : IdemEx → AlgStab := by
  intro _ D θ _ a n S e he h g hh hg Φ hΦ hG hC
  refine ⟨schw θ h g hΦ, fun X => ?_, ?_⟩
  · have hI : IntOff S (mm (mm h.1 X) g.1) ↔ IntOff S X := by
      refine forall_congr' fun v => forall_congr' fun hv => ?_
      have h0 : cv D v e = 0 := by rw [he.2 v, if_neg hv]
      have : (h.1 * X * g.1).map (cv D v) = X.map (cv D v) := by
        rw [Matrix.map_mul, Matrix.map_mul, map_eq_one _ h0 hh, map_eq_one _ h0 hg, Matrix.one_mul, Matrix.mul_one]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      rw [show cv D v (mm (mm h.1 X) g.1 i j) = cv D v (X i j) from congrFun (congrFun this i) j]
    have hs : e • mm (mm h.1 X) g.1 = mm (mm h.1 (e • X)) g.1 := by
      show e • (h.1 * X * g.1) = h.1 * (e • X) * g.1
      rw [Matrix.mul_smul, Matrix.smul_mul]
    have := hG (mm (mm h.1 X) g.1)
    by_cases hX : IntOff S X
    · rw [if_pos (hI.2 hX), hs] at this
      rw [if_pos hX]
      exact this
    · rw [if_neg (fun c => hX (hI.1 c))] at this
      rw [if_neg hX]
      exact this
  · haveI : IsTopologicalRing (AE D) := by first | infer_instance | exact GlobalTheory.AdelicU.isTopologicalRing_tens | exact isTopologicalRing_tens
    exact hC.comp_homeomorph (twoSide h.1 h.2 g.1 g.2 h.3 h.4 g.3 g.4)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem isRho_right {D : D7} {p : ℕ} {f : G D p → ℂ} (hf : IsRho f) (x : G D p) :
    IsRho (fun g => f (g * x)) := by
  refine ⟨hf.1.comp (continuous_mul_const x), ?_⟩
  intro q hq a ha g
  have := hf.2 q hq a ha (g * x)
  simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.MuC
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.KmIwahori

open GlobalTheory.CompanionTheory.HeckeJacquet (mem_Km_iff val_unif_lt_one)
open GlobalTheory.LocGL.IwahoriFactor (one_same one_ne)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) {M : Matrix (Fin N) (Fin N) k}
    (h : ∀ i j, valuation k (M i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
      valuation k (((Zls.unifU k : kˣ) : k) ^ m)) :
    ∃ g ∈ Zls.Km k N m, g.val = M := by
  have hlt : valuation k (((Zls.unifU k : kˣ) : k) ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' (val_unif_lt_one k) (by omega)
  obtain ⟨g, -, hg⟩ := GlobalTheory.StepData.exists_mem_KOne (k := k) (n := Fin N) (M := M)
    fun i j => by
      rw [Matrix.sub_apply]
      exact (h i j).trans_lt hlt
  exact ⟨g, (mem_Km_iff N hm g).2 (by rw [hg]; exact h), hg⟩

variable {α : Type} {μ : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (μ a)]
  [∀ a, DecidableEq (μ a)]

theorem exists_mul_mem_parab {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) {x : GL (Fin N) k}
    (hx : x ∈ Zls.Km k N m) :
    ∃ c ∈ Zls.Km k N m ⊓ unipRadLower k e, x * c ∈ parab k e := by
  have hx' := (mem_Km_iff N hm x).1 hx
  have hA : ∀ a : α, ∃ y ∈ Zls.Km k N m, y.val =
      Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l := fun a =>
    exists_mem_Km hm fun i l => by
      simp only [Matrix.of_apply]
      split_ifs
      · exact hx' i l
      · simp
  choose y hy hyv using hA
  obtain ⟨c, hc, hcv⟩ := exists_mem_Km hm (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j)
    fun i j => (mem_Km_iff N hm _).1 (inv_mem (hy (blk e j))) i j
  have key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l) *
      c.val l j = (1 : Matrix (Fin N) (Fin N) k) i j := fun i j => by
    have := congrFun (congrFun (y (blk e j)).mul_inv i) j
    rw [Matrix.mul_apply, hyv] at this
    rw [hcv]
    exact this
  have h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix (Fin N) (Fin N) k) i j := fun i j h => by
    have := key i j
    simp only [if_neg h.not_gt] at this
    rwa [← Matrix.mul_apply, Matrix.one_mul] at this
  refine ⟨c, ⟨hc, (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩⟩,
    mem_parab_iff.2 fun a b i j h => ?_⟩
  · rw [h1 _ _ (by simpa using h.le), one_ne e h.ne]
  · rw [h1 _ _ (by simp), one_same]
  · have := key (e ⟨a, i⟩) (e ⟨b, j⟩)
    simp only [blk_apply, if_pos h] at this
    rw [Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']

theorem leviEmb_leviProj_mem_Km {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) (p : parab k e)
    (hp : (p : GL (Fin N) k) ∈ Zls.Km k N m) :
    leviEmb k e (leviProj k e p) ∈ Zls.Km k N m := by
  refine (mem_Km_iff N hm _).2 fun i j => ?_
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    have := (mem_Km_iff N hm _).1 hp (e ⟨a, i⟩) (e ⟨a, j⟩)
    simpa [leviEmb, Matrix.blockDiagonal'_apply_eq] using this
  · have hz : ((leviEmb k e (leviProj k e p) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
      simp [leviEmb, Matrix.blockDiagonal'_apply, h]
    rw [hz, one_ne e h]
    simp

theorem exists_factor {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) {x : GL (Fin N) k}
    (hx : x ∈ Zls.Km k N m) :
    ∃ a ∈ Zls.Km k N m ⊓ unipRadLower k e, ∃ b ∈ Zls.Km k N m ⊓ (leviEmb k e).range,
      ∃ c ∈ Zls.Km k N m ⊓ unipRad k e, x = a * b * c := by
  obtain ⟨c, hc, hp⟩ := exists_mul_mem_parab hm e (inv_mem hx)
  have hq : (x⁻¹ * c)⁻¹ ∈ parab k e := inv_mem hp
  have hqK : (x⁻¹ * c)⁻¹ ∈ Zls.Km k N m := inv_mem (mul_mem (inv_mem hx) hc.1)
  have hs : ∀ (g : Levi k μ) a (i j : μ a),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
        (g a : Matrix (μ a) (μ a) k) i j := by
    intro g a i j
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  have hn : ∀ (g : Levi k μ) {a b : α}, a ≠ b → ∀ (i : μ a) (j : μ b),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b h i j
    simp [leviEmb, Matrix.blockDiagonal'_apply, h]
  let p : parab k e := ⟨_, hq⟩
  have hL : leviEmb k e (leviProj k e p) ∈ parab k e :=
    mem_parab_iff.2 fun a b i j h => hn _ h.ne' i j
  let L : parab k e := ⟨_, hL⟩
  have hproj : leviProj k e L = leviProj k e p := by
    funext a
    ext i j
    simp only [leviProj_apply]
    exact hs _ _ _ _
  have hu : ((L⁻¹ * p : parab k e) : GL (Fin N) k) ∈ unipRad k e := by
    change ((L⁻¹ * p : parab k e) : GL (Fin N) k) ∈ (leviProj k e).ker.map (parab k e).subtype
    refine ⟨L⁻¹ * p, MonoidHom.mem_ker.2 ?_, rfl⟩
    rw [map_mul, map_inv, hproj, inv_mul_cancel]
  let u : GL (Fin N) k := ((L⁻¹ * p : parab k e) : GL (Fin N) k)
  have hqu : (x⁻¹ * c)⁻¹ = leviEmb k e (leviProj k e p) * u := by
    change (p : GL (Fin N) k) = (L : GL (Fin N) k) * ((L⁻¹ * p : parab k e) : GL (Fin N) k)
    simp
  have hd := leviEmb_leviProj_mem_Km hm e ⟨_, hq⟩ hqK
  refine ⟨c, hc, _, ⟨hd, ⟨_, rfl⟩⟩, u, ⟨?_, hu⟩, ?_⟩
  · have : u = (leviEmb k e (leviProj k e ⟨_, hq⟩))⁻¹ * (x⁻¹ * c)⁻¹ := by
      rw [eq_inv_mul_iff_mul_eq]
      exact hqu.symm
    show u ∈ Zls.Km k N m
    rw [this]
    exact mul_mem (inv_mem hd) hqK
  · rw [mul_assoc, ← hqu]
    group

theorem c0 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    PositivityTheory.Lbc.C0 k := by
  intro k _ _ _ _ N m h d hd hm
  exact ⟨GlobalTheory.CompanionTheory.HeckeKm.isOpen_Km N m, GlobalTheory.CompanionTheory.HeckeKm.isCompact_Km N m,
    fun x hx => exists_factor hm (stdBlocks d hd) hx⟩

end GlobalTheory.CompanionTheory.KmIwahori

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.height_function_continuous_pos' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x := by
  first | exact @GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos | exact GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos | (intros; apply GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.eisenstein_series_convergent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∃ σ₀ : ℝ, ∀ σ' : ℝ, σ₀ < σ' → ∃ (C : ℝ) (N : ℕ), ∀ x : G2 σ Y, Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') ∧ ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ σ' ≤ C * (ht2 x : ℝ) ^ N := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.godement_sum | exact GlobalTheory.CompanionTheory.GodementH.godement_sum | (intros; apply GlobalTheory.CompanionTheory.GodementH.godement_sum <;> assumption)
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Dblock.CompFrame

theorem exists_comp_frame : ∀ {n D : ℕ} (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin D) ℂ),
    Cᴴ * C = 1 → Cᴴ * Formalism.REAL.Jm ε * C = 0 →
    ∃ (m : ℕ) (R : Matrix (Fin n) (Fin m) ℂ) (ε' : Fin m → Bool),
      Rᴴ * R = 1 ∧ Formalism.REAL.Jm ε * R = R * Formalism.REAL.Jm ε' ∧ Cᴴ * R = 0 ∧
      C * Cᴴ + Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε + R * Rᴴ = 1 := by
  intro n D ε C h1 h2
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := GlobalTheory.CompanionTheory.HCSide.CentreNone.Jm_herm ε
  generalize hJ : Formalism.REAL.Jm ε = J at *
  have hAA : C * Cᴴ * (C * Cᴴ) = C * Cᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Cᴴ, h1, Matrix.one_mul]
  have hAB : C * Cᴴ * (J * C * Cᴴ * J) = 0 := by
    have e : C * Cᴴ * (J * C * Cᴴ * J) = C * (Cᴴ * J * C) * Cᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]; simp
  have hBA : J * C * Cᴴ * J * (C * Cᴴ) = 0 := by
    have e : J * C * Cᴴ * J * (C * Cᴴ) = J * C * (Cᴴ * J * C) * Cᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]; simp
  have hBB : J * C * Cᴴ * J * (J * C * Cᴴ * J) = J * C * Cᴴ * J := by
    have e : J * C * Cᴴ * J * (J * C * Cᴴ * J) = J * C * (Cᴴ * (J * J) * C) * Cᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e, hJJ, Matrix.mul_one, h1, Matrix.mul_one]
  have hPh : (1 - C * Cᴴ - J * C * Cᴴ * J)ᴴ = 1 - C * Cᴴ - J * C * Cᴴ * J := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose, hJh,
      Matrix.mul_assoc]
  have hPP : (1 - C * Cᴴ - J * C * Cᴴ * J) * (1 - C * Cᴴ - J * C * Cᴴ * J) =
      1 - C * Cᴴ - J * C * Cᴴ * J := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hAA, hAB, hBA, hBB]
    abel
  have hPJ : J * (1 - C * Cᴴ - J * C * Cᴴ * J) = (1 - C * Cᴴ - J * C * Cᴴ * J) * J := by
    have e1 : J * (J * C * Cᴴ * J) = C * Cᴴ * J := by
      simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    have e2 : J * C * Cᴴ * J * J = J * (C * Cᴴ) := by
      rw [Matrix.mul_assoc _ J J, hJJ, Matrix.mul_one, Matrix.mul_assoc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2]
    abel
  subst hJ
  obtain ⟨m, ε', R, r1, r2, r3⟩ := GlobalTheory.CompanionTheory.HCSide.CentreNone.exists_frame_J hPh hPP hPJ
  refine ⟨m, R, ε', r1, r3, ?_, ?_⟩
  · have hCP : Cᴴ * (1 - C * Cᴴ - Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) = 0 := by
      have e : Cᴴ * (Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) =
          (Cᴴ * Formalism.REAL.Jm ε * C) * Cᴴ * Formalism.REAL.Jm ε := by
        simp only [Matrix.mul_assoc]
      rw [Matrix.mul_sub, Matrix.mul_sub, e, h2, ← Matrix.mul_assoc, h1]
      simp
    have e : R = (1 - C * Cᴴ - Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) * R := by
      rw [← r2, Matrix.mul_assoc, r1, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, hCP, Matrix.zero_mul]
  · rw [r2]; abel

end GlobalTheory.CompanionTheory.Dblock.CompFrame
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.exists_highest_weight_in_invariant_submodule : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (G : Fin n → Fin n → Module.End ℂ H), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ N : Submodule ℂ H, N ≠ ⊥ → (∀ a b, ∀ w ∈ N, G a b w ∈ N) → ∃ (μ : Fin n → ℝ) (v : H), v ∈ N ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) G μ v := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.HwStable.exists_highest_of_stable | exact GlobalTheory.CompanionTheory.RealCountG.HwStable.exists_highest_of_stable | (intros; apply GlobalTheory.CompanionTheory.RealCountG.HwStable.exists_highest_of_stable <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_positive_hermitian_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (N : GL (Fin n) E),
  N.val.charpoly.Separable → (∀ τ : E →+* ℂ, ∀ z ∈ (N.val.charpoly.map τ).roots, ‖z‖ = 1) →
  ∃ H : Matrix (Fin n) (Fin n) E, IsUnit H.det ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
    N ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ ∀ τ : E →+* ℂ, (H.map τ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.TraceHerm.exists_posDef_herm | exact GlobalTheory.CompanionTheory.TraceHerm.exists_posDef_herm | (intros; apply GlobalTheory.CompanionTheory.TraceHerm.exists_posDef_herm <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped Pointwise ENNReal
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.ReproBessel

theorem finite_inter_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (Γ : Subgroup G) [DiscreteTopology Γ] {C : Set G} (hC : IsCompact C) : ((Γ : Set G) ∩ C).Finite := by
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have hK : IsCompact ((Γ : Set G) ∩ C) := hC.inter_left hcl
  have hΓ : DiscreteTopology (Γ : Set G) := inferInstanceAs (DiscreteTopology Γ)
  exact hK.finite ⟨DiscreteTopology.of_subset hΓ Set.inter_subset_left⟩

end GlobalTheory.CompanionTheory.ReproBessel
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.trace_factor_tensor_decomp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (I : Type) (W H : ι → Type) [AddCommGroup I] [Module ℂ I] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)] [FiniteDimensional ℂ I] [∀ i, FiniteDimensional ℂ (W i)] [∀ i, Nontrivial (W i)] (R : I ≃ₗ[ℂ] ∀ i, W i →ₗ[ℂ] H i) (F : I →ₗ[ℂ] I) (a : ∀ i, H i →ₗ[ℂ] H i) (b : ∀ i, W i →ₗ[ℂ] W i), (∀ x i, R (F x) i = a i ∘ₗ R x i ∘ₗ b i) → (∀ i, FiniteDimensional ℂ (H i)) ∧ LinearMap.trace ℂ I F = ∑ i, LinearMap.trace ℂ (W i) (b i) * LinearMap.trace ℂ (H i) (a i) := by
  first | exact @GlobalTheory.CompanionTheory.HomTrace.trace_of_block_sandwich | exact GlobalTheory.CompanionTheory.HomTrace.trace_of_block_sandwich | (intros; apply GlobalTheory.CompanionTheory.HomTrace.trace_of_block_sandwich <;> assumption)
end
