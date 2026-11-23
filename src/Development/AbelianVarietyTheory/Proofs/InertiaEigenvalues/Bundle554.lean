module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle528
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle527
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle546
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle530
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle339
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

theorem _root_.GlobalTheory.T.fockPolynomialSubstitution_commute_targetGlAction : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (Y : Matrix (Fin m) (Fin m) ℂ) (P : PolF D m n), fockSubst p g (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y P) = fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y (fockSubst p g P) := by
  first | exact @GlobalTheory.FockSubstComm.fockSubst_fockT | exact GlobalTheory.FockSubstComm.fockSubst_fockT | (intros; apply GlobalTheory.FockSubstComm.fockSubst_fockT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.coboundary_deRham_of_coboundary_semistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (c : ↥(GK K) → V) (z : V ⊗[ℚ_[l]] Bst P), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b := by
  first | exact @GlobalTheory.cocycle_dies_dR_of_dies_st | exact GlobalTheory.cocycle_dies_dR_of_dies_st | (intros; apply GlobalTheory.cocycle_dies_dR_of_dies_st <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.bdR_filtration_ker_theta_generator_facts : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → (∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n}) ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a) ∧ (∀ (n : ℕ) (z : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l n ↔ z ∈ Per.FilP l n) ∧ (∀ x : Per.BdR l, ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ))) ∧ (∀ (a : ℤ) (n : ℕ) (x : Per.BdR l), algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ n * x ∈ Per.FilD l (a + n) ↔ x ∈ Per.FilD l a) ∧ Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
  first | exact @GlobalTheory.MemLoc.seed_fil | exact GlobalTheory.MemLoc.seed_fil | (intros; apply GlobalTheory.MemLoc.seed_fil <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory.LieSkew

open GlobalTheory.ExpDeriv

theorem inner_integral_identity : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc hc0 f f' hf hf' hcf' hd H t
  exact GlobalTheory.T.inner_rightRegularRep_sub_eq_intervalIntegral_derivative Γ μ c hc hc0 hf hf' hcf' hd H t (GlobalTheory.T.integrable_conj_mul_translate_path' Γ μ c hc hf' hcf' H t)

theorem hasDerivAt_inner_R : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ H : L2 Γ μ, HasDerivAt (fun t => inner ℂ H (R Γ μ (c t) hf.toL2)) (inner ℂ H hf'.toL2) 0 := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc hc0 f f' hf hf' hcf' hd H
  have hk : Continuous fun s => inner ℂ H (R Γ μ (c s) hf'.toL2) :=
    continuous_const.inner ((continuous_R hf'.toL2).comp hc)
  have e : (fun t => inner ℂ H (R Γ μ (c t) hf.toL2)) =
      fun t => inner ℂ H hf.toL2 + ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
    funext t
    rw [← inner_integral_identity Γ μ c hc hc0 hf hf' hcf' hd H t, add_sub_cancel]
  rw [e]
  have := ((hk.integral_hasStrictDerivAt 0 0).hasDerivAt).const_add (inner ℂ H hf.toL2)
  simpa [hc0] using this

theorem inner_lie_eq_neg_inner_lie {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (μ : Measure (GA E N))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)
    (hW : _root_.GlobalTheory.CuspRep.IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (X : Lie E N) (φ ψ : W) :
    inner ℂ (toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩) (toL2ₗ μ W h ψ) =
      - inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩) := by
  set c : ℝ → GA E N := fun t => infGL E N (expGL X t) with hcdef
  have hc : Continuous c := by
    have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Matrix.of X) := by
      open scoped Matrix.Norms.Operator in
      exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    have hinv : ∀ t, (expGL X t)⁻¹ = expGL X (-t) := fun t =>
      (eq_inv_of_mul_eq_one_right (by rw [← expGL_add, add_neg_cancel, expGL_zero])).symm
    have he : Continuous (expGL X) := Units.continuous_iff.2 ⟨hv, by
      simp only [hinv, expGL_val]
      exact hv.comp continuous_neg⟩
    exact GlobalTheory.CuspQuot.continuous_infGL.comp he
  have hc0 : c 0 = 1 := by simp only [c, expGL_zero, map_one]
  have hcinv : ∀ t, c (-t) = (c t)⁻¹ := fun t => by
    simp only [c, ← map_inv]
    congr 1
    refine (eq_inv_of_mul_eq_one_right ?_)
    rw [← expGL_add, add_neg_cancel, expGL_zero]
  have hcont : ∀ θ ∈ W, Continuous (θ : GA E N → ℂ) := fun θ hθ =>
    ContAut.continuous_of_isOpen_stab E N θ (hA θ hθ).level
  set F := toL2ₗ μ W h φ
  set Ψ := toL2ₗ μ W h ψ
  set F' := toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩
  set Ψ' := toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩
  have dF := hasDerivAt_inner_R (latticeGL E N) μ c hc hc0 (h φ φ.2) (h _ (hW (.lie X) φ.1 φ.2))
    (hcont _ (hW (.lie X) φ.1 φ.2)) (fun x t => hasDerivAt_along X φ.1 x t) Ψ
  have dΨ := hasDerivAt_inner_R (latticeGL E N) μ c hc hc0 (h ψ ψ.2) (h _ (hW (.lie X) ψ.1 ψ.2))
    (hcont _ (hW (.lie X) ψ.1 ψ.2)) (fun x t => hasDerivAt_along X ψ.1 x t) F
  have d1 : HasDerivAt (fun t => inner ℂ (R (latticeGL E N) μ (c t) F) Ψ) (inner ℂ F' Ψ) 0 := by
    have := dF.star
    simp only [← starRingEnd_apply, inner_conj_symm] at this
    exact this
  have d2 : HasDerivAt (fun t => inner ℂ F (R (latticeGL E N) μ (c (-t)) Ψ)) (-inner ℂ F Ψ') 0 := by
    have h0 : HasDerivAt (fun t => inner ℂ F (R (latticeGL E N) μ (c t) Ψ)) (inner ℂ F Ψ') (-0) := by
      rw [neg_zero]; exact dΨ
    have := h0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simpa [Function.comp_def] using this
  have e : (fun t => inner ℂ (R (latticeGL E N) μ (c t) F) Ψ) =
      fun t => inner ℂ F (R (latticeGL E N) μ (c (-t)) Ψ) := by
    funext t
    let U : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
      ⟨(R (latticeGL E N) μ (c t)).toLinearMap, fun v => norm_R _ v⟩
    have hU : ∀ v, U v = R (latticeGL E N) μ (c t) v := fun _ => rfl
    have hΨ : R (latticeGL E N) μ (c t) (R (latticeGL E N) μ (c t)⁻¹ Ψ) = Ψ := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    calc inner ℂ (R (latticeGL E N) μ (c t) F) Ψ
        = inner ℂ (U F) (U (R (latticeGL E N) μ (c t)⁻¹ Ψ)) := by rw [hU, hU, hΨ]
      _ = inner ℂ F (R (latticeGL E N) μ (c t)⁻¹ Ψ) := U.inner_map_map _ _
      _ = _ := by rw [hcinv]
  rw [e] at d1
  exact d1.unique d2

theorem lie_skew : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hW : _root_.GlobalTheory.CuspRep.IsStable W), (∀ φ ∈ W, IsAutForm φ) → ∀ (X : Matrix (Fin N) (Fin N) (Cinf E)) (φ ψ : W), inner ℂ (toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩) (toL2ₗ μ W h ψ) = - inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩) := by
  intro E _ _ _ N μ _ _ W h hW hA X φ ψ
  exact inner_lie_eq_neg_inner_lie μ W h hW hA X φ ψ

end GlobalTheory.LieSkew
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.definiteSpace_forms_functional_principalType : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ),
      HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (fun h => l (R.extV i t y h)) := by
  first | exact @GlobalTheory.DefiniteType.hasType_extV | exact GlobalTheory.DefiniteType.hasType_extV | (intros; apply GlobalTheory.DefiniteType.hasType_extV <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.periodRingCore_crystalline_deRham_invariants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → C.InvB ∧ C.InvdR := by
  first | exact @GlobalTheory.MemLoc.fits_inv | exact GlobalTheory.MemLoc.fits_inv | (intros; apply GlobalTheory.MemLoc.fits_inv <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices


theorem _root_.GlobalTheory.T.exists_crystallineLetter_of_hodgeJump : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ a : ℤ, IsJumpV ((D.loc l).PD K) T.ρ τ a → ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∉ FilAt ((D.loc l).PD K) T τ (a + 1) := by
  first | exact @GlobalTheory.NL.JumpVec.exists_letter_of_jump | exact GlobalTheory.NL.JumpVec.exists_letter_of_jump | (intros; apply GlobalTheory.NL.JumpVec.exists_letter_of_jump <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices


theorem _root_.GlobalTheory.T.mem_wachN_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  first | exact @GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion | exact GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion | (intros; apply GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices


theorem _root_.GlobalTheory.T.wachN_invQPow_gamma_stable : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; let u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)); ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ k : ℕ, (∀ x : W.DD T, W.Q ^ k • x ∈ W.N T → W.Q ^ k • W.γ T x ∈ W.N T) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ w : PowerSeries ↥LL.1, PowerSeries.constantCoeff w = u ^ (-(k : ℤ)) ∧ ∀ (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T) (hγ : W.Q ^ k • W.γ T x ∈ W.N T) (j : ℤ), ex C h T i ζ ⟨W.Q ^ k • W.γ T x, hγ⟩ j = conv w (fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m) j := by
  first | exact @GlobalTheory.NL.GamQ.gam_Q_pow | exact GlobalTheory.NL.GamQ.gam_Q_pow | (intros; apply GlobalTheory.NL.GamQ.gam_Q_pow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.EtaleBasis

section Generic

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}

theorem repr_of_fixed (e : Module.Basis (Fin r) R M) (τ : R →+* R) (A : M →+ M)
    (hA : ∀ c x, A (c • x) = τ c • A x) (he : ∀ i, A (e i) = e i) (x : M) (i : Fin r) :
    e.repr (A x) i = τ (e.repr x i) := by
  have h : A x = ∑ k, τ (e.repr x k) • e k := by
    conv_lhs => rw [← e.sum_repr x]

    simp only [map_sum, hA, he]
  rw [h, e.repr_sum_self]

theorem isUnit_matrix (e : Module.Basis (Fin r) R M) (σ : R →+* R) (Φ : M →+ M)
    (hΦ : ∀ c x, Φ (c • x) = σ c • Φ x) (hs : Submodule.span R (Set.range Φ) = ⊤) :
    IsUnit (Matrix.of fun i j => e.repr (Φ (e j)) i : Matrix (Fin r) (Fin r) R) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  have hle : Submodule.span R (Set.range Φ) ≤ Submodule.span R (Set.range fun j => Φ (e j)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩

    rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [hΦ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  intro y
  have hy : e.equivFun.symm y ∈ Submodule.span R (Set.range fun j => Φ (e j)) :=
    hle (hs ▸ Submodule.mem_top)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  refine ⟨c, funext fun i => ?_⟩
  have h1 : e.equivFun (e.equivFun.symm y) i = y i := by rw [LinearEquiv.apply_symm_apply]
  rw [← h1, ← hc]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem change_basis (e : Module.Basis (Fin r) R M) (σ : R →+* R) (Φ : M →+ M)
    (hΦ : ∀ c x, Φ (c • x) = σ c • Φ x) (V F₁ : Matrix (Fin r) (Fin r) R) (hV : IsUnit V)
    (h : (Matrix.of fun i j => e.repr (Φ (e j)) i : Matrix (Fin r) (Fin r) R) * V.map σ = V * F₁) :
    ∃ e' : Module.Basis (Fin r) R M, (∀ j, e' j = ∑ i, V i j • e i) ∧
      ∀ i j, e'.repr (Φ (e' j)) i = F₁ i j := by
  obtain ⟨u, rfl⟩ := hV
  let L : M ≃ₗ[R] M := Matrix.toLinOfInv e e u.mul_inv u.inv_mul
  have hL : ∀ j, (e.map L) j = ∑ i, (u : Matrix (Fin r) (Fin r) R) i j • e i := by
    intro j
    simp [L, Matrix.toLinOfInv, Matrix.toLin_self]
  refine ⟨e.map L, hL, fun i j => ?_⟩
  have key : Φ ((e.map L) j) = ∑ k, F₁ k j • (e.map L) k := by
    apply e.repr.injective
    ext m
    have hm := congrFun (congrFun h m) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply] at hm

    simp [hL, map_sum, hΦ, map_smul, smul_eq_mul, Finsupp.single_apply]
    simpa only [mul_comm] using hm
  rw [key, Module.Basis.repr_sum_self]

end Generic

section Tensor

variable {O R N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup N] [Module O N]

theorem map_smul_semi (f : R →ₐ[O] R) (a : N →ₗ[O] N) (c : R) (x : R ⊗[O] N) :
    TensorProduct.map f.toLinearMap a (c • x) = f c • TensorProduct.map f.toLinearMap a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  | tmul b t => simp [TensorProduct.smul_tmul']

theorem span_range_map (f : R →ₐ[O] R) :
    Submodule.span R (Set.range (TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul b t =>
    have : b ⊗ₜ[O] t = b • TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) ((1 : R) ⊗ₜ[O] t) := by
      simp [TensorProduct.smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem map_comm (f g : R →ₐ[O] R) (h : ∀ c, f (g c) = g (f c)) (a : N →ₗ[O] N) (x : R ⊗[O] N) :
    TensorProduct.map g.toLinearMap a (TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) x) =
      TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) (TensorProduct.map g.toLinearMap a x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b t => simp [h]

theorem descend {r : ℕ} {ι : Type} (φ : R →ₐ[O] R) (g : ι → (R →ₐ[O] R)) (a : ι → (N →ₗ[O] N))
    (hc : ∀ s c, φ (g s c) = g s (φ c)) (S : Set R)
    (dec : ∀ F : Matrix (Fin r) (Fin r) R, IsUnit F → (∀ i j s, g s (F i j) = F i j) →
      ∃ V F₁ : Matrix (Fin r) (Fin r) R, IsUnit V ∧ (∀ i j s, g s (V i j) = V i j) ∧
        (∀ i j, F₁ i j ∈ S) ∧ F * V.map φ = V * F₁)
    (e : Module.Basis (Fin r) R (R ⊗[O] N))
    (he : ∀ s i, TensorProduct.map (g s).toLinearMap (a s) (e i) = e i) :
    ∃ e' : Module.Basis (Fin r) R (R ⊗[O] N),
      (∀ s i, TensorProduct.map (g s).toLinearMap (a s) (e' i) = e' i) ∧
      ∀ i j, e'.repr (TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[O] N) (e' j)) i ∈ S := by
  let Φ : R ⊗[O] N →+ R ⊗[O] N :=
    (TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[O] N)).toAddMonoidHom
  have hΦ : ∀ (c : R) x, Φ (c • x) = (φ : R →+* R) c • Φ x := map_smul_semi φ _
  obtain ⟨V, F₁, hV, hVg, hS, hE⟩ := dec _ (isUnit_matrix e φ Φ hΦ (span_range_map φ)) (by
    intro i j s
    have h1 := repr_of_fixed e (g s : R →+* R)
      (TensorProduct.map (g s).toLinearMap (a s)).toAddMonoidHom (map_smul_semi (g s) _) (he s) (Φ (e j)) i
    have h2 : (TensorProduct.map (g s).toLinearMap (a s)).toAddMonoidHom (Φ (e j)) = Φ (e j) := by
      have := map_comm φ (g s) (hc s) (a s) (e j)
      rw [he] at this
      exact this
    rw [h2] at h1
    exact h1.symm)
  obtain ⟨e', h1, h2⟩ := change_basis e φ Φ hΦ V F₁ hV hE
  refine ⟨e', fun s j => ?_, fun i j => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul_semi, hVg, he]
  · have := hS i j
    rw [← h2] at this
    exact this

end Tensor

theorem descend_lat {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (T : LocLat G Qp LL O) {r : ℕ} (φ : R →ₐ[O] R) (g : G → (R →ₐ[O] R)) (H : G → Prop)
    (hc : ∀ s c, φ (g s c) = g s (φ c)) (S : Set R)
    (dec : ∀ F : Matrix (Fin r) (Fin r) R, IsUnit F → (∀ i j s, H s → g s (F i j) = F i j) →
      ∃ V F₁ : Matrix (Fin r) (Fin r) R, IsUnit V ∧ (∀ i j s, H s → g s (V i j) = V i j) ∧
        (∀ i j, F₁ i j ∈ S) ∧ F * V.map φ = V * F₁)
    (e : Module.Basis (Fin r) R (TW R T)) (he : ∀ s, H s → ∀ i, TWact (g s) T s (e i) = e i) :
    ∃ e' : Module.Basis (Fin r) R (TW R T), (∀ s, H s → ∀ i, TWact (g s) T s (e' i) = e' i) ∧
      ∀ i j, e'.repr (TWmap φ T (e' j)) i ∈ S := by
  obtain ⟨e', h1, h2⟩ := descend (ι := {s : G // H s}) φ (fun s => g s.1) (fun s => T.actT s.1)
    (fun s c => hc s.1 c) S
    (fun F hU hfix => by
      obtain ⟨V, F₁, hV, hVf, hS, hE⟩ := dec F hU (fun i j s hs => hfix i j ⟨s, hs⟩)
      exact ⟨V, F₁, hV, fun i j s => hVf i j s.1 s.2, hS, hE⟩)
    e (fun s i => he s.1 s.2 i)
  exact ⟨e', fun s hs i => h1 ⟨s, hs⟩ i, h2⟩

theorem map_id_comm {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f g : W →ₐ[Z] W) (h : ∀ w, f (g w) = g (f w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f (Algebra.TensorProduct.map (AlgHom.id O O) g x) =
    Algebra.TensorProduct.map (AlgHom.id O O) g (Algebra.TensorProduct.map (AlgHom.id O O) f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a w => simp [h]

theorem frob_comm_gal {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l)
    (x : RW LL) : φRW LL (AI.gRW LL g x) = AI.gRW LL g (φRW LL x) := by
  refine map_id_comm _ _ (fun w => ?_) x
  ext n
  change (WittVector.map (frobenius (Cb l) l)
      (WittVector.map (autCb l (AI.actT g)).toRingHom w)).coeff n =
    (WittVector.map (autCb l (AI.actT g)).toRingHom (WittVector.map (frobenius (Cb l) l) w)).coeff n
  simp [WittVector.map_coeff, frobenius_def]

theorem fixH_iff {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) {LL : FinExt l}
    (x : RW LL) : FixH AI K x ↔ ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) x = x := by
  unfold FixH
  constructor
  · intro h g hχ
    exact h g.1 g.2 hχ
  · intro h g hg hχ
    have h1 := h ⟨g, hg⟩
    dsimp only at h1
    exact h1 hχ

theorem decomplete {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (hG : Good K s LL) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (hI : IoW I) (r : ℕ)
    (F : Matrix (Fin r) (Fin r) (RW LL)) (hU : IsUnit F)
    (hfix : ∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (F i j) = F i j) :
    ∃ V F₁ : Matrix (Fin r) (Fin r) (RW LL),
      IsUnit V ∧ (∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (V i j) = V i j) ∧
      (∀ i j, F₁ i j ∈ Set.range I.ioE) ∧ F * V.map (φRW LL) = V * F₁ := by
  have h0 : ∀ i j, FixH AI K (F i j) := fun i j => (fixH_iff AI K _).mpr (hfix i j)
  have h1 := GlobalTheory.T.etalePhiMatrix_decompletion_to_wach l P AI K s LL hG Γ R I hI r F hU h0
  obtain ⟨V, F', hV, hVf, hE⟩ := h1
  refine ⟨V, F'.map I.ioE, hV, fun i j => (fixH_iff AI K _).mp (hVf i j), ?_, hE⟩
  intro i j
  rw [Matrix.map_apply]
  exact Set.mem_range_self _

theorem exists_etBasis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ e : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (RW LL) (TW (RW LL) T), EtBasis I T e := by
  intro l _ P AI hF K s LL hG Γ R I hI T
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_cyclotomicKernelFixedBasis_wittTensorLattice l P AI hF K LL T
  unfold EtBasis FixBasis
  unfold FixBasis at he
  exact descend_lat T (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l)) (fun g => P.χQ (g : GQ l) = 1)
    (fun g c => frob_comm_gal AI LL (g : GQ l) c) (Set.range I.ioE)
    (decomplete AI K s LL hG Γ R I hI _) e he

end GlobalTheory.EtaleBasis
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_orthogonal_family_residue_zeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → (∀ i, μ i ≠ 0 ∧ ‖μ i‖ ≤ 1) → Antitone (fun i => ‖μ i‖) → (∀ i j, ‖μ i‖ < l * ‖μ j‖) → (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ i‖) → ∃ (y : Fin h → ℕ → Formalism.Per.Fl l) (j0 : Fin h) (r R : ℝ), 0 ≤ r ∧ r < 1 ∧ R < 1 ∧ (∀ a k, ‖sh (y a k)‖ ≤ R) ∧ (∀ k, ‖sh (y j0 k)‖ ≤ r) ∧ r ^ l ^ h < ‖sh (y j0 0)‖ ∧ ∀ i : Fin h, ∑ j, μ j * abelian₂ h i (y j) = 0 := by
  first | exact @GlobalTheory.CoreOrth.residue_zeros | exact GlobalTheory.CoreOrth.residue_zeros | (intros; apply GlobalTheory.CoreOrth.residue_zeros <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.min_jumpSum_le_jumpSum_of_totally_ramified : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B C : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) ≤ jumpSum (wild F L) ⊤ C := by
  first | exact @GlobalTheory.PMon.Ram.min_jumpSum_le_of_pow_mem_of_inertia_eq_top | exact GlobalTheory.PMon.Ram.min_jumpSum_le_of_pow_mem_of_inertia_eq_top | (intros; apply GlobalTheory.PMon.Ram.min_jumpSum_le_of_pow_mem_of_inertia_eq_top <;> assumption)
end
