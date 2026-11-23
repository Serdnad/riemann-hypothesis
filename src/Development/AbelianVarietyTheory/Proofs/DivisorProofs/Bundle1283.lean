module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
import Development.WeilBound.ThetaLifts.LeviDeterminants.NormIteratedFDerivIdLeOneAdd
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle054
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158

@[expose] public section

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory

theorem exists_fractionalIdeal_smul_mem_lattice :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  apply GlobalTheory.latticeLine_fractionalIdeal <;> assumption

end GlobalTheory
end

section

open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.GaussDerivBound

open scoped Nat

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_id_le_one_add' (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (id : E → E) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | n
  · rw [norm_iteratedFDeriv_zero]; simp
  · rw [← norm_iteratedFDeriv_fderiv,
      show fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E from funext fun _ => fderiv_id]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iteratedFDeriv_diag_le' (B : E →L[ℝ] E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by
  apply PositivityTheory.ThKF0.Lib.norm_iteratedFDeriv_diag_le <;> assumption

theorem norm_iteratedFDeriv_rexp' (i : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_exp_const_mul i 1) y
  simp only [one_mul, one_pow] at h
  rw [show (fun s => Real.exp s) = Real.exp from rfl] at h
  rw [h, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem exists_bound_poly_mul_exp' (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-(c * r ^ 2)) ≤ C := by
  first
  | exact @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | (apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded ..)

theorem weighted_bound : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c α : ℝ), 0 < c → α < 1 → ∀ (k m : ℕ),
    ∃ K : ℝ, ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
      Real.exp (c * α * ‖y‖ ^ 2) ≤ K := by
  intro E _ _ c α hc hα k m
  set B : E →L[ℝ] E →L[ℝ] ℝ := (-c) • innerSL ℝ with hBdef
  have hBy : ∀ y : E, B y y = -(c * ‖y‖ ^ 2) := fun y => by
    simp [hBdef, real_inner_self_eq_norm_sq]
    left
    first | exact real_inner_self_eq_norm_sq y | simp [innerSL_apply, real_inner_self_eq_norm_sq] | rfl
  have hfun : (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) =
      Complex.ofRealLI ∘ (Real.exp ∘ fun y : E => B y y) := by
    funext y
    simp only [Function.comp_apply, Complex.ofRealLI_apply, hBy, Complex.ofReal_exp, Complex.ofReal_neg]
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Real.exp ∘ fun y : E => B y y) := Real.contDiff_exp.comp hq
  have hc' : 0 < c * (1 - α) := mul_pos hc (by linarith)
  obtain ⟨C, hC⟩ := exists_bound_poly_mul_exp' (c * (1 - α)) hc' (k + 2 * m)
  refine ⟨m ! * (2 * (‖B‖ + 1)) ^ m * C, fun x => ?_⟩
  have hn : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [hfun, LinearIsometry.norm_iteratedFDeriv_comp_left _ hg.contDiffAt hn]
  have hfb := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := fun y : E => B y y)
    Real.contDiff_exp hq hn x (C := Real.exp (B x x)) (D := 2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2)
    (fun i _ => (norm_iteratedFDeriv_rexp' i _).le) (fun i hi _ => by
      have hB0 := norm_nonneg B
      have hx0 := norm_nonneg x
      have a1 : ‖B‖ ≤ (‖B‖ + 1) ^ i :=
        le_trans (by linarith) (le_self_pow₀ (by linarith) (by omega))
      have a2 : (1 + ‖x‖) ^ 2 ≤ ((1 + ‖x‖) ^ 2) ^ i :=
        le_self_pow₀ (by nlinarith) (by omega)
      calc ‖iteratedFDeriv ℝ i (fun y : E => B y y) x‖ ≤ ‖B‖ * (2 ^ i * (1 + ‖x‖) ^ 2) :=
            norm_iteratedFDeriv_diag_le' B i x
        _ = 2 ^ i * ‖B‖ * (1 + ‖x‖) ^ 2 := by ring
        _ ≤ 2 ^ i * (‖B‖ + 1) ^ i * ((1 + ‖x‖) ^ 2) ^ i := by gcongr
        _ = (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ i := by rw [mul_pow, mul_pow])
  rw [hBy x] at hfb
  have hx0 := norm_nonneg x
  have hB0 := norm_nonneg B
  have hexp : Real.exp (-(c * ‖x‖ ^ 2)) * Real.exp (c * α * ‖x‖ ^ 2) =
      Real.exp (-(c * (1 - α) * ‖x‖ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (Real.exp ∘ fun y : E => B y y) x‖ * Real.exp (c * α * ‖x‖ ^ 2)
      ≤ (1 + ‖x‖) ^ k * (m ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ m) *
          Real.exp (c * α * ‖x‖ ^ 2) := by
        gcongr
        linarith
    _ = m ! * (2 * (‖B‖ + 1)) ^ m * ((1 + ‖x‖) ^ (k + 2 * m) *
          (Real.exp (-(c * ‖x‖ ^ 2)) * Real.exp (c * α * ‖x‖ ^ 2))) := by
        rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ m = (2 * (‖B‖ + 1)) ^ m * (1 + ‖x‖) ^ (2 * m) by
          rw [mul_pow, pow_mul], pow_add]; ring
    _ ≤ m ! * (2 * (‖B‖ + 1)) ^ m * C := by
        rw [hexp]
        gcongr
        exact hC ‖x‖ hx0

end GlobalTheory.GaussDerivBound
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviPlaneSection

open Matrix

section Alg

variable {S : Type*} [CommRing S] {m : Type*} [Fintype m] [DecidableEq m] {k : ℕ}

end Alg

section Forms

variable {F E : Type} [Field F] [Field E] [Algebra F E]

end Forms


end GlobalTheory.LeviPlaneSection

end
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_highest_vector_real_weight_unitary_compact : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), KRel ε E → KUnit ε E → ∀ N : Submodule ℂ V, FiniteDimensional ℂ N → KStab ε E N → N ≠ ⊥ → ∃ (μ : Fin n → ℝ) (w : V), w ∈ N ∧ w ≠ 0 ∧ KHighest ε E μ w := by
  first | exact @GlobalTheory.exists_kHighest_real_of_finiteDimensional | exact GlobalTheory.exists_kHighest_real_of_finiteDimensional | (intros; apply GlobalTheory.exists_kHighest_real_of_finiteDimensional <;> assumption)
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.raisingWordSpan_stable_of_lowering_kill : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ L : Submodule ℂ V, KStab ε E L → (∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0) → ∀ (a b : Fin n), ∀ y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}, E a b y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} := by
  first | exact @GlobalTheory.HolDS.raisingSpan_stable | exact GlobalTheory.HolDS.raisingSpan_stable | (intros; apply GlobalTheory.HolDS.raisingSpan_stable <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.cmExtensionIdeleConj_ideleMap_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b := by
  first | exact @GlobalTheory.ConjIdeleReal.ideleConj_ideleMap | exact GlobalTheory.ConjIdeleReal.ideleConj_ideleMap | (intros; apply GlobalTheory.ConjIdeleReal.ideleConj_ideleMap <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ConjSpan

section General

open Formalism.IndefR.Bridge Formalism.L2.DIV

theorem span_eq_top {G Γ W W' K V₀ H : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [Field K] [NumberField K] [StarRing K] [AddCommGroup V₀] [Module K V₀]
    [AddCommGroup H] [Module ℂ H] {ι : Γ →* G} {S : CSD K} {τ σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
    {ρ' : Γ →* Module.End ℂ W'} {J : Subgroup G} {χ χ' : J →* ℂˣ} (P : ClassPres ι S τ ρ J χ)
    (c₀ : V₀ →ₛₗ[τ] W) (c₁ : V₀ →ₛₗ[σ] W') (e : S.V ≃ₗ[K] V₀) (he : ∀ x, P.coef x = c₀ (e x))
    (hspan : Submodule.span ℂ (Set.range c₁) = ⊤)
    (hact : ∀ γ v, ∃ v', c₀ v' = ρ γ (c₀ v) ∧ c₁ v' = ρ' γ (c₁ v))
    (hχ : ∀ k, ∃ a : K, τ a = (χ k : ℂ) ∧ σ a = (χ' k : ℂ))
    (E : H →ₗ[ℂ] (G → W')) (hE : Function.Injective E) (hr : LinearMap.range E = AdForms ι ρ' J χ')
    (j : S.Forms → H) (hj : ∀ x h, ∃ v, P.extL x h = c₀ v ∧ E (j x) h = c₁ v) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  classical
  have hinj : Function.Injective c₀ := by
    intro v v' h
    obtain ⟨x, rfl⟩ := e.surjective v
    obtain ⟨x', rfl⟩ := e.surjective v'
    rw [← he, ← he] at h
    rw [PresBasic.coef_injective P h]
  have hval : ∀ (x : S.Forms) c, E (j x) (P.y c) = c₁ (e ((x : S.Cl → S.V) c)) := by
    intro x c
    obtain ⟨v, h1, h2⟩ := hj x (P.y c)
    rw [ClassPres.extL_apply, PresBasic.ext_y, he] at h1
    rw [h2, hinj h1]
  have hρ : ∀ c (g : S.Gam c) (x : S.V), c₁ (e (S.ρ c g x)) =
      (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ) (c₁ (e x)) := by
    intro c g x
    obtain ⟨a, ha, ha'⟩ := hχ (stabK ι (P.stabI c g))
    obtain ⟨v', h1, h2⟩ := hact (P.stabI c g : Γ) (e x)
    have h3 : e (S.ρ c g x) = a • v' := by
      apply hinj
      rw [← he, P.coef_act, map_smulₛₗ, ha, h1, he]
    rw [h3, map_smulₛₗ, ha', h2]
  have hmem : ∀ w, E w ∈ AdForms ι ρ' J χ' := fun w => hr ▸ LinearMap.mem_range_self E w
  have hone : ∀ c (u : W'), ∃ w ∈ Submodule.span ℂ (Set.range j), ∀ c', E w (P.y c') =
      (Pi.single c (∑ g : S.Gam c, (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ) u) : S.Cl → W') c' := by
    intro c u
    have hu : u ∈ Submodule.span ℂ (Set.range c₁) := hspan ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨v, rfl⟩ := hu
      obtain ⟨x, rfl⟩ := e.surjective v
      refine ⟨j (PresBasic.avgForm S c x), Submodule.subset_span ⟨_, rfl⟩, fun c' => ?_⟩
      rw [hval]
      by_cases h : c' = c
      · subst h

        simp only [PresBasic.avgForm, Pi.single_eq_same, map_sum, hρ]
      · simp [PresBasic.avgForm, Pi.single_eq_of_ne h]
    | zero => exact ⟨0, Submodule.zero_mem _, fun c' => by simp⟩
    | add u u' _ _ h h' =>
      obtain ⟨w, hw, h⟩ := h
      obtain ⟨w', hw', h'⟩ := h'
      refine ⟨w + w', Submodule.add_mem _ hw hw', fun c' => ?_⟩
      simp only [map_add (f := _), Pi.add_apply, h, h', smul_add, Finset.sum_add_distrib, Pi.single_add]
    | smul a u _ h =>
      obtain ⟨w, hw, h⟩ := h
      refine ⟨a • w, Submodule.smul_mem _ _ hw, fun c' => ?_⟩
      simp only [map_smul, Pi.smul_apply, h, smul_comm _ a, ← Finset.smul_sum, Pi.single_smul]
  rw [eq_top_iff]
  intro w _
  choose f hf hf' using fun c => hone c ((Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c))
  have key : w = ∑ c, f c := by
    apply hE
    funext g
    obtain ⟨c, ⟨γ, k, rfl⟩, -⟩ := P.reps g
    rw [hmem w γ _ k, hmem _ γ _ k]
    congr 2

    rw [map_sum, Finset.sum_apply]
    simp only [hf']
    rw [Finset.sum_eq_single c (fun c' _ hc => Pi.single_eq_of_ne (Ne.symm hc) _) (by simp), Pi.single_eq_same]
    have hg : ∀ g : S.Gam c, (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ)
        ((Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c)) = (Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c) := by
      intro g
      have h1 := hmem w (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g))
      rw [stabK_spec] at h1
      rw [map_smul, smul_comm, ← h1]
    simp only [hg, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast Fintype.card_ne_zero
  rw [key]
  exact Submodule.sum_mem _ fun c _ => hf c

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem span_eq_top_of_tie {D : D7} {V : HSp D} {C : Bridge.CoefDat D V} {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ χ' : J →* ℂˣ} (P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c₀ : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : Bridge.CoefTie V C P lam c₀ pair nab del) (hM : Bridge.CoefMapTie V C c₀ rho)
    {σ : D.what₂.LL →+* ℂ} (c : CoefA V) (c₁ : VV D.what₂.LL lam →ₛₗ[σ] c.W)
    (hact : ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
      ∀ v, c₁ (rho γE v) = c.ρ (γ : GA D V) (c₁ v))
    (hspan : Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL lam a)) = ⊤)
    (hχ : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjVal σ ((χ k : ℂˣ) : ℂ) ((χ' k : ℂˣ) : ℂ))
    (H : HMod (Bridge.Gf V → c.W)) {ip} (hH : H.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ') ip)
    (j : S.Forms → H.H) (hj : ∀ x h, ∃ v, P.extL x h = c₀ v ∧ H.e (j x) h = c₁ v) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨e, -, he, -⟩ := hP
  have hspan' : Submodule.span ℂ (Set.range c₁) = ⊤ :=
    eq_top_iff.2 (hspan.ge.trans (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)))
  refine span_eq_top (ρ' := c.coef.ρ) P c₀ c₁ e he hspan' (fun γ v => ?_) hχ H.e hH.1 hH.2.1 j hj
  obtain ⟨γE, h⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
    obtain ⟨g, hg⟩ := γ.2
    exact ⟨g, hg.2.symm⟩
  exact ⟨_, hM.1 γ γE h v, hact γ γE h v⟩



theorem span_conjForms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) c c₁ H j, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → Submodule.span ℂ (Set.range j) = ⊤ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hjV gramR c0R c0L hT i σ c c₁ H j hC
  obtain ⟨χ', hχ, hH⟩ := hC.model
  have h1 := hT.coefL i A.μ0
  have h2 := hT.mapL i
  refine span_eq_top_of_tie (V := Vc D i) (R.B.L i A.μ0).pres h1 h2 c c₁ hC.act hC.span hχ H hH j fun x h => ?_
  have h0 := congrFun (hjV i A.μ0 x) h
  exact (hC.base x h).imp fun v hv => ⟨h0.symm.trans hv.1, hv.2⟩

end GlobalTheory.ConjSpan

end
end
