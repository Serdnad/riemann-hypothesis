module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle090
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle433
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open scoped FourierTransform

noncomputable section
namespace GlobalTheory.ThetaRatSum
open MeasureTheory GroundTheory.Automorphic.GJMatrix

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem char_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (x : AF F) :
    ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := GlobalTheory.T.standardTraceAdelicAddChar_apply_eq_adelicChar F ψ hψ x

theorem glue_integral : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ H : (κ → AF F) → ℂ,
    (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔ Integrable H (adeleMeasurePi F)) ∧
    ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F) := GlobalTheory.T.integral_diagonalCoords_eq_pos_mul_adeleHaar F κ

theorem shift_mem {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) (u : κ → AF F) :
    (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi (K := F) (ι := κ) := GlobalTheory.T.adelicSchwartz_restrict_translated_diagonal_mem F κ φ hφ u

theorem schA_le (ι : Type) [Fintype ι] : schA F ι ≤ schwartzBruhatPi (K := F) (ι := ι) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, g, hg, rfl⟩
  have e : pureA F f g = schwartzBruhatTensorPi f g := rfl
  rw [e]
  exact schwartzBruhatTensorPi_mem f ((mem_finiteSchwartzBruhatPi F).2 ⟨hg.1, hg.2⟩)

theorem summable_four {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) :
    Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F
      (fun t : κ → AF F => φ (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t))
      (fun i => algebraMap F (AF F) (uv.2 i))‖ := GlobalTheory.T.summable_partialFourier_adelicSchwartz_rationalPairs F κ φ hφ

abbrev rv (u : κ → F) : κ → AF F := fun i => algebraMap F (AF F) (u i)

theorem dot_elim_left (a b : κ → AF F) : Sum.elim a a ⬝ᵥ Sum.elim b 0 = ∑ i, a i * b i := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem dot_elim_rat (u v : κ → F) :
    Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) (0 : κ → AF F) = algebraMap F (AF F) (u ⬝ᵥ v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, Fintype.sum_sum_type, rv, map_sum, map_mul]

theorem term_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {c₀ : ℝ}
    (hB : ∀ H : (κ → AF F) → ℂ,
      (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔ Integrable H (adeleMeasurePi F)) ∧
      ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F))
    {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) (u v : κ → F) :
    GlobalTheory.DiagForm.lDiag F κ (schr ψ (Sum.elim (rv u) 0, Sum.elim (rv v) 0) φ) =
      c₀ * adelicFourierPi F (fun t : κ → AF F => φ (Sum.elim (t + rv u) t)) (rv v) := by
  set H : (κ → AF F) → ℂ := fun t => φ (Sum.elim (t + rv u) t) *
    (GroundTheory.Global.adelicChar F (∑ i, t i * rv v i) : ℂ) with hH
  have hint : Integrable H (adeleMeasurePi F) :=
    integrable_mul_adelicChar_pi (integrable_of_mem_schwartzBruhatPi (shift_mem hφ _)) _
  have key : GlobalTheory.DiagForm.resD F κ (schr ψ (Sum.elim (rv u) 0, Sum.elim (rv v) 0) φ) =
      fun p => H (GlobalTheory.DiagForm.glue p) := by
    funext p
    show ψ (Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) ⬝ᵥ Sum.elim (rv v) 0 +
        ⅟(2 : AF F) * (Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) 0)) *
        φ (Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) + Sum.elim (rv u) 0) = _
    have h2 : ⅟(2 : AF F) * (Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) (0 : κ → AF F)) =
        algebraMap F (AF F) (⅟(2 : F) * (u ⬝ᵥ v)) := by
      rw [dot_elim_rat, map_mul]
      congr 1
    have h3 : Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) + Sum.elim (rv u) 0 =
        Sum.elim (GlobalTheory.DiagForm.glue p + rv u) (GlobalTheory.DiagForm.glue p) := by
      funext i; cases i <;> simp
    rw [dot_elim_left, h2, AddChar.map_add_eq_mul, hψ.2.1, mul_one, h3, char_eq ψ hψ, hH, mul_comm]
  rw [GlobalTheory.DiagForm.lDiag, LinearMap.comp_apply, key,
    GlobalTheory.DiagForm.Lext_apply _ (((hB H).1).2 hint), (hB H).2, adelicFourierPi]

theorem hasSum_lDiag_schr_rat : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ], ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F (κ ⊕ κ),
      HasSum (fun uv : (κ → F) × (κ → F) => GlobalTheory.DiagForm.lDiag F κ (schr ψ
        (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ))
        (c * thetaSum F φ) := by
  intro F _ _ ψ hψ κ _
  obtain ⟨c₀, hc₀, hB⟩ := glue_integral (F := F) (κ := κ)
  refine ⟨(c₀ : ℂ), by exact_mod_cast hc₀.ne', fun φ hφ => ?_⟩
  set f : (κ → F) → (κ → AF F) → ℂ := fun u t => φ (Sum.elim (t + rv u) t) with hf
  have hT : (fun uv : (κ → F) × (κ → F) => GlobalTheory.DiagForm.lDiag F κ (schr ψ
        (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ)) =
      fun uv => (c₀ : ℂ) * adelicFourierPi F (f uv.1) (rv uv.2) :=
    funext fun uv => term_eq ψ hψ hB hφ uv.1 uv.2
  rw [hT]
  have hs : Summable fun uv : (κ → F) × (κ → F) => (c₀ : ℂ) * adelicFourierPi F (f uv.1) (rv uv.2) :=
    (summable_four hφ).of_norm.mul_left _
  have hP : ∀ u : κ → F, HasSum (fun v => (c₀ : ℂ) * adelicFourierPi F (f u) (rv v))
      ((c₀ : ℂ) * ∑' η : κ → F, φ (Sum.elim (rv η + rv u) (rv η))) := by
    intro u
    obtain ⟨-, h2, h3⟩ := poisson_of_mem_schwartzBruhatPi (shift_mem hφ (rv u))
    refine HasSum.mul_left _ ?_
    have e := h2.of_norm.hasSum
    rw [← h3] at e
    exact e
  have hθ : HasSum (fun uη : (κ → F) × (κ → F) => φ (Sum.elim (rv uη.2 + rv uη.1) (rv uη.2))) (thetaSum F φ) := by
    let e : (κ → F) × (κ → F) ≃ (κ ⊕ κ → F) :=
      { toFun := fun uη => Sum.elim (uη.2 + uη.1) uη.2
        invFun := fun ξ => (ξ ∘ Sum.inl - ξ ∘ Sum.inr, ξ ∘ Sum.inr)
        left_inv := fun uη => by ext i <;> simp
        right_inv := fun ξ => by funext i; cases i <;> simp }
    obtain ⟨h1, -, -⟩ := poisson_of_mem_schwartzBruhatPi (schA_le (F := F) (κ ⊕ κ) hφ)
    have h := h1.of_norm.hasSum
    rw [← e.hasSum_iff] at h
    have hfe : (fun uη : (κ → F) × (κ → F) => φ (Sum.elim (rv uη.2 + rv uη.1) (rv uη.2))) =
        (fun ξ : κ ⊕ κ → F => φ fun i => algebraMap F (AF F) (ξ i)) ∘ e := by
      funext uη
      simp only [Function.comp_apply]
      congr 1
      funext i; cases i <;> simp [e, rv, map_add (f := _)]
    rw [hfe]
    exact h
  have h4 : HasSum (fun u : κ → F => (c₀ : ℂ) * ∑' η : κ → F, φ (Sum.elim (rv η + rv u) (rv η)))
      ((c₀ : ℂ) * thetaSum F φ) :=
    (hθ.prod_fiberwise fun u => (hθ.summable.prod_factor u).hasSum).mul_left _
  have h5 := hs.hasSum.prod_fiberwise hP
  rw [← h5.unique h4]
  exact hs.hasSum

end GlobalTheory.ThetaRatSum
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunIsom

open scoped ComplexOrder

section One

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.ValCmp

theorem cofRel_hw_explicit (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) : ∃ ε : ℤˣ, CofRel R m ν (hw R le_rfl ν)
      ((ε : ℤ) • Formalism.UG.dwAct R (m + 1) (m + 1) (antiDiagGL R (m + 1)) (hw R le_rfl (nuDual ν))) := by
  have hnext : ∀ (μ : Fin (m + 1) → ℕ) (s : Fin m), nuNext μ s.castSucc = μ s.succ := by
    intro μ s
    have : s.castSucc.val + 1 < m + 1 := by simp
    rw [nuNext, dite_eq_left this]
    rfl
  have e1 : Formalism.UG.dwAct R (m + 1) (m + 1) (antiDiagGL R (m + 1)) (hw R le_rfl (nuDual ν)) =
      ∏ s : Fin m, revInitMinor R (m + 1) (m + 1 - (s.val + 1)) ^ (ν s.castSucc - ν s.succ) := by
    rw [hw, map_prod, Fin.prod_univ_castSucc]
    simp only [map_pow, dwAct_antiDiag_lpMinor, hnext]
    have : nuDual ν (Fin.last m) = 0 := by simp [nuDual]
    rw [this, Nat.zero_sub, pow_zero, mul_one, ← Equiv.prod_comp Fin.revPerm]
    refine Finset.prod_congr rfl fun s _ => ?_
    have h1 : ν s.castSucc ≤ ν 0 := hν (Fin.zero_le _)
    have h2 : ν s.succ ≤ ν s.castSucc := hν (Fin.castSucc_lt_succ).le
    have hs := s.isLt
    congr 1
    · congr 1
      simp [Fin.val_rev]
      omega
    · simp only [nuDual, Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]
      omega
  choose ε hε using fun s : Fin m =>
    cofAct_lpMinor R (m + 1) s.val (by have := s.isLt; omega) (by have := s.isLt; omega)
  refine ⟨∏ s : Fin m, ε s ^ (ν s.castSucc - ν s.succ), ?_⟩
  have hsum : ∑ i, ν i - ν 0 = ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ) := by
    have := sum_mul_sub_succ m ν hν
    rw [h0] at this
    omega
  rw [CofRel, e1, hsum, hw, map_prod, Fin.prod_univ_castSucc, h0, Nat.zero_sub, pow_zero, map_one, mul_one]
  simp only [map_pow, hnext, Fin.val_castSucc, hε, zsmul_eq_mul, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

variable {K : Type} [Field K] {n : ℕ}

theorem antiDiag_transpose : ((antiDiagGL K n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
    (((antiDiagGL K n)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  ext a b
  change (if a = b.rev then (1 : K) else 0) = if b = a.rev then 1 else 0
  congr 1
  exact propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩

theorem antiDiag_detPow_sq (c : ℤ) : detPow K n (antiDiagGL K n) c * detPow K n (antiDiagGL K n) c = 1 := by
  rw [funDetPow_eq, ← mul_zpow, ← Matrix.det_mul]
  have : ((antiDiagGL K n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (antiDiagGL K n : GL (Fin n) K) = 1 :=
    (antiDiagGL K n).val_inv
  rw [this]
  simp

theorem funPos_extremal (l : DomWeight n) : ∃ c : K, c * c = 1 ∧
    (genM K n).det ^ funExp l * (c • (detPow K n (antiDiagGL K n) l.dual.detShift •
      rowAct K ((antiDiagGL K n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ (extremal K n l.dual))) =
      cofAct K n (extremal K n l) := by
  cases n with
  | zero =>
    refine ⟨1, one_mul _, ?_⟩
    simp [funCof_zero, extremal, hw, detPow, DomWeight.detShift]
  | succ m =>
    obtain ⟨ε, hε⟩ := cofRel_hw_explicit K m l.natW (funNat_antitone l) (funNat_last l)
    refine ⟨((ε : ℤ) : K) * detPow K (m + 1) (antiDiagGL K (m + 1)) l.dual.detShift, ?_, ?_⟩
    · rw [mul_mul_mul_comm, antiDiag_detPow_sq, mul_one, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    · rw [smul_smul, mul_assoc, antiDiag_detPow_sq, mul_one, Int.cast_smul_eq_zsmul, antiDiag_transpose, funExp_succ,
        extremal, extremal, funNat_dual]
      exact hε

end One

variable {ι : Type} [Fintype ι] {n : ℕ}

def extVec (σ : ι → DomWeight n) : VV ℂ σ :=
  ⟨ten fun τ => extremal ℂ n (σ τ), GlobalTheory.Proof.TensorMapDescent.ten_mem σ _ fun τ =>
    Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (funNat_antitone (σ τ))⟩

theorem pairBK_extVec (σ : ι → DomWeight n) : pairBK σ (extVec σ) (extVec σ) = 1 := by
  have h := pairingBExtremal_holds ℂ ι n σ 1
  rw [map_one, polyAction_one₂] at h
  rw [pairBK_apply]
  exact h

theorem pairBK_funEquiv_extVec (σ : ι → DomWeight n) :
    pairBK (fun τ => (σ τ).dual) (funEquiv σ (extVec σ)) (funEquiv σ (extVec σ)) = 1 := by
  choose c hc hrel using fun τ => funPos_extremal (K := ℂ) (σ τ)
  have h1 := funRel_unique (funEquiv_rel σ (extVec σ)) (funRel_ten hrel)
  have h2 : ∀ (c : ι → ℂ) (x : ι → MvPolynomial (Fin n × Fin n) ℂ), ten (fun τ => c τ • x τ) = (∏ τ, c τ) • ten x := by
    intro c x
    unfold ten
    simp only [map_smul]
    rw [Finset.prod_smul]
  rw [h2, ← funAct_ten (fun τ => (σ τ).dual) (fun _ => GlobalTheory.ValCmp.antiDiagGL ℂ n)] at h1
  have hJ : invTrK (fun _ : ι => GlobalTheory.ValCmp.antiDiagGL ℂ n) = fun _ => GlobalTheory.ValCmp.antiDiagGL ℂ n := by
    funext τ
    apply Units.ext
    rw [invTrK_coe, ← antiDiag_transpose, Matrix.transpose_transpose]
  have h3 := pairingBExtremal_holds ℂ ι n (fun τ => (σ τ).dual) (fun _ => GlobalTheory.ValCmp.antiDiagGL ℂ n)
  rw [hJ] at h3
  rw [pairBK_apply, h1, map_smul, map_smul, LinearMap.smul_apply, h3, smul_smul, ← Finset.prod_mul_distrib]
  simp [hc]

theorem pairBK_inv (σ : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (x y : VV ℂ σ) :
    pairBK σ (rhoK σ (invTrK g) x) (rhoK σ g y) = pairBK σ x y := by
  rw [pairBK_apply, pairBK_apply, rhoK_coe, rhoK_coe]
  exact pairingBInvariantK_holds ℂ ι n σ g x.1 y.1

theorem pairBK_funEquiv (σ : ι → DomWeight n) (a b : VV ℂ σ) :
    pairBK (fun τ => (σ τ).dual) (funEquiv σ a) (funEquiv σ b) = pairBK σ a b := by
  haveI : FiniteDimensional ℂ (VV ℂ σ) := Module.Finite.of_basis (bVV ℂ σ)
  have hnd := pairingBNondegenerate_holds ℂ ι n σ
  have hne : extVec σ ≠ 0 := fun h => by
    have := pairBK_extVec σ
    rw [h] at this
    simp at this
  haveI : Nontrivial (VV ℂ σ) := ⟨⟨_, _, hne⟩⟩
  let T : VV ℂ σ →ₗ[ℂ] VV ℂ σ :=
    (LinearMap.BilinForm.toDual (pairBK σ) hnd).symm.toLinearMap ∘ₗ
      (pairBK fun τ => (σ τ).dual).compl₁₂ (funEquiv σ).toLinearMap (funEquiv σ).toLinearMap
  have hp : ∀ v y, pairBK σ (T v) y = pairBK (fun τ => (σ τ).dual) (funEquiv σ v) (funEquiv σ y) := fun v y => by
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.BilinForm.apply_toDual_symm_apply,
      LinearMap.compl₁₂_apply]
  have hT : ∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ σ), T (rhoK σ g v) = rhoK σ g (T v) := fun g v => by
    refine sub_eq_zero.1 (hnd.1 _ fun y => ?_)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero, hp]
    obtain ⟨y', rfl⟩ : ∃ y', y = rhoK σ (invTrK g) y' :=
      ⟨rhoK σ (invTrK g)⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]⟩
    rw [funEquiv_rhoK, funEquiv_rhoK, pb_invTrK_invTrK, pairBK_inv, ← hp]
    have h := pairBK_inv σ (invTrK g) (T v) y'
    rw [pb_invTrK_invTrK] at h
    exact h.symm
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  have hU := GlobalTheory.CoefModel.eq_bot_or_top σ (G := fun _ => 1) (fun _ => Matrix.PosDef.one) (Module.End.eigenspace T c)
    fun g _ x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hT, hx, map_smul]
  have hall : ∀ v, T v = c • v := fun v => by
    rcases hU with h | h
    · exact absurd h hc
    · exact Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)
  have h1 : c = 1 := by
    have h := hp (extVec σ) (extVec σ)
    rwa [pairBK_funEquiv_extVec, hall, map_smul, LinearMap.smul_apply, pairBK_extVec, smul_eq_mul, mul_one] at h
  rw [← hp, hall, h1, one_smul]

theorem pairK_one_eq (σ : ι → DomWeight n) (x y : VV ℂ σ) :
    pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) x y =
      pairBK σ (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) σ x) y := by
  have h := pairP_eq_pairB σ (1 : ι → GL (Fin n) ℂ) x.1 y.1
  rw [polyAction_one₂] at h
  rw [pairK_apply, pairBK_apply, GlobalTheory.CoefModel.mapVV_coe]
  exact h

theorem pairK_funEquiv (σ : ι → DomWeight n) (a b : VV ℂ σ) :
    pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (funEquiv σ a) (funEquiv σ b) =
      pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) a b := by
  have h := (isFunForm_iff_eq σ _ _).1 (GlobalTheory.BrRat.isFunForm_map (starRingEnd ℂ) σ (isFunForm_funEquiv σ a))
  rw [pairK_one_eq, pairK_one_eq, ← pairBK_funEquiv σ]
  congr 2

theorem pairK_funEquiv_symm_le : ∀ {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) (w : VV ℂ fun τ => (σ τ).dual),
    (pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) ((GlobalTheory.FunObj.funEquiv σ).symm w) ((GlobalTheory.FunObj.funEquiv σ).symm w)).re ≤
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w w).re := by
  intro ι _ n σ w
  rw [← pairK_funEquiv σ, LinearEquiv.apply_symm_apply]

end GlobalTheory.FunIsom

end
end

section

noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.RealLift.LieSecondPf

theorem lieSecond_of_lieScalar : GlobalTheory.FunPr.Hypotheses₂ → DerEx → FockEx → VacLine → LieScalar → LieSecond := by
  intro _ hD hF hV hL F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om χ m hCM hψ hFr hΦ hW hχ
  obtain ⟨hU, dd, omd, hdd, hWS, hres⟩ := hW
  obtain ⟨c, hc⟩ := hL F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hU
  have hFrd := GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr
  obtain ⟨Φd, hΦd⟩ := hF F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) hCM hψ hFrd
  obtain ⟨cd, hcd⟩ := hL F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) Φd omd hCM hψ hFrd hΦd hWS.2.1
  have key : ∀ w (Y : Mat R S), c w * Y.trace = (m w : ℂ) / 2 * Y.trace := by
    intro w Y
    rcases Nat.eq_zero_or_pos (R + S) with h0 | hpos
    · have hR : R = 0 := by omega
      have hS : S = 0 := by omega
      subst hR hS
      have : Y.trace = 0 := by simp [Matrix.trace]
      rw [this, mul_zero, mul_zero]
    · have hbox := GlobalTheory.T.doubledFockVacuum_eq_smul_vacuum_mul_conj hD hV F E σ α β κ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd
      have hl := GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian F E σ α β κ ψ JA JB d dd hψ hdd
      have hne : (∫ x : κ → mixedEmbedding.mixedSpace F,
          Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 := by
        obtain ⟨z, hz, hzx⟩ := hbox
        have h1 : ∀ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x) =
            z * (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x * star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x)) := by
          intro x
          rw [hzx, Sum.elim_comp_inl, Sum.elim_comp_inr, mul_assoc]
        simp_rw [h1]
        rw [MeasureTheory.integral_const_mul]
        refine mul_ne_zero hz (GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero F κ _ ?_)
        intro h0
        exact GlobalTheory.T.tprod_constant_polynomials_ne_zero F P Q R S (hΦ.1 (by rw [h0, map_zero]))
      have h1 := GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces F E σ α β κ P Q R S ψ τ JA JB dd a b A C Φd omd χ m cd hCM hψ hFr hWS hχ hcd hl hne hpos w
      have h2 := GlobalTheory.T.realPlace_splittingConstant_eq_doubledSpace F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ Φd om omd c cd hCM hψ hΦ hres hc hcd hbox hpos w
      rw [h2, h1]
  intro γ hγ Y hY T
  have e : (fun w => fockAct2 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • (1 : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))) =
      fun w => fockAct2 P Q R S (Y w) + (c w * (Y w).trace) • 1 := by
    funext w
    rw [key w (Y w)]
  have := hc γ hγ Y hY T
  rw [← e] at this
  exact this

end GlobalTheory.RealLift.LieSecondPf

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

theorem _root_.GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (bb : GL (Fin n) (Fv F v)) (cc : GL (Fin d) (Fv F v)) (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW (t.comp σ)) = 0 ∧ GlobalTheory.FlipMatch.coX t bb cc z = Z) ∧
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW t) = 0 ∧ GlobalTheory.FlipMatch.coY σ X W t bb cc z = Z) := by
  exact @GlobalTheory.FlipOnto.coX_coY_onto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank : ∀ {D : D7} {V V' : HSp D}, V.rank = V'.rank → NegIdx V 0 → NegIdx V' 0 → Nonempty (GlobalTheory.Mem.Isom.IsoMat V V') := by
  first | exact @GlobalTheory.BottomIsom.isoMat_of_posDef | exact GlobalTheory.BottomIsom.isoMat_of_posDef | (intros; apply GlobalTheory.BottomIsom.isoMat_of_posDef <;> assumption)
end

section

namespace GlobalTheory.Laid

theorem hcfj_holds : GlobalTheory.Published.HilbertClassFieldJ := GlobalTheory.CompanionTheory.Hypotheses₂.hilbertClassFieldJ

end GlobalTheory.Laid
end
