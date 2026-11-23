module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle006
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle157
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweSwap

variable {L : Type} [Field L]

theorem cT_cT {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {a b : Type} (A : Matrix a b L) :
    Formalism.UG.cT σ (Formalism.UG.cT σ A) = A := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_add (σ : L →+* L) {a b : Type} (A B : Matrix a b L) :
    Formalism.UG.cT σ (A + B) = Formalism.UG.cT σ A + Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_zero (σ : L →+* L) {a b : Type} : Formalism.UG.cT σ (0 : Matrix a b L) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_herm {σ : L →+* L} {a : ℕ} {J : Matrix (Fin a) (Fin a) L} (h : ∀ i j, σ (J i j) = J j i) :
    Formalism.UG.cT σ J = J := by
  ext i j; simp [Formalism.UG.cT, h]

theorem inv_mul_cl {a : ℕ} {β : Type} (J : GL (Fin a) L) (Z : Matrix (Fin a) β L) :
    ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * ((J : Matrix (Fin a) (Fin a) L) * Z) = Z := by
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem mul_inv_cl {a : ℕ} {β : Type} (J : GL (Fin a) L) (Z : Matrix (Fin a) β L) :
    (J : Matrix (Fin a) (Fin a) L) * (((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * Z) = Z := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem cT_inv_herm {σ : L →+* L} {a : ℕ} (J : GL (Fin a) L) (h : Formalism.UG.cT σ (J : Matrix (Fin a) (Fin a) L) = J) :
    Formalism.UG.cT σ ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) = (J⁻¹ : GL (Fin a) L) := by
  have h1 : Formalism.UG.cT σ ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (J : Matrix (Fin a) (Fin a) L) = 1 := by
    conv_lhs => rw [← h]
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  calc _ = Formalism.UG.cT σ ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * ((J : Matrix (Fin a) (Fin a) L) *
        ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) := by rw [Units.mul_inv, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem trace_cT (σ : L →+* L) {a : ℕ} (A : Matrix (Fin a) (Fin a) L) :
    σ (Matrix.trace A) = Matrix.trace (Formalism.UG.cT σ A) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Formalism.UG.cT, Matrix.trace, map_sum]

def adj (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (X : Matrix (Fin n) (Fin n') L) :
    Matrix (Fin n') (Fin n) L :=
  ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Formalism.UG.cT σ X * (JS : Matrix (Fin n) (Fin n) L)

theorem adj_add (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (X Y : Matrix (Fin n) (Fin n') L) :
    adj σ JS JT (X + Y) = adj σ JS JT X + adj σ JS JT Y := by
  simp [adj, cT_add, Matrix.mul_add, Matrix.add_mul]

theorem adj_zero (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) :
    adj σ JS JT (0 : Matrix (Fin n) (Fin n') L) = 0 := by
  simp [adj, cT_zero]

theorem adj_pre {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L)
    (x : Matrix (Fin n') (Fin n) L) :
    adj σ JS JT (Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))) = x := by
  simp only [adj, cT_cT hσ, Matrix.mul_assoc, inv_mul_cl, Units.inv_mul, Matrix.mul_one]

theorem locH_adj {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {δ : L} (hδ : σ δ = -δ) {n n' : ℕ} (JS : GL (Fin n) L)
    (JT : GL (Fin n') L) (hS : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS)
    (hTi : Formalism.UG.cT σ ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) = (JT⁻¹ : GL (Fin n') L))
    (X Y : Matrix (Fin n) (Fin n') L) :
    σ (locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y)) = locH σ (-δ) JT JS X Y := by
  have hc : ∀ {a b : Type} (Z : Matrix a b L), (Z.map σ)ᵀ = Formalism.UG.cT σ Z := fun _ => rfl
  simp only [locH, hc, adj, Formalism.UG.cT_mul, cT_cT hσ, hS, hTi, Matrix.mul_assoc, inv_mul_cl, map_mul, hδ, trace_cT]
  congr 1
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.Hk3.HoweSwap

namespace GlobalTheory.Hk3.HoweSwap

variable {L : Type} [Field L]

theorem adj_norm (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (h : GL (Fin n) L) (g : GL (Fin n') L)
    (hh : Formalism.UG.cT σ (h : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (h : Matrix (Fin n) (Fin n) L) = JS)
    (hg : Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (JT : Matrix (Fin n') (Fin n') L) *
      ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) = JT)
    (X : Matrix (Fin n) (Fin n') L) :
    adj σ JS JT ((h : Matrix (Fin n) (Fin n) L) * X * ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) =
      (g : Matrix (Fin n') (Fin n') L) * adj σ JS JT X * ((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  have e2 : Formalism.UG.cT σ (h : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) =
      (JS : Matrix (Fin n) (Fin n) L) * ((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    conv_rhs => rw [← hh]
    rw [Matrix.mul_assoc _ (h : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.mul_one]
  have e1 : ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) =
      (g : Matrix (Fin n') (Fin n') L) * ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) := by
    have e3 : Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (JT : Matrix (Fin n') (Fin n') L) =
        (JT : Matrix (Fin n') (Fin n') L) * (g : Matrix (Fin n') (Fin n') L) := by
      conv_rhs => rw [← hg]
      rw [Matrix.mul_assoc _ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L), Units.inv_mul, Matrix.mul_one]
    calc _ = ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *
          ((JT : Matrix (Fin n') (Fin n') L) * ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L))) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc (Formalism.UG.cT σ _), e3, Matrix.mul_assoc, inv_mul_cl]
  unfold adj
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) *
        Formalism.UG.cT σ X * (Formalism.UG.cT σ (h : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e1, e2]; simp only [Matrix.mul_assoc]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_mul {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : A ∈ HoweDuality.intMat L a b) (hB : B ∈ HoweDuality.intMat L b c) : A * B ∈ HoweDuality.intMat L a c := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem intMat_cT {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : A ∈ HoweDuality.intMat L a b) : Formalism.UG.cT σ A ∈ HoweDuality.intMat L b a := fun i j => by
  have h := hA j i
  simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at h ⊢
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hv]
  exact h

theorem glint_int {a : ℕ} {J : GL (Fin a) L} (h : J ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L)) :
    (J : Matrix (Fin a) (Fin a) L) ∈ HoweDuality.intMat L a a ∧
      ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) ∈ HoweDuality.intMat L a a := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp [Formalism.UG.bc]
  · rw [← map_inv]; simp [Formalism.UG.bc]

end GlobalTheory.Hk3.HoweSwap

namespace GlobalTheory.Hk3.HoweSwap

theorem locPair_swap : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω →
    GlobalTheory.Hk3.LocPair ϖ σ q (-δ) JT JS ψ
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)))
      (ω.comp (MulEquiv.prodComm : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) × Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) ≃* _).toMonoidHom) ∧
    (∀ s : M, GlobalTheory.Hk3.LocVac ρ s → GlobalTheory.Hk3.LocVac
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L))) s) ∧
    ∀ s : M, Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n') L =>
      ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)) s) = ⊤ := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hp
  have hσ : ∀ x, σ (σ x) = x := hp.unr.1
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hp.unr.2.1
  have hS : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := cT_herm hp.hermS
  have hT : Formalism.UG.cT σ (JT : Matrix (Fin n') (Fin n') L) = JT := cT_herm hp.hermT
  have hTi := cT_inv_herm JT hT
  obtain ⟨hS1, hS2⟩ := glint_int hp.intS
  obtain ⟨hT1, hT2⟩ := glint_int hp.intT
  have hai : ∀ X : Matrix (Fin n) (Fin n') L, X ∈ HoweDuality.intMat L n n' → adj σ JS JT X ∈ HoweDuality.intMat L n' n :=
    fun X hX => intMat_mul (intMat_mul hT2 (intMat_cT hv hX)) hS1
  have hprei : ∀ x : Matrix (Fin n') (Fin n) L, x ∈ HoweDuality.intMat L n' n →
      Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∈ HoweDuality.intMat L n n' :=
    fun x hx => intMat_cT hv (intMat_mul (intMat_mul hT1 hx) hS2)
  have hvac : ∀ s, LocVac ρ s → LocVac (fun X => ρ (adj σ JS JT X)) s := fun s hs u hu => hs _ (hai u hu)
  have hvac' : ∀ s, LocVac (fun X => ρ (adj σ JS JT X)) s → LocVac ρ s := fun s hs u hu => by
    have h1 := hs _ (hprei u hu)
    simp only [adj_pre hσ] at h1
    exact h1
  have hrange : ∀ s : M, Set.range (fun x => ρ x s) ⊆ Set.range (fun X => ρ (adj σ JS JT X) s) := by
    rintro s _ ⟨x, rfl⟩
    exact ⟨(Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))), by simp only [adj_pre hσ]⟩
  refine ⟨?_, hvac, fun s hs => ?_⟩
  · refine ⟨hp.unr, hp.odd, hp.intT, hp.intS, hp.hermT, hp.hermS,
      ⟨by rw [Valuation.map_neg]; exact hp.delta.1, by rw [map_neg, hp.delta.2]⟩, hp.psi_int, hp.psi_ne, ?_, ?_, ?_, ?_, ?_⟩
    · show ρ (adj σ JS JT 0) = 1
      rw [adj_zero]; exact hp.rho_zero
    · intro X Y
      show ρ (adj σ JS JT X) * ρ (adj σ JS JT Y) = _ • ρ (adj σ JS JT (X + Y))
      have hb := locH_adj hσ hp.delta.2 JS JT hS hTi X Y
      have ha : locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y) = σ (locH σ (-δ) JT JS X Y) := by rw [← hb, hσ]
      have key : locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y) + σ (locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y)) =
          locH σ (-δ) JT JS X Y + σ (locH σ (-δ) JT JS X Y) := by
        rw [hb]; linear_combination ha
      rw [hp.rho_mul, adj_add, key]
    · rw [eq_top_iff, ← hp.span]
      apply Submodule.span_mono
      rintro w ⟨x, s, hs, rfl⟩
      refine ⟨(Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))), s, hvac s hs, ?_⟩
      show ρ x s = ρ (adj σ JS JT (Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) s
      rw [adj_pre hσ]
    · intro g h x
      show ω (h, g) * ρ (adj σ JS JT _) = ρ (adj σ JS JT _) * ω (h, g)
      rw [hp.norm h g, adj_norm σ JS JT (h : GL (Fin n) L) (g : GL (Fin n') L) h.2 ((Formalism.UG.UJ σ _).inv_mem g.2)]
    · intro g h hg hh s hs
      exact hp.fix h g hh hg s (hvac' s hs)
  · rw [eq_top_iff, ← hs]
    exact Submodule.span_mono (hrange s)

end GlobalTheory.Hk3.HoweSwap
end
end

section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.StabLaw

section
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem rhoS_one (i : ℕ) (P : rowSG Pr sel mu) : rhoS Ch sel mu i P 1 = 1 := by
  unfold rhoS LocE.unitV
  simp [TopStep.reduction_one₂]
end

theorem xiCpl1_stab : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → ∀ (u : Pr.Word) (al : L.β m2) (b : L.β (m2 + 1)) (p : ChPt (R := R) sel mu u m2) (p' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (a : FrmG (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b)), Y ∈ ybSet sel mu cst p'.deco.1.N → a • p' = p' → (fun v => a.1.1 v) '' Y = Y → ∀ x, XiCpl1 Ch sel mu cst L m2 al p p' Y (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst m2 P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((L.levG (m2 + 1) b).chr a.2.1 * (L.levQ (m2 + 1) b).chr a.2.2 : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hg hT hL _ _ _ _ u al b p p' Y a hp1 hfix hY x
  have hd := (TopStep.tilOk_of_avoid (mu := mu) hPr hsel u ⟨hT u, hg⟩).2.2
  obtain ⟨κ', a', hκ', ha', ea'⟩ := TopLaw.exists_pass hd a p'
  have hp2 : (fun v => a.1.1 v) '' Y ∈ ybSet sel mu cst (a • p').deco.1.N := (ybSet_gmap sel mu cst _ a.1.1 Y).2 hp1
  have ha : ∀ P, TopLaw.LevAt (L.levG m2 al) (L.levQ m2 al) P ((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P) ((fun _ => 1 : rowSG Pr sel mu → X.Kˣ) P) := by
    intro P
    refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
    · refine ⟨by rw [Pi.one_apply, map_one]; exact one_mem _, ?_⟩
      exact (map_one _).symm.trans (congrArg _ (Subtype.ext (map_one _).symm))
    · exact ⟨one_mem _, (map_one _).symm⟩
  have hκ : ∀ P, frsF sel mu ((1 : FrmG (L.levG m2 al) (L.levQ m2 al)) • p) P =
      (1 : UF X.E (R.N m2)).1 * (frsF sel mu p P * (((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P)⁻¹).1) := fun P => by
    rw [one_smul]; simp
  have law := CoupledLaw.xiCpl1_law (G := G) (q := (1 : FrmG (L.levG m2 al) (L.levQ m2 al)) • p) hX hPr hL hp1 hp2 hκ hκ' ha ha' x
    (TopLaw.phiT_act _ _ _ _ _ _ _)
  rw [one_smul, hfix, hY] at law
  rw [hfix] at hκ'
  have hdet : ∀ P, (LinearEquiv.det a.1.1 : X.Eˣ) = LinearEquiv.det (κ' P).1 := fun P => by
    have h := congrArg LinearEquiv.det (hκ' P)
    rw [map_mul, map_mul, InvMemClass.coe_inv, map_inv] at h
    rw [mul_left_comm] at h
    exact mul_inv_eq_one.mp (mul_left_cancel (h.symm.trans (mul_one _).symm))
  have hprod : ∀ P, muAt Ch sel mu cst m2 P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) =
      rhoS Ch sel mu m2 P ((LinearEquiv.det ((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P).1 : X.Eˣ) : X.E) *
        rhoT Ch sel mu m2 P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E) := fun P => by
    rw [hdet P, MatLaw.muAt_det, Pi.inv_apply, TopLaw.rhoT_inv, Pi.one_apply, OneMemClass.coe_one, map_one,
      Units.val_one, rhoS_one, one_mul]
  have e : x ∘ₗ ((1 : UF X.E (R.N m2)) : Sp X.E (R.N m2) ≃ₗ[X.E] Sp X.E (R.N m2)).symm.toLinearMap = x :=
    LinearMap.ext fun v => rfl
  rw [e, Finset.prod_const_one, inv_one, inv_one, mul_one, ea'] at law
  rw [Finset.prod_congr rfl fun P _ => hprod P]
  exact law

end GlobalTheory.StabLaw
end
end

section

noncomputable section

namespace GlobalTheory.UnUnitCmp.Val

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

def intFin (L : Type) [Field L] [NumberField L] : Subring (FiniteAdeleRing (𝓞 L) L) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers L}
  one_mem' := fun _ => one_mem _
  zero_mem' := fun _ => zero_mem _
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem finite_quot (N : ℕ) (hN : 0 < N) : Finite (intFin L ⧸ Ideal.span {(N : intFin L)}) := by
  let ι : 𝓞 L →+* intFin L :=
    ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap (𝓞 L) L)).codRestrict _
      fun x v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v x
  have : Finite (𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 L)})
    (Ideal.span {(N : intFin L)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : intFin L)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat L N hN).2 z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : FiniteAdeleRing (𝓞 L) L) - algebraMap L _ (x : L) = ((N : intFin L) : FiniteAdeleRing (𝓞 L) L) * w
    rw [h, add_sub_cancel_left, nsmul_eq_mul]
    simp

theorem finUnit_pow (χ : _root_.Formalism.L2.Host.HChar L) (hχ : χ.IsUnitary) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : _root_.Neutral.B1.Ideles L, _root_.Formalism.L2.Host.IsFinIdele u → u ∈ unitIdl L → ((χ.1 u : ℂˣ) : ℂ) ^ m = 1 := by
  let ψ : _root_.Neutral.B1.Ideles L →* Circle :=
    { toFun := fun x => ⟨(χ.1 x : ℂˣ), by simpa [Submonoid.unitSphere] using hχ x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => Subtype.ext (congrArg Units.val (map_mul χ.1 x y)) }
  have hψ : Continuous ψ := (Units.continuous_val.comp χ.2.1).subtype_mk _
  obtain ⟨-, -, -, m, hm, h⟩ := GlobalTheory.CharFin.finite_order_of_small (R := AdeleRing (𝓞 L) L)
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (RingHom.snd _ _) id continuous_id (fun _ => rfl) (intFin L)
    (fun W hW => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele L W hW) finite_quot ψ hψ
  refine ⟨m, hm, fun u h1 h2 => ?_⟩
  have := h u ⟨funext h1, fun v => (h2 v).le, fun v => ((unitIdl L).inv_mem h2 v).le⟩
  exact congrArg (fun z : Circle => (z : ℂ)) this

theorem infDiag_mul_finPartI (k : Lˣ) : _root_.Formalism.L2.Host.infDiag k * finPartI L (_root_.Neutral.B1.diagUnits L k) = _root_.Neutral.B1.diagUnits L k := by
  classical
  have h : ((_root_.Formalism.L2.Host.infDiag k : _root_.Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold _root_.Formalism.L2.Host.infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) = ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem exists_pow_eq (x : _root_.Neutral.B1.Ideles L) (hx : _root_.Formalism.L2.Host.IsFinIdele x) :
    ∃ h : ℕ, 0 < h ∧ ∃ (u : _root_.Neutral.B1.Ideles L) (k : Lˣ), _root_.Formalism.L2.Host.IsFinIdele u ∧ u ∈ unitIdl L ∧ x ^ h * _root_.Formalism.L2.Host.infDiag k = u * _root_.Neutral.B1.diagUnits L k := by
  have := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨_, Nat.pos_of_ne_zero this.index_ne_zero, ?_⟩
  obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (_root_.Neutral.B1.diagUnits L).range).pow_index_mem x)
  have hf : finPartI L x = x := Units.ext (Prod.ext (funext hx).symm rfl)
  refine ⟨finPartI L u, k, fun _ => rfl, hu, ?_⟩
  rw [← hf, ← map_pow, ← e, map_mul, mul_assoc, mul_comm _ (_root_.Formalism.L2.Host.infDiag k), infDiag_mul_finPartI]

end GlobalTheory.UnUnitCmp.Val
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.unramifiedAt_value_heckeChar_comp_ideleNorm : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (ψ : HChar K) (ψ' : HChar M), (∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x)) → ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f → ψ.UnrAt (w.under (𝓞 K)) → ψ'.UnrAt w ∧ ψ'.val w = ψ.val (w.under (𝓞 K)) ^ f := by
  first | exact @GlobalTheory.NormValGen.unrAt_val_of_comp_norm | exact GlobalTheory.NormValGen.unrAt_val_of_comp_norm | (intros; apply GlobalTheory.NormValGen.unrAt_val_of_comp_norm <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.HilbertClassField

theorem _root_.GlobalTheory.T.cmLattice_good_model_unramified : (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) → ReciprocityTheory.ChartRestriction.L1.ChebOmSt → Formalism.L2.Th1.CM.CM2 := by
  first | exact @GlobalTheory.ArtinClassCM.good_model | exact GlobalTheory.ArtinClassCM.good_model | (intros; apply GlobalTheory.ArtinClassCM.good_model <;> assumption)
end
