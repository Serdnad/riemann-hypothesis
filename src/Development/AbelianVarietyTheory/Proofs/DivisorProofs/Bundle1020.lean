module

public import Formalism.LocalToGlobal.Divisibility.Numbers
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfIrr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ColNorms.NumMean

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms

theorem log_le_of_le_exp {y X : ℝ} (hy : 0 ≤ y) (hX : 0 ≤ X) (h : y ≤ Real.exp X) : Real.log y ≤ X := by
  rcases hy.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; exact hX
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem log_mul_le {h h' : ℕ} {X : ℝ} (hX : 0 ≤ X) (h1 : (h : ℝ) ≤ Real.exp X) (h2 : (h' : ℝ) ≤ Real.exp X) :
    Real.log ((h : ℝ) * h') ≤ 2 * X := by
  refine log_le_of_le_exp (by positivity) (by linarith) ?_
  rw [two_mul, Real.exp_add]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem one_le_rd (N : NumDatum) : 1 ≤ N.rd := by
  have h : (4 * N.R.ord : ℝ) ≤ N.rd ^ 2 := N.H.der.rd_sq_ge
  have h0 : (0 : ℝ) ≤ N.rd := by
    unfold NumDatum.rd Formalism.HC.HostRaw.rd
    positivity
  have ho : (1 : ℝ) ≤ N.R.ord := by exact_mod_cast N.R.ord_pos
  nlinarith

theorem one_le_L (s : Scale) : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le

theorem two_le_b (s : Scale) : 2 ≤ s.b := by
  have := Real.add_one_le_exp s.L
  have := one_le_L s
  unfold Scale.b; linarith

theorem card_RPl (R : Ranks) : (Fintype.card (RPl R) : ℝ) = R.f := by
  have h : Fintype.card R.A = R.ord := R.card_A
  simp [RPl, Ranks.f, Ranks.n, h]

theorem N_le (N : NumDatum) {j : ℕ} (hj : j ≤ N.R.m) : (N.R.N j : ℝ) ≤ N.Nm := by
  have : N.R.N j ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
  exact_mod_cast this

theorem log_le_mul (s : Scale) {y : ℝ} (hy : 0 ≤ y) (k : ℕ) (h : y ≤ s.b ^ k) : Real.log y ≤ k * s.L := by
  have := one_le_L s
  refine log_le_of_le_exp hy (by positivity) ?_
  rw [Real.exp_nat_mul]; exact h

end GlobalTheory.ColNorms.NumMean
end
end

section

open Matrix Formalism.IndefR.Datum
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.CartanRefl

theorem exists_sign {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (hG : G.IsHermitian) (hd : G.det ≠ 0) :
    ∃ s, IsCartanInv G s ∧ ∀ u, u * G = G * u → u * s = s * u := by
  classical
  let U : Matrix (Fin k) (Fin k) ℂ := hG.eigenvectorUnitary.1
  have h1 : U * star U = 1 := hG.eigenvectorUnitary.2.2
  have h2 : star U * U = 1 := hG.eigenvectorUnitary.2.1
  have hs : G = U * diagonal (fun i => (hG.eigenvalues i : ℂ)) * star U := by
    have := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hne : ∀ i, hG.eigenvalues i ≠ 0 := fun i hi => by
    rw [hG.det_eq_prod_eigenvalues] at hd
    exact hd (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))
  have mul : ∀ a b : Fin k → ℂ, (U * diagonal a * star U) * (U * diagonal b * star U) =
      U * diagonal (fun i => a i * b i) * star U := fun a b => by
    calc _ = U * (diagonal a * (star U * U) * diagonal b) * star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one, diagonal_mul_diagonal]
  let e : Fin k → ℝ := fun i => if 0 < hG.eigenvalues i then 1 else -1
  have he : ∀ i, (e i : ℂ) * e i = 1 := fun i => by
    simp only [e]; split_ifs <;> simp
  have hh : (U * diagonal (fun i => (e i : ℂ)) * star U)ᴴ = U * diagonal (fun i => (e i : ℂ)) * star U := by
    simp [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      Pi.star_def]
  refine ⟨U * diagonal (fun i => (e i : ℂ)) * star U, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [mul]
    simp only [he, diagonal_one, Matrix.mul_one, h1]
  · rw [hh]
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [mul, mul]
    congr 3
    funext i
    rw [mul_right_comm, he, one_mul]
  · conv => arg 1; arg 1; rw [hs]
    rw [mul]
    have hp : (diagonal fun i => (hG.eigenvalues i : ℂ) * e i).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      rw [← Complex.ofReal_mul, Complex.zero_lt_real]
      simp only [e]
      split_ifs with h
      · simpa using h
      · have := lt_of_le_of_ne (not_lt.1 h) (hne i)
        linarith
    have hu : IsUnit (star U) := ⟨⟨star U, U, h2, h1⟩, rfl⟩
    have := hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose] at this
  · intro u hu
    obtain ⟨v, rfl⟩ : ∃ v, u = U * v * star U := ⟨star U * u * U, by
      calc u = (U * star U) * u * (U * star U) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]⟩
    have cm : ∀ a b : Matrix (Fin k) (Fin k) ℂ, (U * a * star U) * (U * b * star U) = U * (a * b) * star U := fun a b => by
      calc _ = U * (a * (star U * U) * b) * star U := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2, Matrix.mul_one]
    have inj : ∀ a b : Matrix (Fin k) (Fin k) ℂ, U * a * star U = U * b * star U → a = b := fun a b h => by
      have key : ∀ a : Matrix (Fin k) (Fin k) ℂ, star U * (U * a * star U) * U = a := fun a => by
        calc _ = (star U * U) * a * (star U * U) := by simp only [Matrix.mul_assoc]
          _ = a := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      rw [← key a, h, key]
    have hv : v * diagonal (fun i => (hG.eigenvalues i : ℂ)) = diagonal (fun i => (hG.eigenvalues i : ℂ)) * v := by
      apply inj
      rw [← cm, ← cm, ← hs, hu]
    rw [cm, cm]
    congr 2
    ext i j
    have hij := congrFun (congrFun hv i) j
    rw [mul_diagonal, diagonal_mul] at hij ⊢
    by_cases h0 : v i j = 0
    · simp [h0]
    · have : hG.eigenvalues j = hG.eigenvalues i := by
        rw [mul_comm] at hij
        exact_mod_cast mul_right_cancel₀ h0 hij
      simp only [e, this, mul_comm]

theorem exists_comm {k : ℕ} {G r : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ = G) (hd : G.det ≠ 0)
    (hr : r * r = 1) (hrG : rᴴ * G * r = G) : ∃ s, IsCartanInv G s ∧ s * r = r * s := by
  classical
  have hH : (1 + rᴴ * r).PosDef := PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self r)
  obtain ⟨C, hC, hCH⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hH.isStrictlyPositive
  obtain ⟨⟨C, B, hCB, hBC⟩, rfl⟩ := hC
  simp only [star_eq_conjTranspose] at hCH
  have hCB' : Bᴴ * Cᴴ = 1 := by rw [← conjTranspose_mul, hCB, conjTranspose_one]
  have hBC' : Cᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBC, conjTranspose_one]
  have hr' : rᴴ * rᴴ = 1 := by rw [← conjTranspose_mul, hr, conjTranspose_one]
  have e1 : ∀ X : Matrix (Fin k) (Fin k) ℂ, C * (B * X) = X := fun X => by rw [← Matrix.mul_assoc, hCB, Matrix.one_mul]
  have e2 : ∀ X : Matrix (Fin k) (Fin k) ℂ, B * (C * X) = X := fun X => by rw [← Matrix.mul_assoc, hBC, Matrix.one_mul]
  have e3 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Bᴴ * (Cᴴ * X) = X := fun X => by rw [← Matrix.mul_assoc, hCB', Matrix.one_mul]
  have e4 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Cᴴ * (Bᴴ * X) = X := fun X => by rw [← Matrix.mul_assoc, hBC', Matrix.one_mul]
  have e5 : ∀ X : Matrix (Fin k) (Fin k) ℂ, r * (r * X) = X := fun X => by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
  have e6 : ∀ X : Matrix (Fin k) (Fin k) ℂ, rᴴ * (G * (r * X)) = G * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hrG]
  have hinv : rᴴ * (Cᴴ * C) * r = Cᴴ * C := by
    rw [← hCH, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hr', Matrix.one_mul, hr, add_comm]
  have huu : (C * r * B) * (C * r * B) = 1 := by
    simp only [Matrix.mul_assoc, e2, e5, hCB]
  have hsu : (C * r * B)ᴴ * (C * r * B) = 1 := by
    calc _ = Bᴴ * (rᴴ * (Cᴴ * C) * r) * B := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hinv]; simp only [Matrix.mul_assoc, e3, hCB]
  have hu : (C * r * B)ᴴ = C * r * B := by
    calc _ = (C * r * B)ᴴ * ((C * r * B) * (C * r * B)) := by rw [huu, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hsu, Matrix.one_mul]
  have hG' : (Bᴴ * G * B).IsHermitian := isHermitian_conjTranspose_mul_mul B hG
  have hd' : (Bᴴ * G * B).det ≠ 0 := by
    intro h
    apply hd
    have : G = Cᴴ * (Bᴴ * G * B) * C := by simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]
    rw [this, det_mul, det_mul, h, mul_zero, zero_mul]
  have hc : (C * r * B) * (Bᴴ * G * B) = (Bᴴ * G * B) * (C * r * B) := by
    have : (C * r * B)ᴴ * (Bᴴ * G * B) * (C * r * B) = Bᴴ * G * B := by
      simp only [conjTranspose_mul, Matrix.mul_assoc, e4, e2, e6]
    rw [hu] at this
    conv_lhs => rw [← this]
    rw [← Matrix.mul_assoc (C * r * B), ← Matrix.mul_assoc (C * r * B), huu, Matrix.one_mul]
  obtain ⟨s, ⟨hs1, hs2, hs3⟩, hs4⟩ := exists_sign hG' hd'
  have hs5 := hs4 _ hc
  refine ⟨B * s * C, ⟨?_, ?_, ?_⟩, ?_⟩
  · calc _ = B * (s * s) * C := by simp only [Matrix.mul_assoc, e1]
      _ = 1 := by rw [hs1, Matrix.mul_one, hBC]
  · calc _ = Cᴴ * (sᴴ * (Bᴴ * G * B) * s) * C := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hs2]; simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]
  · have hu : IsUnit C := ⟨⟨C, B, hCB, hBC⟩, rfl⟩
    have := hs3.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    simpa only [Matrix.mul_assoc, e4] using this
  · calc _ = B * (s * (C * r * B)) * C := by simp only [Matrix.mul_assoc, hBC, Matrix.mul_one]
      _ = _ := by rw [← hs5]; simp only [Matrix.mul_assoc, e2]

theorem exists_cartan_comm_quasiReflection : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), Gᴴ = G → G.det ≠ 0 → ∀ x : Fin n → ℂ, star x ⬝ᵥ G *ᵥ x ≠ 0 → ∃ s, IsCartanInv G s ∧ ∀ c : ℂ, s * (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) = (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) * s := by
  intro n G hG hd x hx
  set q := star x ⬝ᵥ G *ᵥ x with hq
  have hM : Matrix.vecMulVec x (star x ᵥ* G) = Matrix.vecMulVec x (star x) * G := by
    rw [vecMulVec_mul]
  have hN : (Matrix.vecMulVec x (star x))ᴴ = Matrix.vecMulVec x (star x) := by
    rw [conjTranspose_vecMulVec, star_star]
  have hMM : Matrix.vecMulVec x (star x ᵥ* G) * Matrix.vecMulVec x (star x ᵥ* G) = q • Matrix.vecMulVec x (star x ᵥ* G) := by
    rw [vecMulVec_mul_vecMulVec, hq, dotProduct_mulVec, vecMulVec_smul]
  have hMG : (Matrix.vecMulVec x (star x ᵥ* G))ᴴ * G = G * Matrix.vecMulVec x (star x ᵥ* G) := by
    rw [hM, conjTranspose_mul, hN, hG, Matrix.mul_assoc]
  have hqs : star q = q := by
    rw [hq, ← star_dotProduct_star, star_star, star_mulVec, hG, dotProduct_mulVec]
  generalize Matrix.vecMulVec x (star x ᵥ* G) = M at hMM hMG ⊢
  have hr : (1 + (-2 / q) • M) * (1 + (-2 / q) • M) = 1 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMM,
      smul_smul, add_assoc, ← add_smul, smul_add]
    have : -2 / q + (-2 / q + -2 / q * (-2 / q * q)) = 0 := by field_simp; ring
    rw [this, zero_smul, add_zero]
  have hrG : (1 + (-2 / q) • M)ᴴ * G = G * (1 + (-2 / q) • M) := by
    have : star (-2 / q) = -2 / q := by rw [star_div₀, hqs]; simp
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, this, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMG]
  obtain ⟨s, hs, hc⟩ := exists_comm hG hd hr (by rw [hrG, Matrix.mul_assoc, hr, Matrix.mul_one])
  refine ⟨s, hs, fun c => ?_⟩
  have hsM : s * M = M * s := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      add_right_inj] at hc
    exact smul_right_injective _ (div_ne_zero (by norm_num) hx) hc
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hsM]

end GlobalTheory.CartanRefl
end

section

noncomputable section
namespace GlobalTheory.HcIrr
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV Polynomial CategoryTheory

theorem isIrrRep_of_equiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (A : G → G) (hA : Function.Surjective A)
    (Ψ : V ≃ₗ[ℂ] V') (h : ∀ g v, Ψ (ρ (A g) v) = ρ' g (Ψ v)) (hirr : IsIrrRep ρ') : IsIrrRep ρ := by
  obtain ⟨hn, hW⟩ := hirr
  refine ⟨Ψ.toEquiv.nontrivial, fun W hinv => ?_⟩
  have hinv' : ∀ g, ∀ v ∈ W.map (Ψ : V →ₗ[ℂ] V'), ρ' g v ∈ W.map (Ψ : V →ₗ[ℂ] V') := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨ρ (A g) w, hinv _ _ hw, h g w⟩
  rcases hW _ hinv' with h0 | h1
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hv' : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V') := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot] at hv'
    simpa using hv'
  · right
    refine eq_top_iff.2 fun v _ => ?_
    have : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V') := h1 ▸ Submodule.mem_top
    obtain ⟨w, hw, hwv⟩ := this
    rwa [← Ψ.injective hwv]

theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem isIrrRep_hcRep_of_parInd (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (h : (GlobalTheory.FinGL.parInd (natBlocks b) (leviTensor b lam)).IsIrreducible) : IsIrrRep (hcRep K b lam) := by
  let L : hcSpace K b lam ≃ₗ[ℂ] Representation.coindV (blockTri (κ := K) (natBlocks b)).subtype (leviTensor b lam) :=
    { toFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (blockTri_le_parab b) p) x⟩
      invFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (parab_le_blockTri b) p) x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact isIrrRep_of_equiv (hcRep K b lam) _ id Function.surjective_id L (fun _ _ => rfl)
    (isIrrRep_of_isIrreducible _ h)

theorem exists_sorted {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hb : Function.Surjective b)
    (hl : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) :
    ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧
      Monotone b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ (∀ c, labO O (lam' c) = labO O (lam c)) ∧
      (IsIrrRep (hcRep K b' lam') → IsIrrRep (hcRep K b lam)) := by
  let e : Fin r ≃ Fin r := (Tuple.sort b).symm
  let b' : Fin r → Fin s := b ∘ e.symm
  let ec : ∀ c, {i // b i = c} ≃ {k // b' k = c} := fun c => e.subtypeEquiv (fun i => by simp [b'])
  let lam' : ∀ c : Fin s, FDRep ℂ (GL {k // b' k = c} K) := fun c => transp (ec c) (lam c)
  let A : GL (Fin r) K ≃* GL (Fin r) K := (glEquiv K e).symm
  have hpar : ∀ p : parab K b', A p.1 ∈ parab K b := by
    intro p
    obtain ⟨h1, h2⟩ := p.2
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show Matrix.reindex e.symm e.symm (p.1 : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      exact h1 _ _ (by simpa [b'] using hij)
    · rw [← map_inv]
      show Matrix.reindex e.symm e.symm ((p.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      exact h2 _ _ (by simpa [b'] using hij)
  have hpar' : ∀ q : parab K b, A.symm q.1 ∈ parab K b' := by
    intro q
    obtain ⟨h1, h2⟩ := q.2
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show Matrix.reindex e e (q.1 : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact h1 _ _ hij
    · rw [← map_inv]
      show Matrix.reindex e e ((q.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact h2 _ _ hij
  have hlevi : ∀ (p : parab K b') (c : Fin s),
      levi K b c ⟨A p.1, hpar p⟩ = (glEquiv K (ec c)).symm (levi K b' c p) := by
    intro p c
    apply Units.ext
    ext i j
    rfl
  have hinfl : ∀ p : parab K b', infl K b lam ⟨A p.1, hpar p⟩ = infl K b' lam' p := by
    intro p
    unfold infl
    congr 1
  have hinfl' : ∀ q : parab K b, infl K b lam q = infl K b' lam' ⟨A.symm q.1, hpar' q⟩ := by
    intro q
    rw [← hinfl]
    congr 2
    exact Subtype.ext (A.apply_symm_apply q.1).symm
  let Ψ : hcSpace K b lam ≃ₗ[ℂ] hcSpace K b' lam' :=
    { toFun := fun F => ⟨fun x => F.1 (A x), fun p x => by
        show F.1 (A (p.1 * x)) = infl K b' lam' p (F.1 (A x))
        rw [map_mul, ← hinfl]
        exact F.2 ⟨A p.1, hpar p⟩ (A x)⟩
      invFun := fun F => ⟨fun x => F.1 (A.symm x), fun q x => by
        show F.1 (A.symm (q.1 * x)) = infl K b lam q (F.1 (A.symm x))
        rw [map_mul, hinfl']
        exact F.2 ⟨A.symm q.1, hpar' q⟩ (A.symm x)⟩
      map_add' := fun F G => rfl
      map_smul' := fun a F => rfl
      left_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.apply_symm_apply x))
      right_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.symm_apply_apply x)) }
  refine ⟨b', lam', hb.comp e.symm.surjective, ?_, fun c => ⟨Formalism.L2.PT.simple_transp _ (hl c).1,
    Formalism.L2.PT.isCuspidal_transp _ (hl c).2⟩, fun c => GlobalTheory.SerOSys.TranspLabel.labO_transp O (ec c) (lam c), ?_⟩
  · exact Tuple.monotone_sort b
  · refine isIrrRep_of_equiv _ _ A A.surjective Ψ fun g F => ?_
    apply Subtype.ext
    funext x
    show F.1 (A x * A g) = F.1 (A (x * g))
    rw [map_mul]

theorem labO_eq_of_readings {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (d : ℕ) (e : α ≃ Fin d) (e' : β ≃ Fin d) (σ : FDRep ℂ (GL α K))
    (σ' : FDRep ℂ (GL β K)) (M : (σ : Type) ≃ₗ[ℂ] (σ' : Type))
    (hM : ∀ g v, M (σ.ρ ((glEquiv K e).symm g) v) = σ'.ρ ((glEquiv K e').symm g) (M v)) :
    labO O σ = labO O σ' := by
  rw [← GlobalTheory.SerOSys.TranspLabel.labO_transp O e σ, ← GlobalTheory.SerOSys.TranspLabel.labO_transp O e' σ']
  unfold labO
  apply O.lab_iso
  exact ⟨GlobalTheory.SerOSys.TranspLabel.repIsoOf _ _ M fun γ v => hM _ v⟩

theorem distinctFactors {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hs : ∀ c, Simple (lam c))
    (hinj : Function.Injective (fun c => labO O (lam c))) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.DistinctFactors (natBlocks b) (leviTensor b lam) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne ⟨d, h, h', W, _, _, ρ, hf, hf'⟩
  obtain ⟨e, L, hL⟩ := GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor K r s b lam hs (b i) d h W ρ hf
  obtain ⟨e', L', hL'⟩ := GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor K r s b lam hs (b j) d h' W ρ hf'
  have hlab : labO O (lam (b i)) = labO O (lam (b j)) := by
    refine labO_eq_of_readings O d e e' _ _ (L.symm.trans L') fun g v => ?_
    obtain ⟨w, rfl⟩ := L.surjective v
    rw [← hL]
    simp [hL']
  exact hne (congrArg (fun c : Fin s => (c : ℕ)) (hinj hlab))

theorem isIrrRep_of_monotone {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (hl : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c))
    (hinj : Function.Injective (fun c => labO O (lam c))) (hm : Monotone b) : IsIrrRep (hcRep K b lam) := by
  have hd : GlobalTheory.FinGL.IsCuspDatum (natBlocks b) (leviTensor b lam) :=
    { mono := fun i j hij => hm hij
      irr := GlobalTheory.T.leviPiTensorRepresentation_isIrreducible K r s b lam fun c => (hl c).1
      infl := fun p hp => by
        rw [leviTensor_apply]
        have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) = LinearMap.id := by
          intro c
          have h1 : levi K b c (Subgroup.inclusion (blockTri_le_parab b) p) = 1 := by
            apply Units.ext
            ext x y
            have := hp x.1 y.1 (by simp [natBlocks, x.2, y.2])
            show ((p : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x.1 y.1 = (1 : Matrix _ _ K) x y
            rw [this]
            simp [Matrix.one_apply, Subtype.ext_iff]
          rw [h1, map_one]
          rfl
        simp only [this]
        exact PiTensorProduct.map_id
      cusp := fun S hS y hy => GlobalTheory.T.cuspidal_piTensor_no_blockUnipotent_fixed K r s b lam (fun c => (hl c).2) S hS y hy }
  exact isIrrRep_hcRep_of_parInd b lam
    ((GlobalTheory.CuspFactor.irrPar_iff_cuspidalProduct.1 GlobalTheory.FinGL.IrrProduct.irrPar).1 K r _ _ _ hd
      (distinctFactors O b lam (fun c => (hl c).1) hinj))

theorem isIrrRep_hcRep : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∀ (C : LabelConv K) (O : LabelMap K C),
    Function.Injective (fun c => labO O (lam c)) → IsIrrRep (hcRep K b lam) := by
  intro K _ _ _ r s b lam hb hl C O hinj
  obtain ⟨b', lam', hb', hm, hl', hlab, hback⟩ := exists_sorted O b lam hb hl
  exact hback (isIrrRep_of_monotone O b' lam' hl'
    (fun c c' h => hinj (by simpa [hlab] using h)) hm)

end GlobalTheory.HcIrr
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem unit_mul_logarithmic_lift (p : ℕ) {Kt : Type} [CommRing Kt] (At : Subring Kt)
    (F : Kt →+* Kt) (v v' t : Kt) (_hp : (p : Kt) * p = 0) (hv' : v' ∈ At) (hvv : v * v' = 1)
    (hF : ∃ w ∈ At, F v = v ^ p + p * w) (ht : F t = t ^ p) :
    ∃ w ∈ At, F (v * t) = (v * t) ^ p * (1 + p * w) := by
  obtain ⟨w, hw, hFv⟩ := hF
  refine ⟨v' ^ p * w, At.mul_mem (At.pow_mem hv' p) hw, ?_⟩
  have h1 : v ^ p * v' ^ p = 1 := by rw [← mul_pow, hvv, one_pow]
  rw [map_mul, hFv, ht, mul_pow]
  linear_combination (-(t ^ p * p * w)) * h1

end GlobalTheory.DI
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.frobenius_lift_unit_times_coord : ∀ (p : ℕ) {Kt : Type} [CommRing Kt] (At : Subring Kt) (F : Kt →+* Kt) (v v' t : Kt), (p : Kt) * p = 0 → v' ∈ At → v * v' = 1 → (∃ w ∈ At, F v = v ^ p + p * w) → F t = t ^ p → ∃ w ∈ At, F (v * t) = (v * t) ^ p * (1 + p * w) := by
  first | exact @_root_.GlobalTheory.DI.unit_mul_logarithmic_lift | exact _root_.GlobalTheory.DI.unit_mul_logarithmic_lift | (intros; apply _root_.GlobalTheory.DI.unit_mul_logarithmic_lift <;> assumption)

end
end
