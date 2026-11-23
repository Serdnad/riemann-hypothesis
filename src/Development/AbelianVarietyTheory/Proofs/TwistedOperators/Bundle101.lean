module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

private theorem jpq_eq_diagonal' (p q : ℕ) : Formalism.UG.Jpq p q =
    Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => (-1 : ℂ))) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

private theorem mul_jpq_comm_of_isKC {p q : ℕ} (X : Mat p q) (hX : IsKC X) :
    X * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * X := by
  rw [jpq_eq_diagonal']
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · simp [hX (Sum.inl a) (Sum.inr b) (by simp [sameBlock])]
  · simp [hX (Sum.inr a) (Sum.inl b) (by simp [sameBlock])]
  · simp

private theorem Jpq_mul_Jpq_mul (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  rw [jpq_eq_diagonal', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp

private theorem exists_UJ_umat_eq_of_inUJ {p q : ℕ} (g : Mat p q) (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q)
    (hK : IsKC g) : gᴴ * g = 1 := by
  calc gᴴ * g = gᴴ * g * (Formalism.UG.Jpq p q * Formalism.UG.Jpq p q) := by rw [Jpq_mul_Jpq_mul, Matrix.mul_one]
    _ = gᴴ * (g * Formalism.UG.Jpq p q) * Formalism.UG.Jpq p q := by simp only [Matrix.mul_assoc]
    _ = gᴴ * Formalism.UG.Jpq p q * g * Formalism.UG.Jpq p q := by rw [mul_jpq_comm_of_isKC g hK]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jpq_mul_Jpq_mul]

private theorem unitary_inv_of_unitary {n : Type} [Fintype n] [DecidableEq n] (u : GL n ℂ)
    (hu : (u : Matrix n n ℂ)ᴴ * (u : Matrix n n ℂ) = 1) :
    ((u⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) = 1 := by
  have h1 : ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) = (u : Matrix n n ℂ)ᴴ := by
    calc ((u⁻¹ : GL n ℂ) : Matrix n n ℂ)
        = (u : Matrix n n ℂ)ᴴ * (u : Matrix n n ℂ) * ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
          rw [hu, Matrix.one_mul]
      _ = (u : Matrix n n ℂ)ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h1, Matrix.conjTranspose_conjTranspose, ← h1]
  exact Units.mul_inv u

private theorem conjTranspose_mul_self_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) : (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, Matrix.one_mul, hB]

private theorem pY_mem_upq {p q : ℕ} (B : Fin p → Fin q → ℂ) : pY B ∈ upq p q := by
  show (pY B)ᴴ * Jm p q + Jm p q * pY B = 0
  rw [show Jm p q = Formalism.UG.Jpq p q from rfl, jpq_eq_diagonal']
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp [pY, pOf, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

private theorem eq_pY_of_mem_pR {p q : ℕ} (Y : Mat p q) (hYm : Y ∈ pR p q) :
    Y = pY (fun i j => Y (Sum.inl i) (Sum.inr j)) := by
  have h2 : Y ∈ upq p q ∧ IsPC Y := hYm
  have hY : Yᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * Y = 0 := h2.1
  have hP : ∀ a b, sameBlock a b → Y a b = 0 := h2.2
  rw [jpq_eq_diagonal'] at hY
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · rw [hP _ _ (by simp [sameBlock])]
    simp [pY, pOf]
  · simp [pY, pOf]
  · have h := congrArg (fun M : Mat p q => M (Sum.inr i) (Sum.inl j)) hY
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply] at h
    simp only [pY, pOf, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, Matrix.of_apply]
    linear_combination -h
  · rw [hP _ _ (by simp [sameBlock])]
    simp [pY, pOf]

theorem exists_action_on_p : ∀ (p q : ℕ) (T : GrpData p q) (L : Mat p q → (Fin p → Fin q → ℂ)), ContinuousOn L {g | IsUnit g} → (∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B) → (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ g : T.G, ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧ ∀ B, ∃ κ ∈ T.Kset, T.expt (pY B) * g = κ * T.expt (pY (ψ B)) := by
  intro p q T L hLc hL hdec g
  have hexp : ∀ X ∈ upq p q, ((T.cov (T.expt X) : GL _ ℂ) : Mat p q) = NormedSpace.exp X := T.16
  have hec : ContinuousOn T.expt (upq p q) := T.17
  have hcov : Continuous fun x : T.G => ((T.cov x : GL _ ℂ) : Mat p q) :=
    Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)
  have hKu : ∀ k ∈ T.Kset, ((T.cov k : GL _ ℂ) : Mat p q)ᴴ * ((T.cov k : GL _ ℂ) : Mat p q) = 1 := by
    intro k hk
    exact exists_UJ_umat_eq_of_inUJ ((T.cov k : GL _ ℂ) : Mat p q) (T.cov_mem k) hk
  have hKinv : ∀ k ∈ T.Kset,
      ((T.cov k⁻¹ : GL _ ℂ) : Mat p q)ᴴ * ((T.cov k⁻¹ : GL _ ℂ) : Mat p q) = 1 := by
    intro k hk
    rw [map_inv]
    exact unitary_inv_of_unitary _ (hKu k hk)
  have hev : ∀ u : T.G, ((T.cov u : GL _ ℂ) : Mat p q)ᴴ * ((T.cov u : GL _ ℂ) : Mat p q) = 1 →
      ∀ C, L ((T.cov (u * T.expt (pY C)) : GL _ ℂ) : Mat p q) = C := by
    intro u hu C
    rw [map_mul, Units.val_mul, hexp _ (pY_mem_upq C)]
    exact hL _ C hu
  have hkey : ∀ h : T.G, ∃ k ∈ T.Kset,
      h = k * T.expt (pY (L ((T.cov h : GL _ ℂ) : Mat p q))) := by
    intro h
    obtain ⟨k, hk, Y, hY, rfl⟩ := hdec h
    obtain ⟨C, hC⟩ : ∃ C, Y = pY C := ⟨_, eq_pY_of_mem_pR Y hY⟩
    subst hC
    exact ⟨k, hk, by rw [hev k (hKu k hk) C]⟩
  refine ⟨fun B => L ((T.cov (T.expt (pY B) * g) : GL _ ℂ) : Mat p q), ?_, ?_, ?_⟩
  · have hof : Continuous fun B : Fin p → Fin q → ℂ => (Matrix.of B : Matrix (Fin p) (Fin q) ℂ) :=
      continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop
    have hpY : Continuous fun B : Fin p → Fin q → ℂ => pY B := by
      simp only [pY, pOf]
      exact Continuous.matrix_fromBlocks continuous_const hof hof.matrix_conjTranspose continuous_const
    have hE : Continuous fun B : Fin p → Fin q → ℂ => T.expt (pY B) :=
      hec.comp_continuous hpY pY_mem_upq
    have hM : Continuous fun B : Fin p → Fin q → ℂ =>
        ((T.cov (T.expt (pY B) * g) : GL _ ℂ) : Mat p q) :=
      hcov.comp (hE.mul continuous_const)
    exact hLc.comp_continuous hM (fun B => (T.cov _).isUnit)
  · constructor
    · intro B1 B2 h12
      dsimp only at h12
      obtain ⟨k1, hk1, e1⟩ := hkey (T.expt (pY B1) * g)
      obtain ⟨k2, hk2, e2⟩ := hkey (T.expt (pY B2) * g)
      rw [← h12] at e2
      generalize L ((T.cov (T.expt (pY B1) * g) : GL _ ℂ) : Mat p q) = C at e1 e2
      have f1 := eq_mul_inv_of_mul_eq e1
      have f2 := eq_mul_inv_of_mul_eq e2
      have e3 : T.expt (pY B1) = (k1 * k2⁻¹) * T.expt (pY B2) := by
        rw [f1, f2]
        group
      have hB1 : L ((T.cov (1 * T.expt (pY B1)) : GL _ ℂ) : Mat p q) = B1 := hev 1 (by simp) B1
      have hB2 : L ((T.cov ((k1 * k2⁻¹) * T.expt (pY B2)) : GL _ ℂ) : Mat p q) = B2 :=
        hev _ (by rw [map_mul, Units.val_mul]; exact conjTranspose_mul_self_mul_eq_one _ _ (hKu k1 hk1) (hKinv k2 hk2)) B2
      rw [one_mul, e3] at hB1
      exact hB1.symm.trans hB2
    · intro C
      obtain ⟨k, hk, e⟩ := hkey (T.expt (pY C) * g⁻¹)
      refine ⟨L ((T.cov (T.expt (pY C) * g⁻¹) : GL _ ℂ) : Mat p q), ?_⟩
      dsimp only
      generalize L ((T.cov (T.expt (pY C) * g⁻¹) : GL _ ℂ) : Mat p q) = B at e ⊢
      have f := eq_inv_mul_of_mul_eq e.symm
      have e' : T.expt (pY B) * g = k⁻¹ * T.expt (pY C) := by
        rw [f]
        group
      rw [e']
      exact hev _ (hKinv k hk) C
  · intro B
    exact hkey (T.expt (pY B) * g)

end GlobalTheory.PolarU
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem exists_lift_blocks (p q : ℕ) (T : GrpData p q) :
    ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  intro U hU V hV
  have hU1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hU2 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hV1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hV2 := Matrix.mem_unitaryGroup_iff'.1 hV
  rw [star_eq_conjTranspose] at hU1 hU2 hV1 hV2
  let g : GL (Ix p q) ℂ :=
    ⟨Matrix.fromBlocks U 0 0 V, Matrix.fromBlocks Uᴴ 0 0 Vᴴ,
      by simp [Matrix.fromBlocks_multiply, hU1, hV1],
      by simp [Matrix.fromBlocks_multiply, hU2, hV2]⟩
  have hg : g ∈ Formalism.UG.Upq p q := by
    show (Matrix.fromBlocks U 0 0 V : Mat p q)ᴴ * Formalism.UG.Jpq p q * Matrix.fromBlocks U 0 0 V
      = Formalism.UG.Jpq p q
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU2, hV2]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((g : GL (Ix p q) ℂ) : Mat p q).det
    (show 0 < 2 by norm_num)
  have hdet : ((g : GL (Ix p q) ℂ) : Mat p q).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hw]; simp)
  obtain ⟨k, ⟨hk, -⟩, -⟩ := T.bij g hg (Units.mk0 w hw0) hw
  have hm : matG T k = Matrix.fromBlocks U 0 0 V := by
    unfold matG; rw [hk]
  refine ⟨k, ?_, hm⟩
  show IsKC (matG T k)
  rw [hm]
  intro a b hab
  cases a <;> cases b <;> simp_all [sameBlock]

end GlobalTheory.PolarU
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

variable {p q : ℕ}

def posMat (p q : ℕ) (f : Bool → ℕ → Bool → ℕ → ℂ) : Mat p q :=
  Matrix.of fun a b => f a.isLeft (posIx a) b.isLeft (posIx b)

theorem sum_ite_val {n : ℕ} (m : ℕ) (g : ℕ → ℂ) :
    (∑ j : Fin n, if m = (j : ℕ) then g j else 0) = if m < n then g m else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨m, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [if_neg]
      rintro rfl
      exact hb rfl
    · simp
  · refine Finset.sum_eq_zero fun j _ => if_neg ?_
    rintro rfl
    exact h j.2

theorem posIx_inl (i : Fin p) : posIx (Sum.inl i : Ix p q) = i := rfl

theorem posIx_inr (j : Fin q) : posIx (Sum.inr j : Ix p q) = j := rfl

theorem aOf_apply (h : ℕ → ℝ) (a b : Ix p q) :
    aOf p q h a b = if a.isLeft = b.isLeft then 0
      else if posIx a = posIx b then ((h (posIx a) : ℝ) : ℂ) else 0 := by
  rcases a with i | i <;> rcases b with j | j <;> by_cases hij : (i : ℕ) = j <;>
    simp [aOf, pOf, posIx_inl, posIx_inr, hij, eq_comm (a := (j : ℕ))]

theorem aOf_symm (h : ℕ → ℝ) (a b : Ix p q) : aOf p q h a b = aOf p q h b a := by
  rw [aOf_apply, aOf_apply]
  by_cases h1 : a.isLeft = b.isLeft
  · simp [h1]
  · by_cases h2 : posIx a = posIx b
    · simp [h1, Ne.symm h1, h2]
    · simp [h1, Ne.symm h1, h2, Ne.symm h2]

theorem sum_aOf (h : ℕ → ℝ) (a : Ix p q) (g : Bool → ℕ → ℂ) :
    ∑ c, aOf p q h a c * g c.isLeft (posIx c)
      = (cutH p q h (posIx a) : ℂ) * g (!a.isLeft) (posIx a) := by
  rw [Fintype.sum_sum_type]
  rcases a with i | i
  · have h1 : ∀ k : Fin p, aOf p q h (Sum.inl i) (Sum.inl k) = 0 := fun k => by simp [aOf_apply]
    have h2 : ∀ k : Fin q, aOf p q h (Sum.inl i) (Sum.inr k) * g false k
        = if (i : ℕ) = k then ((h i : ℝ) : ℂ) * g false k else 0 := fun k => by
      by_cases hk : (i : ℕ) = k <;> simp [aOf_apply, posIx_inl, posIx_inr, hk]
    simp only [h1, posIx_inl, posIx_inr, Sum.isLeft_inl, Sum.isLeft_inr, h2, zero_mul,
      Finset.sum_const_zero, zero_add, Bool.not_true]
    rw [sum_ite_val (n := q) i (fun m => ((h i : ℝ) : ℂ) * g false m)]
    by_cases hi : (i : ℕ) < q <;> simp [cutH, hi]
  · have h1 : ∀ k : Fin q, aOf p q h (Sum.inr i) (Sum.inr k) = 0 := fun k => by simp [aOf_apply]
    have h2 : ∀ k : Fin p, aOf p q h (Sum.inr i) (Sum.inl k) * g true k
        = if (i : ℕ) = k then ((h i : ℝ) : ℂ) * g true k else 0 := fun k => by
      by_cases hk : (i : ℕ) = k <;> simp [aOf_apply, posIx_inl, posIx_inr, hk]
    simp only [h1, posIx_inl, posIx_inr, Sum.isLeft_inl, Sum.isLeft_inr, h2, zero_mul,
      Finset.sum_const_zero, add_zero, Bool.not_false]
    rw [sum_ite_val (n := p) i (fun m => ((h i : ℝ) : ℂ) * g true m)]
    by_cases hi : (i : ℕ) < p <;> simp [cutH, hi]

theorem ad_aOf_posMat (h : ℕ → ℝ) (f : Bool → ℕ → Bool → ℕ → ℂ) :
    aOf p q h * posMat p q f - posMat p q f * aOf p q h
      = posMat p q fun s m t n =>
        (cutH p q h m : ℂ) * f (!s) m t n - (cutH p q h n : ℂ) * f s m (!t) n := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.mul_apply, posMat, Matrix.of_apply]
  rw [sum_aOf h a (fun s m => f s m b.isLeft (posIx b)),
    ← sum_aOf h b (fun t n => f a.isLeft (posIx a) t n)]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm, aOf_symm]

theorem eigP_eq_posMat (ab : PIx p q) :
    eigP ab.1 = vecM (posMat p q fun s m t n =>
      if s ≠ t ∧ m = posIx ab.1.1 ∧ n = posIx ab.1.2 then
        (if ab.1.1.isLeft then 1 else if s then -1 else 1) else 0) := by
  obtain ⟨⟨a, b⟩, hab⟩ := ab
  funext ⟨c, d⟩
  rcases a with i | i <;> rcases b with j | j <;> simp only [sameBlock, not_true] at hab <;>
    rcases c with k | k <;> rcases d with l | l <;>
    simp [eigP, vecM, posMat, posIx_inl, posIx_inr, sameBlock, Fin.ext_iff]
  split_ifs <;> rfl

theorem adMat_sq_mulVec_eigP (p q : ℕ) (h : ℕ → ℝ) (ab : PIx p q) :
    (adMat (aOf p q h) ^ 2) *ᵥ eigP ab.1 = (((rootP h ab.1 : ℝ) : ℂ) ^ 2) • eigP ab.1 := by
  rw [pow_two (adMat _), ← Matrix.mulVec_mulVec, eigP_eq_posMat, adMat_mulVec, ad_aOf_posMat,
    adMat_mulVec, ad_aOf_posMat]
  funext ⟨c, d⟩
  simp only [vecM, posMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, rootP, Bool.not_not]
  generalize c.isLeft = s
  generalize d.isLeft = t
  generalize ab.1.1.isLeft = u
  by_cases hm : posIx c = posIx ab.1.1 ∧ posIx d = posIx ab.1.2
  · rw [hm.1, hm.2]
    cases s <;> cases t <;> cases u <;> simp <;> ring
  · simp [hm]

end GlobalTheory.PolarU
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU.RootProd

theorem shc_neg' (x : ℝ) : shc (-x) = shc x := by
  unfold shc
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (neg_ne_zero.mpr hx), if_neg hx, Real.sinh_neg, neg_div_neg_eq]

theorem shc_zero' : shc 0 = 1 := by
  unfold shc
  exact if_pos rfl

theorem prod_square (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, F i j =
      (∏ i ∈ Finset.range n, F i i) *
        ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F i j * F j i else 1 := by

  have split3 : ∀ i j, F i j = (if j = i then F i i else 1) * (if i < j then F i j else 1) *
      (if j < i then F i j else 1) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, hij.ne', not_lt.mpr hij.le]
    · simp
    · simp [hji, hji.ne, not_lt.mpr hji.le]
  have row : ∀ i ∈ Finset.range n, (∏ j ∈ Finset.range n, F i j) =
      F i i * ((∏ j ∈ Finset.range n, if i < j then F i j else 1) *
        ∏ j ∈ Finset.range n, if j < i then F i j else 1) := by
    intro i hi
    have hd : (∏ j ∈ Finset.range n, if j = i then F i i else 1) = F i i := by
      rw [Finset.prod_ite_eq']
      exact if_pos hi
    rw [← Finset.prod_mul_distrib, ← hd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← mul_assoc]; exact split3 i j

  have below : (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if j < i then F i j else 1) =
      ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F j i else 1 :=
    Finset.prod_comm
  rw [Finset.prod_congr rfl row, Finset.prod_mul_distrib, Finset.prod_mul_distrib, below,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem prod_PIx (p q : ℕ) (h : ℕ → ℝ) :
    ∏ ab : PIx p q, shc (rootP h ab.1) =
      ∏ i ∈ Finset.range p, ∏ j ∈ Finset.range q,
        shc (cutH p q h i - cutH p q h j) * shc (cutH p q h i + cutH p q h j) := by

  rw [← Finset.prod_subtype (Finset.univ.filter fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2)
    (fun ab => by simp) (fun ab => shc (rootP h ab))]
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, sameBlock, not_true_eq_false, not_false_eq_true, if_false,
    if_true, Finset.prod_const_one, one_mul, mul_one, rootP, Sum.isLeft_inl, Sum.isLeft_inr,
    posIx, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true]
  simp_rw [Finset.prod_range, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by rw [add_comm]

theorem prod_rect (m d : ℕ) (h c : ℕ → ℝ) (hc : ∀ n, c n = if n < m then h n else 0) :
    ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j) =
      (∏ i ∈ Finset.range m, shc (2 * h i) * shc (h i) ^ (2 * d)) *
        ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
          if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  have hin : ∀ i ∈ Finset.range m, c i = h i := fun i hi => by
    rw [hc, if_pos (Finset.mem_range.mp hi)]
  have hout : ∀ k, c (m + k) = 0 := fun k => by
    rw [hc, if_neg (by omega)]

  have swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b) := fun a b => by
    rw [show b - a = -(a - b) by ring, shc_neg', add_comm b a]

  have row : ∀ i ∈ Finset.range m,
      (∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j)) =
        (∏ j ∈ Finset.range m, shc (h i - h j) * shc (h i + h j)) * shc (h i) ^ (2 * d) := by
    intro i hi
    rw [Finset.prod_range_add]
    congr 1
    · exact Finset.prod_congr rfl fun j hj => by rw [hin i hi, hin j hj]
    · simp only [hout, hin i hi, sub_zero, add_zero]
      rw [Finset.prod_const, Finset.card_range, ← pow_two, ← pow_mul]
  have diag : ∀ i, shc (h i - h i) * shc (h i + h i) = shc (2 * h i) := fun i => by
    rw [sub_self, shc_zero', one_mul, two_mul]
  have off : ∀ i j, (if i < j then shc (h i - h j) * shc (h i + h j) * (shc (h j - h i) * shc (h j + h i))
      else 1) = if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := fun i j => by
    rw [swap (h i) (h j), sq]
  rw [Finset.prod_congr rfl row, Finset.prod_mul_distrib,
    prod_square m (fun i j => shc (h i - h j) * shc (h i + h j))]
  simp only [diag]
  rw [Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => off i j]
  ring

theorem prod_shc_rootP : ∀ (p q : ℕ) (h : ℕ → ℝ), ∏ ab : PIx p q, shc (rootP h ab.1) = (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) * ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  intro p q h
  have hm : min p q + (max p q - min p q) = max p q := Nat.add_sub_cancel' min_le_max
  have swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b) := fun a b => by
    rw [show b - a = -(a - b) by ring, shc_neg', add_comm b a]
  rw [← prod_rect (min p q) (max p q - min p q) h (cutH p q h) (fun n => rfl), hm, prod_PIx]
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, max_eq_right hpq]
  ·
    rw [min_eq_right hqp, max_eq_left hqp, Finset.prod_comm]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => swap _ _

end GlobalTheory.PolarU.RootProd
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.compressedWords_glWordJetRelations_of_no_types : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V), LowData ε E Λ u j → (∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) → JetRel ε E Λ u j (modJet E j) := by
  first | exact @GlobalTheory.SphJet.ModRel.modJet_jetRel | exact GlobalTheory.SphJet.ModRel.modJet_jetRel | (intros; apply GlobalTheory.SphJet.ModRel.modJet_jetRel <;> assumption)
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.glWordJetRelations_multiplication_equivariant : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (m : ℕ), LowData ε E Λ u j → JetRel ε E Λ u j B → ∀ c d : Fin n, ε c = ε d → ∀ y y' : W, j y' = E d c (j y) → ∀ G G' : (Fin m → Fin n × Fin n) → W, arrTo V n m (fun α => j (G' α)) = arrE E m c d (arrTo V n m fun α => j (G α)) → ∑ α, B (List.ofFn α).reverse y (G' α) = ∑ α, B (List.ofFn α).reverse y' (G α) := by
  first | exact @GlobalTheory.SphJet.jetRel_equivariant | exact GlobalTheory.SphJet.jetRel_equivariant | (intros; apply GlobalTheory.SphJet.jetRel_equivariant <;> assumption)
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.iteratedDeriv_inner_exp_eq_wordJetForms : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) [CompleteSpace W] (j : W →ₗᵢ[ℂ] V) (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)), AnalyticAt ℂ f 1 → (∀ l, funJet ε f l = modJet E j l) → ∀ (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (y x : W), iteratedDeriv m (fun t : ℝ => ⟪y, f (NormedSpace.exp ((t : ℂ) • thM ε X)) x⟫_ℂ) 0 = ⟪j y, (actM E X ^ m) (j x)⟫_ℂ := by
  first | exact @GlobalTheory.SphJet.Taylor.iteratedDeriv_inner_exp | exact GlobalTheory.SphJet.Taylor.iteratedDeriv_inner_exp | (intros; apply GlobalTheory.SphJet.Taylor.iteratedDeriv_inner_exp <;> assumption)
end
