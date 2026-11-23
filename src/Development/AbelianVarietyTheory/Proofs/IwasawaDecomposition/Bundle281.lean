module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle264
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle035
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteImageHeckeSetSplitPlaceCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle273
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PosAgree

open Matrix

variable {k : Type} [CommRing k] {n : ℕ}

theorem vmv_mul_vmv (a α b β : Fin n → k) :
    vecMulVec a α * vecMulVec b β = (α ⬝ᵥ b) • vecMulVec a β := by
  ext i l
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem mul_vmv_mul (A B : Matrix (Fin n) (Fin n) k) (w φ : Fin n → k) :
    A * vecMulVec w φ * B = vecMulVec (A *ᵥ w) (φ ᵥ* B) := by
  ext i l
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun m _ => by ring

theorem vecMul_vmv (φ a α : Fin n → k) : φ ᵥ* vecMulVec a α = (φ ⬝ᵥ a) • α := by
  ext i
  simp only [vecMul, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

def tU (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : GL (Fin n) k :=
  ⟨1 + vecMulVec v φ, 1 - vecMulVec v φ,
    by simp only [add_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv, h, zero_smul]; abel,
    by simp only [sub_mul, mul_add, one_mul, mul_one, vmv_mul_vmv, h, zero_smul]; abel⟩

theorem tU_val (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : (tU v φ h).val = 1 + vecMulVec v φ := rfl

theorem tU_inv_val (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : (tU v φ h)⁻¹.val = 1 - vecMulVec v φ := rfl

theorem conj_val (g : GL (Fin n) k) (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) :
    (g * tU v φ h * g⁻¹).val = 1 + vecMulVec (g.val *ᵥ v) (φ ᵥ* (g⁻¹).val) := by
  rw [Units.val_mul, Units.val_mul, tU_val, mul_add, add_mul, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    mul_vmv_mul]

theorem tU_mem_unip (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) (hl : ∀ i l : Fin n, l.val ≤ i.val → v i * φ l = 0) :
    tU v φ h ∈ unip k n := by
  refine ⟨fun i l (hli : l.val < i.val) => ?_, fun i => ?_⟩
  · rw [tU_val, Matrix.add_apply, vecMulVec_apply, hl i l hli.le, one_apply_ne (fun e => by rw [e] at hli; omega), add_zero]
  · rw [tU_val, Matrix.add_apply, vecMulVec_apply, hl i i le_rfl, one_apply_eq, add_zero]

theorem transvection_eq (i j : Fin n) (c : k) :
    transvection i j c = 1 + vecMulVec (Pi.single i c) (Pi.single j 1) := by
  unfold transvection
  congr 1
  ext p q
  simp only [single_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

end GlobalTheory.PosAgree

namespace GlobalTheory.PosAgree

open Matrix

variable {k : Type} [CommRing k] {n : ℕ}

theorem sdot (p q : Fin n) (x : k) (h : q ≠ p) : Pi.single q 1 ⬝ᵥ Pi.single p x = 0 := by
  rw [single_dotProduct, Pi.single_apply, if_neg h, mul_zero]

theorem comm_a (p0 p1 pm : Fin n) (h01 : p0 ≠ p1) (h0m : p0 ≠ pm) (h1m : p1 ≠ pm) :
    (tU (Pi.single pm (1 : k)) (Pi.single p0 1) (sdot _ _ _ h0m))⁻¹ *
      (tU (Pi.single p0 1) (Pi.single p1 1) (sdot _ _ _ h01.symm) * tU (Pi.single pm 1) (Pi.single p0 1) (sdot _ _ _ h0m) *
        (tU (Pi.single p0 1) (Pi.single p1 1) (sdot _ _ _ h01.symm))⁻¹) =
      tU (Pi.single pm (-1)) (Pi.single p1 1) (sdot _ _ _ h1m) := by
  apply Units.ext
  simp only [Units.val_mul, tU_val, tU_inv_val, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, single_dotProduct, Pi.single_apply, h01, h0m, h1m, h01.symm, h0m.symm, h1m.symm,
    if_false, if_true, mul_zero, zero_smul, add_zero, sub_zero, zero_mul, mul_one]
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all

theorem comm_b (p0 p1 pm : Fin n) (h01 : p0 ≠ p1) (h0m : p0 ≠ pm) (h1m : p1 ≠ pm) (a b : k) :
    tU (Pi.single p0 a) (Pi.single pm 1) (sdot _ _ _ h0m.symm) * tU (Pi.single pm b) (Pi.single p1 1) (sdot _ _ _ h1m) *
      (tU (Pi.single p0 a) (Pi.single pm 1) (sdot _ _ _ h0m.symm))⁻¹ * (tU (Pi.single pm b) (Pi.single p1 1) (sdot _ _ _ h1m))⁻¹ =
      tU (Pi.single p0 (a * b)) (Pi.single p1 1) (sdot _ _ _ h01.symm) := by
  apply Units.ext
  simp only [Units.val_mul, tU_val, tU_inv_val, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, single_dotProduct, Pi.single_apply, h01, h0m, h1m, h01.symm, h0m.symm, h1m.symm,
    if_false, if_true, mul_zero, zero_smul, add_zero, sub_zero, zero_mul, mul_one]
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all [mul_comm]

end GlobalTheory.PosAgree

namespace GlobalTheory.PosAgree

open Matrix

theorem entry_zero : ∀ (k : Type) [CommRing k], IsField k → ∀ n r : ℕ, 2 ≤ r → r < n → ∀ (H : Subgroup (GL (Fin n) k)) (b : GL (Fin n) k), (∀ u ∈ unip k n, ∀ h ∈ H, u * h * u⁻¹ ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → h.val = colMat v m → h ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → (b * h * b⁻¹).val = colMat v m → h ∈ H) → (∀ i j : Fin n, (i : ℕ) + 1 = j → (j : ℕ) < r → ∃ (c : k) (h : GL (Fin n) k), h.val = Matrix.transvection i j c ∧ h ∉ H) → ∀ a c : Fin n, r ≤ (a : ℕ) → (c : ℕ) < r → b.val a c = 0 := by
  intro k _ hk n r hr hrn H b hU h2 h3 h4 a c ha hc
  classical
  by_contra hne
  have ofVal : ∀ (g h : GL (Fin n) k), g ∈ H → g.val = h.val → h ∈ H := fun g h hg e => (Units.ext e) ▸ hg
  have H4 : ∀ i j : Fin n, i.val + 1 = j.val → j.val < r →
      (∀ x : k, ∃ hx, tU (Pi.single i x) (Pi.single j 1) hx ∈ H) → False := by
    intro i j hij hj hall
    obtain ⟨x, h, hh, hn⟩ := h4 i j hij hj
    obtain ⟨hx, hm⟩ := hall x
    exact hn (ofVal _ _ hm (by rw [tU_val, hh, transvection_eq]))
  let φ : Fin n → k := fun l => b.val a l
  have hrow : φ ᵥ* (b⁻¹).val = Pi.single a 1 := by
    have e : φ = Pi.single a 1 ᵥ* b.val := by
      ext l
      simp [φ, vecMul, single_dotProduct]
    rw [e, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  have H3 : ∀ w (hw : φ ⬝ᵥ w = 0), tU w φ hw ∈ H := fun w hw =>
    h3 _ a (b.val *ᵥ w) ha hw (by rw [conj_val, hrow]; rfl)
  let S := Finset.univ.filter (fun l : Fin n => φ l ≠ 0)
  have hcS : c ∈ S := by simp [S, φ, hne]
  set j := S.min' ⟨c, hcS⟩ with hjdef
  have hjc : j ≤ c := Finset.min'_le S c hcS
  have hφj : φ j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem S ⟨c, hcS⟩)).2
  have hlow : ∀ l, l < j → φ l = 0 := fun l hl => by
    by_contra h'
    exact absurd (Finset.min'_le S l (by simp [S, h'])) (not_le.mpr hl)
  obtain ⟨t, ht⟩ := hk.mul_inv_cancel hφj
  have hjr : j.val < r := lt_of_le_of_lt (show j.val ≤ c.val from hjc) hc
  let ψ : Fin n → k := fun l => if j < l then φ l * t else 0
  have hψ : ψ ⬝ᵥ Pi.single j 1 = 0 := by simp [ψ, dotProduct_single]
  have hu : tU (Pi.single j 1) ψ hψ ∈ unip k n := tU_mem_unip _ _ _ (fun i l hli => by
    simp only [Pi.single_apply, ψ]
    split_ifs with h1 h2 <;> first | (simp; done) | (have := Fin.lt_def.mp h2; rw [h1] at hli; omega))
  have hvec : φ ᵥ* ((tU (Pi.single j 1) ψ hψ)⁻¹).val = Pi.single j (φ j) := by
    rw [tU_inv_val, vecMul_sub, vecMul_one, vecMul_vmv, dotProduct_single, mul_one]
    ext l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ψ, Pi.single_apply]
    rcases lt_trichotomy l j with hl | hl | hl
    · rw [if_neg (not_lt.mpr hl.le), if_neg hl.ne, hlow l hl]; ring
    · rw [hl]; simp
    · rw [if_pos hl, if_neg hl.ne']; linear_combination (-(φ l)) * ht
  have KEY : ∀ (v : Fin n → k) (hv : Pi.single j 1 ⬝ᵥ v = 0), tU v (Pi.single j 1) hv ∈ H := by
    intro v hv
    have hw : φ ⬝ᵥ (t • (((tU (Pi.single j 1) ψ hψ)⁻¹).val *ᵥ v)) = 0 := by
      rw [dotProduct_smul, dotProduct_mulVec, hvec, single_dotProduct]
      rw [single_dotProduct, one_mul] at hv
      rw [hv, mul_zero, smul_zero]
    refine ofVal _ _ (hU _ hu _ (H3 _ hw)) ?_
    rw [conj_val, hvec, mulVec_smul, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, tU_val]
    congr 1
    ext p q
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs
    · linear_combination (v p) * ht
    · simp
  rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
  · have hn3 : 3 ≤ n := by omega
    let m0 : Fin n := ⟨n - 1, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have hm0j : j ≠ m0 := fun e => by
      have := congrArg Fin.val e
      simp [m0] at this
      omega
    have hi1j : j ≠ i1 := fun e => by
      have := congrArg Fin.val e
      simp [i1] at this
      omega
    have hm0i1 : i1 ≠ m0 := fun e => by
      have := congrArg Fin.val e
      simp [m0, i1] at this
      omega
    have hX := KEY (Pi.single m0 1) (sdot _ _ _ hm0j)
    have hu1 : tU (Pi.single j 1) (Pi.single i1 1) (sdot _ _ _ hi1j.symm) ∈ unip k n :=
      tU_mem_unip _ _ _ (fun p q hpq => by
        simp only [Pi.single_apply]
        split_ifs with h1 h2 <;> first | (simp; done) | (subst h1 h2; simp [i1] at hpq; omega))
    have hQ : tU (Pi.single m0 (-1)) (Pi.single i1 1) (sdot _ _ _ hm0i1) ∈ H := by
      have := H.mul_mem (H.inv_mem hX) (hU _ hu1 _ hX)
      exact (congrArg (· ∈ H) (comm_a (k := k) j i1 m0 hi1j hm0j hm0i1)).mp this
    refine H4 j i1 (by simp [i1, hj0]) (by simp [i1]; omega) (fun x => ⟨sdot _ _ _ hi1j.symm, ?_⟩)
    have hP : tU (Pi.single j (-x)) (Pi.single m0 1) (sdot _ _ _ hm0j.symm) ∈ unip k n :=
      tU_mem_unip _ _ _ (fun p q hpq => by
        simp only [Pi.single_apply]
        split_ifs with h1 h2 <;> first | (simp; done) | (subst h1 h2; simp [m0] at hpq; omega))
    have hZ := H.mul_mem (hU _ hP _ hQ) (H.inv_mem hQ)
    exact ofVal _ _ hZ ((congrArg Units.val (comm_b j i1 m0 hi1j hm0j hm0i1 (-x) (-1))).trans
      (by rw [tU_val, tU_val, neg_mul_neg, mul_one]))
  · let i : Fin n := ⟨j.val - 1, by omega⟩
    have hij : j ≠ i := fun e => by
      have := congrArg Fin.val e
      simp [i] at this
      omega
    exact H4 i j (by simp [i]; omega) hjr (fun x => ⟨sdot _ _ _ hij, KEY _ _⟩)

end GlobalTheory.PosAgree
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TSetDenom

open GlobalTheory.TSetFinCong (IntM)

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem int_of_double_coset (ϖ : v.adicCompletion F) (k : ℕ) (hϖ : Valued.v ϖ ≤ 1)
    (a b g : GL (Fin n) (v.adicCompletion F))
    (ha : a ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring)
    (hb : b ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring)
    (hg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (ϖ * ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  obtain ⟨ia, ia'⟩ := GlobalTheory.TSetFin.glint_int ha
  obtain ⟨ib, ib'⟩ := GlobalTheory.TSetFin.glint_int hb
  set D := Formalism.UG.diagJ n ϖ k
  let D' : Matrix (Fin n) (Fin n) (v.adicCompletion F) := Matrix.diagonal fun i => if (i : ℕ) < k then 1 else ϖ
  have hDD : D' * D = ϖ • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    simp only [D', D, Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hD : IntM D := GlobalTheory.TSetFinCong.IntM.diagonal fun i => by
    show Valued.v (if (i : ℕ) < k then ϖ else 1) ≤ 1
    split_ifs <;> simp [hϖ]
  have hD' : IntM D' := GlobalTheory.TSetFinCong.IntM.diagonal fun i => by
    show Valued.v (if (i : ℕ) < k then 1 else ϖ) ≤ 1
    split_ifs <;> simp [hϖ]
  have haa : ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * a = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbb : ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * b = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgi : ϖ • ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * D' *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    have h1 : ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * D' *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * g = ϖ • 1 := by
      rw [hg]
      calc _ = ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (D' *
            ((((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * a) * D)) * b := by
            simp only [Matrix.mul_assoc]
        _ = ϖ • 1 := by rw [haa, Matrix.one_mul, hDD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hbb]
    calc ϖ • ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))
        = (ϖ • 1) * ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = _ := by rw [← h1, Matrix.mul_assoc _ (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)), hgg, Matrix.mul_one]
  refine ⟨?_, fun i j => ?_⟩
  · rw [hg]; exact GlobalTheory.TSetFinCong.IntM.mul (GlobalTheory.TSetFinCong.IntM.mul (show IntM _ from ia) hD) (show IntM _ from ib)
  · have h := GlobalTheory.TSetFinCong.IntM.mul (GlobalTheory.TSetFinCong.IntM.mul (show IntM _ from ib') hD') (show IntM _ from ia') i j
    rw [← hgi, Matrix.smul_apply, smul_eq_mul] at h
    exact h

theorem exists_char (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : 𝓞 F) ∈ v.asIdeal) ∧ ∃ a : ℕ, Nat.card (𝓞 F ⧸ v.asIdeal) = p ^ a := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  obtain ⟨a, hp, hcard⟩ := FiniteField.card (𝓞 F ⧸ v.asIdeal) (ringChar (𝓞 F ⧸ v.asIdeal))
  refine ⟨ringChar (𝓞 F ⧸ v.asIdeal), hp, ?_, a, by rw [Nat.card_eq_fintype_card, hcard]⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

end Local

section Glob

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => NumberField.maximalRealSubfield L

open ReciprocityTheory.Aut

theorem conj_entry (x : GA L n) (i j : Fin n) :
    conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hm := x.2
  simp only [ReciprocityTheory.Aut.GA, ReciprocityTheory.Aut.UGroup, Subgroup.mem_mk] at hm
  have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
    Units.inv_eq_of_mul_eq_one_right hm
  simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem natCast_mul_mem (s : SplitPlace L) (c : ℕ) (x : GA L n) (hx : TrivOutside {s.v} x)
    (h1 : ∀ i j, Valued.v ((c : s.v.adicCompletion L⁺) *
      ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v ((c : s.v.adicCompletion L⁺) *
      ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (i j : Fin n) : (c : AL L) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  have hc1 : Valued.v (c : s.v.adicCompletion L⁺) ≤ 1 := GlobalTheory.TSetFinCong.natCast_le_one s.v c
  have hone : ∀ i j, s.proj ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := by
    intro i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hconj1 : conjAL L ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) (AL L)) j i := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  have hdel : ∀ i j, Valued.v ((c : s.v.adicCompletion L⁺) * (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 := by
    intro i j; rw [Valuation.map_mul]; refine mul_le_one' hc1 ?_; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hz : (c : AL L) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (c : AL L) * (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply GlobalTheory.TSetFin.mem_ALint_of_local s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, map_mul, map_mul, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · rw [map_sub, map_mul, map_mul, map_natCast, hone]
      exact (Valuation.map_sub _ _ _).trans (max_le (h1 i j) (hdel i j))
    · rw [map_sub, map_mul, map_mul, map_natCast, conj_entry x i j, hconj1, map_sub, map_mul, map_mul, map_natCast, hone]
      exact (Valuation.map_sub _ _ _).trans (max_le (h2 j i) (hdel j i))
  have hd : (c : AL L) * (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L :=
    Subring.mul_mem _ (natCast_mem (ALint L) c)
      (by by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using add_mem hz hd

theorem tSet_denom (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (k : ℕ) (hϖ : Formalism.AUTREP.IsUnif L s.v ϖ)
    (p : ℕ) (hp : ((p : ℕ) : 𝓞 L⁺) ∈ s.v.asIdeal) (x : Formalism.AUTREP.GAf L n) (hx : x ∈ Formalism.AUTREP.tSet L n s ϖ k)
    (i j : Fin n) :
    (p : AL L) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L ∧
      (p : AL L) * (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  obtain ⟨htriv, a, ha, b, hb, hg⟩ := hx
  have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hunif, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hunif; exact WithZero.coe_ne_zero hunif.symm
  obtain ⟨h1, h2⟩ := int_of_double_coset ϖ k hϖ1 a b _ ha hb hg
  have hpv : Valued.v (p : s.v.adicCompletion L⁺) ≤ WithZero.exp (-1) := by
    refine le_exp_neg_one_of_lt_one ?_
    have e : (p : s.v.adicCompletion L⁺) = algebraMap L⁺ (s.v.adicCompletion L⁺) (((p : ℕ) : 𝓞 L⁺) : L⁺) := by simp
    rw [e, adic_valued_algebraMap]
    exact (s.v.valuation_lt_one_iff_mem (K := L⁺) _).2 hp
  have ht : Valued.v ((p : s.v.adicCompletion L⁺) / ϖ) ≤ 1 := by
    rw [map_div₀, hunif]; exact div_le_one_of_le₀ hpv zero_le'
  have hpe : (p : s.v.adicCompletion L⁺) = (p : s.v.adicCompletion L⁺) / ϖ * ϖ := (div_mul_cancel₀ _ hϖ0).symm
  have hc1 : Valued.v (p : s.v.adicCompletion L⁺) ≤ 1 := GlobalTheory.TSetFinCong.natCast_le_one s.v p
  have A1 : ∀ i j, Valued.v ((p : s.v.adicCompletion L⁺) *
      ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 :=
    fun i j => by rw [Valuation.map_mul]; exact mul_le_one' hc1 (h1 i j)
  have A2 : ∀ i j, Valued.v ((p : s.v.adicCompletion L⁺) *
      ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 :=
    fun i j => by
      rw [map_inv, hpe, mul_assoc, Valuation.map_mul]; exact mul_le_one' ht (h2 i j)
  have htriv_inv : TrivOutside {s.v} (x⁻¹ : GA L n) := by
    intro w hw
    have hmul : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
        (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    have hmap := congrArg (fun M => M.map (compAt L w)) hmul
    simpa only [Matrix.map_mul, htriv w hw, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] using hmap
  exact ⟨natCast_mul_mem s p x htriv A1 A2 i j,
    natCast_mul_mem s p x⁻¹ htriv_inv A2 (fun i j => by rw [inv_inv]; exact A1 i j) i j⟩

end Glob

theorem tSet_denominator : ∀ (D : D7) (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), Formalism.AUTREP.IsUnif D.host.E s.v ϖ → ∃ p : ℕ, p.Prime ∧ s.Above p ∧ (∃ a, s.q = p ^ a) ∧ ∀ x ∈ Formalism.AUTREP.tSet D.host.E n s ϖ k, ∀ a b, (p : EAf D) * (km D n x).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (p : EAf D) * (km D n x⁻¹).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D n s ϖ k hϖ
  obtain ⟨p, hp, hmem, a, ha⟩ := exists_char s.v
  refine ⟨p, hp, hmem, ⟨a, ha⟩, fun x hx i j => ?_⟩
  obtain ⟨k1, k2⟩ := tSet_denom s ϖ k hϖ p hmem x hx i j
  exact ⟨(GlobalTheory.StdFrameExist.mem_ALint_iff (D := D) _).1 k1, (GlobalTheory.StdFrameExist.mem_ALint_iff (D := D) _).1 k2⟩

end GlobalTheory.TSetDenom
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem XE_updS_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) (hOk : A3.fam3.Ok3 1) (hsep : A3.fam3.TypesSep3)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) (b : Bool) :
    (((R.updS R.kap (zeroLam R F c)).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE := by
  have h := cx_XE_scal (R.toCx3 F) F.cr (zeroLam R F c) b fun p hp j v => by
    by_cases he : R.EEp3 p = ⊥
    · exact absurd (partPr_of_bot _ _ _ (qp_bot R F hC hP hOk hsep he b)) hp
    · exact zeroLam_of_ne R F c (hZ p he j).1 fun hv => (hZ p he j).2 v hv
  exact (by with_unfolding_all exact (h :))



def scalReadL (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) : ReadL (R.updS R.kap lam) F X0 Y :=
  { Z with
    met := fun v hv x y => (Z.met v hv x y).trans (by rw [hX true]; rfl)
    met0 := fun v hv x y => (Z.met0 v hv x y).trans (by rw [hX false]; rfl) }


end GlobalTheory.Mem.R3

end
end
