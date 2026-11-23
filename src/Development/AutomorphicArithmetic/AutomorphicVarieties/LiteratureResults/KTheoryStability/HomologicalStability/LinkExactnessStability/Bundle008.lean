module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Mathlib.Tactic.Continuity
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.StabSeq

open scoped Matrix

variable (R : Type) [CommRing R]

theorem padMat_castLE {m n : ℕ} (h : m ≤ n) (A : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    (padMat R A : Matrix (Fin n) (Fin n) R) (Fin.castLE h i) (Fin.castLE h j) = A i j := by
  simp [padMat, Fin.coe_castLE, i.2, j.2]

theorem stab_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (stab R m n h) := by
  intro g g' e
  ext i j
  have := congrArg (fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R) (Fin.castLE h i) (Fin.castLE h j)) e
  simpa [stab, padHom, padMat_castLE] using this

def IsPad (m : ℕ) {n : ℕ} (g : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i k : Fin n, m ≤ (k : ℕ) → g i k = (if i = k then 1 else 0) ∧ g k i = (if k = i then 1 else 0)

theorem padMat_of_isPad {m n : ℕ} (h : m ≤ n) (g : Matrix (Fin n) (Fin n) R) (hg : IsPad R m g) :
    padMat R (Matrix.of fun i j : Fin m => g (Fin.castLE h i) (Fin.castLE h j)) = g := by
  ext i j
  simp only [padMat, Matrix.of_apply]
  split_ifs with h1 h2
  · rfl
  · subst h2
    have : m ≤ (i : ℕ) := by omega
    simpa using ((hg i i this).1).symm
  · by_cases hj : m ≤ (j : ℕ)
    · rw [(hg i j hj).1, if_neg h2]
    · have hi : m ≤ (i : ℕ) := by omega
      rw [(hg j i hi).2, if_neg h2]

theorem mem_range_of_isPad {m n : ℕ} (h : m ≤ n) (g : GL (Fin n) R)
    (hg : IsPad R m (g : Matrix (Fin n) (Fin n) R)) (hg' : IsPad R m ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) :
    g ∈ (stab R m n h).range := by
  set A : Matrix (Fin m) (Fin m) R := Matrix.of fun i j => (g : Matrix (Fin n) (Fin n) R) (Fin.castLE h i) (Fin.castLE h j)
  set B : Matrix (Fin m) (Fin m) R :=
    Matrix.of fun i j => ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) (Fin.castLE h i) (Fin.castLE h j)
  have hA : padHom R h A = g := padMat_of_isPad R h _ hg
  have hB : padHom R h B = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := padMat_of_isPad R h _ hg'
  have inj : ∀ X Y : Matrix (Fin m) (Fin m) R, padHom R h X = padHom R h Y → X = Y := by
    intro X Y e
    ext i j
    have := congrArg (fun x : Matrix (Fin n) (Fin n) R => x (Fin.castLE h i) (Fin.castLE h j)) e
    simpa [padHom, padMat_castLE] using this
  have hAB : A * B = 1 := inj _ _ (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hBA : B * A = 1 := inj _ _ (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨A, B, hAB, hBA⟩, Units.ext ?_⟩
  exact hA

theorem isPad_stab {m n : ℕ} (h : m ≤ n) (A : GL (Fin m) R) :
    IsPad R m (stab R m n h A : Matrix (Fin n) (Fin n) R) := by
  intro i k hk
  have : ¬ (k : ℕ) < m := by omega
  constructor
  · rw [stab_apply, dite_eq_right (by tauto)]
  · rw [stab_apply, dite_eq_right (by tauto)]

theorem stdSeq_fixed_iff (n p : ℕ) (h : p ≤ n) (g : GL (Fin n) R) :
    g ∈ MulAction.stabilizer (GL (Fin n) R) (stdSeq R n p h) ↔
      ∀ j : Fin p, (g : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single (⟨n - p + j, by omega⟩ : Fin n) 1 =
          Pi.single (⟨n - p + j, by omega⟩ : Fin n) 1 ∧
        Pi.single (⟨n - p + j, by omega⟩ : Fin n) 1 ᵥ* ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
          Pi.single (⟨n - p + j, by omega⟩ : Fin n) 1 := by
  have e : ∀ j : Fin p, (fun k : Fin n => if (k : ℕ) = n - p + j then (1 : R) else 0) =
      Pi.single (⟨n - p + j, by omega⟩ : Fin n) 1 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]
  have key : g • stdSeq R n p h = stdSeq R n p h ↔ (g • stdSeq R n p h).1 = (stdSeq R n p h).1 :=
    ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩
  rw [MulAction.mem_stabilizer_iff, key, smul_val]
  simp only [stdSeq, stdList, List.map_ofFn, List.ofFn_inj, funext_iff, Function.comp_apply, pairAct,
    Prod.ext_iff, e]

theorem isPad_of_mem (n p : ℕ) (h : p ≤ n) (g : GL (Fin n) R)
    (hg : g ∈ MulAction.stabilizer (GL (Fin n) R) (stdSeq R n p h)) :
    IsPad R (n - p) (g : Matrix (Fin n) (Fin n) R) := by
  intro i k hk
  have hf := (stdSeq_fixed_iff R n p h g).1 hg ⟨(k : ℕ) - (n - p), by omega⟩
  have hk' : (⟨n - p + ((k : ℕ) - (n - p)), by omega⟩ : Fin n) = k := Fin.ext (by simp; omega)
  simp only [hk'] at hf
  obtain ⟨h1, h2⟩ := hf
  have h3 : Pi.single k 1 ᵥ* (g : Matrix (Fin n) (Fin n) R) = Pi.single k 1 := by
    conv_lhs => rw [← h2]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  constructor
  · have := congrFun h1 i
    rw [Matrix.mulVec_single] at this
    simpa [Pi.single_apply] using this
  · have := congrFun h3 i
    rw [Matrix.single_vecMul] at this
    simpa [Pi.single_apply, eq_comm] using this

theorem range_eq (n p : ℕ) (h : p ≤ n) :
    (stab R (n - p) n (Nat.sub_le n p)).range = MulAction.stabilizer (GL (Fin n) R) (stdSeq R n p h) := by
  ext g
  constructor
  · rintro ⟨A, rfl⟩
    rw [stdSeq_fixed_iff]
    intro j
    have hk : n - p ≤ ((⟨n - p + j, by omega⟩ : Fin n) : ℕ) := by simp
    have P := isPad_stab R (Nat.sub_le n p) A
    have Q := isPad_stab R (Nat.sub_le n p) A⁻¹
    rw [map_inv] at Q
    constructor
    · funext i
      rw [Matrix.mulVec_single]
      simp [(P i _ hk).1, Pi.single_apply]
    · rw [Matrix.single_vecMul]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, one_mul, Matrix.row_apply]
      rw [(Q i _ hk).2]
      simp [Pi.single_apply, eq_comm]
  · intro hg
    exact mem_range_of_isPad R _ g (isPad_of_mem R n p h g hg)
      (isPad_of_mem R n p h g⁻¹ (inv_mem hg))

end GlobalTheory.StabSeq

namespace GlobalTheory.StabSeq

theorem stab_injective_range_eq : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p ≤ n), Function.Injective (stab R (n - p) n (Nat.sub_le n p)) ∧ (stab R (n - p) n (Nat.sub_le n p)).range = MulAction.stabilizer (GL (Fin n) R) (stdSeq R n p h) :=
  fun R _ n p h => ⟨stab_injective R _, range_eq R n p h⟩

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.stabilizer_stdSeq_iso_GL_of_complement : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p ≤ n), Function.Injective (stab R (n - p) n (Nat.sub_le n p)) ∧ (stab R (n - p) n (Nat.sub_le n p)).range = MulAction.stabilizer (GL (Fin n) R) (stdSeq R n p h) := by
  first
  | exact @GlobalTheory.StabSeq.stab_injective_range_eq
end
end StabSeq
end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

noncomputable section

open scoped Matrix

namespace GlobalTheory.HomStab.FacePerm

variable (R : Type) [CommRing R] {n : ℕ}

def pm (f : Fin n → Fin n) : Matrix (Fin n) (Fin n) R := Matrix.of fun a b => if f b = a then 1 else 0

theorem pm_mul (f h : Fin n → Fin n) : pm R f * pm R h = pm R (f ∘ h) := by
  ext a c
  simp [pm, Matrix.mul_apply, mul_ite, Finset.sum_ite_eq]

theorem pm_id : pm R (id : Fin n → Fin n) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [pm]
  · simp [pm, Matrix.one_apply, h, Ne.symm h]

def pmU (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) : GL (Fin n) R :=
  ⟨pm R f, pm R g, by rw [pm_mul, show f ∘ g = id from funext h1, pm_id],
    by rw [pm_mul, show g ∘ f = id from funext h2, pm_id]⟩

theorem pm_mulVec (f : Fin n → Fin n) (k : Fin n) :
    pm R f *ᵥ (fun a : Fin n => if a = k then (1 : R) else 0) = fun a => if a = f k then 1 else 0 := by
  funext a
  simp only [pm, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : a = f k
  · simp [h]
  · simp [h, Ne.symm h]

theorem vecMul_pm (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) (k : Fin n) :
    (fun a : Fin n => if a = k then (1 : R) else 0) ᵥ* pm R g = fun c => if c = f k then 1 else 0 := by
  funext c
  have key : g c = k ↔ c = f k := ⟨fun e => by rw [← e, h1], fun e => by rw [e, h2]⟩
  simp only [pm, Matrix.vecMul, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [key]

theorem pm_mul_apply (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k)
    (M : Matrix (Fin n) (Fin n) R) (a c : Fin n) : (pm R f * M) a c = M (g a) c := by
  have key : ∀ b, f b = a ↔ b = g a := fun b => ⟨fun e => by rw [← e, h2], fun e => by rw [e, h1]⟩
  simp only [pm, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul, key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mul_pm_apply (f : Fin n → Fin n) (M : Matrix (Fin n) (Fin n) R) (a c : Fin n) :
    (M * pm R f) a c = M a (f c) := by
  simp [pm, Matrix.mul_apply, mul_ite, Finset.sum_ite_eq]

variable (m i : ℕ) (hmi : m + i < n)

def cyc (k : Fin n) : Fin n :=
  if h : m ≤ (k : ℕ) ∧ (k : ℕ) < m + i then ⟨k + 1, by omega⟩
  else if (k : ℕ) = m + i then ⟨m, by omega⟩ else k

def cycInv (k : Fin n) : Fin n :=
  if h : m < (k : ℕ) ∧ (k : ℕ) ≤ m + i then ⟨k - 1, by omega⟩
  else if (k : ℕ) = m then ⟨m + i, hmi⟩ else k

theorem cyc_val (k : Fin n) : (cyc m i hmi k : ℕ) =
    if m ≤ (k : ℕ) ∧ (k : ℕ) < m + i then (k : ℕ) + 1 else if (k : ℕ) = m + i then m else k := by
  unfold cyc; split_ifs <;> rfl

theorem cycInv_val (k : Fin n) : (cycInv m i hmi k : ℕ) =
    if m < (k : ℕ) ∧ (k : ℕ) ≤ m + i then (k : ℕ) - 1 else if (k : ℕ) = m then m + i else k := by
  unfold cycInv; split_ifs <;> rfl

theorem cyc_cycInv (k : Fin n) : cyc m i hmi (cycInv m i hmi k) = k := by
  apply Fin.ext
  rw [cyc_val, cycInv_val]
  split_ifs <;> omega

theorem cycInv_cyc (k : Fin n) : cycInv m i hmi (cyc m i hmi k) = k := by
  apply Fin.ext
  rw [cycInv_val, cyc_val]
  split_ifs <;> omega

end GlobalTheory.HomStab.FacePerm

namespace GlobalTheory.HomStab.FacePerm

variable (R : Type) [CommRing R] {n : ℕ}

theorem pairAct_pmU (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) (K : ℕ)
    (hK : K < n) (L : ℕ) (hL : (f ⟨K, hK⟩ : ℕ) = L) :
    pairAct R n (pmU R f g h1 h2) ((fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0),
      (fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0)) =
    ((fun a : Fin n => if (a : ℕ) = L then (1 : R) else 0),
      (fun a : Fin n => if (a : ℕ) = L then (1 : R) else 0)) := by
  subst hL
  have e1 : (fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0) = fun a => if a = ⟨K, hK⟩ then 1 else 0 := by
    funext a
    simp [Fin.ext_iff]
  have e2 : (fun a : Fin n => if (a : ℕ) = (f ⟨K, hK⟩ : ℕ) then (1 : R) else 0) = fun a => if a = f ⟨K, hK⟩ then 1 else 0 := by
    funext a
    simp [Fin.ext_iff]
  rw [e1, e2]
  exact Prod.ext (pm_mulVec R f ⟨K, hK⟩) (vecMul_pm R f g h1 h2 ⟨K, hK⟩)

end GlobalTheory.HomStab.FacePerm


open GlobalTheory.HomStab.FacePerm in
theorem GlobalTheory.HomStab.exists_perm_face_stdSeq : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p + 1 ≤ n) (i : Fin (p + 1)), ∃ g : GL (Fin n) R, g • face R n p i (stdSeq R n (p + 1) h) = stdSeq R n p (by omega) ∧ ∀ x : GL (Fin (n - (p + 1))) R, g * stab R (n - (p + 1)) n (Nat.sub_le _ _) x = stab R (n - (p + 1)) n (Nat.sub_le _ _) x * g := open GlobalTheory.HomStab.FacePerm in by
  intro R _ n p h i
  have hi := i.isLt
  have hmi : n - (p + 1) + (i : ℕ) < n := by omega
  refine ⟨pmU R (cyc (n - (p + 1)) i hmi) (cycInv (n - (p + 1)) i hmi) (cyc_cycInv _ _ hmi) (cycInv_cyc _ _ hmi), ?_, ?_⟩
  · apply Subtype.ext
    show ((stdList R n (p + 1)).eraseIdx i).map (pairAct R n _) = stdList R n p
    apply List.ext_getElem
    · simp only [List.length_map, List.length_eraseIdx, stdList, List.length_ofFn]
      split_ifs <;> omega
    · intro j h1 h2
      have hjp : j < p := by simpa [stdList] using h2
      simp only [List.getElem_map, List.getElem_eraseIdx, stdList, List.getElem_ofFn, Fin.val_mk]
      split_ifs with hj
      · exact pairAct_pmU R _ _ _ _ _ (by omega) _ (by simp only [cyc_val, Fin.val_mk]; split_ifs <;> omega)
      · exact pairAct_pmU R _ _ _ _ _ (by omega) _ (by simp only [cyc_val, Fin.val_mk]; split_ifs <;> omega)
  · intro x
    have lo1 : ∀ k : Fin n, ((cyc (n - (p + 1)) i hmi k : ℕ) < n - (p + 1) ↔ (k : ℕ) < n - (p + 1)) := by
      intro k
      rw [cyc_val]
      split_ifs <;> omega
    have lo2 : ∀ k : Fin n, ((cycInv (n - (p + 1)) i hmi k : ℕ) < n - (p + 1) ↔ (k : ℕ) < n - (p + 1)) := by
      intro k
      rw [cycInv_val]
      split_ifs <;> omega
    have fx1 : ∀ k : Fin n, (k : ℕ) < n - (p + 1) → cyc (n - (p + 1)) i hmi k = k := by
      intro k hk
      apply Fin.ext
      rw [cyc_val]
      split_ifs <;> omega
    have fx2 : ∀ k : Fin n, (k : ℕ) < n - (p + 1) → cycInv (n - (p + 1)) i hmi k = k := by
      intro k hk
      apply Fin.ext
      rw [cycInv_val]
      split_ifs <;> omega
    have bij : ∀ a c : Fin n, cycInv (n - (p + 1)) i hmi a = c ↔ a = cyc (n - (p + 1)) i hmi c := by
      intro a c
      constructor
      · rintro rfl
        rw [cyc_cycInv]
      · rintro rfl
        rw [cycInv_cyc]
    ext a c
    rw [Units.val_mul, Units.val_mul]
    show ((pm R (cyc (n - (p + 1)) i hmi) * padMat R (x : Matrix (Fin (n - (p + 1))) (Fin (n - (p + 1))) R) : Matrix (Fin n) (Fin n) R)) a c = ((padMat R (x : Matrix (Fin (n - (p + 1))) (Fin (n - (p + 1))) R) * pm R (cyc (n - (p + 1)) i hmi) : Matrix (Fin n) (Fin n) R)) a c
    rw [pm_mul_apply R _ _ (cyc_cycInv _ _ hmi) (cycInv_cyc _ _ hmi), mul_pm_apply]
    by_cases ha : (a : ℕ) < n - (p + 1)
    · by_cases hc : (c : ℕ) < n - (p + 1)
      · rw [fx2 a ha, fx1 c hc]
      · simp only [padMat, Matrix.of_apply]
        rw [dite_eq_right, dite_eq_right]
        all_goals first
          | simp only [bij]
          | (rw [lo1]; omega)
          | (rw [lo2]; omega)
    · simp only [padMat, Matrix.of_apply]
      rw [dite_eq_right, dite_eq_right]
      all_goals first
        | simp only [bij]
        | (rw [lo1]; omega)
        | (rw [lo2]; omega)

end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.face_stdSeq_GL_conjugate_commuting_stab : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p + 1 ≤ n) (i : Fin (p + 1)), ∃ g : GL (Fin n) R, g • face R n p i (stdSeq R n (p + 1) h) = stdSeq R n p (by omega) ∧ ∀ x : GL (Fin (n - (p + 1))) R, g * stab R (n - (p + 1)) n (Nat.sub_le _ _) x = stab R (n - (p + 1)) n (Nat.sub_le _ _) x * g := by
  first
  | exact @GlobalTheory.HomStab.exists_perm_face_stdSeq
end
end

section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.ShearLow

theorem main : ∀ (R : Type) [CommRing R] (n : ℕ) (h : (ℕ →₀ R) →ₗ[R] R) (t : ℕ →₀ R), t ∈ low R n → h t = 0 → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x = x + h x • t) ∧ (∀ x, ψ x ∈ low R n ↔ x ∈ low R n) ∧ ∀ j x, ψ x ∈ aff R n j ↔ x ∈ aff R n j := by
  intro R _ n h t ht hht
  have key : ∀ x y : ℕ →₀ R, y ∈ low R n → (x + y ∈ low R n ↔ x ∈ low R n) := by
    intro x y hy
    simp only [low, Set.mem_setOf_eq, Finsupp.add_apply] at hy ⊢
    constructor
    · intro hx i hi
      have hxi := hx i hi
      rw [hy i hi, add_zero] at hxi
      exact hxi
    · intro hx i hi
      rw [hx i hi, hy i hi, add_zero]
  have hts : ∀ c : R, c • t ∈ low R n := by
    intro c
    simp only [low, Set.mem_setOf_eq, Finsupp.smul_apply] at ht ⊢
    intro i hi
    rw [ht i hi, smul_zero]
  let ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R) :=
    { toFun := fun x => x + h x • t
      invFun := fun x => x - h x • t
      map_add' := by
        intro x y
        simp only [map_add (f := _), add_smul]
        abel
      map_smul' := by
        intro c x
        simp only [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]
      left_inv := by
        intro x
        simp only [map_add (f := _), map_smul, hht, smul_eq_mul, mul_zero, add_zero, add_sub_cancel_right]
      right_inv := by
        intro x
        simp only [map_sub, map_smul, hht, smul_eq_mul, mul_zero, sub_zero, sub_add_cancel] }
  have hψ : ∀ x, ψ x = x + h x • t := fun x => rfl
  refine ⟨ψ, hψ, ?_, ?_⟩
  · intro x
    rw [hψ]
    exact key x _ (hts _)
  · intro j x
    rw [hψ]
    simp only [aff, Set.mem_setOf_eq]
    have e : x + h x • t - (Finsupp.single j 1) = (x - Finsupp.single j 1) + h x • t := by abel
    rw [e]
    exact key _ _ (hts _)

end GlobalTheory.ShearLow

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exists_transvection_preserving_low_and_aff : ∀ (R : Type) [CommRing R] (n : ℕ) (h : (ℕ →₀ R) →ₗ[R] R) (t : ℕ →₀ R), t ∈ low R n → h t = 0 → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x = x + h x • t) ∧ (∀ x, ψ x ∈ low R n ↔ x ∈ low R n) ∧ ∀ j x, ψ x ∈ aff R n j ↔ x ∈ aff R n j := by
  first
  | exact @GlobalTheory.ShearLow.main
end
end
