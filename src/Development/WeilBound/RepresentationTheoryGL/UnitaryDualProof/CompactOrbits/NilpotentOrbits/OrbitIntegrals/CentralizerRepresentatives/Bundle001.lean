module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.IsChain
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem sigma_fin_eq_iff {ι : Type} {l : ι → ℕ} {b a : ι} {j : Fin (l b)} {i : Fin (l a)} :
    (⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, i⟩ ↔ b = a ∧ (j : ℕ) = i := by
  constructor
  · intro h
    cases h
    simp
  · rintro ⟨rfl, h⟩
    rw [Fin.ext h]

theorem chain_repr_N {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr (N z) ⟨a, i⟩ = if h : 0 < (i : ℕ) then B.repr z ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by
  classical
  have key : (B.coord ⟨a, i⟩).comp N =
      if h : 0 < (i : ℕ) then B.coord ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by
    apply B.ext
    rintro ⟨b, j⟩
    rw [LinearMap.comp_apply, hB]
    by_cases hi : 0 < (i : ℕ)
    · rw [dite_eq_left hi]
      by_cases hj : (j : ℕ) + 1 < l b
      · rw [dite_eq_left hj, Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
          Module.Basis.repr_self_apply]
        have hiff : ((⟨b, ⟨j + 1, hj⟩⟩ : Σ a, Fin (l a)) = ⟨a, i⟩) ↔
            ((⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, ⟨i - 1, by omega⟩⟩) := by
          rw [sigma_fin_eq_iff, sigma_fin_eq_iff]
          constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by simp only at h2 ⊢; omega⟩
        exact if_congr hiff rfl rfl
      · rw [dite_eq_right hj, map_zero, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg]
        intro h
        rw [sigma_fin_eq_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp only at h2
        have := i.2
        omega
    · rw [dite_eq_right hi]
      split_ifs with hj
      · rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg, LinearMap.zero_apply]
        intro h
        rw [sigma_fin_eq_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp only at h2
        omega
      · simp
  have := LinearMap.congr_fun key z
  rw [LinearMap.comp_apply, Module.Basis.coord_apply] at this
  rw [this]
  split_ifs <;> simp

theorem chain_repr_Npow {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr ((N ^ m) z) ⟨a, i⟩ = if h : m ≤ (i : ℕ) then B.repr z ⟨a, ⟨i - m, by omega⟩⟩ else 0 := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    by_cases h1 : m + 1 ≤ (i : ℕ)
    · rw [dite_eq_left (by omega), dite_eq_left h1, chain_repr_N hB, dite_eq_left (by simp; omega)]
      congr 2
    · rw [dite_eq_right h1]
      split_ifs with h2
      · rw [chain_repr_N hB, dite_eq_right]
        simp
        omega
      · rfl

theorem chain_repr_of_ker {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (hz : (N ^ m) z = 0) (a : ι) (i : Fin (l a))
    (hi : (i : ℕ) + m < l a) : B.repr z ⟨a, i⟩ = 0 := by
  have h := chain_repr_Npow hB m z a ⟨i + m, hi⟩
  rw [hz, map_zero, dite_eq_left (by simp)] at h
  rw [Finsupp.zero_apply] at h
  rw [h]
  congr 2
  ext
  simp

theorem chain_Npow_zero {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (b : ι) (hb : 0 < l b) (j : ℕ) :
    (N ^ j) (B ⟨b, ⟨0, hb⟩⟩) = if h : j < l b then B ⟨b, ⟨j, h⟩⟩ else 0 := by
  induction j with
  | zero => simp [hb]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    by_cases hj : j < l b
    · rw [dite_eq_left hj, hB]
    · rw [dite_eq_right hj, map_zero, dite_eq_right (by omega)]

theorem repr_centralizer_eq_zero (N : W →ₗ[E] W) {ι : Type} [Fintype ι] (l : ι → ℕ)
    (B : Module.Basis (Σ a, Fin (l a)) E W) (hB : IsChain N l B) (s : ι → ℕ) (_hs : ∀ a, s a ≤ l a)
    (hC : ∀ a b, s a ≤ s b + (l a - l b)) (v : W) (hv : v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0)
    (A : W →ₗ[E] W) (hA : A ∘ₗ N = N ∘ₗ A) (a : ι) (i : Fin (l a)) (hi : (i : ℕ) < s a) :
    B.repr (A v) ⟨a, i⟩ = 0 := by
  have hc : Commute A N := hA

  rw [hv, map_sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : s b < l b
  · rw [dite_eq_left hb]
    have hlb : 0 < l b := by omega
    have h1 : B ⟨b, ⟨s b, hb⟩⟩ = (N ^ s b) (B ⟨b, ⟨0, hlb⟩⟩) := by
      rw [chain_Npow_zero hB b hlb, dite_eq_left hb]
    have hcomm : ∀ m : ℕ, ∀ x, A ((N ^ m) x) = (N ^ m) (A x) := fun m x =>
      LinearMap.congr_fun (hc.pow_right m).eq x
    rw [h1, hcomm, chain_repr_Npow hB]
    split_ifs with h2
    · refine chain_repr_of_ker hB (l b) _ ?_ a _ ?_
      · rw [← hcomm, chain_Npow_zero hB b hlb, dite_eq_right (lt_irrefl _), map_zero]
      · have := hC a b
        show (i : ℕ) - s b + l b < l a
        omega
    · rfl
  · rw [dite_eq_right hb, map_zero, map_zero, Finsupp.zero_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

section

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

def cbFam (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (y : ι → W) : (Σ a, Fin (l a)) → W :=
  fun p => (N ^ (p.2 : ℕ)) (y p.1)

theorem cb_pow_succ (N : W →ₗ[E] W) (i : ℕ) (x : W) : N ((N ^ i) x) = (N ^ (i + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]

theorem cb_pow_pow (N : W →ₗ[E] W) (m j : ℕ) (x : W) : (N ^ m) ((N ^ j) x) = (N ^ (m + j)) x := by
  rw [← Module.End.mul_apply, ← pow_add]

theorem cb_pow_zero_of_le (N : W →ₗ[E] W) {m j : ℕ} {x : W} (h : (N ^ m) x = 0) (hj : m ≤ j) :
    (N ^ j) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show m + d = d + m from add_comm _ _, ← cb_pow_pow, h, map_zero]

theorem cb_isChain_of_fam (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (y : ι → W)
    (hy : ∀ a, (N ^ l a) (y a) = 0) (B : Module.Basis (Σ a, Fin (l a)) E W)
    (hB : ∀ p, B p = cbFam N l y p) : IsChain N l B := by
  intro a i
  rw [hB]
  simp only [cbFam]
  rw [cb_pow_succ]
  split_ifs with h
  · rw [hB]; rfl
  · have hi := i.isLt
    rw [show (i : ℕ) + 1 = l a by omega, hy]

theorem cb_isChain_apply (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : ℕ) (hi : i < l a) :
    B ⟨a, ⟨i, hi⟩⟩ = (N ^ i) (B ⟨a, ⟨0, h0⟩⟩) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := hB a ⟨i, by omega⟩
    rw [dite_eq_left (show ((⟨i, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a from hi)] at h1
    rw [← h1, ih (by omega), cb_pow_succ]

theorem cb_isChain_apply' (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : Fin (l a)) :
    B ⟨a, i⟩ = (N ^ (i : ℕ)) (B ⟨a, ⟨0, h0⟩⟩) := by
  obtain ⟨i, hi⟩ := i
  exact cb_isChain_apply N hB a h0 i hi

theorem cb_isChain_len (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) : (N ^ l a) (B ⟨a, ⟨0, h0⟩⟩) = 0 := by
  have h1 := hB a ⟨l a - 1, by omega⟩
  rw [dite_eq_right (show ¬ (((⟨l a - 1, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a) by simp; omega)] at h1
  rw [cb_isChain_apply N hB a h0 (l a - 1) (by omega), cb_pow_succ] at h1
  rwa [show l a - 1 + 1 = l a by omega] at h1

theorem cb_eq_top (N : W →ₗ[E] W) (hN : IsNilpotent N) (S : Submodule E W)
    (hS : ∀ x ∈ S, N x ∈ S) (h : S ⊔ LinearMap.range N = ⊤) : S = ⊤ := by
  have key : ∀ k : ℕ, S ⊔ LinearMap.range (N ^ k) = ⊤ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id, sup_top_eq]
    | succ k ih =>
      rw [eq_top_iff]
      intro w _
      have hw : w ∈ S ⊔ LinearMap.range N := h ▸ Submodule.mem_top
      obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨z', rfl⟩ := hz
      have hz' : z' ∈ S ⊔ LinearMap.range (N ^ k) := ih ▸ Submodule.mem_top
      obtain ⟨x2, hx2, z2, hz2, rfl⟩ := Submodule.mem_sup.mp hz'
      obtain ⟨z3, rfl⟩ := hz2
      rw [map_add (f := _)]
      apply Submodule.mem_sup.mpr
      refine ⟨x + N x2, S.add_mem hx (hS _ hx2), (N ^ (k + 1)) z3, ⟨z3, rfl⟩, ?_⟩
      rw [cb_pow_succ, add_assoc]
  obtain ⟨K, hK⟩ := hN
  have := key K
  rwa [hK, LinearMap.range_zero, sup_bot_eq] at this

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

section

noncomputable section

open Matrix Submodule

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {k : Type} [Field k] {n : ℕ}

def gradeColMat (b : Module.Basis (Fin n) k (Fin n → k)) : Matrix (Fin n) (Fin n) k :=
  (Pi.basisFun k (Fin n)).toMatrix b

def gradeRowMat (b : Module.Basis (Fin n) k (Fin n → k)) : Matrix (Fin n) (Fin n) k :=
  b.toMatrix (Pi.basisFun k (Fin n))

def gradeBasisGL (b : Module.Basis (Fin n) k (Fin n → k)) : GL (Fin n) k :=
  ⟨gradeColMat b, gradeRowMat b, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩

theorem gradeColMat_mulVec (b : Module.Basis (Fin n) k (Fin n → k)) (u : Fin n → k) :
    gradeColMat b *ᵥ u = ∑ i, u i • b i := by
  ext r
  simp [gradeColMat, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, mul_comm]

theorem grade_mat_ext {ι : Type} (b : Module.Basis ι k (Fin n → k)) (X Y : Matrix (Fin n) (Fin n) k)
    (h : ∀ i, X *ᵥ b i = Y *ᵥ b i) : X = Y := by
  apply Matrix.toLin'.injective
  exact b.ext fun i => by simpa [Matrix.toLin'_apply] using h i

theorem grade_eig {ι : Type} (b : Module.Basis ι k (Fin n → k)) (g : Matrix (Fin n) (Fin n) k) (d : ι → k)
    (hg : ∀ i, g *ᵥ b i = d i • b i) (S : Set ι) (c : k) (hS : ∀ i ∈ S, d i = c) (y : Fin n → k)
    (hy : y ∈ span k (b '' S)) : g *ᵥ y = c • y := by
  let f : (Fin n → k) →ₗ[k] (Fin n → k) := Matrix.toLin' g - c • LinearMap.id
  have hle : span k (b '' S) ≤ LinearMap.ker f := by
    rw [span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp [f, Matrix.toLin'_apply, hg, hS i hi]
  have := hle hy
  simp only [LinearMap.mem_ker, f, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Matrix.toLin'_apply] at this
  exact sub_eq_zero.mp this

theorem grade_fin (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → ℤ)
    (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (hZ : ∀ z ∈ Z, ∀ j, z *ᵥ b j ∈ span k (b '' {j' | w j' = w j}))
    (hN : ∀ j, N *ᵥ b j ∈ span k (b '' {j' | w j' = w j + 1}))
    (hv : v ∈ span k (b '' {j | w j = 0}))
    (hA : ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
      ∀ j, w j < 0 → b.repr (a *ᵥ v) j = 0) :
    (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k :=
          (gradeBasisGL b).val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * (gradeBasisGL b)⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = (gradeBasisGL b).val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  classical
  refine ⟨fun t => ?_, fun a ha haN => ?_⟩
  · intro g
    have hrow : ∀ j, gradeRowMat b *ᵥ b j = Pi.single j 1 := by
      intro j
      have h1 : gradeColMat b *ᵥ Pi.single j 1 = b j := by
        rw [gradeColMat_mulVec]
        simp [Pi.single_apply]
      rw [← h1, Matrix.mulVec_mulVec]
      show (b.toMatrix (Pi.basisFun k (Fin n)) * (Pi.basisFun k (Fin n)).toMatrix b) *ᵥ _ = _
      rw [Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mulVec]
    have hgdef : g = gradeColMat b * diagonal (fun i => ((t ^ w i : kˣ) : k)) * gradeRowMat b := rfl
    clear_value g
    have hg : ∀ j, g *ᵥ b j = ((t ^ w j : kˣ) : k) • b j := by
      intro j
      rw [hgdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hrow, gradeColMat_mulVec]
      simp [Matrix.mulVec_diagonal, Pi.single_apply]
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · apply grade_mat_ext b
      intro j
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, Matrix.mulVec_smul]
      rw [grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j' | w j' = w j} _ (fun i hi => by rw [hi]) _ (hZ a ha j)]
    · apply grade_mat_ext b
      intro j
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hg, Matrix.mulVec_smul,
        grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j' | w j' = w j + 1} (((t ^ (w j + 1) : kˣ) : k))
          (fun i hi => by rw [hi]) _ (hN j), smul_smul, _root_.zpow_add_one, Units.val_mul, Units.val_zpow_eq_zpow_val,
        mul_comm]
    · rw [grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j | w j = 0} 1 (fun i hi => by rw [hi]; simp) v hv, one_smul]
  · refine ⟨⇑(b.repr (a *ᵥ v)), ?_, fun i hi => hA a ha haN i hi⟩
    simp only [gradeBasisGL]
    rw [gradeColMat_mulVec, b.sum_repr]

theorem grade_of_basis {κ : Type} [Fintype κ] (β : Module.Basis κ k (Fin n → k)) (ω : κ → ℤ)
    (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (hZ : ∀ z ∈ Z, ∀ j, z *ᵥ β j ∈ span k (β '' {j' | ω j' = ω j}))
    (hN : ∀ j, N *ᵥ β j ∈ span k (β '' {j' | ω j' = ω j + 1}))
    (hv : v ∈ span k (β '' {j | ω j = 0}))
    (hA : ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
      ∀ j, ω j < 0 → β.repr (a *ᵥ v) j = 0) :
    ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  have hcard : Fintype.card κ = n := by
    rw [← Module.finrank_eq_card_basis β, Module.finrank_fin_fun]
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b := β.reindex e
  let w : Fin n → ℤ := fun i => ω (e.symm i)
  have hb : ∀ j, β j = b (e j) := fun j => by simp [b]
  have himg : ∀ c : ℤ, β '' {j | ω j = c} = b '' {i | w i = c} := by
    intro c
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e j, by simpa [w] using hj, (hb j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e.symm i, hi, by simp [b]⟩
  refine ⟨gradeBasisGL b, w, grade_fin b w Z N v ?_ ?_ ?_ ?_⟩
  · intro z hz i
    have := hZ z hz (e.symm i)
    rw [himg] at this
    simpa [b, w] using this
  · intro i
    have := hN (e.symm i)
    rw [himg] at this
    simpa [b, w] using this
  · rw [← himg]; exact hv
  · intro a ha haN i hi
    have := hA a ha haN (e.symm i) hi
    simpa [b] using this

theorem grade_of_frame {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {M : Type} [Fintype M] {L : M → Type}
    [∀ m, Fintype (L m)] {R : Z → (m : M) → L m → L m → k} {o : (m : M) → L m → k}
    {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k} (F : Frame Z M L R o N v) :
    ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  let ω : (Σ m, L m × (Σ a : F.ι m, Fin (F.l m a))) → ℤ := fun j => ((j.2.2.2 : ℕ) : ℤ) - (F.s j.1 j.2.2.1 : ℤ)
  apply grade_of_basis F.β ω Z N v
  · rintro z hz ⟨m, p, jj⟩
    rw [show (z : Matrix (Fin n) (Fin n) k) = ((⟨z, hz⟩ : Z) : Matrix (Fin n) (Fin n) k) from rfl, F.hZ]
    refine sum_mem fun q _ => smul_mem _ _ (subset_span ⟨⟨m, q, jj⟩, rfl, rfl⟩)
  · rintro ⟨m, p, a, i⟩
    rw [F.hN]
    split_ifs with h
    · exact subset_span ⟨_, by simp only [Set.mem_ofPred_eq, ω]; push_cast; ring, rfl⟩
    · exact zero_mem _
  · suffices h : (∑ m, ∑ p, ∑ a, if h : F.s m a < F.l m a then o m p • F.β ⟨m, (p, ⟨a, ⟨F.s m a, h⟩⟩)⟩ else 0) ∈
        span k (F.β '' {j | ω j = 0}) by rw [← F.hv] at h; exact h
    refine sum_mem fun m _ => sum_mem fun p _ => sum_mem fun a _ => ?_
    split_ifs with h
    · exact smul_mem _ _ (subset_span ⟨_, by simp [ω], rfl⟩)
    · exact zero_mem _
  · rintro A hA hAN ⟨m, p, a, i⟩ hi
    exact F.hA A hA hAN m p a i (by simp only [ω] at hi; omega)

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end
