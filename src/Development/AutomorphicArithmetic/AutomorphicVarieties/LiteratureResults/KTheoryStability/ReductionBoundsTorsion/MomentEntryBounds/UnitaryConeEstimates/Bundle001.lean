module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.Complex.BigOperators
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.NumberField.Units.Basic

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

abbrev G (ι : Type) (N : ℕ) : Type := ι → SpecialLinearGroup (Fin N) ℂ

variable {ι : Type} {N : ℕ}

abbrev mt (x : G ι N) (w : ι) : Matrix (Fin N) (Fin N) ℂ :=
  ((x w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)

def dg (s : Fin N → ℝ) (hs : ∑ i, s i = 0) : G ι N := fun _ =>
  ⟨diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ), by
    rw [det_diagonal, ← Complex.ofReal_prod, ← Real.exp_sum, hs, Real.exp_zero, Complex.ofReal_one]⟩

def Cone (T : ℝ) (s : Fin N → ℝ) : Prop := ∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + T

def W (s : Fin N → ℝ) : ℝ := ∑ i : Fin N, ∑ j : Fin N, if (j : ℕ) = i + 1 then |s i - s j| else 0

def Phi (s : Fin N → ℝ) : ℝ := ∑ i : Fin N, ∑ j : Fin N, if i < j then s i - s j else 0

def PB (M : ℝ) : Set (G ι N) := {p | ∀ w, (mt p w).BlockTriangular id ∧ ∀ i j, ‖mt p w i j‖ ≤ M}

def KS : Set (G ι N) := {k | ∀ w, mt k w ∈ unitaryGroup (Fin N) ℂ}

def OmG [Fintype ι] (M : ℝ) : Set (G ι N) :=
  {p | (∀ w, (mt p w).BlockTriangular id) ∧ (∀ w i j, ‖mt p w i j‖ ≤ M) ∧ (∀ w i, M⁻¹ ≤ ‖mt p w i i‖) ∧
    ∀ i, ∏ w, ‖mt p w i i‖ = 1}

def Sg (P : Set (G ι N)) (T : ℝ) : Set (G ι N) :=
  {x | ∃ p ∈ P, ∃ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), (∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + T) ∧
    ∃ k ∈ KS, x = p * dg s hs * k}

def Xb (P : Set (G ι N)) (T : ℝ) (m : Fin N → ℤ) : Set (G ι N) :=
  {x | ∃ p ∈ P, ∃ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), Cone T s ∧ (∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1) ∧
    ∃ k ∈ KS, x = p * dg s hs * k}

def Zb (R : ℝ) : Set (G ι N) := {z | ∀ w i j, ‖mt z w i j‖ ≤ R}

open scoped Classical in
open Classical in
def nu (w0 : ι) : SpecialLinearGroup (Fin N) GaussianInt →* G ι N :=
  (MonoidHom.mulSingle (fun _ : ι => SpecialLinearGroup (Fin N) ℂ) w0).comp
    (SpecialLinearGroup.map GaussianInt.toComplex)

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
end

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem entry_mul_le {A B : Matrix (Fin N) (Fin N) ℂ} {a b : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ a)
    (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin N) : ‖(A * B) i j‖ ≤ N * (a * b) := by
  rw [Matrix.mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin N, a * b := by
        gcongr with k
        rw [norm_mul]
        exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ((norm_nonneg _).trans (hA i k))
    _ = N * (a * b) := by simp

theorem adj_le {A : Matrix (Fin N) (Fin N) ℂ} {M : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ M) (i j : Fin N) :
    ‖adjugate A i j‖ ≤ (N.factorial : ℝ) * (max M 1) ^ N := by
  rw [adjugate_apply]
  have hb : ∀ k l, (NormedField.toAbsoluteValue ℂ) (A.updateRow j (Pi.single i 1) k l) ≤ max M 1 := by
    intro k l
    show ‖A.updateRow j (Pi.single i 1) k l‖ ≤ max M 1
    rcases eq_or_ne k j with rfl | hk
    · rw [updateRow_self]
      by_cases hl : l = i
      · subst hl; simp
      · simp [hl]
    · rw [updateRow_ne hk]; exact (hA k l).trans (le_max_left _ _)
  have h := Matrix.det_le hb
  rw [nsmul_eq_mul, Fintype.card_fin] at h
  exact h

theorem tri (M : ℝ) : ∃ R0 : ℝ, ∀ (h p p' u : Matrix (Fin N) (Fin N) ℂ) (s s' : Fin N → ℝ),
    (∀ i, |s i - s' i| ≤ 1) → h.BlockTriangular id → p.BlockTriangular id → p'.BlockTriangular id →
    (∀ i j, ‖p i j‖ ≤ M) → (∀ i j, ‖p' i j‖ ≤ M) → p.det = 1 → p'.det = 1 → u ∈ unitaryGroup (Fin N) ℂ →
    h * p * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) =
      p' * diagonal (fun i => ((Real.exp (s' i) : ℝ) : ℂ)) * u →
    ∀ i j, ‖h i j‖ ≤ R0 := by
  refine ⟨N * (N * (M * Real.exp 1) * ((N.factorial : ℝ) * (max M 1) ^ N)), ?_⟩
  intro h p p' u s s' hss hh hp hp' hpM hp'M hpd hp'd hu heq i j
  set a := diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) with ha
  set a' := diagonal (fun i => ((Real.exp (s' i) : ℝ) : ℂ)) with ha'
  set ai := diagonal (fun i => ((Real.exp (-s i) : ℝ) : ℂ)) with hai
  have haai : a * ai = 1 := by
    rw [ha, hai, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have hpadj : p * adjugate p = 1 := by rw [mul_adjugate, hpd, one_smul]
  have hrec : h * p * a * ai * adjugate p = h := by
    rw [show h * p * a * ai * adjugate p = h * (p * (a * ai) * adjugate p) by simp only [Matrix.mul_assoc],
      haai, Matrix.mul_one, hpadj, Matrix.mul_one]
  rw [heq] at hrec
  have hdet' : IsUnit (p' * a').det := by
    rw [det_mul, hp'd, one_mul, ha', det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun k _ => by exact_mod_cast (Real.exp_pos _).ne')
  have hu_eq : u = (p' * a')⁻¹ * (h * p * a) := by
    rw [heq, Matrix.nonsing_inv_mul_cancel_left (A := p' * a') (B := u) hdet']
  have hut : u.BlockTriangular id := by
    haveI := invertibleOfIsUnitDet (p' * a') hdet'
    rw [hu_eq]
    exact (blockTriangular_inv_of_blockTriangular (hp'.mul (blockTriangular_diagonal _))).mul
      ((hh.mul hp).mul (blockTriangular_diagonal _))
  have hstar : star u * u = 1 := (mem_unitaryGroup_iff'.1 hu)
  have hinv : u⁻¹ = star u := Matrix.inv_eq_left_inv hstar
  have hut' : (star u).BlockTriangular id := by
    rw [← hinv]
    haveI : Invertible u := invertibleOfLeftInverse _ _ hstar
    exact blockTriangular_inv_of_blockTriangular hut
  have hoff : ∀ k l, k ≠ l → u k l = 0 := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with h1 | h1
    · have := hut' (show id k < id l from h1)
      rw [star_apply] at this
      simpa using this
    · exact hut h1
  have hD : ∀ k l, ‖(a' * u * ai) k l‖ ≤ Real.exp 1 := by
    intro k l
    rw [ha', hai, mul_diagonal, diagonal_mul]
    by_cases hkl : k = l
    · subst hkl
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      calc Real.exp (s' k) * ‖u k k‖ * Real.exp (-s k) ≤ Real.exp (s' k) * 1 * Real.exp (-s k) := by
            gcongr; exact entry_norm_bound_of_unitary hu k k
        _ = Real.exp (s' k - s k) := by rw [mul_one, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp 1 := Real.exp_le_exp.2 (by have := hss k; rw [abs_le] at this; linarith)
    · rw [hoff k l hkl]; simp; positivity
  rw [← hrec, show p' * a' * u * ai * adjugate p = p' * (a' * u * ai) * adjugate p by
    simp only [Matrix.mul_assoc]]
  exact entry_mul_le (entry_mul_le hp'M hD) (adj_le hpM) i j

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.KB.MomentRationality.Cz.Red

def dd {R : Type*} [CommRing R] (N : ℕ) (u : R) : Matrix (Fin N) (Fin N) R :=
  diagonal fun i => if (i : ℕ) = 0 then u else 1

theorem dd_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) (u : R) :
    (dd N u).map f = dd N (f u) := by
  unfold dd
  rw [diagonal_map (map_zero f)]
  congr 1
  funext i
  split_ifs <;> simp

theorem dd_mul {R : Type*} [CommRing R] (N : ℕ) (u v : R) : dd N u * dd N v = dd N (u * v) := by
  unfold dd
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem dd_one {R : Type*} [CommRing R] (N : ℕ) : dd N (1 : R) = 1 := by
  unfold dd
  simp

theorem det_dd {R : Type*} [CommRing R] {N : ℕ} (hN : 1 ≤ N) (u : R) : (dd N u).det = u := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  unfold dd
  rw [det_diagonal, Fin.prod_univ_succ]
  simp [Fin.val_succ]

def ddGL {R : Type*} [CommRing R] (N : ℕ) (u : Rˣ) : GL (Fin N) R :=
  ⟨dd N (u : R), dd N ((u⁻¹ : Rˣ) : R), by rw [dd_mul, Units.mul_inv, dd_one],
    by rw [dd_mul, Units.inv_mul, dd_one]⟩

theorem exists_root {N : ℕ} (hN : N ≠ 0) {d : ℂ} (hd : d ≠ 0) : ∃ z : ℂ, z ≠ 0 ∧ z ^ N * d = 1 := by
  refine ⟨d⁻¹ ^ ((N : ℂ)⁻¹), ?_, ?_⟩
  · intro h
    have := Complex.cpow_nat_inv_pow d⁻¹ hN
    rw [h, zero_pow hN] at this
    exact inv_ne_zero hd this.symm
  · rw [Complex.cpow_nat_inv_pow _ hN, inv_mul_cancel₀ hd]

theorem cancel_left {N : ℕ} {A X B : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) {z c : ℂ} (hz : z ≠ 0)
    (h : (z • A) * X = c • (A * B)) : X = (z⁻¹ * c) • B := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have h2 : A * (z • X) = A * (c • B) := by
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.smul_mul, h]
  have h3 : z • X = c • B := by
    have := congrArg (fun Y => A⁻¹ * Y) h2
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu] using this
  rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hz, one_smul]

open NumberField in
theorem units_fin {L : Type*} [Field L] [NumberField L] (N : ℕ) (hN : 0 < N) :
    ∃ S : Finset (𝓞 L)ˣ, ∀ u : (𝓞 L)ˣ, ∃ v : (𝓞 L)ˣ, ∃ u0 ∈ S, u = v ^ N * u0 := by
  classical
  let f : Units.torsion L × (Fin (Units.rank L) → Fin N) → (𝓞 L)ˣ :=
    fun p => (p.1 : (𝓞 L)ˣ) * ∏ i, Units.fundSystem L i ^ ((p.2 i : ℕ) : ℤ)
  refine ⟨(Set.finite_range f).toFinset, fun u => ?_⟩
  obtain ⟨⟨ζ, e⟩, hu, -⟩ := Units.exist_unique_eq_mul_prod L u
  have h1 : ∀ i, 0 ≤ e i % N := fun i => Int.emod_nonneg (e i) (by omega)
  have h2 : ∀ i, e i % N < N := fun i => Int.emod_lt_of_pos (e i) (by omega)
  refine ⟨∏ i, Units.fundSystem L i ^ (e i / N), f (ζ, fun i => ⟨(e i % N).toNat, by
    have := h2 i; have := h1 i; omega⟩), by simp, ?_⟩
  have hsplit : ∀ i, Units.fundSystem L i ^ e i =
      (Units.fundSystem L i ^ (e i / N)) ^ N * Units.fundSystem L i ^ (((e i % N).toNat : ℕ) : ℤ) := by
    intro i
    rw [Int.toNat_of_nonneg (h1 i), ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_add]
    congr 1
    linarith [Int.mul_ediv_add_emod (e i) N]
  rw [hu]
  simp only [f]
  rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_mul_distrib, Finset.prod_pow]
  ac_rfl

end PositivityTheory.KB.MomentRationality.Cz.Red
end
end
