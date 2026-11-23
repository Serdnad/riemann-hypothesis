module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle003
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow

@[expose] public section

section

open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem graded_inv {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ)
    (G G' : Matrix Ix Ix R) (hG : ∀ p q, deg p ≠ deg q → G p q = 0) (hGG : G * G' = 1) :
    ∀ p q, deg p ≠ deg q → G' p q = 0 := by
  have hGG' : G' * G = 1 := mul_eq_one_comm.mp hGG
  let G'' : Matrix Ix Ix R := Matrix.of fun p q => if deg p = deg q then G' p q else 0
  have h1 : G * G'' = 1 := by
    ext p q
    by_cases hpq : deg p = deg q
    · rw [← hGG, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : deg r = deg q
      · simp [G'', hr]
      · rw [hG p r (by omega)]; simp
    · rw [Matrix.mul_apply, Matrix.one_apply_ne (by rintro rfl; exact hpq rfl)]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : deg r = deg q
      · rw [hG p r (by omega)]; simp
      · simp [G'', hr]
  have h2 : G' = G'' := by
    calc G' = G' * (G * G'') := by rw [h1, Matrix.mul_one]
      _ = G'' := by rw [← Matrix.mul_assoc, hGG', Matrix.one_mul]
  intro p q hpq
  rw [h2]; simp [G'', hpq]

theorem submatrix_mul_of_support {R Ix J K L : Type} [CommRing R] [Fintype Ix] [Fintype L]
    (A B : Matrix Ix Ix R) (f : J → Ix) (g : K → Ix) (i : L → Ix) (hi : Function.Injective i)
    (h : ∀ p q r, r ∉ Set.range i → A (f p) r * B r (g q) = 0) :
    (A * B).submatrix f g = A.submatrix f i * B.submatrix i g := by
  classical
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  exact Fintype.sum_of_injective i hi _ (fun r => A (f p) r * B r (g q))
    (fun r hr => h p q r hr) (fun _ => rfl)

theorem torsSq_conj : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) (G G' : Matrix Ix Ix R) (t : R), (∀ p q, deg p ≠ deg q → G p q = 0) → G * G' = 1 → IsCx deg D → TorsSq deg D t → ∃ t', TorsSq deg (G' * D * G) t' ∧ t' * (G.submatrix (fun p : {p // Even (deg p)} => p.1) (fun p : {p // Even (deg p)} => p.1)).det ^ 2 = t * (G.submatrix (fun p : {p // ¬ Even (deg p)} => p.1) (fun p : {p // ¬ Even (deg p)} => p.1)).det ^ 2 := by
  intro R Ix _ _ _ deg D G G' t hG hGG _ hT
  obtain ⟨h, hh, hDh, e, rfl⟩ := hT
  have hG' := graded_inv deg G G' hG hGG
  have hGG' : G' * G = 1 := mul_eq_one_comm.mp hGG
  have hev : ∀ (p : {p // Even (deg p)}) r,
      r ∉ Set.range (fun p : {p // Even (deg p)} => p.1) → deg p.1 ≠ deg r := by
    intro p r hr hd
    exact hr ⟨⟨r, hd ▸ p.2⟩, rfl⟩
  have hod : ∀ (p : {p // Even (deg p)}) r,
      r ∉ Set.range (fun p : {p // Even (deg p)} => (e p).1) → deg r ≠ deg (e p).1 := by
    intro p r hr hd
    exact hr ⟨e.symm ⟨r, hd ▸ (e p).2⟩, by simp⟩
  refine ⟨_, ⟨G' * h * G, ?_, ?_, e, rfl⟩, ?_⟩
  · intro p q hpq
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : deg r = deg q
    · rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun s _ => ?_
      by_cases hs : deg p = deg s
      · rw [hh s r (by omega)]; simp
      · rw [hG' p s hs]; simp
    · rw [hG r q hr]; simp
  · calc G' * D * G * (G' * h * G) + G' * h * G * (G' * D * G)
        = G' * (D * (G * G') * h + h * (G * G') * D) * G := by noncomm_ring
      _ = 1 := by rw [hGG, Matrix.mul_one, Matrix.mul_one, hDh, Matrix.mul_one, hGG']
  · have e1 : G' * D * G + G' * h * G = G' * (D + h) * G := by noncomm_ring
    have e2 : (G' * (D + h) * G).submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1)
        = G'.submatrix (fun p : {p // Even (deg p)} => p.1) (fun p : {p // Even (deg p)} => p.1) *
          (D + h).submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1) *
          G.submatrix (fun p => (e p).1) (fun p => (e p).1) := by
      rw [submatrix_mul_of_support (G' * (D + h)) G _ _ (fun p => (e p).1)
          (Subtype.val_injective.comp e.injective)
          (fun p q r hr => by rw [hG _ _ (hod q r hr), mul_zero]),
        submatrix_mul_of_support G' (D + h) _ _ (fun p : {p // Even (deg p)} => p.1)
          Subtype.val_injective (fun p q r hr => by rw [hG' _ _ (hev p r hr), zero_mul])]
    have e3 : (G.submatrix (fun p => (e p).1) (fun p => (e p).1)).det =
        (G.submatrix (fun p : {p // ¬ Even (deg p)} => p.1)
          (fun p : {p // ¬ Even (deg p)} => p.1)).det := by
      rw [← Matrix.det_submatrix_equiv_self e]; rfl
    have e4 : (G'.submatrix (fun p : {p // Even (deg p)} => p.1)
          (fun p : {p // Even (deg p)} => p.1)).det *
        (G.submatrix (fun p : {p // Even (deg p)} => p.1)
          (fun p : {p // Even (deg p)} => p.1)).det = 1 := by
      rw [← Matrix.det_mul, ← submatrix_mul_of_support G' G _ _ (fun p : {p // Even (deg p)} => p.1)
          Subtype.val_injective (fun p q r hr => by rw [hG' _ _ (hev p r hr), zero_mul]), hGG',
        Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]
    rw [e1, e2, Matrix.det_mul, Matrix.det_mul, e3]
    set a := (G'.submatrix (fun p : {p // Even (deg p)} => p.1)
          (fun p : {p // Even (deg p)} => p.1)).det
    set b := (G.submatrix (fun p : {p // Even (deg p)} => p.1)
          (fun p : {p // Even (deg p)} => p.1)).det
    set c := (G.submatrix (fun p : {p // ¬ Even (deg p)} => p.1)
          (fun p : {p // ¬ Even (deg p)} => p.1)).det
    set d := ((D + h).submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1)).det
    calc (a * d * c) ^ 2 * b ^ 2 = (a * b) ^ 2 * (d ^ 2 * c ^ 2) := by ring
      _ = _ := by rw [e4]; ring

end GlobalTheory.KeyKa
end

section

open GlobalTheory.KeyKa
namespace GlobalTheory.KaUnique

theorem sign_swap {R : Type} [CommRing R] {g : ℕ} (P : Finset (Fin g)) {i i' : Fin g} (hi : i ∉ P) (hi' : i' ∉ P)
    (hne : i ≠ i') :
    ((-1 : R) ^ (P.filter (· < i)).card * (-1) ^ ((insert i P).filter (· < i')).card) +
      ((-1 : R) ^ (P.filter (· < i')).card * (-1) ^ ((insert i' P).filter (· < i)).card) = 0 := by
  rw [Finset.filter_insert, Finset.filter_insert]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_pos h, if_neg (not_lt.2 h.le), Finset.card_insert_of_notMem (fun hh => hi (Finset.mem_filter.1 hh).1)]
    ring
  · rw [if_pos h, if_neg (not_lt.2 h.le), Finset.card_insert_of_notMem (fun hh => hi' (Finset.mem_filter.1 hh).1)]
    ring

theorem isCx_kosD {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (hc : ∀ i i' j, j + 1 < g → m i j (j + 1) * m i' (j + 1) (j + 1 + 1) = m i' j (j + 1) * m i (j + 1) (j + 1 + 1))
    (he : ∀ i, ev 0 * m i 0 (0 + 1) = 0) : IsCx kdeg (kosD m ev) := by
  have hc' : ∀ i i' j j₁ j₁' j₂, j₁ = j + 1 → j₁' = j + 1 → j₂ = j + 1 + 1 → j₂ ≤ g →
      m i j j₁ * m i' j₁ j₂ = m i' j j₁' * m i j₁' j₂ := by
    rintro i i' j _ _ _ rfl rfl rfl h
    exact hc i i' j h
  have he' : ∀ i j j₁, j = 0 → j₁ = 0 + 1 → ev j * m i j j₁ = 0 := by
    rintro i _ _ rfl rfl
    exact he i
  refine ⟨fun p q h => ?_, ?_⟩
  · rcases p with p | p <;> rcases q with q | q
    · simp only [kosD]
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      rintro ⟨hi, hq⟩
      apply h
      simp [kdeg, hq, Finset.card_insert_of_notMem hi]
    · rfl
    · simp only [kosD]
      refine if_neg fun hq => h ?_
      simp [kdeg, hq]
    · rfl
  ext p q
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.zero_apply]
  have h0 : ∑ a : Fin d, kosD m ev p (.inr a) * kosD m ev (.inr a) q = 0 :=
    Finset.sum_eq_zero fun a _ => by rcases p with p | p <;> exact zero_mul _
  rw [h0, add_zero]
  rcases q with ⟨Q, c⟩ | q
  swap
  · exact Finset.sum_eq_zero fun a _ => mul_zero _
  rw [Fintype.sum_sigma]
  rcases p with ⟨P, a⟩ | a
  · let F : Fin g × Fin g → R := fun ii => if ii.1 ∉ P ∧ ii.2 ∉ insert ii.1 P ∧ Q = insert ii.2 (insert ii.1 P) then
      ((-1 : R) ^ (P.filter (· < ii.1)).card * (-1) ^ ((insert ii.1 P).filter (· < ii.2)).card) *
        (m ii.1 P.card (insert ii.1 P).card * m ii.2 (insert ii.1 P).card Q.card) a c else 0
    have h1 : ∑ I : Finset (Fin g), ∑ k : Fin (N I.card), kosD m ev (.inl ⟨P, a⟩) (.inl ⟨I, k⟩) *
        kosD m ev (.inl ⟨I, k⟩) (.inl ⟨Q, c⟩) = ∑ ii, F ii := by
      simp only [kosD, Finset.sum_mul_sum]
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin (N _)))) (t := (Finset.univ : Finset (Fin g)))]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Finset.sum_eq_single (insert i P)]
      · simp only [F, Matrix.mul_apply, Finset.mul_sum]
        by_cases h₁ : i ∉ P
        · by_cases h₂ : i' ∉ insert i P ∧ Q = insert i' (insert i P)
          · rw [if_pos ⟨h₁, h₂⟩]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [if_pos ⟨h₁, trivial⟩, if_pos h₂]; ring
          · rw [if_neg fun hh => h₂ hh.2]
            exact Finset.sum_eq_zero fun k _ => by rw [if_neg h₂, mul_zero]
        · rw [if_neg fun hh => h₁ hh.1]
          exact Finset.sum_eq_zero fun k _ => by rw [if_neg fun hh => h₁ hh.1, zero_mul]
      · intro I _ hI
        exact Finset.sum_eq_zero fun k _ => by rw [if_neg fun hh => hI hh.2, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1]
    have hsw : ∀ i i' : Fin g, (i ∉ P ∧ i' ∉ insert i P ∧ Q = insert i' (insert i P)) →
        (i' ∉ P ∧ i ∉ insert i' P ∧ Q = insert i (insert i' P)) := by
      rintro i i' ⟨h₁, h₂, h₃⟩
      rw [Finset.mem_insert, not_or] at h₂
      refine ⟨h₂.2, ?_, h₃.trans (Finset.insert_comm _ _ _)⟩
      rw [Finset.mem_insert, not_or]
      exact ⟨fun e => h₂.1 e.symm, h₁⟩
    refine Finset.sum_involution (fun ii _ => ii.swap) ?_ ?_ (fun _ _ => Finset.mem_univ _) (fun _ _ => rfl)
    · rintro ⟨i, i'⟩ _
      simp only [F, Prod.swap]
      by_cases h : i ∉ P ∧ i' ∉ insert i P ∧ Q = insert i' (insert i P)
      · have h' := hsw _ _ h
        rw [if_pos h, if_pos h', hc' i i' P.card (insert i P).card (insert i' P).card Q.card
          (Finset.card_insert_of_notMem h.1) (Finset.card_insert_of_notMem h'.1)
          (by rw [h.2.2, Finset.card_insert_of_notMem h.2.1, Finset.card_insert_of_notMem h.1])
          (by simpa using Q.card_le_univ), ← add_mul,
          sign_swap P h.1 h'.1 (fun e => h.2.1 (e ▸ Finset.mem_insert_self _ _)), zero_mul]
      · rw [if_neg h, if_neg fun hh => h (hsw _ _ hh), add_zero]
    · rintro ⟨i, i'⟩ _ hF e
      apply hF
      obtain rfl : i' = i := congrArg Prod.fst e
      exact if_neg fun hh => hh.2.1 (Finset.mem_insert_self _ _)
  · refine Finset.sum_eq_zero fun I _ => ?_
    simp only [kosD]
    by_cases hI : I = ∅
    · simp only [if_pos hI, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h : i ∉ I ∧ Q = insert i I
      · have := congrFun (congrFun (he' i I.card Q.card (by simp [hI])
          (by rw [h.2, Finset.card_insert_of_notMem h.1]; simp [hI])) a) c
        rw [Matrix.mul_apply, Matrix.zero_apply] at this
        simp only [if_pos h, mul_left_comm _ ((-1 : R) ^ _), ← Finset.mul_sum, this, mul_zero]
      · simp only [if_neg h, mul_zero, Finset.sum_const_zero]
    · simp only [if_neg hI, zero_mul, Finset.sum_const_zero]

end GlobalTheory.KaUnique
end

section

open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem torsSq_map : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) (R' : Type) [CommRing R'] (f : R →+* R') (t : R), TorsSq deg D t → TorsSq deg (D.map f) (f t) := by
  intro R Ix _ _ _ deg D R' _ f t H
  obtain ⟨h, h1, h2, e, h3⟩ := H
  refine ⟨h.map f, ?_, ?_, e, ?_⟩
  · intro p q hpq
    simp [Matrix.map_apply, h1 p q hpq]
  · have := congrArg (f.mapMatrix : Matrix Ix Ix R →+* Matrix Ix Ix R') h2
    rw [map_add (f := _), map_mul, map_mul, map_one] at this
    exact this
  · rw [h3, map_pow, RingHom.map_det]
    congr 2
    ext p q
    simp [Matrix.map_apply]

end GlobalTheory.KeyKa
end

section

open GlobalTheory.KeyKa

namespace GlobalTheory.TorsionHolomorphic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod {ι : Type} (s : Finset ι) (f : ι → E → ℂ) (W : Set E)
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) :
    DifferentiableOn ℂ (fun e => ∏ i ∈ s, f i e) W := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact differentiableOn_const 1
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact (hf a).mul ih

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_sum {ι : Type} (s : Finset ι) (f : ι → E → ℂ) (W : Set E)
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) :
    DifferentiableOn ℂ (fun e => ∑ i ∈ s, f i e) W :=
  DifferentiableOn.fun_sum (fun i _ => hf i)


variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det {n : Type} [Fintype n] [DecidableEq n] (A : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W) :
    DifferentiableOn ℂ (fun e => (A e).det) W := by
  have hdet : (fun e => (A e).det) =
      fun e => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A e (σ i) i := by
    funext e
    exact Matrix.det_apply' _
  rw [hdet]
  refine DifferentiableOn.fun_sum (fun σ _ => ?_)
  exact (differentiableOn_const _).mul
    (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod Finset.univ (fun i e => A e (σ i) i) W
      (fun i => hA _ _))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul {n : Type} [Fintype n] (A B : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W)
    (hB : ∀ p q, DifferentiableOn ℂ (fun e => B e p q) W) (p q : n) :
    DifferentiableOn ℂ (fun e => (A e * B e) p q) W := by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum (fun r _ => (hA p r).mul (hB r q))


variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv {n : Type} [Fintype n] [DecidableEq n] (A : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W)
    (hdet : ∀ e ∈ W, (A e).det ≠ 0) (p q : n) :
    DifferentiableOn ℂ (fun e => (A e)⁻¹ p q) W := by
  have key : ∀ e, (A e)⁻¹ p q = ((A e).det)⁻¹ * (A e).adjugate p q := by
    intro e
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  simp only [key]
  refine (DifferentiableOn.inv (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det A W hA) hdet).mul ?_
  simp only [Matrix.adjugate_apply]
  have hentry : ∀ i j, DifferentiableOn ℂ
      (fun e => (A e).updateRow q (Pi.single p 1) i j) W := by
    intro i j
    by_cases hi : i = q
    · subst hi
      simp only [Matrix.updateRow_self]
      exact differentiableOn_const _
    · simp only [Matrix.updateRow_ne hi]
      exact hA i j
  exact _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det (fun e => (A e).updateRow q (Pi.single p 1))
    W hentry

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem degree_part_homotopy_of_anticommutator_eq_one {Ix : Type} [Fintype Ix] [DecidableEq Ix]
    (deg : Ix → ℕ) (D h : Matrix Ix Ix ℂ) (hD : ∀ p q, deg q ≠ deg p + 1 → D p q = 0)
    (hh : D * h + h * D = 1) :
    D * Matrix.of (fun p q => if deg p = deg q + 1 then h p q else 0) +
      Matrix.of (fun p q => if deg p = deg q + 1 then h p q else 0) * D = 1 := by
  ext p q
  have h1 : ∀ r, D p r * (if deg r = deg q + 1 then h r q else 0) =
      if deg p = deg q then D p r * h r q else 0 := by
    intro r
    by_cases hr : deg r = deg p + 1
    · by_cases hpq : deg p = deg q
      · rw [if_pos (by omega), if_pos hpq]
      · rw [if_neg (by omega), if_neg hpq, mul_zero]
    · rw [hD p r hr, zero_mul, zero_mul, ite_self]
  have h2 : ∀ r, (if deg p = deg r + 1 then h p r else 0) * D r q =
      if deg p = deg q then h p r * D r q else 0 := by
    intro r
    by_cases hr : deg q = deg r + 1
    · by_cases hpq : deg p = deg q
      · rw [if_pos (by omega), if_pos hpq]
      · rw [if_neg (by omega), if_neg hpq, zero_mul]
    · rw [hD r q hr, mul_zero, mul_zero, ite_self]
  have hpq' := congrFun (congrFun hh p) q
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply] at hpq' ⊢
  simp only [h1, h2]
  by_cases hpq : deg p = deg q
  · simp only [if_pos hpq]
    exact hpq'
  · simp only [if_neg hpq, Finset.sum_const_zero, add_zero]
    have hne : p ≠ q := fun h => hpq (h ▸ rfl)
    rw [Matrix.one_apply_ne hne]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem contracting_homotopy_of_det_anticommutator_ne_zero {Ix : Type} [Fintype Ix]
    [DecidableEq Ix] (D h : Matrix Ix Ix ℂ) (hDD : D * D = 0)
    (hdet : (D * h + h * D).det ≠ 0) :
    D * (h * (D * h + h * D)⁻¹) + h * (D * h + h * D)⁻¹ * D = 1 := by
  set A := D * h + h * D with hA
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hcomm : D * A = A * D := by
    rw [hA, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hDD, Matrix.zero_mul, zero_add,
      Matrix.mul_assoc h D D, hDD, Matrix.mul_zero, add_zero, Matrix.mul_assoc]
  have hinv : A⁻¹ * D = D * A⁻¹ := by
    calc A⁻¹ * D = A⁻¹ * D * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A hu, Matrix.mul_one]
      _ = A⁻¹ * (D * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * D) * A⁻¹ := by rw [hcomm]
      _ = D * A⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hu, Matrix.one_mul]
  calc D * (h * A⁻¹) + h * A⁻¹ * D = D * h * A⁻¹ + h * D * A⁻¹ := by
        rw [Matrix.mul_assoc h, hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    _ = A * A⁻¹ := by rw [hA, Matrix.add_mul]
    _ = 1 := Matrix.mul_nonsing_inv A hu


variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.TorsionHolomorphic.exists_differentiableOn_torsSq :
    ∀ (E Ix : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : E → Matrix Ix Ix ℂ) (W : Set E) (e₀ : E) (t₀ : ℂ), IsOpen W → e₀ ∈ W → (∀ p q, DifferentiableOn ℂ (fun e => D e p q) W) → (∀ e ∈ W, _root_.GlobalTheory.KeyKa.IsCx deg (D e)) → _root_.GlobalTheory.KeyKa.TorsSq deg (D e₀) t₀ → ∃ (W' : Set E) (t : E → ℂ), IsOpen W' ∧ e₀ ∈ W' ∧ W' ⊆ W ∧ DifferentiableOn ℂ t W' ∧ ∀ e ∈ W', _root_.GlobalTheory.KeyKa.TorsSq deg (D e) (t e) := by
  intro E Ix _ _ _ _ deg D W e₀ t₀ hW he₀ hD hcx htor
  obtain ⟨h₀, -, hcontr₀, σ, -⟩ := htor
  set A : E → Matrix Ix Ix ℂ := fun e => D e * h₀ + h₀ * D e with hAdef
  have hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W := by
    intro p q
    simp only [hAdef, Matrix.add_apply]
    exact (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul D (fun _ => h₀) W hD (fun _ _ => differentiableOn_const _)
      p q).add (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul (fun _ => h₀) D W
        (fun _ _ => differentiableOn_const _) hD p q)
  have hAdet := _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det A W hA
  set W' := W ∩ (fun e => (A e).det) ⁻¹' {(0 : ℂ)}ᶜ with hW'
  have hW'open : IsOpen W' := hAdet.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  have hsub : W' ⊆ W := Set.inter_subset_left
  have hdetW' : ∀ e ∈ W', (A e).det ≠ 0 := fun e he => he.2
  have hAe₀ : A e₀ = 1 := hcontr₀
  have he₀' : e₀ ∈ W' := ⟨he₀, by simp [hAe₀]⟩
  set hh : E → Matrix Ix Ix ℂ := fun e =>
    Matrix.of (fun p q => if deg p = deg q + 1 then (h₀ * (A e)⁻¹) p q else 0) with hhdef
  have hhdiff : ∀ p q, DifferentiableOn ℂ (fun e => hh e p q) W' := by
    intro p q
    simp only [hhdef, Matrix.of_apply]
    by_cases hpq : deg p = deg q + 1
    · simp only [if_pos hpq]
      exact _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul (fun _ => h₀) (fun e => (A e)⁻¹) W'
        (fun _ _ => differentiableOn_const _)
        (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv A W' (fun i j => (hA i j).mono hsub) hdetW') p q
    · simp only [if_neg hpq]
      exact differentiableOn_const _
  refine ⟨W', fun e => ((D e + hh e).submatrix (fun p : {p // Even (deg p)} => (p : Ix))
    (fun p : {p // Even (deg p)} => ((σ p : {p // ¬Even (deg p)}) : Ix))).det ^ 2,
    hW'open, he₀', hsub, ?_, ?_⟩
  · refine DifferentiableOn.pow ?_ 2
    refine _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det (fun e => (D e + hh e).submatrix
      (fun p : {p // Even (deg p)} => (p : Ix))
      (fun p : {p // Even (deg p)} => ((σ p : {p // ¬Even (deg p)}) : Ix))) W' (fun i j => ?_)
    simp only [Matrix.submatrix_apply, Matrix.add_apply]
    exact ((hD _ _).mono hsub).add (hhdiff _ _)
  · intro e he
    refine ⟨hh e, ?_, ?_, σ, rfl⟩
    · intro p q hpq
      simp only [hhdef, Matrix.of_apply, if_neg hpq]
    · exact degree_part_homotopy_of_anticommutator_eq_one deg (D e) (h₀ * (A e)⁻¹) (hcx e (hsub he)).1
        (contracting_homotopy_of_det_anticommutator_ne_zero (D e) h₀ (hcx e (hsub he)).2 (hdetW' e he))

end GlobalTheory.TorsionHolomorphic
end

section


theorem _root_.GlobalTheory.T.exists_perm_representatives_mod_similitude : ∀ (g m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ k n : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, ∀ k' n' : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, (∀ I I', I ≠ I' → ¬ ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k' I' c + ∑ r, al r c • d r ∧ n' I c = n' I' c + ∑ r, al r c • e r) → ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ g)), ∀ I, ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k (σ I) c + ∑ r, al r c • d r ∧ n' I c = n (σ I) c + ∑ r, al r c • e r := by
  first | exact @GlobalTheory.exists_representatives_mod_similitude_transpose | exact GlobalTheory.exists_representatives_mod_similitude_transpose | (intros; apply GlobalTheory.exists_representatives_mod_similitude_transpose <;> assumption)
end
