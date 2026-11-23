module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstAdapt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem adapted_basis_instance : InstAdaptBasis := by
  intro n ε ι _ _ B hG
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJs : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  set J := Formalism.REAL.Jm ε with hJdef
  set G := Bᴴ * J * B with hGdef
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have hGi : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have hGh : Gᴴ = G := by
    rw [hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hJs, Matrix.mul_assoc]
  have hGih : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  set Q := B * G⁻¹ * Bᴴ * J with hQdef
  have hQB : Q * B = B := by
    calc Q * B = B * (G⁻¹ * (Bᴴ * J * B)) := by simp only [hQdef, Matrix.mul_assoc]
      _ = B := by rw [← hGdef, hGi, Matrix.mul_one]
  have hQQ : Q * Q = Q := by
    calc Q * Q = (Q * B) * (G⁻¹ * Bᴴ * J) := by simp only [hQdef, Matrix.mul_assoc]
      _ = Q := by rw [hQB]; simp only [hQdef, Matrix.mul_assoc]
  have hQJ : Qᴴ * J = J * Q := by
    simp only [hQdef, Matrix.conjTranspose_mul, hJs, hGih, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  set P := 1 - Q with hPdef
  have hPP : P * P = P := by
    simp only [hPdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQQ]
    abel
  have hPJ : Pᴴ * J = J * P := by
    rw [hPdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, hQJ,
      Matrix.one_mul, Matrix.mul_one]
  have hQP : Q * P = 0 := by rw [hPdef, Matrix.mul_sub, Matrix.mul_one, hQQ, sub_self]
  have hPQ : P * Q = 0 := by rw [hPdef, Matrix.sub_mul, Matrix.one_mul, hQQ, sub_self]
  obtain ⟨W1, l1, hW1J, hQW1, hsp1, hcard1, -⟩ := inst_qfamily ε Q hQQ hQJ
  obtain ⟨W2, l2, hW2J, hPW2, -, hcard2, -⟩ := inst_qfamily ε P hPP hPJ
  have hcross : W1ᴴ * J * W2 = 0 := by
    calc W1ᴴ * J * W2 = (Q * W1)ᴴ * J * (P * W2) := by rw [hQW1, hPW2]
      _ = W1ᴴ * (Qᴴ * J) * P * W2 := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
        rw [hQJ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Q P, hQP]
        simp
  have hcross' : W2ᴴ * J * W1 = 0 := by
    calc W2ᴴ * J * W1 = (P * W2)ᴴ * J * (Q * W1) := by rw [hQW1, hPW2]
      _ = W2ᴴ * (Pᴴ * J) * Q * W1 := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
        rw [hPJ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P Q, hPQ]
        simp
  have hrk : Q.rank + P.rank = n := by
    apply le_antisymm
    · have h1 : LinearMap.range P.mulVecLin ≤ LinearMap.ker Q.mulVecLin := by
        rintro _ ⟨x, rfl⟩
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
          hQP, Matrix.zero_mulVec]
      have h2 := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
      have h3 := Submodule.finrank_mono h1
      have h4 : Module.finrank ℂ (Fin n → ℂ) = n := by
        first
          | exact Module.finrank_fin_fun ℂ
          | simp
      simp only [← Matrix.finrank_range_mulVecLin]
      omega
    · have h := inst_rank_add_le Q P
      have hsum : Q + P = 1 := by rw [hPdef]; abel
      rw [hsum, Matrix.rank_one, Fintype.card_fin] at h
      exact h
  have hcardsum : Fintype.card ({i // l1 i ≠ 0} ⊕ {i // l2 i ≠ 0}) = n := by
    refine Eq.trans ?_ hrk
    rw [Fintype.card_sum]
    convert congrArg₂ (· + ·) hcard1 hcard2 using 2
  obtain ⟨e⟩ : Nonempty (Fin n ≃ ({i // l1 i ≠ 0} ⊕ {i // l2 i ≠ 0})) :=
    ⟨(Fintype.equivFinOfCardEq hcardsum).symm⟩
  obtain ⟨A, hAe⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ, ∀ r k, A r k =
      Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) (e k) :=
    ⟨Matrix.of fun r k =>
      Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) (e k),
      fun _ _ => rfl⟩
  obtain ⟨ε', hε'⟩ : ∃ ε' : Fin n → Bool, ∀ k, ε' k =
      Sum.elim (fun j : {i // l1 i ≠ 0} => decide (0 < l1 j))
        (fun j : {i // l2 i ≠ 0} => decide (0 < l2 j)) (e k) :=
    ⟨fun k => Sum.elim (fun j : {i // l1 i ≠ 0} => decide (0 < l1 j))
        (fun j : {i // l2 i ≠ 0} => decide (0 < l2 j)) (e k), fun _ => rfl⟩
  have hcol : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n), M *ᵥ Pi.single k 1 = fun r => M r k := by
    intro M k
    funext r
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨A, ε', Finset.univ.filter (fun k => (e k).isLeft = true), ?_, ?_, ?_⟩
  · ext k k'
    rw [inst_gram_entry]
    simp only [Formalism.REAL.Jm, Matrix.diagonal_apply, hAe, hε']
    rcases hk : e k with j | j <;> rcases hk' : e k' with j' | j' <;>
      simp only [Sum.elim_inl, Sum.elim_inr]
    · rw [← inst_gram_entry W1 J W1 (j : Fin n) j', hW1J, Matrix.diagonal_apply]
      have hkk : k = k' ↔ (j : Fin n) = j' := by
        rw [← e.apply_eq_iff_eq, hk, hk', Sum.inl.injEq, Subtype.ext_iff]
      by_cases h : (j : Fin n) = j'
      · rw [if_pos h, if_pos (hkk.mpr h), if_neg j.2]
        by_cases hp : 0 < l1 j <;> simp [hp]
      · rw [if_neg h, if_neg (fun h' => h (hkk.mp h'))]
    · rw [← inst_gram_entry W1 J W2 (j : Fin n) j', hcross, Matrix.zero_apply, if_neg]
      intro h
      subst h
      rw [hk] at hk'
      exact Sum.inl_ne_inr hk'
    · rw [← inst_gram_entry W2 J W1 (j : Fin n) j', hcross', Matrix.zero_apply, if_neg]
      intro h
      subst h
      rw [hk] at hk'
      exact Sum.inr_ne_inl hk'
    · rw [← inst_gram_entry W2 J W2 (j : Fin n) j', hW2J, Matrix.diagonal_apply]
      have hkk : k = k' ↔ (j : Fin n) = j' := by
        rw [← e.apply_eq_iff_eq, hk, hk', Sum.inr.injEq, Subtype.ext_iff]
      by_cases h : (j : Fin n) = j'
      · rw [if_pos h, if_pos (hkk.mpr h), if_neg j.2]
        by_cases hp : 0 < l2 j <;> simp [hp]
      · rw [if_neg h, if_neg (fun h' => h (hkk.mp h'))]
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hk : e i with j | j
    · refine ⟨G⁻¹ *ᵥ (Bᴴ *ᵥ (J *ᵥ (W1 *ᵥ Pi.single (j : Fin n) 1))), ?_⟩
      have h1 : A *ᵥ Pi.single i 1 = W1 *ᵥ Pi.single (j : Fin n) 1 := by
        rw [hcol, hcol]
        funext r
        show A r i = W1 r (j : Fin n)
        rw [hAe, hk, Sum.elim_inl]
      rw [h1]
      calc W1 *ᵥ Pi.single (j : Fin n) 1 = (Q * W1) *ᵥ Pi.single (j : Fin n) 1 := by rw [hQW1]
        _ = _ := by simp only [hQdef, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · rw [hk] at hi
      simp at hi
  · intro j
    have hb : Q *ᵥ (B *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by rw [Matrix.mulVec_mulVec, hQB]
    obtain ⟨y, hy0, hy⟩ := hsp1 _ hb
    refine ⟨fun k => Sum.elim (fun j' : {i // l1 i ≠ 0} => y j') (fun _ => (0 : ℂ)) (e k), ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases he : e k with j' | j'
      · rw [he] at hk
        simp at hk
      · simp only [he, Sum.elim_inr]
    · rw [hy]
      funext r
      simp only [Matrix.mulVec, dotProduct, hAe]
      symm
      rw [Fintype.sum_equiv e _ (fun x => Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j)
        (fun j : {i // l2 i ≠ 0} => W2 r j) x *
          Sum.elim (fun j' : {i // l1 i ≠ 0} => y j') (fun _ => (0 : ℂ)) x) (fun k => rfl)]
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i => l1 i ≠ 0) (fun i => W1 r i * y i)]
      have h0 : ∑ i : {i // ¬ l1 i ≠ 0}, W1 r i * y i = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hy0 i (not_not.mp i.2), mul_zero]
      rw [h0, add_zero]

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

section

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Real

variable {n r : ℕ} (ε : Fin n → Bool)

def RFrame (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Prop :=
  (∀ a b, hJ ε (e a) (e b) = 0) ∧ (∀ a b, hJ ε (f a) (f b) = 0) ∧
  (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) ∧ hJ ε z z ≠ 0

theorem rFrame_of {I : Formalism.MainNotions.S.AutInst} {r : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E}
    (hF : IsFrame I e f z) (v : NumberField.InfinitePlace I.F) :
    RFrame (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a)) (rv I v z) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [rv_hJ, h1, map_zero]
  · rw [rv_hJ, h2, map_zero]
  · rw [rv_hJ, h3]; split_ifs <;> simp
  · rw [rv_hJ, (h4 a).1, map_zero]
  · rw [rv_hJ, (h4 a).2, map_zero]
  · rw [rv_hJ]
    exact fun h => h5 ((map_eq_zero_iff _ (I.φ v).injective).mp h)

def hJL (u : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun := hJ ε u
  map_add' x y := by simp [hJ, Matrix.mulVec_add, dotProduct_add]
  map_smul' c x := by simp [hJ, Matrix.mulVec_smul, dotProduct_smul]

theorem hJL_apply (u x : Fin n → ℂ) : hJL ε u x = hJ ε u x := rfl

def piW (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.id - ∑ a, (hJL ε (f a)).smulRight (e a) - ∑ a, (hJL ε (e a)).smulRight (f a) -
    ((hJ ε z z)⁻¹ • hJL ε z).smulRight z

theorem piW_apply (e f : Fin r → Fin n → ℂ) (z x : Fin n → ℂ) :
    piW ε e f z x = x - ∑ a, hJ ε (f a) x • e a - ∑ a, hJ ε (e a) x • f a -
      ((hJ ε z z)⁻¹ * hJ ε z x) • z := by
  simp [piW, hJL_apply, smul_eq_mul, mul_comm]

variable {ε}

theorem hJ_sub_right (u x y : Fin n → ℂ) : hJ ε u (x - y) = hJ ε u x - hJ ε u y := by
  simp [hJ, Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_sum_right {ι : Type*} (s : Finset ι) (u : Fin n → ℂ) (g : ι → Fin n → ℂ) :
    hJ ε u (∑ i ∈ s, g i) = ∑ i ∈ s, hJ ε u (g i) := by
  exact map_sum (hJL ε u) g s

theorem hJ_smul_right (u x : Fin n → ℂ) (c : ℂ) : hJ ε u (c • x) = c * hJ ε u x := by
  simp [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

variable {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}

theorem hJ_e_piW (hF : RFrame ε e f z) (b : Fin r) (x : Fin n → ℂ) : hJ ε (e b) (piW ε e f z x) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  rw [piW_apply]
  simp only [hJ_sub_right, hJ_sum_right, hJ_smul_right, hee, hef, (hz b).1]
  simp

private theorem hJ_conj_lemma (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  unfold hJ
  simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

theorem hJ_f_piW (hF : RFrame ε e f z) (b : Fin r) (x : Fin n → ℂ) : hJ ε (f b) (piW ε e f z x) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  have h1 : ∀ a, hJ ε (f b) (e a) = if a = b then 1 else 0 := fun a => by
    rw [hJ_conj_lemma, hef a b]
    by_cases h : a = b
    · subst h; simp
    · simp [h]
  rw [piW_apply]
  simp only [hJ_sub_right, hJ_sum_right, hJ_smul_right, hff, h1, (hz b).2]
  simp

theorem hJ_z_piW (hF : RFrame ε e f z) (x : Fin n → ℂ) : hJ ε z (piW ε e f z x) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  have h1 : ∀ a, hJ ε z (e a) = 0 := fun a => by rw [hJ_conj_lemma, (hz a).1, star_zero]
  have h2 : ∀ a, hJ ε z (f a) = 0 := fun a => by rw [hJ_conj_lemma, (hz a).2, star_zero]
  rw [piW_apply]
  simp only [hJ_sub_right, hJ_sum_right, hJ_smul_right, h1, h2, mul_zero, Finset.sum_const_zero, sub_zero]
  field_simp
  ring

theorem piW_of_perp {y : Fin n → ℂ} (he : ∀ a, hJ ε (e a) y = 0) (hf : ∀ a, hJ ε (f a) y = 0)
    (hz : hJ ε z y = 0) : piW ε e f z y = y := by
  rw [piW_apply]
  simp [he, hf, hz]

theorem piW_e (hF : RFrame ε e f z) (b : Fin r) : piW ε e f z (e b) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  have h1 : ∀ a, hJ ε (f a) (e b) = if a = b then 1 else 0 := fun a => by
    rw [hJ_conj_lemma, hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have h2 : hJ ε z (e b) = 0 := by rw [hJ_conj_lemma, (hz b).1, star_zero]
  rw [piW_apply]
  simp [h1, hee, h2]

theorem piW_spanLt (hF : RFrame ε e f z) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) :
    piW ε e f z x = 0 := by
  have hle : spanLt e a ≤ LinearMap.ker (piW ε e f z) := by
    rw [spanLt, Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    exact LinearMap.mem_ker.mpr (piW_e hF b)
  exact LinearMap.mem_ker.mp (hle hx)

theorem fix_sub_piW {h : Matrix (Fin n) (Fin n) ℂ} (he : ∀ a, h *ᵥ e a = e a)
    (hf : ∀ a, h *ᵥ f a = f a) (hz : h *ᵥ z = z) (x : Fin n → ℂ) :
    h *ᵥ (x - piW ε e f z x) = x - piW ε e f z x := by
  have hx : x - piW ε e f z x = ∑ a, hJ ε (f a) x • e a + ∑ a, hJ ε (e a) x • f a +
      ((hJ ε z z)⁻¹ * hJ ε z x) • z := by
    rw [piW_apply]; abel
  rw [hx]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, he, hf, hz]

def PwM (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (piW ε e f z)

def hPart (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 - PwM ε e f z + PwM ε e f z * g * PwM ε e f z

theorem continuous_hPart (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    Continuous (hPart ε e f z) := by
  unfold hPart
  fun_prop

theorem hPart_mulVec (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    hPart ε e f z g *ᵥ x = x - piW ε e f z x + piW ε e f z (g *ᵥ piW ε e f z x) := by
  have hP : ∀ y, PwM ε e f z *ᵥ y = piW ε e f z y := fun y => by
    rw [PwM, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  simp only [hPart, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hP]

private theorem hJ_mulVec_of_inUJ' {h : Matrix (Fin n) (Fin n) ℂ} (hU : Formalism.REAL.inUJ ε h) (u v : Fin n → ℂ) :
    hJ ε (h *ᵥ u) (h *ᵥ v) = hJ ε u v := by
  unfold Formalism.REAL.inUJ at hU
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]

theorem hPart_mul (hF : RFrame ε e f z) {nm h : Matrix (Fin n) (Fin n) ℂ} (hn : InN ε e z nm)
    (hU : Formalism.REAL.inUJ ε h) (he : ∀ a, h *ᵥ e a = e a) (hf : ∀ a, h *ᵥ f a = f a) (hz : h *ᵥ z = z) :
    hPart ε e f z (nm * h) = h := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hPart_mulVec]
  have hey : ∀ a, hJ ε (e a) (h *ᵥ piW ε e f z x) = 0 := fun a => by
    have := hJ_mulVec_of_inUJ' hU (e a) (piW ε e f z x)
    rw [he a] at this
    rw [this]; exact hJ_e_piW hF a x
  have hfy : ∀ a, hJ ε (f a) (h *ᵥ piW ε e f z x) = 0 := fun a => by
    have := hJ_mulVec_of_inUJ' hU (f a) (piW ε e f z x)
    rw [hf a] at this
    rw [this]; exact hJ_f_piW hF a x
  have hzy : hJ ε z (h *ᵥ piW ε e f z x) = 0 := by
    have := hJ_mulVec_of_inUJ' hU z (piW ε e f z x)
    rw [hz] at this
    rw [this]; exact hJ_z_piW hF x
  have h0 : piW ε e f z ((nm - 1) *ᵥ (h *ᵥ piW ε e f z x)) = 0 :=
    piW_spanLt hF r (hn.2 _ hey)
  have hpy : piW ε e f z (h *ᵥ piW ε e f z x) = h *ᵥ piW ε e f z x := piW_of_perp hey hfy hzy
  have hsplit : (nm * h) *ᵥ piW ε e f z x =
      h *ᵥ piW ε e f z x + (nm - 1) *ᵥ (h *ᵥ piW ε e f z x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hx : h *ᵥ x = (x - piW ε e f z x) + h *ᵥ piW ε e f z x := by
    rw [← fix_sub_piW he hf hz x, ← Matrix.mulVec_add, sub_add_cancel]
  rw [hsplit, map_add (f := _), hpy, h0, add_zero, hx]

end Real

end PI.ScMuExists.UnitaryGroupMassFormula
end
end
