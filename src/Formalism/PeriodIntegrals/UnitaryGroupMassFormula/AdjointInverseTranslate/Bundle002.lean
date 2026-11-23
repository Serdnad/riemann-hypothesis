module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL

theorem ofFn_prod_sum {A : Type*} [Ring A] {ι : Type*} [Fintype ι] :
    ∀ (t : ℕ) (F : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, F k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => F k (c k)).prod := by
  intro t
  induction t with
  | zero => intro F; simp
  | succ t ih =>
    intro F
    rw [List.ofFn_succ, List.prod_cons, ih (fun k => F k.succ), Finset.sum_mul_sum]
    first
    | (rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
       simp [List.ofFn_succ, Fin.consEquiv])
    | (rw [← (Equiv.piFinSucc t ι).symm.sum_comp, Fintype.sum_prod_type]
       simp [List.ofFn_succ, Equiv.piFinSucc])

theorem ofFn_prod_smul {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (t : ℕ) (w : Fin t → ℂ) (X : Fin t → A),
      (List.ofFn fun k => w k • X k).prod = (∏ k, w k) • (List.ofFn X).prod := by
  intro t
  induction t with
  | zero => intro w X; simp
  | succ t ih =>
    intro w X
    rw [List.ofFn_succ, List.prod_cons, ih (fun k => w k.succ) (fun k => X k.succ), Fin.prod_univ_succ,
      List.ofFn_succ, List.prod_cons]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring

theorem tm_conj {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (x : ℂ) (i j : Fin n) :
    Tm (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) x i j =
      ∑ p : Fin n × Fin n, (P p.1 i * Q j p.2) • Tm E x p.1 p.2 := by
  simp only [Tm]
  simp only [smul_add, Finset.sum_add_distrib, Fintype.sum_prod_type]
  congr 1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_smul]
  have hsum : ∑ c, P c i * Q j c = (Q * P) j i := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  rw [hsum, hQP, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

private theorem sum_perm_mul_sum_prod_smul_eq_sum_sum {A : Type*} [Ring A] [Algebra ℂ A] {t n : ℕ}
    (s : Equiv.Perm (Fin t) → A) (w1 : Fin n → Fin t → ℂ) (w2 : Fin t → Fin n → ℂ)
    (G : (Fin t → Fin n) → (Fin t → Fin n) → A) :
    ∑ σ : Equiv.Perm (Fin t), s σ * ∑ cd : Fin t → Fin n × Fin n,
        (∏ k, w1 (cd k).1 (σ k) * w2 k (cd k).2) • G (fun k => (cd k).1) (fun k => (cd k).2) =
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((∏ j, w1 (c j) j) * ∏ j, w2 j (d j)) •
        ∑ σ : Equiv.Perm (Fin t), s σ * G (fun k => c (σ k)) d := by
  have h1 : ∀ σ : Equiv.Perm (Fin t), ∑ cd : Fin t → Fin n × Fin n,
      (∏ k, w1 (cd k).1 (σ k) * w2 k (cd k).2) • G (fun k => (cd k).1) (fun k => (cd k).2) =
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((∏ j, w1 (c j) j) * ∏ j, w2 j (d j)) •
        G (fun k => c (σ k)) d := by
    intro σ
    rw [← (Equiv.arrowProdEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type]
    rw [← (Equiv.arrowCongr σ.symm (Equiv.refl (Fin n))).sum_comp]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.arrowCongr_apply, Equiv.symm_symm,
      Equiv.coe_refl, Equiv.coe_fn_symm_mk, Function.comp_apply, id]
    congr 1
    rw [Finset.prod_mul_distrib]
    congr 1
    exact Equiv.prod_comp σ (fun j => w1 (c j) j)
  simp only [h1, Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]

theorem q_expansion : QExpand := by
  unfold QExpand
  intro A _ _ n t E P Q a b u hQP
  simp only [qminor]
  simp only [tm_conj E P Q hQP, ofFn_prod_sum, ofFn_prod_smul]
  exact sum_perm_mul_sum_prod_smul_eq_sum_sum (fun σ => ((Equiv.Perm.sign σ : ℤ) : A)) (fun x j => P x (a j))
    (fun k y => Q (b k) y) (fun c1 d => (List.ofFn fun k => Tm E (u - ((k : ℕ) : ℂ)) (c1 k) (d k)).prod)

end AAInvW
end
end

section

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

def hkSig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩

def hkEps (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = hkSig k r i then hkEps k r i else 0 := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [Hpk, hkSig, hkEps, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hk_sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkSig k r (hkSig k r i) = i := by
  apply Fin.ext
  simp only [hkSig]
  split_ifs <;> omega

theorem hk_eps_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkEps k r (hkSig k r i) = hkEps k r i := by
  simp only [hkEps, hkSig]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hk_eps_mul_self (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkEps k r i * hkEps k r i = 1 := by
  unfold hkEps
  split_ifs <;> norm_num

theorem hk_star_eps (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (hkEps k r i) = hkEps k r i := by
  unfold hkEps
  split_ifs <;> simp

theorem hk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [hk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hk_sig_sig, hk_eps_sig]
  by_cases h : j = i
  · subst h; simp [hk_eps_mul_self]
  · simp [h, one_apply_ne' h]

theorem hk_conjTranspose (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hk_apply, hk_apply]
  by_cases h : j = hkSig k r i
  · subst h
    simp [hk_sig_sig, hk_eps_sig, hk_star_eps]
  · have h' : i ≠ hkSig k r j := fun e => h (by rw [e, hk_sig_sig])
    simp [h, h']

theorem hpk_involution : HpkInvol := fun k r => ⟨hk_conjTranspose k r, hk_mul_self k r⟩

end AAInvW
end
end

section

open Matrix

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem inUH_mul {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) :
    inUH H (a * b) := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem operators_commute_translations_of_left_right (hL : LeftAA) (hR : RightAA) (hS : SsetUH) : OperatorsCommuteTranslations := by
  unfold OperatorsCommuteTranslations
  intro E _ _ k r z z' m hm u ell f _ _ hf s hs s' hs' g hg
  have hsg : inUH (Hpk k r) (s * g) := inUH_mul (hS k r z s hs) hg
  obtain ⟨hL1, hL2⟩ := hL E k r z m hm u ell (fun x => f (x * s')) s g hs hg
  obtain ⟨hR1, hR2⟩ := hR E k r z' m hm u ell f s' (s * g) hf hs' hsg
  exact ⟨hL1.trans hR1, hL2.trans hR2⟩

end AAInvW
end
end

section

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

def OpModel : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), HInvol H →
    ∃ (M : Submodule ℂ ({x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E))
      (cls : (Matrix (Fin n) (Fin n) ℂ → E) → M) (Eh : Fin n → Fin n → Module.End ℂ M),
      GlRel Eh ∧
      (∀ (t : ℕ) (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
          (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUH H g),
        SmoothOnH H f → qminorOp (EabH H) a b u f g = ((qminor Eh a b u (cls f) : M) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨g, hg⟩) ∧
      ∀ s : Matrix (Fin n) (Fin n) ℂ, inUH H s → ∃ ρ : Module.End ℂ M,
        (∀ f : Matrix (Fin n) (Fin n) ℂ → E, SmoothOnH H f → cls (fun x => f (x * s)) = ρ (cls f)) ∧
        (∀ (ψ : M) (y : Matrix (Fin n) (Fin n) ℂ) (hy : inUH H y) (y' : Matrix (Fin n) (Fin n) ℂ)
            (hy' : inUH H y'), y' = y * s → ((ρ ψ : M) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨y, hy⟩ = (ψ : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨y', hy'⟩) ∧
        ∀ a b : Fin n, Eh a b * ρ = ρ * ∑ c, ∑ d, (s⁻¹ c a * s b d) • Eh c d

end AAInvW
end
end

section

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def inLH {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) : Prop := Xᴴ * H + H * X = 0

section Basic

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}

lemma ana_inv (hH : HInvol H) : H⁻¹ = H := Matrix.inv_eq_left_inv hH.2

lemma ana_isUnit (hH : HInvol H) : IsUnit H := IsUnit.of_mul_eq_one _ hH.2

lemma ana_HH_left (hH : HInvol H) (A : Matrix (Fin n) (Fin n) ℂ) : H * (H * A) = A := by
  rw [← Matrix.mul_assoc, hH.2, Matrix.one_mul]

lemma ana_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  unfold inUH at *
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha, hb]

lemma ana_exp (hH : HInvol H) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inLH H Y) :
    inUH H (NormedSpace.exp Y) := by
  have hY' : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
    rw [ana_inv hH, Matrix.mul_neg, ← hY', Matrix.mul_assoc, hH.2, Matrix.mul_one]
  have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ (ana_isUnit hH), ana_inv hH]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  unfold inUH
  rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH.2, Matrix.mul_one, Matrix.mul_assoc, hc,
    Matrix.mul_one]

lemma ana_rsmul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (r : ℝ) : inLH H ((r : ℂ) • X) := by
  unfold inLH at *
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

lemma ana_expt (hH : HInvol H) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (t : ℝ) :
    inUH H (NormedSpace.exp ((t : ℂ) • X)) := ana_exp hH (ana_rsmul hX t)

lemma ana_add {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) (hB : inLH H B) : inLH H (A + B) := by
  unfold inLH at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Aᴴ * H + Bᴴ * H + (H * A + H * B) = (Aᴴ * H + H * A) + (Bᴴ * H + H * B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]

lemma ana_neg {A : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) : inLH H (-A) := by
  unfold inLH at *
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hA, neg_zero]

lemma ana_sub {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) (hB : inLH H B) : inLH H (A - B) := by
  rw [sub_eq_add_neg]; exact ana_add hA (ana_neg hB)

lemma ana_bracket {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (hY : inLH H Y) :
    inLH H (X * Y - Y * X) := by
  unfold inLH at *
  have hX' : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * H = H * Y * X := by
    rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * H = H * X * Y := by
    rw [Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2,
    Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  abel

lemma ana_HXH {X : Matrix (Fin n) (Fin n) ℂ} (hH : HInvol H) (hX : inLH H X) : H * Xᴴ * H = -X := by
  have hX' : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ana_HH_left hH]

lemma ana_hpart1_eq (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H Z = (1 / 2 : ℂ) • (Z - H * Zᴴ * H) := by
  unfold hpart1; rw [ana_inv hH]

lemma ana_hpart2_eq (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H Z = (1 / (2 * Complex.I) : ℂ) • (Z + H * Zᴴ * H) := by
  unfold hpart2; rw [ana_inv hH]

lemma ana_thetaH (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) : (H * Zᴴ * H)ᴴ * H = H * Z := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.1, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, Matrix.mul_assoc, hH.2, Matrix.mul_one]

lemma ana_Htheta (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) : H * (H * Zᴴ * H) = Zᴴ * H := by
  rw [Matrix.mul_assoc, ana_HH_left hH]

lemma ana_hpartMem (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inLH H (hpart1 H Z) ∧ inLH H (hpart2 H Z) ∧ Z = hpart1 H Z + Complex.I • hpart2 H Z ∧
      (inLH H Z → hpart1 H Z = Z ∧ hpart2 H Z = 0) := by
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold inLH
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul,
      ana_thetaH hH, Matrix.mul_smul, Matrix.mul_sub, ana_Htheta hH, star_one_half, ← smul_add]
    simp
  · unfold inLH
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul,
      ana_thetaH hH, Matrix.mul_smul, Matrix.mul_add, ana_Htheta hH, star_one_div_two_I, neg_smul,
      add_comm (H * Z), neg_add_cancel]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
    norm_num
  · intro hX
    rw [ana_HXH hH hX, sub_neg_eq_add, add_neg_cancel, smul_zero, ← two_smul ℂ Z, smul_smul]
    norm_num

lemma ana_hpart_unique (hH : HInvol H) {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : inLH H P) (hQ : inLH H Q) :
    hpart1 H (P + Complex.I • Q) = P ∧ hpart2 H (P + Complex.I • Q) = Q := by
  have hZ : H * (P + Complex.I • Q)ᴴ * H = -P + Complex.I • Q := by
    rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, ana_HXH hH hP, ana_HXH hH hQ, Complex.star_def, Complex.conj_I]
    module
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH, hZ]
  constructor
  · module
  · have : P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q := by module
    rw [this, smul_smul, one_div, inv_mul_cancel₀ (by simp), one_smul]

lemma ana_hpart1_sub (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H (Z - W) = hpart1 H Z - hpart1 H W := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart1_eq hH, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

lemma ana_hpart2_sub (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (Z - W) = hpart2 H Z - hpart2 H W := by
  rw [ana_hpart2_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

lemma ana_hpart1_add (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H (Z + W) = hpart1 H Z + hpart1 H W := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart1_eq hH, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  module

lemma ana_hpart2_add (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (Z + W) = hpart2 H Z + hpart2 H W := by
  rw [ana_hpart2_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  module

lemma ana_inv2I : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
  rw [one_div, mul_inv, Complex.inv_I]; ring

lemma ana_hpart1_smul (hH : HInvol H) (x y : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H (((x : ℂ) + (y : ℂ) * Complex.I) • Z) = (x : ℂ) • hpart1 H Z - (y : ℂ) • hpart2 H Z := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart2_eq hH, ana_inv2I, conjTranspose_smul,
    Matrix.mul_smul, Matrix.smul_mul]
  have hs : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hs]
  match_scalars <;> first | ring1 | linear_combination ((y : ℂ) / 2) * Complex.I_sq | linear_combination (-(y : ℂ) / 2) * Complex.I_sq

lemma ana_hpart2_smul (hH : HInvol H) (x y : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (((x : ℂ) + (y : ℂ) * Complex.I) • Z) = (x : ℂ) • hpart2 H Z + (y : ℂ) • hpart1 H Z := by
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, ana_inv2I, conjTranspose_smul,
    Matrix.mul_smul, Matrix.smul_mul]
  have hs : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hs]
  match_scalars <;> first | ring1 | linear_combination ((y : ℂ) / 2) * Complex.I_sq | linear_combination (-(y : ℂ) / 2) * Complex.I_sq

end Basic

end AAInvW
end
end
