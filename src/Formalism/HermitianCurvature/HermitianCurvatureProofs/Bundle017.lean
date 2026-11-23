module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.AxiomsFromFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
public import Formalism.HermitianCurvature.StatementJ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakApproximationGL
public import Formalism.HermitianCurvature.StatementG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.Jx10

theorem pull {α X : Type} [DecidableEq X] (η : α → X) (F : Finset α) (k : X → X → ℂ)
    (h : A5.IsPSD (F.image η) k) : A5.IsPSD F (fun x y => k (η x) (η y)) := by
  apply Formalism.FourierDecayAlt.P.Jx9.pull <;> assumption

theorem inter_of_module (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E)
    (hL : ∀ (a : 𝓞 (maximalRealSubfield E)) (t : E), t ∈ L →
      algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L) (t : E)
    (h : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ S6.locAt E P L) : t ∈ L := by
  by_contra ht
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add (f := _), add_mul] at ha hb ⊢
        exact L.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, mul_assoc] at ha ⊢
        exact hL c _ ha }
  have hI : I ≠ ⊤ := by
    intro hI
    apply ht
    have h1 : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := by
      rw [hI]
      exact Submodule.mem_top
    have h2 : algebraMap (𝓞 (maximalRealSubfield E)) E 1 * t ∈ L := h1
    simpa using h2
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨a, haP, haL⟩ := h P hP
  exact haP (hIP haL)

end Formalism.FourierDecayAlt.P.Jx10

namespace Formalism.FourierDecayAlt.P


open Classical in
theorem local_kernel_psd : Formalism.FourierDecayAlt.J.LocalKernelPSD := by
  intro hag hgram K _ _ _ R ψ hLD α η Y
  rw [(hag α Y _).1, ← (hag α Y _).2]
  exact Jx10.pull η Y (A5.Kp R ψ) (hgram K R ψ hLD (Y.image η))

theorem intersection_of_local : Formalism.FourierDecayAlt.J.IntersectionOfLocal := by
  intro E _ _ _ L hL t
  obtain ⟨hL1, -⟩ := hL
  constructor
  · intro ht P hP
    unfold Formalism.FourierDecayAlt.S6.locAt
    rw [Set.mem_setOf_eq]
    refine ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1), ?_⟩
    rw [map_one, one_mul]
    exact ht
  · intro h
    exact Jx10.inter_of_module E L hL1 t h

theorem lattice_of_local : Formalism.FourierDecayAlt.J.LatticeOfLocal := by
  intro E _ _ _ L hL Q _ pl M hcov hM
  have hint := intersection_of_local E L hL
  ext t
  rw [AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, hint]
  constructor
  · intro h p
    rw [hM]
    intro P _ hP
    exact h P hP
  · intro h P hP
    obtain ⟨p, hp⟩ := hcov P hP
    exact (hM p t).mp (h p) P hp hP

theorem pull_lattice_typed : Formalism.FourierDecayAlt.J.PullLatticeTyped := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u α ψ η Θ hR hu t
  rw [hT E g ν s hg hpd P hP hgP K o σ hσ t]
  show (u : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t ∈ R ↔ _
  rw [hR, hu]
  have e : (((g : K)⁻¹, (-1) ^ s * (g : K)⁻¹) : K × K) *
      (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t =
      (σ t / (g : K), (-1) ^ s * σ (IsCMField.complexConj E t) / (g : K)) := by
    ext
    · simp [div_eq_mul_inv, mul_comm]
    · simp [div_eq_mul_inv]; ring
  rw [e]

end Formalism.FourierDecayAlt.P
end

section

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors

namespace Formalism.FourierDecayAlt.P.Jx1

theorem conv {α : Type} (F : Finset α) (k : α → α → ℂ) (h : TB.PSDOn F k) :
    TA.PSDOn F (fun x y => k y x) := by
  unfold TB.PSDOn at h
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h
  obtain ⟨hH, hN⟩ := h
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · have e := hH.apply ⟨y, hy⟩ ⟨x, hx⟩
    simp only [Matrix.of_apply] at e
    show k x y = conj (k y x)
    rw [← e]
    simp
  · have hb := (Complex.le_def.mp (hN (fun i => conj (a i)))).1
    simp only [Complex.zero_re] at hb
    refine le_of_le_of_eq hb ?_
    congr 1
    rw [Finset.sum_comm, ← Finset.sum_coe_sort F]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.star_def, Complex.conj_conj]
    ring

private theorem im_quadratic_form_eq_zero_of_hermitian {α : Type} (F : Finset α) (k : α → α → ℂ)
    (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y).im = 0 := by
  have h : conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by

    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    rw [← hh v hv u hu]
    ring
  exact Complex.conj_eq_iff_im.mp h

private theorem tb_psdOn_of_ta_psdOn {α : Type} (F : Finset α) (k : α → α → ℂ) (h : TA.PSDOn F k) :
    TB.PSDOn F k := by
  classical
  unfold TB.PSDOn
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply]
    rw [h.1 i i.2 j j.2]
    simp
  · set a : α → ℂ := fun u => if hu : u ∈ F then x ⟨u, hu⟩ else 0 with ha
    have hQ : star x ⬝ᵥ (Matrix.of fun u v : F => k u v).mulVec x =
        ∑ u ∈ F, ∑ v ∈ F, conj (a u) * k u v * a v := by
      rw [← Finset.sum_coe_sort F]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [ha, Complex.star_def, mul_assoc]
    rw [hQ, Complex.le_def]
    simp only [Complex.zero_re, Complex.zero_im]
    exact ⟨h.2 a, (im_quadratic_form_eq_zero_of_hermitian F k h.1 a).symm⟩

theorem t_PSDTranspose : PSDTranspose := by
  unfold PSDTranspose
  intro α F k h
  exact tb_psdOn_of_ta_psdOn F _ (conv F k h)

section Tower
variable {E : Type} [Field E]

end Tower

section Agree
variable {α : Type}

theorem q_im (F : Finset α) (k : α → α → ℂ) (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y).im = 0 := by
  have h : conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by

    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    rw [← hh v hv u hu]
    ring
  exact Complex.conj_eq_iff_im.mp h

theorem ta_to_tb (F : Finset α) (k : α → α → ℂ) (h : TA.PSDOn F k) : TB.PSDOn F k := by
  exact tb_psdOn_of_ta_psdOn F k h

theorem psd_form_conj_rewrite (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y) =
      ∑ x ∈ F, ∑ y ∈ F, conj ((fun z => conj (a z)) x) * k x y * (fun z => conj (a z)) y := by
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Complex.conj_conj]
  ring

theorem psd_kernel_hermitian (F : Finset α) (k : α → α → ℂ) (h : A5.IsPSD F k) :
    ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y) := by
  classical
  intro x hx y hy
  set B : (α → ℂ) → (α → ℂ) → ℂ := fun a b => ∑ u ∈ F, ∑ v ∈ F, a u * conj (b v) * k u v with hB
  have hS : ∀ a, (B a a).im = 0 := fun a => (h a).1
  have hexp : ∀ a b, B (a + b) (a + b) = B a a + B b b + (B a b + B b a) := by
    intro a b
    simp only [hB, Pi.add_apply, map_add (f := _), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hpol : ∀ a b, (B a b + B b a).im = 0 := by
    intro a b
    have h0 := hS (a + b)
    rw [hexp, Complex.add_im, Complex.add_im, hS a, hS b] at h0
    simpa using h0
  have hsc1 : ∀ (c : ℂ) a b, B (c • a) b = c * B a b := by
    intro c a b
    simp only [hB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hsc2 : ∀ (c : ℂ) a b, B a (c • b) = conj c * B a b := by
    intro c a b
    simp only [hB, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hBe : ∀ p q, p ∈ F → q ∈ F →
      B (fun u => if u = p then 1 else 0) (fun u => if u = q then 1 else 0) = k p q := by
    intro p q hp hq
    simp [hB, apply_ite (starRingEnd ℂ), ite_mul, hp, hq]
  have h1 := hpol (fun u => if u = x then 1 else 0) (fun u => if u = y then 1 else 0)
  have h2 := hpol (fun u => if u = x then 1 else 0) (Complex.I • fun u => if u = y then 1 else 0)
  rw [hsc2, hsc1] at h2
  rw [hBe x y hx hy, hBe y x hy hx] at h1 h2
  apply Complex.ext <;> simp [Complex.mul_im] at h1 h2 ⊢ <;> linarith

theorem t_PSDAgree : PSDAgree := by
  unfold PSDAgree
  intro α F k
  refine ⟨⟨fun h => conv F _ (t_PSDTranspose α F k h), ta_to_tb F k⟩, ⟨fun h => ⟨psd_kernel_hermitian F k h, fun a => ?_⟩, fun h => ?_⟩⟩
  · have h2 := (h (fun z => conj (a z))).2
    refine le_of_le_of_eq h2 ?_
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [Complex.conj_conj]
    ring
  · intro a
    rw [psd_form_conj_rewrite F k a]
    exact ⟨q_im F k h.1 _, h.2 _⟩

end Agree

theorem t_BoxSumLattice : BoxSumLattice := by
  apply Formalism.FourierDecayAlt.P.Jx2.t_BoxSumLattice <;> assumption

end Formalism.FourierDecayAlt.P.Jx1

namespace Formalism.FourierDecayAlt.P

theorem psd_agree : Formalism.FourierDecayAlt.J.PSDAgree := Jx1.t_PSDAgree

theorem box_sum_lattice : Formalism.FourierDecayAlt.J.BoxSumLattice := Jx1.t_BoxSumLattice

end Formalism.FourierDecayAlt.P
end

section

open Matrix MeasureTheory

namespace Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic

open Formalism.FourierDecayAlt.G

private lemma wMat_mul_apply_eq_rev {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (r c : Fin m) :
    (wMat m * M) r c = M r.rev c := by
  simp [wMat, Matrix.mul_apply]

private lemma wMat_mulVec_apply_eq_rev {m : ℕ} (v : Fin m → ℂ) (r : Fin m) : (wMat m *ᵥ v) r = v r.rev := by
  simp [wMat, Matrix.mulVec, dotProduct]

private lemma finSumFinEquiv_symm_castSucc_eq_inl {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (Fin.castSucc i : Fin (n + 1)) = (Sum.inl i : Fin n ⊕ Fin 1) := by
  rw [Equiv.symm_apply_eq]; rfl

private lemma finSumFinEquiv_symm_last_eq_inr (n : ℕ) : finSumFinEquiv.symm (Fin.last n) = (Sum.inr 0 : Fin n ⊕ Fin 1) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem wM_succ_last {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) i.succ (Fin.last n) = B i := by
  rw [wMat_mul_apply_eq_rev]
  first
    | simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]
    | simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

theorem wM_succ_cast {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i j : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) i.succ j.castSucc = t * (1 : Matrix (Fin n) (Fin n) ℂ) i j + X i j := by
  rw [wMat_mul_apply_eq_rev]
  first
    | simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]
    | simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

theorem wM_zero_cast {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (j : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) 0 j.castSucc = ρ j := by
  rw [wMat_mul_apply_eq_rev]
  first
    | simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]
    | simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

theorem wM_zero_last {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    (wMat (n + 1) * Mcoord t X B ρ σ) 0 (Fin.last n) = σ := by
  rw [wMat_mul_apply_eq_rev]
  first
    | simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]
    | simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

theorem diagonal_cons_succ {n : ℕ} (a b : ℂ) (x : Fin n → ℂ) (i : Fin n) (j : Fin (n + 1)) :
    Matrix.diagonal (Fin.cons a x : Fin (n + 1) → ℂ) i.succ j =
      Matrix.diagonal (Fin.cons b x : Fin (n + 1) → ℂ) i.succ j := by
  simp only [Matrix.diagonal_apply, Fin.cons_succ]

theorem xOf_redOf (m : ℕ) (p : XY m) (k : Fin (m + 1)) :
    xOf (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 k = p.1 k := by
  refine Fin.lastCases ?_ (fun k => ?_) k
  · rw [G6.xOf_last]
    simp [redOf, triXY, strictUpper, Fin.succ_last]
  · rw [G6.xOf_castSucc]
    have h : k.castSucc < k.succ := Fin.castSucc_lt_succ
    simp [redOf, triXY, strictUpper, h]

theorem wM_redOf (m : ℕ) (t ρ₁ : ℂ) (p : XY m) :
    wMat (m + 2) * Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
        (Fin.cons ρ₁ (redOf m p).2.1) (redOf m p).1 =
      t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ p.1 : Fin (m + 2) → ℂ) + strictUpper p.2 := by
  apply Formalism.FourierDecayAlt.P.WeakApproximationGL.matrix_redOf <;> assumption

end Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic

theorem cofactor_lower_bound_radius : Formalism.FourierDecayAlt.G.CofLowerR := by
  intro m Kc hK h0 R hR
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0
  have hD : ∀ D ∈ Kc, d ≤ ‖D‖ := by
    intro D hDK
    by_contra hlt
    exact hball (by simpa [Metric.mem_ball] using not_le.mp hlt) hDK
  set R' : ℝ := max 1 R with hR'
  have hR1 : 1 ≤ R' := le_max_left _ _
  have hRR : R ≤ R' := le_max_right _ _
  have hR0 : 0 < R' := lt_of_lt_of_le one_pos hR1
  set Cm : ℝ := ((m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) ^ m) with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set q : ℝ := d / (2 * (Cm + 1) * R' ^ (m + 2)) with hq
  have hq0 : 0 < q := by positivity
  refine ⟨min 1 (q ^ 2), d / (2 * R'), by positivity, by positivity, ?_⟩
  intro ε hε hε2 D hDK t ht htle X B ρ₁ ρ' σ hS hX hB hρ₁ hρ' hσ hrel
  have hT : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hT1 : ‖t‖ ≤ 1 := le_trans htle (min_le_left _ _)
  have hTq : ‖t‖ ≤ q ^ 2 := le_trans htle (min_le_right _ _)
  set L₀ : ℝ := ‖t‖ ^ (-ε) with hL₀def
  have hL₀ : 1 ≤ L₀ := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hT hT1 (by linarith)
  have hL₀0 : 0 < L₀ := lt_of_lt_of_le one_pos hL₀
  set L : ℝ := R' * L₀ with hLdef
  have hL : 1 ≤ L := by nlinarith
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hRL : R * L₀ ≤ L := mul_le_mul_of_nonneg_right hRR hL₀0.le
  have hsq : L ^ (m + 2) * ‖t‖ ≤ R' ^ (m + 2) * q := by
    rw [hLdef, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (le_trans (G6.rpow_bound m hT hT1 hε2) (Real.sqrt_le_iff.mpr ⟨hq0.le, hTq⟩)) (by positivity)
  have hRb := G6.remainder_norm_le_strict_upper (t := t) hL hT1 hS (fun i j => (hX i j).trans hRL) (fun i => (hB i).trans hRL)
    (fun k => (hρ' k).trans hRL)
  have h1 : ‖t ^ (m + 1) * σ‖ ≤ L ^ (m + 2) * ‖t‖ := by
    rw [norm_mul, norm_pow, mul_comm]
    refine mul_le_mul (le_trans (hσ.trans hRL) (le_self_pow₀ hL (by omega)))
      (pow_le_of_le_one hT.le hT1 (by omega)) (by positivity) (by positivity)
  have h2 : ‖Cof X B t * ρ₁‖ ≤ ‖Cof X B t‖ * L := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hρ₁.trans hRL) (norm_nonneg _)
  have hDeq : D = t ^ (m + 1) * σ - Cof X B t * ρ₁ - R0 X B ρ' t := by
    rw [hrel]; ring
  have h3 : ‖D‖ ≤ L ^ (m + 2) * ‖t‖ + ‖Cof X B t‖ * L + Cm * (L ^ (m + 2) * ‖t‖) := by
    calc ‖D‖ = ‖t ^ (m + 1) * σ - Cof X B t * ρ₁ - R0 X B ρ' t‖ := by rw [← hDeq]
      _ ≤ ‖t ^ (m + 1) * σ‖ + ‖Cof X B t * ρ₁‖ + ‖R0 X B ρ' t‖ :=
          le_trans (norm_sub_le _ _) (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ _ := add_le_add (add_le_add h1 h2) hRb
  have h4 : (Cm + 1) * (L ^ (m + 2) * ‖t‖) ≤ d / 2 := by
    calc (Cm + 1) * (L ^ (m + 2) * ‖t‖) ≤ (Cm + 1) * (R' ^ (m + 2) * q) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = d / 2 := by rw [hq]; field_simp
  have h5 : d / 2 ≤ ‖Cof X B t‖ * L := by
    have := hD D hDK
    nlinarith
  have hinv : ‖t‖ ^ ε = L₀⁻¹ := by
    rw [hL₀def, Real.rpow_neg hT.le, inv_inv]
  have e : d / (2 * R') * L₀⁻¹ = d / 2 / L := by
    rw [hLdef]; field_simp
  rw [hinv, e, div_le_iff₀ hL0]
  exact h5

theorem amplitude_eq : Formalism.FourierDecayAlt.G.AmpEq := by
  intro m β D t ht V _ _ Φ p
  have hx := xOf_redOf m p
  unfold amp redIntegrand
  rw [smul_smul, ← mul_assoc, ← (additive_character_psi β _ _).1]
  congr 3
  unfold gRem g0 rhoXY
  simp only [hx]
  field_simp
  ring

theorem limit_coordinates_xy : Formalism.FourierDecayAlt.G.LimitCoordsXY := by
  intro m z y
  rw [wM_redOf m 0 z (fun _ => z, y)]
  congr 1
  rw [zero_smul, zero_add]
  ext i j
  by_cases h : i = j
  · subst h
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp [Matrix.diagonal, Matrix.smul_apply]
  · simp [Matrix.diagonal, h, Matrix.smul_apply]

end Formalism.FourierDecayAlt.P
end
