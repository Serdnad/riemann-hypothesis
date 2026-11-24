module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.LineTransport
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
public import Mathlib.CategoryTheory.Category.Basic
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.TypeStar
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Blocks

variable {n : Type*} [Fintype n]

def sliceL (a : Fin 4) : (Fin 4 × n → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun := slice a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem slice_analyticAt (a : Fin 4) (z : Fin 4 × n → ℂ) :
    AnalyticAt ℂ (slice a : (Fin 4 × n → ℂ) → n → ℂ) z :=
  (LinearMap.toContinuousLinearMap (sliceL (n := n) a)).analyticAt z

def mk4 (u : Fin 4 → n → ℂ) : Fin 4 × n → ℂ := fun p => u p.1 p.2

theorem blockSlice_fourfoldMk (u : Fin 4 → n → ℂ) (a : Fin 4) : slice a (mk4 u) = u a := rfl

theorem slice_add (a : Fin 4) (z w : Fin 4 × n → ℂ) : slice a (z + w) = slice a z + slice a w := rfl

def emb0 : (n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun v := fun p => if p.1 = 0 then v p.2 else 0
  map_add' u v := by
    funext p
    by_cases hp : p.1 = 0 <;> simp [hp]
  map_smul' c v := by
    funext p
    by_cases hp : p.1 = 0 <;> simp [hp]

theorem blockSlice_firstBlockEmb (a : Fin 4) (v : n → ℂ) : slice a (emb0 v) = if a = 0 then v else 0 := by
  funext i
  by_cases ha : a = 0 <;> simp [slice, emb0, ha]

theorem firstBlockEmb_mem_fourfoldLattice (Λ : AddSubgroup (n → ℂ)) {x : n → ℂ} (hx : x ∈ Λ) : emb0 x ∈ pow4 Λ := by
  intro a
  rw [blockSlice_firstBlockEmb]
  split_ifs
  · exact hx
  · exact Λ.zero_mem

theorem prod_blockSlice_firstBlockEmb (α : (n → ℂ) → ℂ) (hα0 : α 0 = 1) (x : n → ℂ) :
    ∏ a, α (slice a (emb0 x)) = α x := by
  rw [Finset.prod_eq_single (0 : Fin 4)]
  · rw [blockSlice_firstBlockEmb, if_pos rfl]
  · intro a _ ha
    rw [blockSlice_firstBlockEmb, if_neg ha, hα0]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem matrixForm_fourfoldBlock_firstBlockEmb (h : Matrix n n ℂ) (z : Fin 4 × n → ℂ) (x : n → ℂ) :
    matH (blk4 h) z (emb0 x) = matH h (slice 0 z) x := by
  rw [matrixForm_fourfoldBlock, Finset.sum_eq_single (0 : Fin 4)]
  · rw [blockSlice_firstBlockEmb, if_pos rfl]
  · intro a _ ha
    rw [blockSlice_firstBlockEmb, if_neg ha, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fourfoldTensor_smul (c : ℂ) (θ : (n → ℂ) → ℂ) : tens4 (c • θ) = c ^ 4 • tens4 θ := by
  funext z
  simp only [tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem restrict_mem (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (hα0 : α 0 = 1)
    {P : (Fin 4 × n → ℂ) → ℂ}
    (hP : P ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ))
    (z₁ : Fin 4 × n → ℂ) (hz₁ : slice 0 z₁ = 0) :
    (fun v => P (z₁ + emb0 v)) ∈ Th (matH h) α Λ := by
  refine ⟨?_, ?_⟩
  · intro v _
    exact (hP.1 (z₁ + emb0 v) (Set.mem_univ _)).comp_of_eq
      (analyticAt_const.add ((LinearMap.toContinuousLinearMap (emb0 (n := n))).analyticAt v)) rfl
  · intro x hx v
    have h1 := hP.2 (emb0 x) (firstBlockEmb_mem_fourfoldLattice Λ hx) (z₁ + emb0 v)
    simp only [opU, prod_blockSlice_firstBlockEmb α hα0, matrixForm_fourfoldBlock_firstBlockEmb, slice_add, hz₁, zero_add] at h1 ⊢
    rw [blockSlice_firstBlockEmb, if_pos rfl, blockSlice_firstBlockEmb, if_pos rfl, add_assoc, ← map_add (f := _)] at h1
    exact h1

end Blocks

theorem fourfoldTensorMem : Tens4Mem := by
  apply _root_.GlobalTheory.Mem.Col2.ThetaVec.tens4Mem <;> assumption

theorem FourthRoot_of (h4 : Tens4Mem) : FourthRoot := by
  apply _root_.GlobalTheory.Mem.Col2.ThetaVec.fourthRoot <;> assumption

theorem fourth_root : FourthRoot := FourthRoot_of fourfoldTensorMem

theorem exp_pi_I_int (m : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (m : ℂ)) = 1 ∨
      Complex.exp ((Real.pi : ℂ) * Complex.I * (m : ℂ)) = -1 := by
  rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
  · left
    have : (Real.pi : ℂ) * Complex.I * ((2 * j : ℤ) : ℂ) = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  · right
    have : (Real.pi : ℂ) * Complex.I * ((2 * j + 1 : ℤ) : ℂ)
        = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

theorem quadMultiplierSemicharacter : AlphaQSemi := by
  intro V _ _ H hH b d hb Λ hdual hstab
  have key : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k e : ℤ, altE H x y = (e : ℝ) ∧
      Real.sqrt d * (H x y).re = 2 * (k : ℝ) - (b : ℝ) * (e : ℝ) := by
    intro x hx y hy
    obtain ⟨e, he⟩ := hdual hx y hy
    obtain ⟨k, hk⟩ := hdual (hstab x hx) y hy
    refine ⟨k, e, he, ?_⟩
    have hθ : Formalism.L2.Th1.F.cmTheta b d = ⟨(b : ℝ) / 2, Real.sqrt d / 2⟩ := by
      apply Complex.ext <;> simp [Formalism.L2.Th1.F.cmTheta]
    simp only [altE, map_smul, LinearMap.smul_apply, smul_eq_mul, hθ, Complex.mul_im] at hk he
    rw [he] at hk
    linarith
  have hq : ∀ x ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H x = (m : ℝ) := by
    intro x hx
    obtain ⟨k, e, he, hk⟩ := key x hx x hx
    have him : altE H x x = 0 := by
      have := altE_swap H hH x x
      linarith
    rw [him] at he
    refine ⟨k, ?_⟩
    rw [← he] at hk
    simp only [qOf]
    linarith
  have hadd : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H (x + y) - qOf (Real.sqrt d / 2) H x
        - qOf (Real.sqrt d / 2) H y - altE H x y = 2 * (m : ℝ) := by
    intro x hx y hy
    obtain ⟨k, e, he, hk⟩ := key x hx y hy
    obtain ⟨t, rfl⟩ := hb
    refine ⟨k - (t + 1) * e, ?_⟩
    have hs := re_swap H hH x y
    simp only [qOf, map_add (f := _), LinearMap.add_apply, Complex.add_re]
    rw [hs, he]
    push_cast at hk ⊢
    linarith
  refine ⟨hq, hadd, ?_, ?_⟩
  · intro x hx
    obtain ⟨m, hm⟩ := hq x hx
    simp only [alphaQ, hm]
    exact_mod_cast exp_pi_I_int m
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hadd x hx y hy
    have h1 : qOf (Real.sqrt d / 2) H (x + y)
        = qOf (Real.sqrt d / 2) H x + qOf (Real.sqrt d / 2) H y + altE H x y + 2 * (m : ℝ) := by
      linarith
    simp only [alphaQ]
    rw [h1, ← Complex.exp_add, ← Complex.exp_add]
    have h2 : (Real.pi : ℂ) * Complex.I * ((qOf (Real.sqrt d / 2) H x + qOf (Real.sqrt d / 2) H y
          + altE H x y + 2 * (m : ℝ) : ℝ) : ℂ)
        = ((Real.pi : ℂ) * Complex.I * (qOf (Real.sqrt d / 2) H x : ℂ)
          + (Real.pi : ℂ) * Complex.I * (qOf (Real.sqrt d / 2) H y : ℂ)
          + (Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [h2, Complex.exp_add _ ((m : ℂ) * _), Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem quadMultiplierRules : AlphaQRules := by
  refine ⟨?_, ?_⟩
  · intro V W _ _ _ _ H H' g hg c x
    simp only [alphaQ, qOf, hg x x]
  · intro n _ h c x
    simp only [alphaQ, qOf, matrixForm_fourfoldBlock]
    rw [← Complex.exp_sum]
    congr 1
    rw [Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]

theorem isSemiChar_congr {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V)
    (α β : V → ℂ) (hab : ∀ x ∈ Λ, α x = β x) (hβ : IsSemiChar H Λ β) : IsSemiChar H Λ α := by
  refine ⟨fun x hx => by rw [hab x hx]; exact hβ.1 x hx, fun x hx y hy => ?_⟩
  rw [hab x hx, hab y hy, hab _ (Λ.add_mem hx hy)]
  exact hβ.2 x hx y hy

theorem ThetaVector_of (hLine : LineTransport) (hStd : ThStd) (hF0 : ProductThetaMem) (hSD : StdSelfDual)
    (hSC : StdSemiChar) (hIso : ThIsom) (h4 : FourthRoot) : ThetaVector := by
  intro L ω₀ n _ _ h Λ α β g D κ hκ
  have hHerm : IsHerm (stdH L (Fin 4 × n)) := (standardFormBasic L (Fin 4 × n)).2.1
  have hβ1 : IsSemiChar (stdH L (Fin 4 × n)) (stdLat L (Fin 4 × n)) β :=
    isSemiChar_congr _ _ _ _ D.betaStd (hSC L ω₀ (Fin 4 × n) D.per)
  obtain ⟨hFmem, hF1⟩ := hF0 L ω₀ (Fin 4 × n) D.per D.half β D.betaStd
  have hFne : F0 L ω₀ (Fin 4 × n) ≠ 0 := by
    intro h0
    rw [h0] at hF1
    simp at hF1
  obtain ⟨hIne, hIline⟩ := hLine (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hHerm (stdLat L (Fin 4 × n))
    (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β (hSD L _) D.selfDual hβ1 D.betaSemi
    D.idx₁ D.idx₂ _ hFmem hFne (fun F hF => ⟨F 0, hStd L ω₀ _ D.per D.half β D.betaStd F hF⟩)
  have hImem := InterTh_of semicharacterHom heisenbergAnalytic (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hHerm
    (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β D.betaSemi
    D.idx₁ _ hFmem
  have hβg : (fun v => β (g v)) = fun x => ∏ a, α (slice a x) := funext D.betaAlpha
  have hiso := hIso (Fin 4 × n → ℂ) (Fin 4 × n → ℂ) (matH (blk4 h)) (stdH L (Fin 4 × n)) g D.isom
    (pow4 Λ) β
  rw [hβg] at hiso
  have hK : kernel4 L ω₀ Λ β g ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ) :=
    (hiso _).1 hImem
  have hK0 : kernel4 L ω₀ Λ β g ≠ 0 := by
    intro h0
    apply hIne
    funext w
    have := congrFun h0 (g.symm w)
    simpa [kernel4] using this
  have hP : κ • kernel4 L ω₀ Λ β g ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ) :=
    Submodule.smul_mem _ κ hK
  have hP0 : κ • kernel4 L ω₀ Λ β g ≠ 0 := smul_ne_zero hκ hK0
  have hPline : ∀ G ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ),
      ∃ c : ℂ, G = c • (κ • kernel4 L ω₀ Λ β g) := by
    intro G hG
    have hG' : (fun w => G (g.symm w)) ∈ Th (stdH L (Fin 4 × n)) β
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) := by
      refine (hiso _).2 ?_
      simpa using hG
    obtain ⟨c, hc⟩ := hIline _ hG'
    refine ⟨c * κ⁻¹, funext fun z => ?_⟩
    have h1 := congrFun hc (g z)
    simp only [LinearEquiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Pi.smul_apply, smul_eq_mul, kernel4]
    rw [h1]
    field_simp
  obtain ⟨hex, huniq⟩ := h4 n h Λ α D.alpha0 _ hP hP0 hPline
  refine ⟨hex, fun θ hθ hθP => ⟨?_, huniq θ hθ hθP⟩⟩
  rintro rfl
  apply hP0
  rw [← hθP]
  funext z
  exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4)) rfl

end Formalism.L2.Th1.H
