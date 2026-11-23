module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.RowActDiagMonomial
public import Formalism.PeriodIntegrals.Bundle022
public import Formalism.PeriodIntegrals.Bundle023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliOps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.MultisetProdNormLeOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionA
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.Params

@[expose] public section

section

noncomputable section

namespace PI.WGL.XiA

open Formalism.BasicNotions MvPolynomial

theorem embGL_apply {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) (a b : Fin N) :
    ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) a b =
      if ha : a.1 < n then (if hb : b.1 < n then (g : Matrix (Fin n) (Fin n) ℂ) ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0)
      else (if b.1 < n then 0 else 1) := by
  apply PI.WGB.embGL_apply_B <;> assumption

theorem rowAct_initMinor {N s : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (I : Fin s → Fin N) (hI : StrictMono I)
    (hs : s ≤ N) (hG : ∀ a b : Fin N, a < b → G b a = 0)
    (hcl : ∀ p b, G b (I p) ≠ 0 → b ∈ Set.range I) :
    Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs) =
      C (∏ p, G (I p) (I p)) * Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs := by
  classical
  set B : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun p p' => G (I p') (I p) with hB
  have hmat : ((Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) G.transpose : MvPolynomial (Fin N × Fin N) ℂ →+* MvPolynomial (Fin N × Fin N) ℂ)).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) =
      (C : ℂ →+* MvPolynomial (Fin N × Fin N) ℂ).mapMatrix B *
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, hB,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.transpose_apply]
    rw [XiU.sum_comp_eq I hI.injective]
    intro b hb
    have : G b (I p) = 0 := by
      by_contra hne
      exact hb (hcl p b hne)
    simp [this]
  have hBdet : B.det = ∏ p, G (I p) (I p) := by
    rw [Matrix.det_of_isLowerTriangular B]
    · rfl
    · intro p p' hpp'
      exact hG _ _ (hI (by simpa using hpp'))
  have hdet := RingHom.map_det ((Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) G.transpose :
      MvPolynomial (Fin N × Fin N) ℂ →+* MvPolynomial (Fin N × Fin N) ℂ))
    (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ))
  rw [RingHom.coe_coe] at hdet
  show Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)).det =
    C (∏ p, G (I p) (I p)) * (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)).det
  rw [hdet, hmat, Matrix.det_mul, ← RingHom.map_det, hBdet]

theorem lpMinor_eq {N : ℕ} (s : ℕ) (hr : s ≤ N) (hn : s ≤ N) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) s hr hn = Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (Fin.castLE hr) hn := rfl

theorem rowsZ_strictMono {n N : ℕ} (h : n + 1 = N) (i : Fin n) : StrictMono (rowsZ h i) := by
  unfold rowsZ
  intro p q hpq
  have hpq' := Fin.lt_def.mp hpq
  have hq := q.isLt
  have hi := i.isLt
  simp only
  split_ifs with h1 h2 h2 <;> simp only [Fin.lt_def] <;> omega

def GoodG (n : ℕ) {N : ℕ} (h : n + 1 = N) (G : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (∀ a b : Fin N, a < b → G b a = 0) ∧ (∀ b : Fin N, b.1 ≠ n → G b ⟨n, by omega⟩ = 0)

def xiScal {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (G : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∏ i : Fin n, (∏ p : Fin (i.1 + 1), G (Fin.castLE (by omega) p) (Fin.castLE (by omega) p)) ^ (aa h lam sg i).toNat *
    (∏ p : Fin (i.1 + 1), G (rowsZ h i p) (rowsZ h i p)) ^ (bb h lam sg i).toNat

theorem rowAct_xi {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (G : Matrix (Fin N) (Fin N) ℂ) (hG : GoodG n h G) :
    Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (xi ℂ h lam sg) = C (xiScal h lam sg G) * xi ℂ h lam sg := by
  have hlp : ∀ i : Fin n, Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose
      (Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) (i.1 + 1) (by omega) (by omega)) =
      C (∏ p : Fin (i.1 + 1), G (Fin.castLE (by omega) p) (Fin.castLE (by omega) p)) *
        Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) (i.1 + 1) (by omega) (by omega) := by
    intro i
    rw [lpMinor_eq]
    apply rowAct_initMinor G _ (Fin.strictMono_castLE _) _ hG.1
    intro p b hb
    have hle : b ≤ Fin.castLE (by omega) p := by
      by_contra hlt
      push Not at hlt
      exact hb (hG.1 _ _ hlt)
    refine ⟨⟨b.1, ?_⟩, Fin.ext rfl⟩
    have := p.2
    simp only [Fin.le_def, Fin.coe_castLE] at hle
    omega
  have hrz : ∀ i : Fin n, Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (rowsZ h i) (by omega)) =
      C (∏ p : Fin (i.1 + 1), G (rowsZ h i p) (rowsZ h i p)) *
        Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (rowsZ h i) (by omega) := by
    intro i
    apply rowAct_initMinor G _ (rowsZ_strictMono h i) _ hG.1
    intro p b hb
    by_cases hp : p.1 = i.1
    · have e : rowsZ h i p = ⟨n, by omega⟩ := by
        simp only [rowsZ, hp, if_true]; ext; simp; omega
      rw [e] at hb
      have hbn : b.1 = n := by
        by_contra hne
        exact hb (hG.2 b hne)
      refine ⟨⟨i.1, by omega⟩, ?_⟩
      simp only [rowsZ, if_true]
      ext; simp; omega
    · have e : rowsZ h i p = ⟨p.1, by omega⟩ := by
        simp only [rowsZ, hp, if_false]
      rw [e] at hb
      have hle : b.1 ≤ p.1 := by
        by_contra hlt
        push Not at hlt
        exact hb (hG.1 _ _ (by simpa [Fin.lt_def] using hlt))
      have hpi : p.1 < i.1 := by have := p.2; omega
      refine ⟨⟨b.1, by omega⟩, ?_⟩
      have : b.1 ≠ i.1 := by omega
      simp only [rowsZ, this, if_false]
  unfold xi xiScal
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, map_pow, hlp i, hrz i, mul_pow, mul_pow, map_mul, map_pow, map_pow]
  ring

theorem initMinor_mem {N s : ℕ} (I : Fin s → Fin N) (hs : s ≤ N) :
    Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (fun t : Fin N => if t.1 < s then 1 else 0) := by
  have hm := Formalism.GradedWeylDivisibility.bidetMem ℂ N N 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : Formalism.GradedWeylDivisibility.bideterminant ℂ (r := N) (n := N) (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) =
      Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs := by
    simp [Formalism.GradedWeylDivisibility.bideterminant]
  have e2 : Formalism.GradedWeylDivisibility.shapeDeg (n := N) (fun _ : Fin 1 => s) = fun t : Fin N => if t.1 < s then 1 else 0 := by
    funext t
    by_cases ht : t.1 < s <;> simp [Formalism.GradedWeylDivisibility.shapeDeg, ht]
  rwa [e1, e2] at hm

private theorem mul_mem_dualWeyl_complex {N : ℕ} (ν μ : Fin N → ℕ) (f g : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) (hg : g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N μ) :
    f * g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν + μ) := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf hg ⊢
  rw [Submodule.mem_inf] at hf hg ⊢
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hf1 hg1 ⊢
    exact hf1.mul hg1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at hf2 hg2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, hf2 l j hlj, hg2 l j hlj]

private theorem one_mem_dualWeyl_complex {N : ℕ} :
    (1 : MvPolynomial (Fin N × Fin N) ℂ) ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N 0 := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact MvPolynomial.isWeightedHomogeneous_one _ _
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero]
    intro l j hlj
    rw [map_one, map_one]

theorem pow_mem {N : ℕ} (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) (k : ℕ) : f ^ k ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (k • ν) := by
  induction k with
  | zero => simpa using one_mem_dualWeyl_complex (N := N)
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_dualWeyl_complex _ _ _ _ ih hf

theorem prod_mem {N : ℕ} {ι : Type*} (s : Finset ι) (ν : ι → Fin N → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) ℂ)
    (hf : ∀ i ∈ s, f i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν i)) :
    ∏ i ∈ s, f i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_dualWeyl_complex (N := N)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_complex _ _ _ _ (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem tele_sum (ℓ : ℕ → ℤ) (n t : ℕ) (ht : t ≤ n) :
    ∑ i ∈ Finset.range n, (if t ≤ i then ℓ i - ℓ (i + 1) else 0) = ℓ t - ℓ n := by
  induction n with
  | zero =>
    have ht0 : t = 0 := by omega
    subst ht0
    simp
  | succ n ih =>
    rcases Nat.lt_or_ge n t with h | h
    · have htn : t = n + 1 := by omega
      subst htn
      rw [Finset.sum_eq_zero]
      · ring
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [if_neg (by omega)]
    · rw [Finset.sum_range_succ, ih h, if_pos h]
      ring

end PI.WGL.XiA
end
end

section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem ioIntegral_of (hZ : CapelliZ) (hL : LiftMod) (hV : ZScalarVanish) : IoIntegral := by
  intro n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨Z, hZi, hZa⟩ := hZ n N h lam sg hI
  obtain ⟨m, hm, hd⟩ := hL n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨f', hf', hZf⟩ := hZi m hm
  refine ⟨f', hf', ?_⟩
  have hsC : MvPolynomial.map (Int.castRingHom ℂ) s ∈ nablaSq ℂ n sg :=
    Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW s hs
  have hO : OtherPart h lam sg ≤ LinearMap.ker Z := by
    unfold OtherPart
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun hne => iSup_le fun hw =>
      iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [LinearMap.mem_ker, hZa mu hmu φ hφ t ht, hV n N h lam sg mu hI hmu hne hw, Int.cast_zero, zero_smul]
  have h0 := hO hd
  rw [LinearMap.mem_ker, map_sub, hZf, hZa sg hI io0 hE _ hsC] at h0
  have hz : zScalar h lam sg sg = cBr h lam sg := rfl
  rw [hz] at h0
  rw [map_smul]
  exact (sub_eq_zero.mp h0).symm

theorem sqAct_smul {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) (c : ℂ)
    (x : MvPolynomial (Fin k × Fin k) ℂ) : sqAct ℂ k mu g (c • x) = c • sqAct ℂ k mu g x := by
  rw [sqAct, sqAct, map_smul, smul_comm]

theorem gTLower_of_steps (hN : Numbers) (hX : XiFacts) (hE : IoExists) (hP4 : IoIntegral)
    (hA : AdjointBr) (hB : BrIntegral) : PI.GTLower := by
  intro n N h lam sg hI
  obtain ⟨hc0, hcB, hdeg⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, -⟩ := hX n N h lam sg hI
  obtain ⟨io0, ⟨hE1, hE2⟩, hx, hW⟩ := hE n N h lam sg hI
  let c : ℂ := ((cBr h lam sg : ℤ) : ℂ)
  let io := c • io0
  have hio : ∀ x, io x = c • io0 x := fun x => rfl
  have I2 : ∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam := fun s hs =>
    Submodule.smul_mem _ _ (hE1 s hs)
  have I3 : ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
      io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s) := by
    intro g s hs
    rw [hio, hio, hE2 g s hs, sqAct_smul]
  have I4 : io (extremal ℂ n sg) = c • xi ℂ h lam sg := by rw [hio, hx]
  have I5 : LastWeight lam sg io := by
    intro a s hs
    rw [hio, sqAct_smul, hW a s hs, smul_comm]
  have I1 : ∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
      io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f := by
    intro s hs
    obtain ⟨f, hf, hf'⟩ := hP4 n N h lam sg hI io0 ⟨hE1, hE2⟩ hx hW s hs
    exact ⟨f, hf, by rw [hio, ← map_smul]; exact hf'⟩
  obtain ⟨I6, br, hrest, hT⟩ := hA n N h lam sg hI io ⟨I2, I3⟩ I4 I5
  have B1 := hB n N h lam sg hI io br I1 I2 hrest.1 hT
  exact ⟨hc0, hcB, hxi0, hdeg, io, br, ⟨I1, I2, I3, I4, I5, I6⟩, ⟨B1, hrest⟩, hT⟩

end PI.WGL
end
end

section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem embGL_cc {n : ℕ} (g : GL (Fin n) ℂ) (i j : Fin n) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem embGL_lc {n : ℕ} (g : GL (Fin n) ℂ) (j : Fin n) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem embGL_cl {n : ℕ} (g : GL (Fin n) ℂ) (i : Fin n) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem embGL_ll {n : ℕ} (g : GL (Fin n) ℂ) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n) = 1 := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

def lmapPoly {σ τ : Type} (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) (p : Polynomial (MvPolynomial σ ℂ)) :
    Polynomial (MvPolynomial τ ℂ) :=
  ∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.C (φ (p.coeff k)) * Polynomial.X ^ k

theorem lmapPoly_coeff {σ τ : Type} (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (p : Polynomial (MvPolynomial σ ℂ)) (k : ℕ) : (lmapPoly φ p).coeff k = φ (p.coeff k) := by
  simp only [lmapPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hk; omega), map_zero]

theorem lmapPoly_eval {σ τ : Type} (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (p : Polynomial (MvPolynomial σ ℂ)) (t : ℂ) : (lmapPoly φ p).eval (C t) = φ (p.eval (C t)) := by

  rw [Polynomial.eval_eq_sum_range (p := p), lmapPoly, Polynomial.eval_finsetSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← C_pow]
  rw [mul_comm (φ _), mul_comm (p.coeff i), ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]

theorem det_one_add_single {n : ℕ} (a b : Fin n) (t : ℂ) :
    (1 + Matrix.single a b t).det = if a = b then t + 1 else 1 := by
  by_cases hab : a = b
  · subst hab
    have hD : (1 + Matrix.single a a t) = Matrix.diagonal (fun i => if i = a then 1 + t else 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases hia : i = a
        · subst hia; simp
        · simp [hia, Ne.symm hia]
      · simp [hij, Matrix.single_apply]
        intro h1 h2; exact absurd (h1.symm.trans h2) hij
    rw [hD, Matrix.det_diagonal, Finset.prod_ite_eq']
    simp [add_comm]
  · have := Matrix.det_transvection_of_ne a b hab t
    unfold Matrix.transvection at this
    rw [this, if_neg hab]

theorem embGL_transvec {n : ℕ} (g : GL (Fin n) ℂ) (a b : Fin n) (t : ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b t) :
    ((embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).transpose =
      1 + Matrix.single b.castSucc a.castSucc t := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.transpose_apply, embGL_ll, Matrix.single_apply]
    | cast j =>
      simp [Matrix.transpose_apply, embGL_cl, Matrix.one_apply]
      exact fun h => Fin.castSucc_ne_last j h.symm
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.transpose_apply, embGL_lc, Matrix.single_apply, Matrix.one_apply]
    | cast j =>
      rw [Matrix.transpose_apply, embGL_cc, hg]
      simp [Matrix.single_apply, Matrix.one_apply, eq_comm, and_comm]

theorem eqv_pol {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (a b : Fin n) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    φ (pol ℂ a b s) + (if a = b then (mu.detShift : ℂ) • φ s else 0) =
      pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) (φ s) +
        (if a = b then (lam.detShift : ℂ) • φ s else 0) := by
  subst h
  have hι : ∀ x : Fin n, Fin.castLE (by omega : n ≤ n + 1) x = Fin.castSucc x := fun x => Fin.ext rfl
  rw [hι a, hι b]
  set d1 := mu.detShift with hd1
  set d2 := lam.detShift with hd2
  set K : ℤ := |d1| + |d2| with hK
  have hK1 : 0 ≤ d1 + K := by have := neg_abs_le d1; have := abs_nonneg d2; omega
  have hK2 : 0 ≤ d2 + K := by have := neg_abs_le d2; have := abs_nonneg d1; omega
  set e1 := (d1 + K).toNat with he1d
  set e2 := (d2 + K).toNat with he2d
  have he1 : (e1 : ℤ) = d1 + K := Int.toNat_of_nonneg hK1
  have he2 : (e2 : ℤ) = d2 + K := Int.toNat_of_nonneg hK2
  set Q : Polynomial (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) :=
    if a = b then Polynomial.X + 1 else 1 with hQ
  set P := Q ^ e1 * lmapPoly φ (rowGen ℂ a b s) - Q ^ e2 * rowGen ℂ a.castSucc b.castSucc (φ s) with hP
  have key : ∀ t : ℕ, P.eval (C (t : ℂ)) ∈ (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro t
    rw [Submodule.mem_bot]
    set D : ℂ := if a = b then (t : ℂ) + 1 else 1 with hD
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (PI.WHw.det_one_add_single_ne a b t)
    have hgv : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b (t : ℂ) := rfl
    have hgT : (g : Matrix (Fin n) (Fin n) ℂ).transpose = 1 + Matrix.single b a (t : ℂ) := by
      rw [hgv, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
    have hgT' := embGL_transvec g a b t hgv
    have hu : ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) = D := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, det_one_add_single]
    have hu' : ((Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) : ℂˣ) : ℂ) = D := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hgT', det_one_add_single]
      rcases eq_or_ne a b with hab | hab
      · subst hab; simp [hD]
      · simp [hD, hab, Ne.symm hab]
    have huu : Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = Matrix.GeneralLinearGroup.det g :=
      Units.ext (hu'.trans hu.symm)
    have heq := hφ.2 g s hs
    unfold sqAct detPow at heq
    rw [hgT, hgT', huu, map_smul, ← PI.WHw.eval_rowGen, ← PI.WHw.eval_rowGen] at heq
    set u := Matrix.GeneralLinearGroup.det g
    have heq2 := congrArg (fun x => ((u ^ K : ℂˣ) : ℂ) • x) heq
    simp only [smul_smul, ← Units.val_mul, ← zpow_add] at heq2
    rw [show K + mu.detShift = (e1 : ℤ) by omega, show K + lam.detShift = (e2 : ℤ) by omega,
      zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu] at heq2
    have hQe : Q.eval (C (t : ℂ)) = C D := by
      rw [hQ, hD]; split_ifs <;> simp
    rw [hP, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_pow, hQe, lmapPoly_eval, ← C_pow, ← C_pow, ← smul_eq_C_mul, ← smul_eq_C_mul, heq2, sub_self]
  have h1 := PI.WHw.coeff_mem_of_eval ⊥ P key 1
  rw [Submodule.mem_bot] at h1
  have hL0 : (lmapPoly φ (rowGen ℂ a b s)).coeff 0 = φ s := by
    rw [lmapPoly_coeff, rowGen_coeff_zero]
  have hL1 : (lmapPoly φ (rowGen ℂ a b s)).coeff 1 = φ (pol ℂ a b s) := by
    rw [lmapPoly_coeff, pol_eq_rowDiv]; rfl
  have hG0 : (rowGen ℂ a.castSucc b.castSucc (φ s)).coeff 0 = φ s := rowGen_coeff_zero ℂ _ _ _
  have hG1 : (rowGen ℂ a.castSucc b.castSucc (φ s)).coeff 1 = pol ℂ a.castSucc b.castSucc (φ s) := by
    rw [pol_eq_rowDiv]; rfl
  have hc1 : ∀ (e : ℕ) (F : Polynomial (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)),
      (Q ^ e * F).coeff 1 = F.coeff 1 + (if a = b then (e : MvPolynomial _ ℂ) * F.coeff 0 else 0) := by
    intro e F
    rw [hQ]
    split_ifs with hab
    · rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_X_add_one_pow]
      simp
    · simp
  rw [hP, Polynomial.coeff_sub, hc1, hc1, hL0, hL1, hG0, hG1] at h1
  by_cases hab : a = b
  · simp only [hab, if_true] at h1 ⊢
    have c1 : ((e1 : ℕ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) = C ((d1 : ℂ) + (K : ℂ)) := by
      rw [← map_natCast C]; congr 1; exact_mod_cast he1
    have c2 : ((e2 : ℕ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) = C ((d2 : ℂ) + (K : ℂ)) := by
      rw [← map_natCast C]; congr 1; exact_mod_cast he2
    rw [c1, c2, map_add (f := _), map_add (f := _)] at h1
    rw [smul_eq_C_mul, smul_eq_C_mul]
    subst hab
    linear_combination h1
  · simp only [hab, if_false, add_zero] at h1 ⊢
    exact sub_eq_zero.mp h1

end PI.WGL
end
end
