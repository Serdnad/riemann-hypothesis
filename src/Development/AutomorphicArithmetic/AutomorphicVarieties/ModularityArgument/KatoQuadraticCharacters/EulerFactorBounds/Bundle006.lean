module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.XiAction

private theorem vc {M k : ℕ} [NeZero M] (h : k ∣ M) (a : ZMod M) :
    ((a.val : ℕ) : ZMod k) = ZMod.castHom h (ZMod k) a := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem cnd_iff (l N M : ℕ) [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g δ : SL(2, ℤ))
    (hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0) (hδl : ((en δ 1 0 : ℤ) : ZMod l) = 0) (ν : (ZMod M)ˣ)
    (h1 : ((ν : ZMod M).val : ZMod N) = (en δ 0 0 : ZMod N)) (h2 : ((ν : ZMod M).val : ZMod l) = 1)
    (m m' : Matrix (Fin 2) (Fin 2) (ZMod M))
    (h : m * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = (ν : ZMod M) • m') :
    Cnd l N g m ↔ Cnd l N g m' := by
  have e : ∀ i, m i 0 * (en δ 0 0 : ZMod M) + m i 1 * (en δ 1 0 : ZMod M) = (ν : ZMod M) * m' i 0 := by
    intro i
    have := congrFun (congrFun h i) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, en] using this
  have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  have uN : (en δ 0 0 : ZMod N) * (en δ 1 1 : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at this
    rw [hδN] at this; simpa using this
  have ul : (en δ 0 0 : ZMod l) * (en δ 1 1 : ZMod l) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at this
    rw [hδl] at this; simpa using this
  have eN : ∀ i, ((m i 0).val : ZMod N) = ((m' i 0).val : ZMod N) := by
    intro i
    have := congrArg (ZMod.castHom hN (ZMod N)) (e i)
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_intCast, map_intCast, hδN, ← vc hN, ← vc hN, ← vc hN, ← vc hN, h1] at this
    linear_combination (en δ 1 1 : ZMod N) * this - (((m i 0).val : ZMod N) - ((m' i 0).val : ZMod N)) * uN
  have el : ∀ i, ((m i 0).val : ZMod l) * (en δ 0 0 : ZMod l) = ((m' i 0).val : ZMod l) := by
    intro i
    have := congrArg (ZMod.castHom hl (ZMod l)) (e i)
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_intCast, map_intCast, hδl, ← vc hl, ← vc hl, ← vc hl, ← vc hl, h2] at this
    linear_combination this
  unfold Cnd
  rw [eN 0, eN 1, ← el 0, ← el 1]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h3 => ?_, fun h3 => ?_⟩)
  · linear_combination (en δ 0 0 : ZMod l) * h3
  · linear_combination (en δ 1 1 : ZMod l) * h3 -
      ((en g 1 0 : ZMod l) * ((m 0 0).val : ZMod l) - (en g 0 0 : ZMod l) * ((m 1 0).val : ZMod l)) * ul

private theorem wt_dvd (l n M w : ℕ) [Fact l.Prime] [NeZero M] (hl : l ^ n ∣ M) (δ : Matrix (Fin 2) (Fin 2) ℤ)
    (ν : ZMod M) (h2 : (ν.val : ZMod (l ^ n)) = 1) (d d' : ZMod M) (hd : d' = ν ^ 2 * d)
    (m m' : Matrix (Fin 2) (Fin 2) (ZMod M))
    (h : m * δ.map (Int.castRingHom (ZMod M)) = ν • m') (u : Fin 2 → ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣ (d.val : ℤ_[l]) * (((m 0 0).val : ℤ_[l]) * (mZl l δ *ᵥ u) 0 + ((m 0 1).val : ℤ_[l]) * (mZl l δ *ᵥ u) 1) ^ w -
      (d'.val : ℤ_[l]) * (((m' 0 0).val : ℤ_[l]) * u 0 + ((m' 0 1).val : ℤ_[l]) * u 1) ^ w := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  have e : ∀ j, ((m 0 0).val : ZMod (l ^ n)) * (δ 0 j : ZMod (l ^ n)) + ((m 0 1).val : ZMod (l ^ n)) * (δ 1 j : ZMod (l ^ n)) =
      ((m' 0 j).val : ZMod (l ^ n)) := by
    intro j
    have h0 : m 0 0 * (δ 0 j : ZMod M) + m 0 1 * (δ 1 j : ZMod M) = ν * m' 0 j := by
      have := congrFun (congrFun h 0) j
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have := congrArg (ZMod.castHom hl (ZMod (l ^ n))) h0
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_intCast, map_intCast, ← vc hl, ← vc hl, ← vc hl, ← vc hl, h2, one_mul] at this
    exact this
  have ed : (d'.val : ZMod (l ^ n)) = (d.val : ZMod (l ^ n)) := by
    rw [vc hl d', hd, map_mul, map_pow, ← vc hl, ← vc hl, h2, one_pow, one_mul]
  have ev : ∀ i, (mZl l δ *ᵥ u) i = (δ i 0 : ℤ_[l]) * u 0 + (δ i 1 : ℤ_[l]) * u 1 := by
    intro i
    simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [ev, ev]
  simp only [map_sub, map_mul, map_pow, map_add (f := _), map_natCast, map_intCast]
  rw [ed, ← e 0, ← e 1, sub_eq_zero]
  congr 2
  ring

private theorem cls_step {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (n N : ℕ) (hN : 0 < N) (δ δ' : SL(2, ℤ))
    (hc : !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1])
    (f f' : X.Kˣ) (hf : Cgr (l ^ n) (slU X (ofSL δ') f) f') (k k' : ℤ_[l]) (hk : (l : ℤ_[l]) ^ n ∣ k - k') :
    AdicCompletion.eval (idl l) (X.Kl l) n
      (k • X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        k' • clsK X l n (slD X N (f' : X.K))) = 0 := by
  obtain ⟨c1, -, -, c4, c5, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, a5, -⟩ := sApi Ω ε X l n
  obtain ⟨-, s2, s3, -⟩ := sSlD Ω ε X N hN
  have r1 := c5 (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f))
  have r2 := c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f')
  have r3 := c4 _ _ _ _ r1 r2 (by
    obtain ⟨h, hh⟩ := hf
    refine ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) h, ?_⟩
    rw [← map_pow, ← map_mul, ← hh]
    apply Units.ext
    have := s2 _ _ (by rw [δ.det_coe]; exact one_pos) hc (f : X.K)
    rw [s3 δ'] at this
    exact this)
  have r4 := a5 k k' (X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K)))) hk
  have r5 : AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        clsK X l n (slD X N (f' : X.K))) = 0 := r3
  rw [← sub_add_sub_cancel _ (k' • X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K)))),
    map_add, r4, ← smul_sub, map_smul, r5, smul_zero, add_zero]

private theorem conj_ex (N : ℕ) (δ : SL(2, ℤ)) (h : (N : ℤ) ∣ en δ 1 0) : ∃ δ' : SL(2, ℤ),
    !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] := by
  obtain ⟨c, hc⟩ := h
  have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  refine ⟨⟨!![en δ 0 0, N * en δ 0 1; c, en δ 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of, ← hdet, hc]; ring
  · unfold en at hc
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, en, hc, mul_comm]

private theorem cd_row (N M₀ M : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (hM : M = N * M₀) (δ δ' : SL(2, ℤ))
    (hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0)
    (hc : !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1])
    (ν : ZMod M) (m m' : Matrix (Fin 2) (Fin 2) (ZMod M)) (hm : ((m 1 0).val : ZMod N) = 0) (hm' : ((m' 1 0).val : ZMod N) = 0)
    (h : m * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = ν • m') (x : Row M₀) :
    rt (x ᵥ* cD N M₀ m) δ' = ((ν.val : ZMod M₀) • x) ᵥ* cD N M₀ m' := by
  obtain ⟨d1, -, -, d4⟩ := sCdFacts N M₀ M hM
  have hN : N ∣ M := hM ▸ dvd_mul_right N M₀
  have e1 : ν • m' = !![ν, 0; 0, ν] * m' := by
    ext i j
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : x ᵥ* cD N M₀ (!![ν, 0; 0, ν] : Matrix (Fin 2) (Fin 2) (ZMod M)) = (ν.val : ZMod M₀) • x := by
    funext j
    fin_cases j <;> simp [cD, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  unfold rt
  rw [← d4 _ _ hc, Matrix.vecMul_vecMul, ← d1 _ _ hm ?_, h, e1, d1 _ _ ?_ hm', ← Matrix.vecMul_vecMul, e2]
  · simp
  · rw [vc hN, Matrix.map_apply, eq_intCast, map_intCast]; exact hδN

end UpperTheory.V.Z.Kato.Nb.XiAction

open UpperTheory.V.Z.Kato.Nb.XiAction in
theorem UpperTheory.V.Z.Kato.Nb.sXiAct :
    UpperTheory.V.Z.Kato.Nb.SXiAct := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g L x y hxy P a ha δ hδ ν h1 h2 hP u
  have hN : N ∣ M := L.eq ▸ dvd_mul_right N M₀
  have hln : l ^ n ∣ M := L.eq ▸ L.dl.mul_left N
  have hl1 : l ∣ l ^ n := dvd_pow_self l (by have := L.pos; omega)
  have hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hδ.1
  have hδl : ((en δ 1 0 : ℤ) : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 hδ.2
  have h2' : ((ν : ZMod M).val : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hl1 (ZMod l)) h2
    rwa [map_natCast, map_one] at this
  obtain ⟨δ', hc⟩ := conj_ex N δ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hδN)
  let D : GL (Fin 2) (ZMod M) := Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ)
  let S : GL (Fin 2) (ZMod M) := Matrix.GeneralLinearGroup.scalar (Fin 2) ν
  let e : GL (Fin 2) (ZMod M) ≃ GL (Fin 2) (ZMod M) := (Equiv.mulRight D).trans (Equiv.mulLeft S⁻¹)
  have he : ∀ m, m * D = S * e m := fun m => by simp [e]
  have hrel : ∀ m : GL (Fin 2) (ZMod M), (m : Matrix (Fin 2) (Fin 2) (ZMod M)) *
      (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = (ν : ZMod M) • (e m : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    intro m
    have := congrArg (fun z : GL (Fin 2) (ZMod M) => (z : Matrix (Fin 2) (Fin 2) (ZMod M))) (he m)
    simp only [Units.val_mul] at this
    rw [Matrix.smul_eq_diagonal_mul]
    exact this
  have hdet : ∀ m, Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det (e m) * ν ^ 2 := by
    intro m
    apply Units.ext
    have := congrArg Matrix.det (hrel m)
    rw [Matrix.det_mul, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, δ.det_coe, map_one, mul_one] at this
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [this, mul_comm]; simp
  have hcnd := fun m : GL (Fin 2) (ZMod M) => cnd_iff l N M hN (hl1.trans hln) g δ hδN hδl ν h1 h2' _ _ (hrel m)
  show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l _ (Xi X l n N M₀ M w g x y P a _) - _) = 0
  unfold Xi

  rw [map_sum, map_sub, map_sum, map_sum, sub_eq_zero]
  refine Finset.sum_equiv e (fun m => ?_) (fun m hm => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcnd m, hdet m, hP]
  · have hm1 := (Finset.mem_filter.1 hm).2.1
    have hm2 := (hcnd m).1 hm1
    rw [← sub_eq_zero, ← map_sub, map_smul]
    refine cls_step X l n N (NeZero.pos N) δ δ' hc _ _ ?_ _ _ ?_
    · rw [← cd_row N M₀ M L.eq δ δ' hδN hc _ _ _ hm1.1 hm2.1 (hrel m), ← cd_row N M₀ M L.eq δ δ' hδN hc _ _ _ hm1.1 hm2.1 (hrel m)]
      exact (ha _ _ ((sCdFacts N M₀ M L.eq).2.2.1 m hm1.1 x y hxy)).2 δ'
    · refine wt_dvd l n M w hln _ ν h2 _ _ ?_ _ _ (hrel m) u
      rw [hdet m, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      congr 1
      rw [mul_inv, mul_comm _ (ν ^ 2)⁻¹, mul_inv_cancel_left]
end

section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

noncomputable section

namespace UpperTheory.V.Z.Kato.Nb.InverseLimitApi

private def Fm (R : Type) [CommRing R] (w : ℕ) : Submodule R ((Fin 2 → R) → R) :=
  Submodule.span R {φ | ∃ i j : ℕ, i + j = w ∧ φ = fun u => u 0 ^ i * u 1 ^ j}

private theorem fm_mul {R : Type} [CommRing R] {a b : ℕ} {φ ψ : (Fin 2 → R) → R} (hφ : φ ∈ Fm R a) (hψ : ψ ∈ Fm R b) :
    φ * ψ ∈ Fm R (a + b) := by
  induction hφ using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul k x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  | mem x hx =>
    induction hψ using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
    | mem y hy =>
      obtain ⟨i, j, rfl, rfl⟩ := hx
      obtain ⟨i', j', rfl, rfl⟩ := hy
      refine Submodule.subset_span ⟨i + i', j + j', by omega, ?_⟩
      funext u
      simp only [Pi.mul_apply]
      ring

private theorem fm_pow {R : Type} [CommRing R] {φ : (Fin 2 → R) → R} (hφ : φ ∈ Fm R 1) (k : ℕ) : φ ^ k ∈ Fm R k := by
  induction k with
  | zero => exact Submodule.subset_span ⟨0, 0, rfl, by funext u; simp⟩
  | succ k ih => rw [pow_succ]; exact fm_mul ih hφ

private theorem fm_lin {R : Type} [CommRing R] (m : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    (fun u => (m *ᵥ u) i) ∈ Fm R 1 := by
  have h0 : (fun u : Fin 2 → R => u 0 ^ 1 * u 1 ^ 0) ∈ Fm R 1 := Submodule.subset_span ⟨1, 0, rfl, rfl⟩
  have h1 : (fun u : Fin 2 → R => u 0 ^ 0 * u 1 ^ 1) ∈ Fm R 1 := Submodule.subset_span ⟨0, 1, rfl, rfl⟩
  have h := add_mem (Submodule.smul_mem _ (m i 0) h0) (Submodule.smul_mem _ (m i 1) h1)
  convert h using 1
  funext u
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem un_pow (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) (j : ℕ) : f ^ j ∈ X.Un m := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
  induction j with
  | zero => simpa using (h m).1
  | succ j ih => rw [pow_succ]; exact ((h m).2 _ ih _ hf).1

private def Cf (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : Submodule ℤ_[l] (X.Khat l) where
  carrier := {x | ∃ f ∈ X.Un (l ^ n), Rep X l n f x}
  zero_mem' := by
    obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
    obtain ⟨h1, -, h3, -⟩ := sCls Ω ε X l n
    refine ⟨1, (h _).1, ?_⟩
    simpa using h3 1 _ 0 (h1 1)
  add_mem' := by
    rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
    obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
    obtain ⟨-, h2, -⟩ := sCls Ω ε X l n
    exact ⟨f * g, ((h _).2 f hf g hg).1, (h2 _ _ _ _ ha hb).1⟩
  smul_mem' := by
    rintro k a ⟨f, hf, ha⟩
    obtain ⟨-, -, -, -, -, -, h⟩ := sCls Ω ε X l n
    obtain ⟨j, hj⟩ := h f k a ha
    exact ⟨f ^ j, un_pow X _ f hf j, hj⟩

private def Pm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) : Submodule ℤ_[l] (X.Fn l) where
  carrier := {t | PolMod X l w n t}
  zero_mem' := ⟨0, fun _ => (Cf X l n).zero_mem, fun u => by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    refine ⟨c + d, fun i => (Cf X l n).add_mem (hc i) (hd i), fun u => ?_⟩
    simp only [Pi.add_apply, ha u, hb u, smul_add, Finset.sum_add_distrib]
  smul_mem' := by
    rintro k a ⟨c, hc, ha⟩
    refine ⟨k • c, fun i => (Cf X l n).smul_mem k (hc i), fun u => ?_⟩
    simp only [Pi.smul_apply, ha u, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

private theorem pm_fm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (c : X.Khat l) (hc : c ∈ Cf X l n)
    (φ : (Fin 2 → ℤ_[l]) → ℤ_[l]) (hφ : φ ∈ Fm ℤ_[l] w) : (fun u => φ u • c) ∈ Pm X l w n := by
  induction hφ using Submodule.span_induction with
  | zero =>
    convert (Pm X l w n).zero_mem using 1
    funext u; simp
  | add x y _ _ hx hy =>
    convert (Pm X l w n).add_mem hx hy using 1
    funext u; simp [add_smul]
  | smul k x _ hx =>
    convert (Pm X l w n).smul_mem k hx using 1
    funext u; simp [mul_smul]
  | mem x hx =>
    obtain ⟨i, j, rfl, rfl⟩ := hx
    refine ⟨Pi.single ⟨i, by omega⟩ c, fun k => ?_, fun u => ?_⟩
    · show Pi.single (M := fun _ => X.Khat l) _ c k ∈ Cf X l n
      rw [Pi.single_apply]
      split_ifs
      · exact hc
      · exact zero_mem _
    · rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin (i + j + 1))]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, smul_zero]
      · simp

private theorem pm_act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (t : X.Fn l)
    (ht : PolMod X l w n t) : PolMod X l w n (X.act l m t) := by
  obtain ⟨c, hc, ht⟩ := ht
  have key : ∀ i : Fin (w + 1), (fun u => (((fun u => (mZl l m *ᵥ u) 0) ^ (i : ℕ) * (fun u => (mZl l m *ᵥ u) 1) ^ (w - (i : ℕ)) :
      (Fin 2 → ℤ_[l]) → ℤ_[l]) u) • X.kmap l (X.sl (toGQ m)).toRingEquiv (c i)) ∈ Pm X l w n := by
    intro i
    apply pm_fm
    · obtain ⟨f, hf, hr⟩ := hc i
      obtain ⟨-, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
      obtain ⟨-, -, -, -, h', -⟩ := sCls Ω ε X l n
      exact ⟨slU X (toGQ m) f, h _ _ f hf, h' (X.sl (toGQ m)).toRingEquiv f _ hr⟩
    · have := fm_mul (fm_pow (fm_lin (mZl l m) 0) i) (fm_pow (fm_lin (mZl l m) 1) (w - i))
      rwa [show (i : ℕ) + (w - i) = w by omega] at this
  have h := (Pm X l w n).sum_mem fun i (_ : i ∈ Finset.univ) => key i
  show X.act l m t ∈ Pm X l w n
  convert h using 1
  funext u
  show X.kmap l (X.sl (toGQ m)).toRingEquiv (t (mZl l m *ᵥ u)) = _
  rw [ht, map_sum (X.kmap l (X.sl (toGQ m)).toRingEquiv), Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl

private theorem pm_down (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (t : X.Fn l)
    (ht : PolMod X l w (n + 1) t) : PolMod X l w n t := by
  obtain ⟨c, hc, ht⟩ := ht
  refine ⟨c, fun i => ?_, ht⟩
  obtain ⟨f, hf, hr⟩ := hc i
  obtain ⟨-, -, -, -, -, h, -⟩ := sCls Ω ε X l n
  refine ⟨f, fun W hW => ?_, h _ _ hr⟩
  obtain ⟨g, hg⟩ := hf W hW
  refine ⟨g ^ l, ?_⟩
  rw [Units.val_pow_eq_pow_val, ← pow_mul, ← pow_succ']
  exact hg

private def Im (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) : Submodule ℤ_[l] (X.Fn l) where
  carrier := {a | InvM X l N w n a}
  zero_mem' := by
    obtain ⟨he, -⟩ := sApi Ω ε X l n
    refine ⟨⟨0, (Pm X l w n).zero_mem, he.refl _⟩, fun γ _ => ?_, 0, zero_mem _, fun u => by simp⟩
    rw [map_zero]; exact he.refl _
  add_mem' := by
    rintro a b ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩ ⟨⟨s, hs, hbs⟩, hb, y, hy, hyb⟩
    obtain ⟨-, h, -⟩ := sApi Ω ε X l n
    refine ⟨⟨t + s, (Pm X l w n).add_mem ht hs, (h _ _ _ _ hat hbs).1⟩, fun γ hγ => ?_, x + y, add_mem hx hy, ?_⟩
    · rw [(X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ)).map_add]
      exact (h _ _ _ _ (ha γ hγ) (hb γ hγ)).1
    · have := (h x ((l : ℤ_[l]) ^ cL X l N w • a) y ((l : ℤ_[l]) ^ cL X l N w • b) hxa hyb).1
      rw [← smul_add] at this
      exact this
  smul_mem' := by
    rintro k a ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩
    obtain ⟨-, -, h, -⟩ := sApi Ω ε X l n
    refine ⟨⟨k • t, (Pm X l w n).smul_mem k ht, h _ _ _ hat⟩, fun γ hγ => ?_, k • x, Submodule.smul_mem _ _ hx, ?_⟩
    · rw [map_smul]; exact h _ _ _ (ha γ hγ)
    · have := h k x ((l : ℤ_[l]) ^ cL X l N w • a) hxa
      rw [smul_comm] at this
      exact this

private theorem main : SInvApi := by
  intro Ω _ _ _ ε X l _ N w n
  refine ⟨(Im X l N w n).zero_mem, fun a b ha hb => ⟨(Im X l N w n).add_mem ha hb, (Im X l N w n).sub_mem ha hb⟩,
    fun k a ha => (Im X l N w n).smul_mem k ha, ?_, fun ι S a h => (Im X l N w n).sum_mem h, ?_, ?_,
    fun m t _ ht => pm_act X l w n m t ht⟩
  · rintro a b hab ⟨⟨t, ht, hbt⟩, hb, x, hx, hxb⟩
    obtain ⟨he, -, hs, -, -, hm, -⟩ := sApi Ω ε X l n
    refine ⟨⟨t, ht, he.trans hab hbt⟩, fun γ hγ => he.trans (hm _ _ _ hab) (he.trans (hb γ hγ) (he.symm hab)), x, hx, ?_⟩
    exact he.trans (x := x) (y := (l : ℤ_[l]) ^ cL X l N w • b) hxb (hs _ _ _ (he.symm hab))
  · rintro a ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩
    obtain ⟨-, -, -, -, -, -, -, h, -⟩ := sApi Ω ε X l n
    exact ⟨⟨t, pm_down X l w n t ht, h _ _ hat⟩, fun γ hγ => h _ _ (ha γ hγ), x, hx,
      h x ((l : ℤ_[l]) ^ cL X l N w • a) hxa⟩
  · intro a
    obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := sApi Ω ε X l n
    exact ⟨⟨0, (Pm X l w 0).zero_mem, h _ _⟩, fun γ _ => h _ _, 0, zero_mem _, h 0 ((l : ℤ_[l]) ^ cL X l N w • a)⟩

end UpperTheory.V.Z.Kato.Nb.InverseLimitApi

theorem UpperTheory.V.Z.Kato.Nb.sInvApi :
    UpperTheory.V.Z.Kato.Nb.SInvApi :=
  UpperTheory.V.Z.Kato.Nb.InverseLimitApi.main

end
end
