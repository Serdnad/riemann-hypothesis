module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Mathlib.Algebra.Module.Lattice.Full
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle095
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped Classical

namespace GlobalTheory.LoopVol

theorem measurePreserving_affine {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (hM : M.det = 1) (b : ι → ℂ) :
    MeasurePreserving (fun c : ι → ℂ => M *ᵥ c + b) volume volume := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' M).restrictScalars ℝ
  have hdet : LinearMap.det f = 1 := by
    simp only [f, LinearMap.det_restrictScalars, LinearMap.det_toLin', hM, map_one]
  have hfun : (f : (ι → ℂ) → ι → ℂ) = fun c => M *ᵥ c := by
    funext c
    simp [f, Matrix.toLin'_apply]
  have hlin : MeasurePreserving (fun c : ι → ℂ => M *ᵥ c) volume volume := by
    rw [← hfun]
    refine ⟨(LinearMap.continuous_of_finiteDimensional f).measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  exact (measurePreserving_add_right volume b).comp hlin

variable {N : ℕ}

theorem ofRoots_eq (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2) (c : R → ℂ) (i j : Fin N) :
    ofRoots R c i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j + ∑ q : R, if q.1 = (i, j) then c q else 0 := by
  simp only [ofRoots]
  by_cases h : (i, j) ∈ R
  · rw [dite_eq_left h, Matrix.one_apply_ne (hR _ h).ne, zero_add, Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro h'
      exact hq (Subtype.ext h')
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [dite_eq_right h, Finset.sum_eq_zero, add_zero, Matrix.one_apply]
    intro q _
    rw [if_neg]
    intro h'
    apply h
    rw [← h']
    exact q.2

theorem det_two_sided (R : Finset (Fin N × Fin N)) (a b : Matrix (Fin N) (Fin N) ℂ) (ha : IsUpUni a)
    (hb : IsUpUni b) : (Matrix.of fun q q' : R => a q.1.1 q'.1.1 * b q'.1.2 q.1.2).det = 1 := by
  let key : R → Fin N ×ₗ (Fin N)ᵒᵈ := fun q => toLex (q.1.1, OrderDual.toDual q.1.2)
  have hinj : Function.Injective key := by
    intro x y h
    simp only [key, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  let e := Equiv.ofInjective key hinj
  rw [← Matrix.det_reindex_self e, Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, (ha _ _).2 rfl,
      (hb _ _).2 rfl, mul_one]
  · intro i j hlt
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
    have hk : key (e.symm j) < key (e.symm i) := by
      simp only [e, Equiv.apply_ofInjective_symm]
      exact hlt
    simp only [key, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual] at hk
    rcases hk with h1 | ⟨-, h2⟩
    · rw [(ha _ _).1 h1, zero_mul]
    · rw [(hb _ _).1 h2, mul_zero]

theorem measurePreserving_mul (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2)
    (a b : Matrix (Fin N) (Fin N) ℂ) (ha : IsUpUni a) (hb : IsUpUni b) :
    MeasurePreserving (fun (c : R → ℂ) (q : R) => (a * ofRoots R c * b) q.1.1 q.1.2) volume volume := by
  have hent : ∀ (c : R → ℂ) (x y : Fin N),
      (a * ofRoots R c * b) x y = ∑ q : R, a x q.1.1 * b q.1.2 y * c q + (a * b) x y := by
    intro c x y
    have hO : ofRoots R c = 1 + ∑ q : R, c q • Matrix.of (fun i j => if q.1 = (i, j) then (1 : ℂ) else 0) := by
      ext i j
      rw [ofRoots_eq R hR c i j, Matrix.add_apply, Matrix.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [hO, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.add_apply, add_comm, Finset.mul_sum,
      Finset.sum_mul, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_comm (c q)]
    congr 1
    simp [Matrix.mul_apply, Prod.ext_iff, ite_and]
  have h := measurePreserving_affine (Matrix.of fun q q' : R => a q.1.1 q'.1.1 * b q'.1.2 q.1.2)
    (det_two_sided R a b ha hb) (fun q : R => (a * b) q.1.1 q.1.2)
  convert h using 1
  funext c q
  simp only [hent, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]

theorem measurePreserving_mul_pi {ι : Type*} [Fintype ι] (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2)
    (a b : ι → Matrix (Fin N) (Fin N) ℂ) (ha : ∀ v, IsUpUni (a v)) (hb : ∀ v, IsUpUni (b v)) :
    MeasurePreserving (fun (c : ι → R → ℂ) (v : ι) (q : R) => (a v * ofRoots R (c v) * b v) q.1.1 q.1.2)
      volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume) fun v =>
    measurePreserving_mul R hR (a v) (b v) (ha v) (hb v)

end GlobalTheory.LoopVol

end
end

section

open Formalism.BasicNotions GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG.DuWinThree

theorem star_pow {a G : ℝ} (ha : 0 < a) (hG : 0 < G) {n : ℕ} (hn : 0 < n) :
    (a ^ ((1 : ℝ) / n) * G ^ (-(2 : ℝ) / n)) ^ n = a / G ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [mul_pow, ← Real.rpow_natCast (a ^ _), ← Real.rpow_natCast (G ^ _), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hG.le, div_mul_cancel₀ _ hn', div_mul_cancel₀ _ hn', Real.rpow_one,
    Real.rpow_neg hG.le, div_eq_mul_inv]
  norm_num

theorem window {S T : ℝ} {f k : ℕ} (hS : 0 < S) (hT : 2 ≤ T) (hf : 1 ≤ f) (hfk : f ≤ k)
    (h1 : S ≤ T) (h2 : T ≤ (1 + 1 / ((f * k : ℕ) : ℝ)) * S) :
    S ^ (f * k) / 2 ≤ (T ^ k - 1) ^ f ∧ (T ^ k - 1) ^ f ≤ 3 * S ^ (f * k) := by
  have hk2 : 2 * k ≤ 2 ^ k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : j < 2 ^ j := Nat.lt_two_pow_self
    rw [pow_succ]; omega
  have hTk : (2 * f : ℝ) ≤ T ^ k := by
    calc (2 * f : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (by omega : 2 * f ≤ 2 ^ k)
      _ ≤ T ^ k := pow_le_pow_left₀ (by norm_num) hT k
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hP : 0 < T ^ k := by linarith
  have hpow : (T ^ k) ^ f = T ^ (f * k) := by rw [← pow_mul, mul_comm]
  constructor
  · have e : T ^ k - 1 = T ^ k * (1 + (-(1 / T ^ k))) := by field_simp; ring
    have hsm : 1 / T ^ k ≤ 1 := by rw [div_le_one hP]; linarith
    have hb := one_add_mul_le_pow (a := -(1 / T ^ k)) (by linarith) f
    have hc : (f : ℝ) * (1 / T ^ k) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hP]; linarith
    have hd : S ^ (f * k) ≤ T ^ (f * k) := pow_le_pow_left₀ hS.le h1 _
    have hTn : 0 ≤ T ^ (f * k) := by positivity
    rw [e, mul_pow, hpow]
    calc S ^ (f * k) / 2 ≤ T ^ (f * k) * (1 / 2) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hTn
  · have hn : 0 < f * k := Nat.mul_pos hf (by omega)
    have hn' : (0 : ℝ) < ((f * k : ℕ) : ℝ) := by exact_mod_cast hn
    have he : (1 + 1 / ((f * k : ℕ) : ℝ)) ^ (f * k) ≤ 3 := by
      have h3 : 1 + 1 / ((f * k : ℕ) : ℝ) ≤ Real.exp (1 / ((f * k : ℕ) : ℝ)) := by
        have := Real.add_one_le_exp (1 / ((f * k : ℕ) : ℝ)); linarith
      calc _ ≤ Real.exp (1 / ((f * k : ℕ) : ℝ)) ^ (f * k) := pow_le_pow_left₀ (by positivity) h3 _
        _ = Real.exp 1 := by rw [← Real.exp_nat_mul, mul_one_div_cancel hn'.ne']
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    calc (T ^ k - 1) ^ f ≤ (T ^ k) ^ f := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = T ^ (f * k) := hpow
      _ ≤ ((1 + 1 / ((f * k : ℕ) : ℝ)) * S) ^ (f * k) := pow_le_pow_left₀ (by linarith) h2 _
      _ ≤ 3 * S ^ (f * k) := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right he (by positivity)

end GlobalTheory.Diag.PG.DuWinThree

namespace GlobalTheory.Diag.PG

open GlobalTheory.Diag.PG.DuWinThree

theorem duWin_three_of_count : ∀ D : D7, (∀ u, (D.duS u : ℝ) = ((D.mem u).A.duStar : ℝ) *
    (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) → DuWin D 3 := by
  intro D h u
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < (D.mem u).A.Dstar := (D.mem u).A.Dstar_pos
  have hd : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  have hT : 2 ≤ (D.mem u).A.T := (D.mem u).A.T_prime.two_le
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hf : 1 ≤ D.R.f := le_trans (by have := D.R.two_le_m; omega) (D.R.m_le_f : D.R.m ≤ D.R.f)
  have hn : 0 < D.R.f * D.R.k := Nat.mul_pos hf (by omega)
  have hS : 0 < (D.mem u).A.Tstar := by
    unfold ColumnsAtT.Tstar ColumnsAtT.Xu
    positivity
  have hSn : (D.mem u).A.Tstar ^ (D.R.f * D.R.k) =
      (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 := by
    rw [← star_pow (div_pos hD hd) hG hn, ColumnsAtT.Tstar, ColumnsAtT.Xu, Nat.cast_mul]
  obtain ⟨w1, w2⟩ := D.T_win u
  obtain ⟨a, b⟩ := window hS (by exact_mod_cast hT) hf hfk w1 (by rw [Nat.cast_mul]; exact w2)
  rw [hSn] at a b
  rw [h u, ← D.Dstar_eq u]
  set X := (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f
  have hG2 : (D.mem u).A.GamP ^ (-2 : ℤ) = 1 / (D.mem u).A.GamP ^ 2 := by
    rw [zpow_neg, one_div]; norm_cast
  rw [hG2]
  set c := (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 with hcdef
  have hc0 : 0 < c := by positivity
  have e : 1 / (D.mem u).A.GamP ^ 2 * (D.mem u).A.Dstar = ((D.mem u).A.duStar : ℝ) * c := by
    rw [hcdef]; field_simp
  rw [e]
  constructor
  · have := mul_le_mul_of_nonneg_left a hd.le
    nlinarith
  · have := mul_le_mul_of_nonneg_left b hd.le
    nlinarith

end GlobalTheory.Diag.PG
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧ (S.St ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.K0 ≠ 0 ∧ ∀ h ∈ S.St, S.mu (h • Λ) = S.mu Λ) ∧ ∀ C, S.IsCls C → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 ∧ (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 ∧ 1 ≤ S.wC C ∧ ∀ h ∈ S.St, S.wC (h • C) = S.wC C := by
  first | exact @GlobalTheory.HL.volSt | exact GlobalTheory.HL.volSt | (intros; apply GlobalTheory.HL.volSt <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_mem_St_approximating_local_elements : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, (∀ p, n p ∈ (G.S p).St) → {p | n p ∉ (G.S p).K0}.Finite → ∃ g ∈ G.St, ∀ p g', A.Ext p g g' → (n p)⁻¹ * g' ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
  first | exact @GlobalTheory.HL.StrongSt.strong_approx_stab | exact GlobalTheory.HL.StrongSt.strong_approx_stab | (intros; apply GlobalTheory.HL.StrongSt.strong_approx_stab <;> first | assumption | exact (show Submodule.IsFullLattice _ _ from by assumption).toIsLattice)
end

section

open GlobalTheory.Count Finset

namespace GlobalTheory.Count

theorem layerProd_mul_layerProd (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (G H : ℝ → ℝ) :
    layerProd n f j τ G * layerProd n f j τ H = layerProd n f j τ (fun la => G la * H la) := by
  simp only [layerProd, mul_pow, Finset.prod_mul_distrib]
  ring

private theorem layerProd_const_eq_pow (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (c : ℝ) :
    layerProd n f j τ (fun _ => c) = c ^ (∑ i, ∑ k ∈ univ.filter (fun k => i < k),
      (2 * j i * j k * f + 2 * j i * j k * f) + ∑ i, (2 * j i * (n - 2 * ∑ l, j l) * f + j i ^ 2 * f)) := by
  simp only [layerProd, ← pow_add, Finset.prod_pow_eq_pow_sum]

private theorem layerProd_exponent_le_three_mul_sum_mul (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (hn : 2 * ∑ i, j i ≤ n) :
    ∑ i, ∑ k ∈ univ.filter (fun k => i < k), (2 * j i * j k * f + 2 * j i * j k * f) +
      ∑ i, (2 * j i * (n - 2 * ∑ l, j l) * f + j i ^ 2 * f) ≤ 3 * (∑ i, j i) * n * f := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i, j i := ⟨_, rfl⟩
  rw [← hS] at hn ⊢
  have h1 : ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k ≤ S * S := by
    calc ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k ≤ ∑ i, ∑ k, j i * j k :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = S * S := by rw [hS, Finset.sum_mul_sum]
  have h2 : ∑ i, j i ^ 2 ≤ S * S := by
    calc ∑ i, j i ^ 2 ≤ ∑ i, j i * S := Finset.sum_le_sum fun i _ => by
          rw [sq, hS]
          exact Nat.mul_le_mul_left _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      _ = S * S := by rw [← Finset.sum_mul, hS]
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * S + m := ⟨n - 2 * S, by omega⟩
  have hm : 2 * S + m - 2 * S = m := by omega
  have e1 : ∑ i, ∑ k ∈ univ.filter (fun k => i < k), (2 * j i * j k * f + 2 * j i * j k * f) =
      4 * f * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ i, (2 * j i * m * f + j i ^ 2 * f) = 2 * m * f * S + f * ∑ i, j i ^ 2 := by
    rw [hS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hm, e1, e2]
  nlinarith [Nat.mul_le_mul_left f h1, Nat.mul_le_mul_left f h2, Nat.zero_le (S * m * f)]

theorem layerProd_le_exp (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (G : ℝ → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (hn : 2 * ∑ i, j i ≤ n) (hτ : StrictMono τ) (h01 : ∀ i, 0 < τ i ∧ τ i < 1)
    (hG : ∀ la, 0 < la → la < 1 → 0 ≤ G la ∧ G la ≤ Real.exp x) :
    layerProd n f j τ G ≤ Real.exp (((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * x) := by
  have hpos : ∀ i, 0 < τ i := fun i => (h01 i).1
  have hlt : ∀ i, τ i < 1 := fun i => (h01 i).2
  have hb : ∀ la, 0 < la → la < 1 → ∀ e : ℕ, 0 ≤ G la ^ e ∧ G la ^ e ≤ Real.exp x ^ e :=
    fun la h0 h1 e => ⟨pow_nonneg (hG la h0 h1).1 e, pow_le_pow_left₀ (hG la h0 h1).1 (hG la h0 h1).2 e⟩
  have hr : ∀ i k, i < k → 0 < τ i / τ k ∧ τ i / τ k < 1 :=
    fun i k hik => ⟨div_pos (hpos i) (hpos k), (div_lt_one (hpos k)).2 (hτ hik)⟩
  have hp : ∀ i k, 0 < τ i * τ k ∧ τ i * τ k < 1 := fun i k =>
    ⟨mul_pos (hpos i) (hpos k), by nlinarith [hpos i, hpos k, hlt i, hlt k]⟩
  have hs : ∀ i, 0 < τ i ^ 2 ∧ τ i ^ 2 < 1 := fun i => ⟨pow_pos (hpos i) 2, by nlinarith [hpos i, hlt i]⟩
  have hex : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have key : layerProd n f j τ G ≤ layerProd n f j τ (fun _ => Real.exp x) := by
    simp only [layerProd]
    apply mul_le_mul
    · apply Finset.prod_le_prod₀
      · intro i _
        apply Finset.prod_nonneg
        intro k hk
        have hik := (Finset.mem_filter.1 hk).2
        exact mul_nonneg (hb _ (hr i k hik).1 (hr i k hik).2 _).1 (hb _ (hp i k).1 (hp i k).2 _).1
      · intro i _
        apply Finset.prod_le_prod₀
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          exact mul_nonneg (hb _ (hr i k hik).1 (hr i k hik).2 _).1 (hb _ (hp i k).1 (hp i k).2 _).1
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          exact mul_le_mul (hb _ (hr i k hik).1 (hr i k hik).2 _).2 (hb _ (hp i k).1 (hp i k).2 _).2
            (hb _ (hp i k).1 (hp i k).2 _).1 (pow_nonneg hex _)
    · apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (hb _ (hpos i) (hlt i) _).1 (hb _ (hs i).1 (hs i).2 _).1
      · intro i _
        exact mul_le_mul (hb _ (hpos i) (hlt i) _).2 (hb _ (hs i).1 (hs i).2 _).2
          (hb _ (hs i).1 (hs i).2 _).1 (pow_nonneg hex _)
    · apply Finset.prod_nonneg
      intro i _
      exact mul_nonneg (hb _ (hpos i) (hlt i) _).1 (hb _ (hs i).1 (hs i).2 _).1
    · apply Finset.prod_nonneg
      intro i _
      apply Finset.prod_nonneg
      intro k _
      positivity
  refine key.trans ?_
  rw [layerProd_const_eq_pow, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_right _ hx
  exact_mod_cast layerProd_exponent_le_three_mul_sum_mul n f j hn

private theorem mul_prod_mul_le_prod_of_le_one {a : ℕ} (X : ℝ) (u v : Fin a → ℝ) (hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    (hu : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) :
    X * ∏ i, u i * v i ≤ ∏ i, u i := by
  rw [Finset.prod_mul_distrib]
  have hA : 0 ≤ ∏ i, u i := Finset.prod_nonneg fun i _ => hu i
  have hB0 : 0 ≤ ∏ i, v i := Finset.prod_nonneg fun i _ => hv0 i
  have hB1 : ∏ i, v i ≤ 1 := Finset.prod_le_one₀ (fun i _ => hv0 i) (fun i _ => hv1 i)
  calc X * ((∏ i, u i) * ∏ i, v i) ≤ 1 * ((∏ i, u i) * ∏ i, v i) :=
        mul_le_mul_of_nonneg_right hX1 (mul_nonneg hA hB0)
    _ ≤ ∏ i, u i := by rw [one_mul]; exact mul_le_of_le_one_right hA hB1

theorem layerProd_count_mul_density_le_two :
    ∀ (n f q a : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (de : ℝ), ∑ i, j i ≤ q → 2 * q ≤ n → StrictMono τ →
      (∀ i, 0 < τ i ∧ τ i < 1 / 2) → 0 ≤ de → de * q * n * f ≤ 1 / 100 →
      layerProd n f j τ (fun la => 1 + 12 * de / la) * layerProd n f j τ (fun la => la) ≤ 2 ∧
      layerProd n f j τ (fun la => la) ≤ ∏ i, τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f) := by
  intro n f q a j τ de hq hqn hτ h01 hde hsmall
  have hS2 : 2 * ∑ i, j i ≤ n := by omega
  have hpos : ∀ i, 0 < τ i := fun i => (h01 i).1
  have hlt : ∀ i, τ i < 1 := fun i => by linarith [(h01 i).2]
  constructor
  · rw [layerProd_mul_layerProd]
    have hb := layerProd_le_exp n f j τ (fun la => (1 + 12 * de / la) * la) (12 * de) (by positivity)
      hS2 hτ (fun i => ⟨hpos i, hlt i⟩) (fun la h0 h1 => by
        show 0 ≤ (1 + 12 * de / la) * la ∧ (1 + 12 * de / la) * la ≤ Real.exp (12 * de)
        rw [add_mul, div_mul_cancel₀ _ h0.ne', one_mul]
        exact ⟨by linarith, by linarith [Real.add_one_le_exp (12 * de)]⟩)
    refine hb.trans ?_
    have hnat : 3 * (∑ i, j i) * n * f ≤ 3 * q * n * f := by gcongr
    have hcast : ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) ≤ 3 * q * n * f := by exact_mod_cast hnat
    have hexp : ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de) ≤ 36 / 100 := by
      calc ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de) ≤ (3 * q * n * f : ℝ) * (12 * de) :=
            mul_le_mul_of_nonneg_right hcast (by positivity)
        _ = 36 * (de * q * n * f) := by ring
        _ ≤ 36 / 100 := by linarith
    calc Real.exp (((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de)) ≤ Real.exp (36 / 100) :=
          Real.exp_le_exp.2 hexp
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log (by norm_num)
  · unfold layerProd
    refine mul_prod_mul_le_prod_of_le_one _ (fun i => τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f))
      (fun i => (τ i ^ 2) ^ (j i ^ 2 * f)) ?_ ?_ (fun i => pow_nonneg (hpos i).le _)
      (fun i => pow_nonneg (pow_pos (hpos i) 2).le _) ?_
    · apply Finset.prod_nonneg
      intro i _
      apply Finset.prod_nonneg
      intro k _
      exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
    · apply Finset.prod_le_one₀
      · intro i _
        apply Finset.prod_nonneg
        intro k _
        exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
      · intro i _
        apply Finset.prod_le_one₀
        · intro k _
          exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          have hq1 : τ i / τ k ≤ 1 := ((div_lt_one (hpos k)).2 (hτ hik)).le
          have hp1 : τ i * τ k ≤ 1 := by nlinarith [hpos i, hpos k, hlt i, hlt k]
          exact mul_le_one₀ (pow_le_one₀ (div_pos (hpos i) (hpos k)).le hq1)
            (pow_nonneg (mul_pos (hpos i) (hpos k)).le _) (pow_le_one₀ (mul_pos (hpos i) (hpos k)).le hp1)
    · intro i
      have : τ i ^ 2 ≤ 1 := by nlinarith [hpos i, hlt i]
      exact pow_le_one₀ (pow_pos (hpos i) 2).le this

end GlobalTheory.Count
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf


open scoped Matrix.Norms.L2Operator in
theorem isCompact_closed_inter_opn_le {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ)) (hS : IsClosed S)
    (R : ℝ) : IsCompact {g | g ∈ S ∧ opn g ≤ R} := by

  let e := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
  have hK : IsCompact (e ⁻¹' Metric.closedBall 0 R) :=
    e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hset : {g | g ∈ S ∧ opn g ≤ R} = S ∩ e ⁻¹' Metric.closedBall 0 R := by
    ext g
    simp [opn, e, mem_closedBall_zero_iff]
  rw [hset]
  exact hK.inter_left hS

theorem isCompact_normBounded : ∀ (k r : ℕ) (S : Set (Mat k r)), IsClosedSub k r S →
    ∀ R : ℝ, IsCompact {g | g ∈ S ∧ opn g ≤ R} := by
  intro k r S hS R
  exact isCompact_closed_inter_opn_le S hS.2.1 R

end GlobalTheory.SgInf
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem folner_single_translate : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r))
    (Om : ℕ → Set (Mt k r)), IsFolner S μ Om → ∀ p ∈ S,
    Filter.Tendsto (fun j => μ {s | s ∈ Om j ∧ lmulM p s ∈ Om j} / μ (Om j)) Filter.atTop (nhds 1) := by
  intro k r S μ Om h p hp
  obtain ⟨_, hC⟩ := h
  obtain ⟨Oc, hOc, hlim⟩ := hC {p} isCompact_singleton (Set.singleton_subset_iff.2 hp)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun j => ?_) (fun j => ?_)
  · refine ENNReal.div_le_div_right (measure_mono fun x hx => ?_) _
    exact ⟨(hOc j).2.1 hx, (hOc j).2.2 p rfl x hx⟩
  · exact (ENNReal.div_le_div_right (measure_mono fun x (hx : x ∈ {s | s ∈ Om j ∧ lmulM p s ∈ Om j}) => hx.1) _).trans ENNReal.div_self_le_one

end GlobalTheory.SgInf
end
