module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamTotalDifferentialOneFunctionPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.OrdCalc

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem vne (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≠ 0 := (map_ne_zero v.1).2 hx

theorem ord_mul (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul (vne v hx) (vne v hy)]; ring

theorem ord_zpow (v : Place k F) (x : F) (m : ℤ) : ord v (x ^ m) = m * ord v x := by
  unfold ord
  rw [map_zpow₀, WithZero.log_zpow]; simp [smul_eq_mul]

theorem le_one_iff (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x ≤ 1 ↔ 0 ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) one_ne_zero, WithZero.log_one, neg_nonneg]

theorem le_iff (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) (vne v hy), neg_le_neg_iff]

theorem eq_one_iff (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x = 1 ↔ ord v x = 0 := by
  have h1 := WithZero.log_le_log (vne v hx) (one_ne_zero (α := WithZero (Multiplicative ℤ)))
  have h2 := WithZero.log_le_log (one_ne_zero (α := WithZero (Multiplicative ℤ))) (vne v hx)
  rw [WithZero.log_one] at h1 h2
  unfold ord
  constructor
  · intro h; rw [h, WithZero.log_one]; simp
  · intro h
    exact le_antisymm (h1.1 (by omega)) (h2.1 (by omega))

theorem exists_unif (v : Place k F) : ∃ π : F, π ≠ 0 ∧ ord v π = 1 := by
  obtain ⟨π, hπ⟩ := v.2.1 (WithZero.exp (-1 : ℤ))
  refine ⟨π, ?_, ?_⟩
  · rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  · unfold ord; rw [hπ, WithZero.log_exp]; simp

theorem nrm_max (v : Place k F) (n : ℕ) (x : Fin n → F) (hx : x ≠ 0) :
    ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hx
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i0, Finset.mem_univ _⟩ (fun i => v.1 (x i))
  have hle : ∀ j, v.1 (x j) ≤ v.1 (x i) := fun j => by
    rw [← hi]; exact Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j)
  refine ⟨i, ?_, hi, ?_, hle⟩
  · intro h0
    have := hle i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  · unfold ordVec ord nrm; rw [hi]

theorem nrm_smul (v : Place k F) (n : ℕ) (x : Fin n → F) (c : F) :
    nrm v (c • x) = v.1 c * nrm v x := by
  unfold nrm
  apply le_antisymm
  · apply Finset.sup_le; intro i _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_mul' le_rfl (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ i))
  · rcases isEmpty_or_nonempty (Fin n) with h | h
    · simp [Finset.univ_eq_empty]
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => v.1 (x i))
      rw [hi]
      calc v.1 c * v.1 (x i) = v.1 ((c • x) i) := by simp
      _ ≤ _ := Finset.le_sup (f := fun i => v.1 ((c • x) i)) (Finset.mem_univ i)

theorem nrm_mulVec_le (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : nrm v (u.mulVec x) ≤ nrm v x := by
  unfold nrm
  apply Finset.sup_le; intro i _
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (u i j) * v.1 (x j) ≤ 1 * Finset.univ.sup (fun i => v.1 (x i)) :=
        mul_le_mul' (hu i j) (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j))
  _ = _ := one_mul _

theorem mul_int (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) (hu' : ∀ i j, v.1 (u' i j) ≤ 1) : ∀ i j, v.1 ((u * u') i j) ≤ 1 := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro l _
  rw [map_mul]
  calc v.1 (u i l) * v.1 (u' l j) ≤ 1 * 1 := mul_le_mul' (hu i l) (hu' l j)
  _ = 1 := one_mul _

theorem det_adj_int (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : v.1 u.det ≤ 1 ∧ ∀ i j, v.1 (u.adjugate i j) ≤ 1 := by
  let M : Matrix (Fin n) (Fin n) v.O := fun i j => ⟨u i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu i j)⟩
  have hM : M.map v.O.subtype = u := by ext i j; rfl
  constructor
  · have e : u.det = ((M.det : v.O) : F) := by
      rw [← hM]; exact (RingHom.map_det v.O.subtype M).symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.det).2
  · intro i j
    have e : u.adjugate i j = ((M.adjugate i j : v.O) : F) := by
      rw [← hM]
      have := congrFun (congrFun (RingHom.map_adjugate v.O.subtype M) i) j
      exact this.symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.adjugate i j).2

theorem unimod_mul_inv (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : Unimod v u) (hu' : Unimod v u') : Unimod v (u * u') ∧ Unimod v u⁻¹ := by
  refine ⟨⟨mul_int v n u u' hu.1 hu'.1, by rw [Matrix.det_mul, map_mul, hu.2, hu'.2, one_mul]⟩, ?_⟩
  have hd : u.det ≠ 0 := fun h => by have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hu.2, inv_one, one_mul]
    exact (det_adj_int v n u hu.1).2 i j
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hu.2, inv_one]

theorem nrm_unimod (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : Unimod v u) : nrm v (u.mulVec x) = nrm v x := by
  have hd : IsUnit u.det := isUnit_iff_ne_zero.2 (fun h => by
    have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this)
  apply le_antisymm (nrm_mulVec_le v n u x hu.1)
  have h := nrm_mulVec_le v n u⁻¹ (u.mulVec x) (unimod_mul_inv v n u u hu hu).2.1
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul u hd, Matrix.one_mulVec] at h

end GlobalTheory.Nef.OrdCalc

open GlobalTheory.Nef.OrdCalc in
theorem GlobalTheory.Nef.ord_calculus : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ v : Place k F, (∀ x y : F, x ≠ 0 → y ≠ 0 → ord v (x * y) = ord v x + ord v y) ∧ (∀ x : F, x ≠ 0 → ∀ m : ℤ, ord v (x ^ m) = m * ord v x) ∧ (∀ x : F, x ≠ 0 → (v.1 x ≤ 1 ↔ 0 ≤ ord v x)) ∧ (∀ x : F, x ≠ 0 → (v.1 x = 1 ↔ ord v x = 0)) ∧ (∀ x y : F, x ≠ 0 → y ≠ 0 → (v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x)) ∧ (∃ π : F, π ≠ 0 ∧ ord v π = 1) ∧ (∀ (n : ℕ) (x : Fin n → F), x ≠ 0 → ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i)) ∧ (∀ (n : ℕ) (x : Fin n → F) (c : F), nrm v (c • x) = v.1 c * nrm v x) ∧ (∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F), Unimod v u → nrm v (u.mulVec x) = nrm v x) ∧ (∀ (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F), Unimod v u → Unimod v u' → Unimod v (u * u') ∧ Unimod v u⁻¹) := by
  intro k F _ _ _ v
  exact ⟨fun x y hx hy => ord_mul v x y hx hy, fun x _ m => ord_zpow v x m,
    fun x hx => le_one_iff v x hx, fun x hx => eq_one_iff v x hx, fun x y hx hy => le_iff v x y hx hy,
    exists_unif v, fun n x hx => nrm_max v n x hx, fun n x c => nrm_smul v n x c,
    fun n u x hu => nrm_unimod v n u x hu, fun n u u' hu hu' => unimod_mul_inv v n u u' hu hu'⟩
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open PowerSeries Finset

theorem hankelInt_sumLemma {F : Type} [Field F] (E Q : PowerSeries F) (n : ℕ) (i : Fin (n + 1)) (s : ℕ) :
    ∑ l : Fin (n + 1), (if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0) * coeff ((l : ℕ) + s) Q =
      coeff ((i : ℕ) + s) ((trunc ((i : ℕ) + 1) E : PowerSeries F) * Q) := by
  have hi : (i : ℕ) + 1 ≤ n + 1 := by omega
  rw [Fin.sum_univ_eq_sum_range (fun l => (if l ≤ (i : ℕ) then coeff ((i : ℕ) - l) E else 0) * coeff (l + s) Q) (n + 1)]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hf : (range (n + 1)).filter (fun l => l ≤ (i : ℕ)) = range ((i : ℕ) + 1) := by
    ext l; simp only [mem_filter, mem_range]; omega
  rw [hf, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a (trunc ((i : ℕ) + 1) E : PowerSeries F) * coeff b Q)]
  simp only [Polynomial.coeff_coe, coeff_trunc, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hg : (range ((i : ℕ) + s).succ).filter (fun a => a < (i : ℕ) + 1) = range ((i : ℕ) + 1) := by
    ext l; simp only [mem_filter, mem_range, Nat.succ_eq_add_one]; omega
  rw [hg, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  rw [show (i : ℕ) - ((i : ℕ) + 1 - 1 - l) = l by omega, show (i : ℕ) + 1 - 1 - l + s = (i : ℕ) + s - l by omega]

theorem hankel_integral : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  intro O F _ _ ι e ψ φ n h
  set E := PowerSeries.map ι e with hE
  set P : ℕ → PowerSeries F := fun i => (trunc (i + 1) E : PowerSeries F) with hP
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) O := Matrix.of fun i j =>
    coeff ((i : ℕ) + j) ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i l =>
    if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0
  let H : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j => coeff ((i : ℕ) + j) φ
  have hmapP : ∀ k, PowerSeries.map ι (trunc k e : PowerSeries O) = (trunc k E : PowerSeries F) := by
    intro k; ext m; simp only [hE, coeff_map, Polynomial.coeff_coe, coeff_trunc]; split_ifs <;> simp
  have hX : ∀ i : ℕ, X ^ (i + 1) ∣ E - P i := by
    intro i; rw [X_pow_dvd_iff]; intro m hm
    simp [hP, Polynomial.coeff_coe, coeff_trunc, hm]
  have hdiv : ∀ i j : ℕ, coeff (i + j) ((E - P i) * (E - P j) * φ) = 0 := by
    intro i j
    have h3 : X ^ (i + 1 + (j + 1)) ∣ (E - P i) * (E - P j) * φ := by
      rw [pow_add]; exact Dvd.dvd.mul_right (mul_dvd_mul (hX i) (hX j)) φ
    exact X_pow_dvd_iff.mp h3 _ (by omega)
  have hent : N.map ι = T * H * T.transpose := by
    ext i j
    have inner : ∀ l : Fin (n + 1), ∑ m, H l m * T.transpose m j = coeff ((l : ℕ) + j) (P j * φ) := by
      intro l
      rw [Nat.add_comm (l : ℕ) (j : ℕ)]
      refine Eq.trans ?_ (hankelInt_sumLemma E φ n j l)
      refine sum_congr rfl fun m _ => ?_
      simp only [H, T, Matrix.of_apply, Matrix.transpose_apply]; rw [mul_comm, add_comm (l : ℕ)]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.mul_apply, inner]
    rw [show (∑ x, T i x * coeff ((x : ℕ) + j) (P j * φ)) = coeff ((i : ℕ) + j) (P i * (P j * φ)) from hankelInt_sumLemma E (P j * φ) n i j]
    simp only [Matrix.map_apply, N, Matrix.of_apply]
    have key : PowerSeries.map ι ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)
        = P i * (P j * φ) - (E - P i) * (E - P j) * φ := by
      rw [map_sub, map_mul, map_mul, map_sub, hmapP, hmapP, ← h, ← hE]
      simp only [hP]; ring
    rw [← coeff_map, key, map_sub, hdiv, sub_zero]
  have hT : T.det = ι (constantCoeff e) ^ (n + 1) := by
    rw [Matrix.det_of_lowerTriangular T ?_]
    · simp [T, E, Finset.prod_const]
    · intro i j hij
      have hij' : i < j := hij
      have h1 : ¬ j ≤ i := not_le.mpr hij'
      have h2 : ¬ ((j : ℕ) ≤ i) := h1
      simp [T, h1, h2]
  refine ⟨N.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hent, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hT]
  show _ = _ * H.det
  ring

end GlobalTheory.Nef
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.CechDR.FormExtJ

open GlobalTheory.CatCoh

section Inst

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (j : ℕ)

@[reducible] def opModJ : Module Bᵐᵒᵖ (Om R B j) :=
  Module.compHom _ ((RingHom.id B).fromOpposite mul_comm)

attribute [local instance] opModJ

theorem isCentralScalarJ : IsCentralScalar B (Om R B j) := ⟨fun _ _ ↦ rfl⟩

theorem isScalarTowerJ : IsScalarTower R Bᵐᵒᵖ (Om R B j) := ⟨fun r b m ↦ smul_assoc r b.unop m⟩

end Inst

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

def extMapJ {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) (Om R (F.obj T) j) →ₐ[R] TrivSqZeroExt (F.obj T') (Om R (F.obj T') j) where
  toFun c := TrivSqZeroExt.inl (mp F φ c.fst) + TrivSqZeroExt.inr (pOm F j φ c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [pOm_smul]
  commutes' r := by
    ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl']
    · simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_extMapJ {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) :
    (extMapJ F j φ c).fst = mp F φ c.fst := by
  simp [extMapJ]

theorem snd_extMapJ {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) :
    (extMapJ F j φ c).snd = pOm F j φ c.snd := by
  simp [extMapJ]

def omjExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) (Om R (F.obj T) j))
  map φ := CommAlgCat.ofHom (extMapJ F j φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMapJ F j _ c).trans (mp_id F T _)) ((snd_extMapJ F j _ c).trans (pOm_id F _)))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMapJ F j _ c).trans ((mp_comp F φ ψ _).trans (by
      change _ = ((extMapJ F j ψ) (extMapJ F j φ c)).fst
      rw [fst_extMapJ, fst_extMapJ])))
    ((snd_extMapJ F j _ c).trans ((pOm_comp F φ ψ _).trans (by
      change _ = ((extMapJ F j ψ) (extMapJ F j φ c)).snd
      rw [snd_extMapJ, snd_extMapJ]))))

theorem mp_omjExt_inr {T T' : C} (φ : T ⟶ T') (x : Om R (F.obj T) j) :
    mp (omjExt F j) φ (TrivSqZeroExt.inr x : (omjExt F j).obj T) =
      (TrivSqZeroExt.inr (pOm F j φ x) : (omjExt F j).obj T') := by
  change extMapJ F j φ (TrivSqZeroExt.inr x) = _
  exact TrivSqZeroExt.ext ((fst_extMapJ F j φ _).trans (by simp)) ((snd_extMapJ F j φ _).trans (by simp))

theorem snd_mp_omjExt {T T' : C} (φ : T ⟶ T') (c : (omjExt F j).obj T) :
    (mp (omjExt F j) φ c).snd = pOm F j φ c.snd := snd_extMapJ F j φ c

theorem isUnit_mp_omjExt_iff {T S : C} (u : T ⟶ S) (c : (omjExt F j).obj T) :
    IsUnit (mp (omjExt F j) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_extMapJ F j u c)))

theorem span_inlJ_eq_top {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (omjExt F j).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) (Om R (F.obj S) j))) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

end GlobalTheory.CechDR.FormExtJ
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory

theorem cocycle_one_forms_coboundary_of_restrict : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (ω : Ω[F.obj T⁄R]), (∀ t (u : T ⟶ G.obj t), p1 F u ω = 0) → ω = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → Ω[F.obj (G.obj t)⁄R]), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 F (G.map a) (s t u)) → ∃ ω : Ω[F.obj T⁄R], ∀ t u, p1 F u ω = s t u) → ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) → ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T) := by
  intro R _ C _ C' _ F G hSep hGlue κ hκ θ' hθ'
  have key : ∀ T : C, ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t),
      p1 F u ω = θ' t - κ T (G.obj t) u := by
    intro T
    refine hGlue T (fun t u ↦ θ' t - κ T (G.obj t) u) ?_
    intro t t' u a
    simp only [map_sub]
    rw [hκ u (G.map a), hθ' a]
    abel
  choose θ hθ using key
  refine ⟨θ, fun T T' φ ↦ ?_⟩
  have h0 : κ T T' φ - θ T' + p1 F φ (θ T) = 0 := by
    refine hSep T' _ (fun t u ↦ ?_)
    have e1 := hκ φ u
    have e2 := hθ T' t u
    have e3 := hθ T t (φ ≫ u)
    rw [oneFormsMapOfFunctorMorphism_comp] at e3
    simp only [map_add (f := _), map_sub, e2, e3]
    rw [e1]
    abel
  rw [← sub_eq_zero]
  rw [← h0]
  abel

end GlobalTheory
end

section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem AnPer.dw_comap_linear : ∀ {I I' : Type} [Fintype I] [Fintype I'] {g g' : ℕ} {W : Opens (Tot I g)} {W' : Opens (Tot I' g')} (b : (I' → ℂ) → I → ℂ) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ p ∈ W', AnalyticAt ℂ b p.1) → ∀ (hΦ : AnalyticOnNhd ℂ (fun p : Tot I' g' ↦ ((b p.1, M p.2) : Tot I g)) W') (h : ∀ p ∈ W', ((b p.1, M p.2) : Tot I g) ∈ W) (a : Fin g') (f : Hol W), dw a (Hol.comap _ hΦ h f) = ∑ c, M (Pi.single a 1) c • Hol.comap _ hΦ h (dw c f) := by
  intro I I' _ _ g g' W W' b M hb hΦ h a f
  refine Hol.ext_fn fun p hp ↦ ?_
  have e : HasFDerivAt (fun p : Tot I' g' ↦ ((b p.1, M p.2) : Tot I g))
      (((fderiv ℂ b p.1).comp (ContinuousLinearMap.fst ℂ _ _)).prod
        ((LinearMap.toContinuousLinearMap M).comp (ContinuousLinearMap.snd ℂ _ _))) p :=
    ((hb p hp).differentiableAt.hasFDerivAt.comp p hasFDerivAt_fst).prodMk
      ((LinearMap.toContinuousLinearMap M).hasFDerivAt.comp p hasFDerivAt_snd)
  have hv : ((0 : I → ℂ), M (Pi.single a 1)) = ∑ c, M (Pi.single a 1) c • (((0 : I → ℂ), Pi.single c 1) : Tot I g) := by
    ext i
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  change (Hol.der _ (Hol.comap _ hΦ h f)).fn p = _
  rw [Hol.fn_der_comap _ _ _ _ f hp, e.fderiv]
  have e2 : (((fderiv ℂ b p.1).comp (ContinuousLinearMap.fst ℂ _ _)).prod
        ((LinearMap.toContinuousLinearMap M).comp (ContinuousLinearMap.snd ℂ _ _)))
        (((0 : I' → ℂ), Pi.single a 1) : Tot I' g') = ((0 : I → ℂ), M (Pi.single a 1)) := by
    simp

  rw [e2, hv, map_sum, ← Hol.ev_apply p hp, map_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, Hol.ev_apply p hp, Hol.fn_comap _ _ _ _ hp]
  change _ = _ * (Hol.der _ f).fn _
  rw [Hol.fn_der _ _ (h p hp)]

end GlobalTheory
end
end

section

set_option autoImplicit false

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer

theorem Close.comap_linear : ∀ {I I' : Type} [Fintype I] [Fintype I'] {g g' : ℕ} {W : Opens (Tot I g)} {W' : Opens (Tot I' g')} {C : Type} [CommRing C] (J : Ideal C) (ρ₁ ρ₂ : Hol W' →+* C) (ψ : Hol W →+* Hol W') (M : Fin g → Fin g' → ℂ), (∀ a f, dw a (ψ f) = ∑ b, M b a • ψ (dw b f)) → Close J ρ₁ ρ₂ → Close J (ρ₁.comp ψ) (ρ₂.comp ψ) := by
  intro I I' _ _ g g' W W' C _ J ρ₁ ρ₂ ψ M hψ h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail σ τ _ s ih =>
    obtain ⟨n, h1, h2, h3⟩ := s
    refine Relation.ReflTransGen.tail ih
      ⟨fun b ↦ ∑ a, σ (algebraMap ℂ (Hol W') (M b a)) * n a,
        fun b ↦ J.sum_mem fun a _ ↦ J.mul_mem_left _ (h1 a), fun b c ↦ ?_, fun f ↦ ?_⟩
    · rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun a' _ ↦ ?_
      calc σ (algebraMap ℂ (Hol W') (M b a)) * n a * (σ (algebraMap ℂ (Hol W') (M c a')) * n a')
          = σ (algebraMap ℂ (Hol W') (M b a)) * σ (algebraMap ℂ (Hol W') (M c a')) * (n a * n a') := by ring
        _ = 0 := by rw [h2, mul_zero]
    · simp only [RingHom.comp_apply]
      rw [h3 (ψ f)]
      congr 1

      simp_rw [hψ, map_sum, Algebra.smul_def, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
      ring

end GlobalTheory.AnPer
end
