module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.QRDecomp


open Matrix in
open scoped ComplexOrder in
theorem _root_.GlobalTheory.QRDecomp.exists_qr (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    ∃ (Q : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ),
      Qᴴ * Q = 1 ∧ u.BlockTriangular id ∧ IsUnit u.det ∧ A = Q * u := by
  classical
  have hinj : Function.Injective A.mulVec := by
    intro v w h
    have h2 : (Aᴴ * A) *ᵥ v = (Aᴴ * A) *ᵥ w := by rw [← mulVec_mulVec, ← mulVec_mulVec, h]
    exact (mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hA)) h2
  have hS : (Aᴴ * A).PosDef := PosDef.conjTranspose_mul_self A hinj
  set L := LDL.lowerInv hS
  set d := LDL.diagEntries hS
  haveI : Invertible L := LDL.invertibleLowerInv hS
  have hLu : IsUnit L.det := isUnit_det_of_invertible L
  have hD : diagonal d = L * (Aᴴ * A) * Lᴴ := LDL.diag_eq_lowerInv_conj hS
  have hDpos : (diagonal d).PosDef := by
    rw [hD]
    exact hS.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hLu))
  have hd : ∀ i, 0 < d i := fun i => by simpa using hDpos.diag_pos (i := i)
  have hdre : ∀ i, d i = ((d i).re : ℂ) ∧ 0 < (d i).re := fun i => by
    have h := hd i
    rw [Complex.pos_iff] at h
    exact ⟨Complex.ext (by simp) (by simp [h.2]), h.1⟩
  let r : Fin m → ℂ := fun i => ((Real.sqrt (d i).re : ℝ) : ℂ)
  have hr0 : ∀ i, r i ≠ 0 := fun i => by
    simp only [r, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (hdre i).2).ne'
  have hrr : ∀ i, star (r i) * r i = d i := fun i => by
    simp only [r, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hdre i).2.le, ← (hdre i).1]
  have hLt : Lᴴ.BlockTriangular id := fun i j hij => by
    have h : LDL.lowerInv hS j i = 0 := LDL.isLowerTriangular_lowerInv hS hij
    simp [conjTranspose_apply, L, h]
  refine ⟨A * Lᴴ * diagonal (fun i => (r i)⁻¹), diagonal r * (Lᴴ)⁻¹, ?_, ?_, ?_, ?_⟩
  · have h1 : (A * Lᴴ * diagonal fun i => (r i)⁻¹)ᴴ * (A * Lᴴ * diagonal fun i => (r i)⁻¹)
        = (diagonal fun i => star (r i)⁻¹) * (L * (Aᴴ * A) * Lᴴ) * diagonal fun i => (r i)⁻¹ := by
      simp only [conjTranspose_mul, diagonal_conjTranspose, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rfl
    rw [h1, ← hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← hrr i]
    have h0 := hr0 i
    have h0' : star (r i) ≠ 0 := star_ne_zero.mpr h0
    rw [star_inv₀]
    field_simp
  · exact (blockTriangular_diagonal r).mul (blockTriangular_inv_of_blockTriangular hLt)
  · rw [det_mul, det_diagonal]
    exact (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hr0 i)).mul
      (isUnit_nonsing_inv_det _ (isUnit_det_of_invertible Lᴴ))
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    have h1 : (fun i => (r i)⁻¹ * r i) = fun _ => (1 : ℂ) :=
      funext fun i => inv_mul_cancel₀ (hr0 i)
    rw [h1, diagonal_one, Matrix.one_mul, mul_inv_of_invertible, Matrix.mul_one]

end GlobalTheory.QRDecomp
end

section

open Module

namespace GlobalTheory

section Subgroups

variable {M : Type*} [AddCommGroup M]

theorem exists_ker_eq_of_index_prime {p : ℕ} (hp : p.Prime) (H : AddSubgroup M)
    (hH : H.index = p) : ∃ f : M →ₗ[ℤ] ZMod p, f.toAddMonoidHom.ker = H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have e : (M ⧸ H) ≃+ ZMod p := addEquivOfPrimeCardEq (p := p) hH (Nat.card_zmod p)
  refine ⟨(e.toAddMonoidHom.comp (QuotientAddGroup.mk' H)).toIntLinearMap, ?_⟩
  ext x
  simp [AddMonoidHom.mem_ker]

theorem encard_setOf_index_prime_le [Module.Free ℤ M] [Module.Finite ℤ M] {p : ℕ}
    (hp : p.Prime) :
    {H : AddSubgroup M | H.index = p}.encard ≤ ((p ^ finrank ℤ M : ℕ) : ℕ∞) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let b := Module.finBasis ℤ M
  let φ : (Fin (finrank ℤ M) → ZMod p) → AddSubgroup M :=
    fun w => (b.constr ℤ w).toAddMonoidHom.ker
  have hsub : {H : AddSubgroup M | H.index = p} ⊆ φ '' Set.univ := by
    intro H hH
    obtain ⟨f, hf⟩ := exists_ker_eq_of_index_prime hp H hH
    refine ⟨(b.constr ℤ).symm f, Set.mem_univ _, ?_⟩
    simp only [φ, LinearEquiv.apply_symm_apply]
    exact hf
  refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
  simp

theorem exists_le_relIndex_eq_prime {p : ℕ} (hp : p.Prime) (H : AddSubgroup M)
    (h0 : H.index ≠ 0) (hd : p ∣ H.index) :
    ∃ K : AddSubgroup M, H ≤ K ∧ H.relIndex K = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : H.FiniteIndex := ⟨h0⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := M ⧸ H) p hd
  refine ⟨(AddSubgroup.zmultiples x).comap (QuotientAddGroup.mk' H), ?_, ?_⟩
  · intro y hy
    simp only [AddSubgroup.mem_comap, QuotientAddGroup.mk'_apply]
    rw [(QuotientAddGroup.eq_zero_iff y).2 hy]
    exact zero_mem _
  · have h1 : H = (⊥ : AddSubgroup (M ⧸ H)).comap (QuotientAddGroup.mk' H) := by
      ext y; simp
    have h2 := AddSubgroup.relIndex_comap (⊥ : AddSubgroup (M ⧸ H)) (QuotientAddGroup.mk' H)
      ((AddSubgroup.zmultiples x).comap (QuotientAddGroup.mk' H))
    rw [← h1, AddSubgroup.map_comap_eq_self_of_surjective (QuotientAddGroup.mk'_surjective H),
      AddSubgroup.relIndex_bot_left, Nat.card_zmultiples, hx] at h2
    exact h2

theorem encard_biUnion_le_mul {α β : Type*} (s : Set α) (t : α → Set β) (a b : ℕ)
    (hs : s.encard ≤ a) (ht : ∀ i ∈ s, (t i).encard ≤ b) :
    (⋃ i ∈ s, t i).encard ≤ ((a * b : ℕ) : ℕ∞) := by
  have hfin : s.Finite := Set.finite_of_encard_le_coe hs
  have key : (⋃ i ∈ s, t i).encard ≤ s.encard * b := by
    clear hs
    induction s, hfin using Set.Finite.induction_on with
    | empty => simp
    | @insert i s hi _ ih =>
      rw [Set.biUnion_insert, Set.encard_insert_of_notMem hi, add_mul, one_mul, add_comm]
      exact (Set.encard_union_le _ _).trans (add_le_add (ht i (Set.mem_insert _ _))
        (ih fun j hj => ht j (Set.mem_insert_of_mem _ hj)))
  refine key.trans ?_
  push_cast
  gcongr

theorem setOf_le_relIndex_eq_image (K : AddSubgroup M) (m : ℕ) :
    {H : AddSubgroup M | H ≤ K ∧ H.relIndex K = m} =
      (fun H' : AddSubgroup K => H'.map K.subtype) '' {H' | H'.index = m} := by
  ext H
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨H.addSubgroupOf K, h2, by simp [AddSubgroup.addSubgroupOf_map_subtype, h1]⟩
  · rintro ⟨H', h, rfl⟩
    refine ⟨AddSubgroup.map_subtype_le _, ?_⟩
    rw [AddSubgroup.relIndex, AddSubgroup.addSubgroupOf,
      AddSubgroup.comap_map_eq_self_of_injective K.subtype_injective]
    exact h

theorem encard_setOf_index_eq_le [Module.Free ℤ M] [Module.Finite ℤ M] {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H.index = m}.encard ≤ ((m ^ finrank ℤ M : ℕ) : ℕ∞) := by
  induction m using induction_on_primes with
  | zero => exact absurd rfl hm
  | one =>
    have : {H : AddSubgroup M | H.index = 1} = {⊤} := by ext H; simp
    simp [this]
  | prime_mul p a hp ih =>
    have ha : a ≠ 0 := fun h => hm (by simp [h])
    have hsub : {H : AddSubgroup M | H.index = p * a} ⊆
        ⋃ K ∈ {K : AddSubgroup M | K.index = a}, {H | H ≤ K ∧ H.relIndex K = p} := by
      intro H hH
      have hH' : H.index = p * a := hH
      obtain ⟨K, hK, hr⟩ := exists_le_relIndex_eq_prime hp H (hH' ▸ hm) (hH' ▸ dvd_mul_right _ _)
      have := AddSubgroup.relIndex_mul_index hK
      rw [hr, hH'] at this
      exact Set.mem_biUnion (x := K) (Nat.eq_of_mul_eq_mul_left hp.pos this) ⟨hK, hr⟩
    refine (Set.encard_le_encard hsub).trans
      ((encard_biUnion_le_mul _ _ _ (p ^ finrank ℤ M) (ih ha) ?_).trans ?_)
    · intro K _
      rw [setOf_le_relIndex_eq_image]
      refine (Set.encard_image_le _ _).trans ?_
      haveI : Module.Finite ℤ K := inferInstanceAs (Module.Finite ℤ K.toIntSubmodule)
      haveI : Module.Free ℤ K := inferInstanceAs (Module.Free ℤ K.toIntSubmodule)
      refine (encard_setOf_index_prime_le hp).trans ?_
      have : finrank ℤ K ≤ finrank ℤ M := Submodule.finrank_le K.toIntSubmodule
      exact_mod_cast Nat.pow_le_pow_right hp.pos this
    · rw [mul_pow, mul_comm]

theorem encard_setOf_le_relIndex_eq_le (K : AddSubgroup M) [Module.Free ℤ K] [Module.Finite ℤ K]
    {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H ≤ K ∧ H.relIndex K = m}.encard ≤ ((m ^ finrank ℤ K : ℕ) : ℕ∞) := by
  rw [setOf_le_relIndex_eq_image]
  exact (Set.encard_image_le _ _).trans (encard_setOf_index_eq_le hm)

theorem encard_setOf_submodule_le_relIndex_eq_le {R : Type*} [Ring R] [Module R M]
    (L : Submodule R M) [Module.Free ℤ L] [Module.Finite ℤ L] {m : ℕ} (hm : m ≠ 0) :
    {H : Submodule R M | H ≤ L ∧ H.toAddSubgroup.relIndex L.toAddSubgroup = m}.encard ≤
      ((m ^ finrank ℤ L : ℕ) : ℕ∞) := by
  haveI : Module.Free ℤ L.toAddSubgroup := inferInstanceAs (Module.Free ℤ L)
  haveI : Module.Finite ℤ L.toAddSubgroup := inferInstanceAs (Module.Finite ℤ L)
  refine le_trans ?_ (encard_setOf_le_relIndex_eq_le L.toAddSubgroup hm)
  refine Set.encard_le_encard_of_injOn (f := Submodule.toAddSubgroup) ?_
    Submodule.toAddSubgroup_injective.injOn
  rintro H ⟨h1, h2⟩
  exact ⟨h1, h2⟩

end Subgroups

section DeterminedMaps

open MeasureTheory Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end DeterminedMaps

end GlobalTheory
end

section

open MeasureTheory Real Set Filter Topology
open scoped ENNReal Nat

namespace GlobalTheory.FlagVolume

theorem lintegral_radial {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹) =
      ENNReal.ofReal ((2 * (m + 1) * A ^ (m + 1))⁻¹) := by
  have hd : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹)
      (r * ((A + r ^ 2) ^ (m + 2))⁻¹) r := by
    intro r _
    have hp : 0 < A + r ^ 2 := by positivity
    have h1 : HasDerivAt (fun r : ℝ ↦ A + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add A
    have h2 := ((h1.pow (m + 1)).const_mul (2 * ((m : ℝ) + 1))).fun_inv
      (show 2 * ((m : ℝ) + 1) * (A + r ^ 2) ^ (m + 1) ≠ 0 by positivity)
    refine h2.fun_neg.congr_deriv ?_
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((A + r ^ 2) ^ (m + 2))⁻¹ := fun r hr ↦ by
    have : 0 < r := hr
    positivity
  have hl : Tendsto (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹) atTop (𝓝 0) := by
    rw [← neg_zero]
    refine Tendsto.neg (Tendsto.inv_tendsto_atTop ?_)
    refine Tendsto.const_mul_atTop (by change (0 : ℝ) < 2 * ((m : ℝ) + 1); positivity) ?_
    exact (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp
      (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_deriv_of_nonneg' hd hnn hl)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hnn)),
    integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn hl]
  simp

theorem lintegral_complex_inv_pow {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (m + 2))⁻¹) =
      ENNReal.ofReal (π / (m + 1) * (A ^ (m + 1))⁻¹) := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 •
      ENNReal.ofReal (((A + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ENNReal.ofReal (p.1 * ((A + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ ↦ (1 : ℝ≥0∞)) p.2 := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp ↦ ?_
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_mul (le_of_lt hp.1)]
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ ↦ ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹))
      (g := fun _ : ℝ ↦ (1 : ℝ≥0∞)) (by fun_prop) (by fun_prop), lintegral_radial hA]
  simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

theorem lintegral_fin_succ {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y = ∫⁻ z : ℂ, ∫⁻ w : Fin n → ℂ, f (Fin.cons z w) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm
  rw [← h.lintegral_comp hf, Measure.volume_eq_prod, lintegral_prod
    (fun a ↦ f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm a))
    (hf.comp h.measurable).aemeasurable]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem lintegral_pi_inv_pow (n : ℕ) : ∀ (m : ℕ) {A : ℝ}, 0 < A →
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((A + ∑ k, ‖z k‖ ^ 2) ^ (m + n + 1))⁻¹) =
      ENNReal.ofReal (π ^ n * m ! / (m + n)! * (A ^ (m + 1))⁻¹) := by
  induction n with
  | zero =>
    intro m A hA
    have : (m ! : ℝ) ≠ 0 := by positivity
    simp [volume_pi, this]
  | succ n ih =>
    intro m A hA
    rw [lintegral_fin_succ (by fun_prop)]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← add_assoc]
    have h : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ,
        ENNReal.ofReal (((A + ‖z‖ ^ 2 + ∑ k, ‖w k‖ ^ 2) ^ (m + n + 1 + 1))⁻¹) =
        ENNReal.ofReal (π ^ n * (m + 1)! / (m + 1 + n)!) *
          ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (m + 2))⁻¹) := fun z ↦ by
      rw [← ENNReal.ofReal_mul (by positivity), ← ih (m + 1) (by positivity),
        show m + 1 + n = m + n + 1 by ring]
    simp only [h]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_complex_inv_pow hA,
      ← ENNReal.ofReal_mul (by positivity), show m + 1 + n = m + n + 1 by ring,
      Nat.factorial_succ m]
    congr 1
    push_cast
    field_simp
    ring

theorem lintegral_comp_vecMul {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℂ)
    (hR : R.det ≠ 0) {f : (n → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ b, f b = ENNReal.ofReal (‖R.det‖ ^ 2) * ∫⁻ y, f (Matrix.vecMul y R) := by
  let T : (n → ℂ) →ₗ[ℝ] (n → ℂ) := (Matrix.toLin' R.transpose).restrictScalars ℝ
  have hT : LinearMap.det T = ‖R.det‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hp : 0 < ‖R.det‖ ^ 2 := by positivity
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (n → ℂ))
    (f := T) (hT ▸ hp.ne')
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have h1 : ∫⁻ y, f (Matrix.vecMul y R) = ∫⁻ y, f (T y) := by
    simp [T, Matrix.mulVec_transpose]
  rw [h1, ← lintegral_map hf hTm, hmap, lintegral_smul_measure, hT, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hp.le, abs_of_pos (inv_pos.2 hp), mul_inv_cancel₀ hp.ne']
  simp

end GlobalTheory.FlagVolume
end
