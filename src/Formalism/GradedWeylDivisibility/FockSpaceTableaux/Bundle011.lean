module

import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle006
public import Formalism.GradedWeylDivisibility.Bundle001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle008
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle007
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle009
public import Formalism.GradedWeylDivisibility.StatementD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Interval
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

section

open MvPolynomial
open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

private lemma pairW_apply {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) (b : Fin r)
    (t : Fin n) :
    pairW l j v (b, t) = if v.2 = j then (if (v.1, l) = (b, t) then 1 else 0)
      else (if v = (b, t) then 1 else 0) := by
  classical
  unfold pairW
  split_ifs <;> simp_all [Finsupp.single_apply]

theorem lcplead_weight_apply {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (d : Fin r × Fin n →₀ ℕ)
    (b : Fin r) (t : Fin n) :
    Finsupp.weight (pairW l j) d (b, t) =
      if t = l then d (b, l) + d (b, j) else if t = j then 0 else d (b, t) := by
  apply Formalism.GradedWeylDivisibility.lcpeel_weight_apply <;> assumption

section
variable {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n}

theorem lcplead_hom_row (hlj : l ≠ j) {ω : Fin r × Fin n →₀ ℕ} {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (b : Fin r) : m (b, l) + m (b, j) = ω (b, l) := by
  rw [← hg (mem_support_iff.mp hm), lcplead_weight_apply l j hlj m b l, if_pos rfl]

theorem lcplead_hom_off (hlj : l ≠ j) {ω : Fin r × Fin n →₀ ℕ} {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (b : Fin r) (t : Fin n) (htl : t ≠ l) (htj : t ≠ j) : m (b, t) = ω (b, t) := by
  rw [← hg (mem_support_iff.mp hm), lcplead_weight_apply l j hlj m b t, if_neg htl, if_neg htj]

private lemma support_eq_of_pairW_homogeneous_of_erase_eq (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m m' : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (hm' : m' ∈ g.support) (h1 : m' (a0, l) = m (a0, l))
    (h2 : (m'.erase (a0, l)).erase (a0, j) = (m.erase (a0, l)).erase (a0, j)) : m' = m := by
  ext v
  by_cases hv1 : v = (a0, l)
  · rw [hv1, h1]
  by_cases hv2 : v = (a0, j)
  · have e1 := lcplead_hom_row hlj hg hm a0
    have e2 := lcplead_hom_row hlj hg hm' a0
    rw [hv2]; omega
  have := congrArg (fun f => f v) h2
  simpa [Finsupp.erase_ne hv1, Finsupp.erase_ne hv2] using this

theorem lcplead_coeff_peel (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support) :
    AddMonoidAlgebra.coeff (peel l j a0 (m (a0, l)) g) ((m.erase (a0, l)).erase (a0, j)) = AddMonoidAlgebra.coeff g m := by
  classical
  unfold peel
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro m' hm' hne
    rw [Finset.mem_filter] at hm'
    rw [if_neg]
    intro heq
    exact hne (support_eq_of_pairW_homogeneous_of_erase_eq hlj a0 hg hm hm'.1 hm'.2 heq)
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨hm, rfl⟩)).elim

theorem lcplead_mem_support_peel (a0 : Fin r) (k : ℕ) {g : MvPolynomial (Fin r × Fin n) B}
    {p : Fin r × Fin n →₀ ℕ} (hp : p ∈ (peel l j a0 k g).support) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ p = (m.erase (a0, l)).erase (a0, j) := by
  classical
  unfold peel at hp
  obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hp)
  rw [Finset.mem_filter] at hm
  exact ⟨m, hm.1, hm.2, Finset.mem_singleton.mp (support_monomial_subset hpm)⟩

theorem lcplead_recon (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support) :
    m = Finsupp.single (a0, l) (m (a0, l)) + Finsupp.single (a0, j) (ω (a0, l) - m (a0, l)) +
      (m.erase (a0, l)).erase (a0, j) := by
  have h := lcplead_hom_row hlj hg hm a0
  have hne : ((a0, l) : Fin r × Fin n) ≠ (a0, j) := by simp [hlj]
  ext v
  simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply]
  by_cases h1 : v = (a0, l)
  · subst h1; simp [hne, Ne.symm hlj]
  · by_cases h2 : v = (a0, j)
    · subst h2; simp [hne]; omega
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

end

theorem lcplead_cmIdx_val {r n : ℕ} (b : Fin r) (t : Fin n) :
    ((cmIdx r n (b, t) : Fin (n * r)) : ℕ) = b + r * t := by
  simp [cmIdx, finProdFinEquiv]

theorem lcplead_cmIdx_lt {r n : ℕ} {b a0 : Fin r} {t l : Fin n}
    (h : cmIdx r n (b, t) < cmIdx r n (a0, l)) : t < l ∨ (t = l ∧ b < a0) := by
  have h' : (b : ℕ) + r * t < a0 + r * l := by
    have := Fin.lt_def.mp h
    rwa [lcplead_cmIdx_val, lcplead_cmIdx_val] at this
  rcases lt_trichotomy (t : ℕ) l with h1 | h1 | h1
  · exact Or.inl (Fin.lt_def.mpr h1)
  · refine Or.inr ⟨Fin.ext h1, Fin.lt_def.mpr ?_⟩
    rw [h1] at h'
    exact Nat.lt_of_add_lt_add_right h'
  · exfalso
    have h2 := Nat.mul_le_mul_left r (show (l : ℕ) + 1 ≤ t from h1)
    have h3 := a0.isLt
    rw [Nat.mul_add, mul_one] at h2
    omega

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem componentDegree : CompDeg := by
  intro B _ r n l j ω s f hf
  rw [← lccomp_component_colAddGen]
  exact (lccomp_degreeOf_component_le _ _ _ _).trans hf

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem isWeightedHomogeneous_of_map_of_injective {R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Injective φ) {σ M : Type*} [AddCommMonoid M] {w : σ → M}
    {m : M} {f : MvPolynomial σ R} (hf : IsWeightedHomogeneous w (map φ f) m) :
    IsWeightedHomogeneous w f m := by
  intro d hd
  apply hf
  rw [MvPolynomial.coeff_map]
  intro h0
  exact hd (hφ (h0.trans (map_zero φ).symm))

theorem dualWeylModuleIntRat : DualWeylIntRat := by
  intro r n ν f
  have hφ : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  constructor
  · exact dualWeylModuleMap ℤ ℚ (Int.castRingHom ℚ) r n ν f
  · intro h
    rw [lsat_mem_dualWeyl] at h ⊢
    obtain ⟨hw, hc⟩ := h
    refine ⟨isWeightedHomogeneous_of_map_of_injective hφ hw, ?_⟩
    intro l j hlj
    apply MvPolynomial.map_injective (f := Int.castRingHom ℚ) hφ
    rw [lsat_map_colAddGen, MvPolynomial.map_rename]
    exact hc l j hlj

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

def LFocks_rowMat {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ :=
  fun v w => if v.2 = w.2 then g v.1 w.1 else 0

lemma LFocks_rowAct_eq_sub {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    rowAct ℂ (n := n) g = sub (LFocks_rowMat g) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, sub, aeval_X, LFocks_rowMat]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single v.2]
  · simp
  · intro s _ hs; simp [Ne.symm hs]
  · simp

lemma LFocks_rowMat_conjTranspose {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    (LFocks_rowMat (n := n) g).conjTranspose = LFocks_rowMat g.conjTranspose := by
  ext v w
  simp only [Matrix.conjTranspose_apply, LFocks_rowMat]
  by_cases h : v.2 = w.2
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

theorem fischerInnerRowActionAdjoint : FockRowAdj := by
  intro r n g f h
  rw [LFocks_rowAct_eq_sub, LFocks_rowAct_eq_sub, LFocks_subAdj, LFocks_rowMat_conjTranspose]

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem ldbasis_ssIdx_subset_Iic (k n : ℕ) (ν : Fin n → ℕ) :
    ssIdx k n ν ⊆ Set.Iic (Finsupp.equivFunOnFinite.symm (fun v : Fin k × Fin n => ν v.2)) := by
  intro m hm
  simp only [ssIdx, Set.mem_setOf_eq] at hm
  rw [Set.mem_Iic]
  intro v
  obtain ⟨a, t⟩ := v
  show m (a, t) ≤ ν t
  rw [← hm.2 t]
  exact Finset.single_le_sum (f := fun a' => m (a', t)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem semistandard_index_finite : SSIdxFinite := by
  intro k n ν
  exact (Set.finite_Iic _).subset (ldbasis_ssIdx_subset_Iic k n ν)

end Formalism.GradedWeylDivisibility
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma ldlat_rowAct_one {R : Type*} [CommRing R] {k n : ℕ} :
    rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [rowAct, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1 (fun b _ hb => by simp [Matrix.one_apply_ne (Ne.symm hb)]) (by simp)]
  simp

lemma ldlat_rowAct_inv_left (h : RowActMul) {K : Type} [Field K] {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (x : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g (rowAct K g⁻¹ x) = x := by
  rw [← AlgHom.comp_apply, h K k n g g⁻¹, Matrix.nonsing_inv_mul g hg, ldlat_rowAct_one, AlgHom.id_apply]

lemma ldlat_rowAct_inv_right (h : RowActMul) {K : Type} [Field K] {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (x : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g⁻¹ (rowAct K g x) = x := by
  rw [← AlgHom.comp_apply, h K k n g⁻¹ g, Matrix.mul_nonsing_inv g hg, ldlat_rowAct_one, AlgHom.id_apply]

lemma ldlat_map_bidet {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ}
    (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show (map φ : MvPolynomial (Fin r × Fin n) R → _) = ((map φ : MvPolynomial _ R →+* MvPolynomial _ S)) from rfl,
    RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

lemma ldlat_isWH_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {σ M : Type*}
    [AddCommMonoid M] {w : σ → M} {f : MvPolynomial σ R} {μ : M}
    (hf : IsWeightedHomogeneous w f μ) : IsWeightedHomogeneous w (map φ f) μ := by
  intro m hm
  apply hf
  intro h0
  apply hm
  rw [coeff_map, h0, map_zero]

lemma ldlat_linInd_field {F K : Type*} [Field F] [Field K] [Algebra F K] {σ ι : Type*}
    {v : ι → MvPolynomial σ F} (hv : LinearIndependent F v) :
    LinearIndependent K (fun i => map (algebraMap F K) (v i)) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hsum i hi
  let B := Module.Free.chooseBasis F K
  apply B.ext_elem
  intro j
  have key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0 := by
    ext m
    have h1 := congrArg (AddMonoidAlgebra.coeff · m) hsum
    simp only [coeff_sum, AddMonoidAlgebra.coeff_smul_apply, coeff_map, smul_eq_mul] at h1 ⊢
    change _ = 0 at h1 ⊢
    have h2 := congrArg (fun x => B.repr x j) h1

    simp only [map_sum, map_zero, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero,
    Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have := hv s (fun i => B.repr (c i) j) key i hi
  simpa using this

lemma ldlat_linInd_base {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) {σ ι : Type*} {b : ι → MvPolynomial σ R}
    (hb : LinearIndependent R b) : LinearIndependent K (fun i => map (algebraMap R K) (b i)) := by
  letI : Algebra (FractionRing R) K := (IsFractionRing.lift hinj).toAlgebra
  have h1 : LinearIndependent R (fun i => map (algebraMap R (FractionRing R)) (b i)) := by
    have := hb.map' (mapAlgHom (Algebra.ofId R (FractionRing R))).toLinearMap (by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      exact map_injective _ (IsFractionRing.injective R (FractionRing R)) hxy)
    exact this
  have h2 : LinearIndependent (FractionRing R) (fun i => map (algebraMap R (FractionRing R)) (b i)) :=
    (LinearIndependent.iff_fractionRing R (FractionRing R)).mp h1
  have h3 := ldlat_linInd_field (K := K) h2
  have hc : (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)) = algebraMap R K := by
    ext r
    simp [RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]
  convert h3 using 2 with i
  rw [map_map, hc]

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem ldbasis_linearIndependent {σ R ι : Type*} [CommRing R] (o : MonomialOrder σ)
    (v : ι → MvPolynomial σ R) (hinj : Function.Injective fun i => o.degree (v i))
    (hlc : ∀ i, o.leadingCoeff (v i) = 1) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have htne : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨j, hj, hjmax⟩ :=
    (s.filter fun j => g j ≠ 0).exists_max_image (fun j => o.toSyn (o.degree (v j))) htne
  have hcoeff := congrArg (AddMonoidAlgebra.coeff · (o.degree (v j))) hsum
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, MvPolynomial.coeff_sum,
    Finset.sum_eq_single j] at hcoeff
  · rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at hcoeff
    have hone : (v j).coeff (o.degree (v j)) = 1 := hlc j
    rw [hone, mul_one] at hcoeff
    exact (Finset.mem_filter.mp hj).2 hcoeff
  · intro k hk hkj
    rw [AddMonoidAlgebra.coeff_smul_apply]
    by_cases hgk : g k = 0
    · rw [hgk, zero_smul]
    · have hle := hjmax k (Finset.mem_filter.mpr ⟨hk, hgk⟩)
      have hne : o.degree (v k) ≠ o.degree (v j) := fun h => hkj (hinj h)
      have hlt : o.toSyn (o.degree (v k)) < o.toSyn (o.degree (v j)) :=
        lt_of_le_of_ne hle (fun h => hne (o.toSyn.injective h))
      rw [o.coeff_eq_zero_of_lt hlt, smul_zero]
  · intro hj'
    exact absurd (Finset.mem_filter.mp hj).1 hj'

theorem ldbasis_sum_single_perm {r s : ℕ} (I : Fin s → Fin r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (I (σ q)) 1 : Fin r → ℕ)) = ∑ p : Fin s, Pi.single (I p) 1 := by
  exact Equiv.sum_comp σ (fun p => (Pi.single (I p) 1 : Fin r → ℕ))

theorem ldbasis_initMinor_rowHom (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (initMinor R (n := n) I hs) (∑ p : Fin s, Pi.single (I p) 1) := by
  unfold initMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hprod : IsWeightedHomogeneous (rowW r n)
      (∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (∑ p, Pi.single (I p) 1) := by
    rw [← ldbasis_sum_single_perm I σ]
    exact IsWeightedHomogeneous.prod _ _ _ (fun i _ => isWeightedHomogeneous_X R (rowW r n) _)
  intro d hd
  apply hprod
  intro h0
  apply hd
  show AddMonoidAlgebra.coeff ((Equiv.Perm.sign σ) •
    ∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)) d = 0
  rw [Units.smul_def, AddMonoidAlgebra.coeff_smul_apply, h0, smul_zero]

theorem ldbasis_bidet_rowHom (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    IsWeightedHomogeneous (rowW r n) (bideterminant R sz hsz I)
      (∑ k : Fin K, ∑ p : Fin (sz k), Pi.single (I k p) 1) := by
  unfold bideterminant
  exact IsWeightedHomogeneous.prod _ _ _ (fun k _ => ldbasis_initMinor_rowHom R (I k) (hsz k))

theorem ldbasis_rowWt_bidetExp {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    rowWt (bidetExp sz hsz I) = ∑ k : Fin K, ∑ p : Fin (sz k), (Pi.single (I k p) 1 : Fin r → ℕ) := by
  classical
  funext a
  simp only [rowWt, rowDeg, bidetExp, Finsupp.finsetSum_apply, Finset.sum_apply,
    Finsupp.single_apply, Pi.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : I k p = a
  · subst h
    simp [Prod.ext_iff]
  · simp [Prod.ext_iff, h, Ne.symm h]

end Formalism.GradedWeylDivisibility
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_action_mul : RowActMul := by
  intro R _ k n g h
  apply MvPolynomial.algHom_ext
  intro v

  simp only [AlgHom.comp_apply, rowAct, aeval_X, map_sum, map_mul, aeval_C, Matrix.mul_apply,
  MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end Formalism.GradedWeylDivisibility
end
end
