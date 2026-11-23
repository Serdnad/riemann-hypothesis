module

public import ReciprocityTheory.SemistableReduction.Bundle010
public import Lemmata.GeneralBFactBisAlt.Imports
public import Lemmata.GeneralBFactSecond.Imports
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import ReciprocityTheory.SemistableReduction.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle007

@[expose] public section

section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Polynomial

theorem unip_conj_pow {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) (n : ℕ) :
    (Q * M * Q⁻¹) ^ n = Q * M ^ n * Q⁻¹ := by
  have hinv : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ)
  have hinv' : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  induction n with
  | zero => simp [hinv']
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc Q * M ^ n * Q⁻¹ * (Q * M * Q⁻¹) = Q * M ^ n * (Q⁻¹ * Q) * M * Q⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = Q * (M ^ n * M) * Q⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem unip_trace_conj {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) :
    (Q * M * Q⁻¹).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ), Matrix.one_mul]

theorem unip_trace_map {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K) :
    (M.map σ).trace = σ M.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem unip_map_pow {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K)
    (n : ℕ) : (M.map σ) ^ n = (M ^ n).map σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, Matrix.map_mul]

theorem unip_trace_aeval_one {K : Type*} [Field K] {r : ℕ} (γ : Matrix (Fin r) (Fin r) K)
    (hγ : ∀ k, k ≤ r → (γ ^ k).trace = r) (P : K[X]) (hP : P.natDegree ≤ r) :
    (aeval γ P).trace = r * P.eval 1 := by
  have hlt : P.natDegree < r + 1 := Nat.lt_succ_of_le hP
  rw [Polynomial.aeval_eq_sum_range' hlt, Matrix.trace_sum, Polynomial.eval_eq_sum_range' hlt,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Matrix.trace_smul, hγ k hk', smul_eq_mul, one_pow, mul_one, mul_comm]

theorem unipotent_holds : UnipotentStatement := by
  intro K _ _ r g γ Q hT hg hQ hA
  set A : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ := fun σ => Q σ * γ.map σ * (Q σ)⁻¹ with hAdef
  have hc : 0 ≤ Real.exp (2 / (3 * (r : ℝ))) := (Real.exp_pos _).le
  have htrA : ∀ σ n, ((A σ) ^ n).trace = σ ((γ ^ n).trace) := by
    intro σ n
    simp only [hAdef]
    rw [unip_conj_pow _ _ (hQ σ), unip_trace_conj _ _ (hQ σ), unip_map_pow, unip_trace_map]
  have htrB : ∀ σ n, n ≤ r → ‖((A σ) ^ n).trace‖ ≤ r * Real.exp (1 / 3) := by
    intro σ n hn
    have hd : ∀ i, ‖((A σ) ^ n) i i‖ ≤ Real.exp (1 / 3) := by
      intro i
      have h1 := unip_diag_sq_le (A σ) _ hc (hA σ) n i
      have h2 : Real.exp (2 / (3 * (r : ℝ))) ^ n ≤ Real.exp (1 / 3) ^ 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        rcases Nat.eq_zero_or_pos r with hr | hr
        · subst hr
          have : n = 0 := by omega
          subst this; norm_num
        · have hr' : (0 : ℝ) < r := by exact_mod_cast hr
          have hn' : (n : ℝ) ≤ r := by exact_mod_cast hn
          calc (n : ℝ) * (2 / (3 * r)) = (2 / 3) * ((n : ℝ) / r) := by field_simp
            _ ≤ (2 / 3) * 1 := by gcongr; exact (div_le_one hr').mpr hn'
            _ = ((2 : ℕ) : ℝ) * (1 / 3) := by norm_num
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp (h1.trans h2)
    calc ‖((A σ) ^ n).trace‖ = ‖∑ i, ((A σ) ^ n) i i‖ := rfl
      _ ≤ ∑ i, ‖((A σ) ^ n) i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin r, Real.exp (1 / 3) := Finset.sum_le_sum (fun i _ => hd i)
      _ = r * Real.exp (1 / 3) := by simp
  have hT1 : ∀ n, 1 ≤ n → n ≤ r → (γ ^ n).trace = r := by
    intro n h1 h2
    obtain ⟨z, hz⟩ := hT n h1 h2
    by_cases hz0 : z = 0
    · rw [hz0] at hz
      simp only [map_zero, mul_zero] at hz
      exact sub_eq_zero.mp (by simpa using hz)
    · exfalso
      obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hz0
      have e1 : σ ((γ ^ n).trace - r) = (g : ℂ) * σ z := by rw [hz, map_mul, map_natCast]
      rw [map_sub, map_natCast, ← htrA σ n] at e1
      have hn1 : ‖((A σ) ^ n).trace - r‖ ≤ r * Real.exp (1 / 3) + r := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_natCast]
        linarith [htrB σ n h2]
      rw [e1, norm_mul, Complex.norm_natCast] at hn1
      have : (g : ℝ) ≤ g * ‖σ z‖ := le_mul_of_one_le_right (Nat.cast_nonneg _) hσ
      nlinarith
  have hTall : ∀ k, k ≤ r → (γ ^ k).trace = r := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp [Matrix.trace_one]
    · exact hT1 k h hk
  have hN : ∀ k, 1 ≤ k → k ≤ r → ((γ - 1) ^ k).trace = 0 := by
    intro k h1 h2
    have := unip_trace_aeval_one γ hTall ((X - C 1) ^ k)
      (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]; exact h2)
    simp only [map_pow, map_sub, aeval_X, map_one, eval_pow, eval_sub, eval_X, eval_one,
      sub_self] at this
    rw [this, zero_pow (by omega : k ≠ 0), mul_zero]
  refine ⟨unip_pow_card_eq_zero (γ - 1) hN, fun σ => ?_⟩
  have hinv' : Q σ * (Q σ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hQ σ))
  have heq : Q σ * (γ.map σ - 1) * (Q σ)⁻¹ = A σ - 1 := by
    simp only [hAdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv']
  rw [heq, unip_hs_sub_one]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have htr1 : (A σ).trace = r := by
    have h7 := htrA σ 1
    rw [pow_one] at h7
    rw [h7, hT1 1 le_rfl hr, map_natCast]
  rw [htr1, Complex.natCast_re]
  have h5 := unip_hs_le (A σ) _ (hA σ)
  have h6 := unip_exp_bound r hr
  nlinarith

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

namespace DegAdd

open NumberField

theorem exists_int_smul_mem_span {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (v : Fin n → Fin r → K) {x : Fin r → K} (hx : x ∈ Submodule.span K (Set.range v)) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range v) := by
  first | exact Bl.general_b_fact_bis_other.goal1 .. | (apply Bl.general_b_fact_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_other.goal1 <;> assumption)

theorem relIndex_ne_zero_of_fg {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : L.FG) (v : Fin n → Fin r → K)
    (hv : ∀ x ∈ L, x ∈ Submodule.span K (Set.range v)) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
  set N := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.addSubgroupOf L.toAddSubgroup
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  let f : L →+ (L.toAddSubgroup ⧸ N) :=
    { toFun := fun x => QuotientAddGroup.mk (⟨x.1, x.2⟩ : L.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : Module.Finite ℤ (L.toAddSubgroup ⧸ N) := by
    refine Module.Finite.of_surjective f.toIntLinearMap ?_
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨⟨y, hy⟩, rfl⟩
  have : Finite (L.toAddSubgroup ⧸ N) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨d, hd, hdy⟩ := exists_int_smul_mem_span v (hv y hy)
    refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
    change (d • (QuotientAddGroup.mk (⟨y, hy⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸ N)) = 0
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hdy
  exact AddSubgroup.index_ne_zero_of_finite

theorem range_fin_append {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Set.range (Fin.append b c) = Set.range b ∪ Set.range c := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, (Fin.append_left b c i).symm⟩
    | right j => exact Or.inr ⟨j, (Fin.append_right b c j).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd m i, Fin.append_left b c i⟩
    · exact ⟨Fin.natAdd k j, Fin.append_right b c j⟩

theorem fin_append_comp_equiv {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Fin.append b c ∘ finSumFinEquiv = Sum.elim b c := by
  funext i
  cases i <;> simp

theorem indep_parts {K : Type} [Field K] {r k m : ℕ}
    {b : Fin k → Fin r → K} {c : Fin m → Fin r → K} (h : LinearIndependent K (Fin.append b c)) :
    LinearIndependent K b ∧ LinearIndependent K c ∧
      Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c)) := by
  have h2 := h.comp finSumFinEquiv finSumFinEquiv.injective
  rw [fin_append_comp_equiv] at h2
  have h3 := linearIndependent_sum.mp h2
  simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr] using h3

theorem index_split {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hb : ∀ i, b i ∈ L) (hc : ∀ j, c j ∈ L)
    (hdis : Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c))) :
    (Submodule.span (𝓞 K) (Set.range (Fin.append b c))).toAddSubgroup.relIndex L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex (satSub L b).toAddSubgroup *
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
        L.toAddSubgroup := by
  set Sb := Submodule.span (𝓞 K) (Set.range b)
  set Sc := Submodule.span (𝓞 K) (Set.range c)
  set S := satSub L b
  have hA : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) = Sb ⊔ Sc := by
    rw [range_fin_append, Submodule.span_union]
  have hSbS : Sb ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨hb i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hScL : Sc ≤ L := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hc j
  have hSL : S ≤ L := inf_le_left
  have hmeet : ∀ x, x ∈ Sb ⊔ Sc → x ∈ S → x ∈ Sb := by
    intro x hx1 hx2
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx1
    have hyK : y ∈ Submodule.span K (Set.range b) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hy
    have hzK : z ∈ Submodule.span K (Set.range c) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hz
    have hxK : y + z ∈ Submodule.span K (Set.range b) := hx2.2
    have hz' : z ∈ Submodule.span K (Set.range b) := by
      have h := Submodule.sub_mem _ hxK hyK
      simpa using h
    have hz0 : z = 0 := Submodule.disjoint_def.mp hdis z hz' hzK
    simpa [hz0] using hy
  have hinf : (Sb ⊔ Sc).toAddSubgroup ⊓ S.toAddSubgroup = Sb.toAddSubgroup := by
    ext x
    constructor
    · intro h
      exact hmeet x (AddSubgroup.mem_inf.mp h).1 (AddSubgroup.mem_inf.mp h).2
    · intro h
      exact AddSubgroup.mem_inf.mpr ⟨(le_sup_left : Sb ≤ Sb ⊔ Sc) h, hSbS h⟩
  have key : (Sb ⊔ Sc).toAddSubgroup.relIndex (S ⊔ Sc).toAddSubgroup =
      Sb.toAddSubgroup.relIndex S.toAddSubgroup := by
    have hsup : (S ⊔ Sc).toAddSubgroup = S.toAddSubgroup ⊔ (Sb ⊔ Sc).toAddSubgroup := by
      rw [← Submodule.sup_toAddSubgroup, ← sup_assoc, sup_eq_left.mpr hSbS]
    rw [hsup, AddSubgroup.relIndex_sup_right, ← hinf, AddSubgroup.inf_relIndex_right]
  have le1 : (Sb ⊔ Sc).toAddSubgroup ≤ (S ⊔ Sc).toAddSubgroup :=
    fun x hx => (sup_le_sup_right hSbS Sc) hx
  have le2 : (S ⊔ Sc).toAddSubgroup ≤ L.toAddSubgroup := fun x hx => (sup_le hSL hScL) hx
  rw [hA, ← AddSubgroup.relIndex_mul_relIndex _ _ _ le1 le2, key]

end DegAdd

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Module

theorem sc_scale {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (x : Fin r → K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ L := by
  first | exact Bl.general_b_fact_second.goal1 .. | (apply Bl.general_b_fact_second.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second.goal1 <;> assumption)

theorem sc_li_scale {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] {v : ι → V}
    (hv : LinearIndependent K v) (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    LinearIndependent K (fun i => a i • v i) := by
  have := hv.units_smul (fun i => Units.mk0 (a i) (ha i))
  convert this using 1
  funext i
  simp [Units.smul_def]

theorem sc_kerfam {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (N : Matrix (Fin r) (Fin r) K) :
    ∃ b : Fin (finrank K (LinearMap.ker N.mulVecLin)) → Fin r → K,
      (∀ i, b i ∈ L) ∧ (∀ i, N *ᵥ b i = 0) ∧ LinearIndependent K b ∧
      ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b) := by
  set b0 := Module.finBasis K (LinearMap.ker N.mulVecLin)
  choose d hd0 hdL using fun i => sc_scale L hL (b0 i : Fin r → K)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have ha : ∀ i, algebraMap (𝓞 K) K (d i) ≠ 0 := fun i h =>
    hd0 i (hinj (by rw [h, map_zero]))
  refine ⟨fun i => algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K), fun i => ?_, fun i => ?_, ?_, ?_⟩
  · show algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K) ∈ L
    rw [algebraMap_smul]; exact hdL i
  · have h := (b0 i).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    rw [mulVec_smul, h, smul_zero]
  · exact sc_li_scale (b0.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha
  · intro y hy
    have hy' : y ∈ LinearMap.ker N.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hy
    have hsum := b0.sum_repr ⟨y, hy'⟩
    have hsum' : y = ∑ i, b0.repr ⟨y, hy'⟩ i • (b0 i : Fin r → K) := by
      calc y = ((⟨y, hy'⟩ : LinearMap.ker N.mulVecLin) : Fin r → K) := rfl
        _ = ((∑ i, b0.repr ⟨y, hy'⟩ i • b0 i : LinearMap.ker N.mulVecLin) : Fin r → K) := by
          rw [hsum]
        _ = _ := by rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
    rw [hsum']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hb : (b0 i : Fin r → K) =
        (algebraMap (𝓞 K) K (d i))⁻¹ • (algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K)) := by
      rw [inv_smul_smul₀ (ha i)]
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem sc_imfam {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (N : Matrix (Fin r) (Fin r) K) :
    ∃ c : Fin (finrank K (LinearMap.range N.mulVecLin)) → Fin r → K,
      (∀ j, c j ∈ L) ∧ LinearIndependent K (fun j => N *ᵥ c j) := by
  set e := Module.finBasis K (LinearMap.range N.mulVecLin)
  have hex : ∀ j, ∃ y, N *ᵥ y = (e j : Fin r → K) := by
    intro j
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (e j).2
    exact ⟨y, by rw [← Matrix.mulVecLin_apply]; exact hy⟩
  choose y hy using hex
  choose d hd0 hdL using fun j => sc_scale L hL (y j)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have ha : ∀ j, algebraMap (𝓞 K) K (d j) ≠ 0 := fun j h =>
    hd0 j (hinj (by rw [h, map_zero]))
  refine ⟨fun j => algebraMap (𝓞 K) K (d j) • y j, fun j => ?_, ?_⟩
  · show algebraMap (𝓞 K) K (d j) • y j ∈ L
    rw [algebraMap_smul]; exact hdL j
  · have := sc_li_scale (e.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha
    have heq : (fun j => N *ᵥ (algebraMap (𝓞 K) K (d j) • y j)) = fun j =>
        algebraMap (𝓞 K) K (d j) • ((LinearMap.range N.mulVecLin).subtype ∘ e) j := by
      funext j; simp [mulVec_smul, hy]
    rw [heq]; exact this

theorem sc_append_li {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hbN : ∀ i, N *ᵥ b i = 0) (hb : LinearIndependent K b)
    (hc : LinearIndependent K (fun j => N *ᵥ c j)) : LinearIndependent K (Fin.append b c) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  have h1 : ∑ j, g (Fin.natAdd k j) • (N *ᵥ c j) = 0 := by
    have := congrArg N.mulVecLin hg

    simpa [map_add (f := _), map_sum, map_smul, Matrix.mulVecLin_apply, hbN] using this
  have hc0 := Fintype.linearIndependent_iff.mp hc _ h1
  have hb0 : ∀ i, g (Fin.castAdd m i) = 0 := by
    apply Fintype.linearIndependent_iff.mp hb
    simpa [hc0] using hg
  intro i
  exact Fin.addCases (fun i => hb0 i) (fun j => hc0 j) i

theorem sc_rank_pos {K : Type} [Field K] [NumberField K] {r : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (hN : N ≠ 0) : 0 < finrank K (LinearMap.range N.mulVecLin) := by
  refine Nat.pos_of_ne_zero fun h0 => hN ?_
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have := LinearMap.toMatrix'_toLin' N
  rw [Matrix.toLin'_apply', h0, map_zero] at this
  exact this.symm

theorem sc_index {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (N : Matrix (Fin r) (Fin r) K)
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) (hcL : ∀ j, c j ∈ L)
    (hbN : ∀ i, N *ᵥ b i = 0) (hker : ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b)) :
    (Submodule.span (𝓞 K) (Set.range fun j => N *ᵥ c j)).toAddSubgroup.relIndex
        (L.map (N.mulVecLin.restrictScalars (𝓞 K))).toAddSubgroup =
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex L.toAddSubgroup := by
  set f := N.mulVecLin.restrictScalars (𝓞 K) with hf
  have hfx : ∀ x, f x = N *ᵥ x := fun x => rfl
  have hspanb : Submodule.span K (Set.range b) ≤ LinearMap.ker N.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [hbN i]
  have hspanc : Submodule.span (𝓞 K) (Set.range c) ≤
      (Submodule.span (𝓞 K) (Set.range fun j => N *ᵥ c j)).comap f := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨j, (hfx (c j)).symm⟩
  rw [Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.inf_relIndex_right (AddSubgroup.comap _ _),
    ← AddSubgroup.inf_relIndex_right (Submodule.toAddSubgroup _)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup,
    AddMonoidHom.coe_coe]
  constructor
  · rintro ⟨hx, hxL⟩
    refine ⟨?_, hxL⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_range_iff_exists_fun (𝓞 K) |>.mp hx
    set z := ∑ j, a j • c j with hz
    have hzc : z ∈ Submodule.span (𝓞 K) (Set.range c) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hzL : z ∈ L := Submodule.sum_mem _ fun j _ => L.smul_mem _ (hcL j)
    have hfz : f (x - z) = 0 := by

      rw [map_sub, hz, map_sum]
      simp only [map_smul]
      simp only [hfx] at ha ⊢
      rw [ha, sub_self]
    have hsat : x - z ∈ satSub L b := by
      refine ⟨L.sub_mem hxL hzL, ?_⟩
      exact hker _ (by rw [← hfx]; exact hfz)
    exact Submodule.mem_sup.mpr ⟨x - z, hsat, z, hzc, sub_add_cancel x z⟩
  · rintro ⟨hx, hxL⟩
    refine ⟨?_, hxL⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hy0 : f y = 0 := by
      have h := hspanb hy.2
      rw [LinearMap.mem_ker] at h
      exact h
    rw [map_add (f := _), hy0, zero_add]
    exact hspanc hz

end ReciprocityTheory.MultiplicativeHeights
end
