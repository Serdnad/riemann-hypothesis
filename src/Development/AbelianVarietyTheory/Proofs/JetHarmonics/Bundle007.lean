module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Complex.Cardinality

@[expose] public section

section

namespace GlobalTheory

theorem mem_span_prime_of_not_isUnit_of_pow_sub_mem {O : Type} [CommRing O] [IsLocalRing O] (g : ℕ)
    (hg : g.Prime) (y : O) (hy : y ^ g - y ∈ Ideal.span {(g : O)}) (hn : ¬ IsUnit y) :
    y ∈ Ideal.span {(g : O)} := by
  have hm : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal y).mpr hn
  have hpos : 1 ≤ g - 1 := by have := hg.two_le; omega
  have hz : y ^ (g - 1) ∈ IsLocalRing.maximalIdeal O := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hpos
    rw [hk, pow_add, pow_one]
    exact Ideal.mul_mem_right _ _ hm
  obtain ⟨u, hu⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    ((IsLocalRing.mem_maximalIdeal _).mp hz)
  have e : y ^ g = y * y ^ (g - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hg.one_lt.le]
  have hy' : y = -(y ^ g - y) * ↑u⁻¹ := by
    calc y = y * (↑u * ↑u⁻¹) := by simp
      _ = -(y ^ g - y) * ↑u⁻¹ := by rw [hu, e]; ring
  rw [hy']
  exact Ideal.mul_mem_right _ _ (neg_mem hy)

theorem hom_value_congruent_int_mod_prime :
    ∀ (A O : Type) [CommRing A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ (σ : A →+* O) (x : A), (∃ i : ℤ, σ x - (i : O) ∈ Ideal.span {(g : O)}) ∧ (¬ IsUnit (σ x) → σ x ∈ Ideal.span {(g : O)}) := by
  intro A O _ _ _ g hg hgu hA σ x
  have hy : σ x ^ g - σ x ∈ Ideal.span {(g : O)} := by
    have h := Ideal.mem_map_of_mem σ (hA x)
    rw [Ideal.map_span, Set.image_singleton, map_natCast, map_sub, map_pow] at h
    exact h
  refine ⟨?_, fun hn => mem_span_prime_of_not_isUnit_of_pow_sub_mem g hg (σ x) hy hn⟩
  have : Fact g.Prime := ⟨hg⟩
  have : NeZero g := ⟨hg.ne_zero⟩
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hgu
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  have hgk : ((g : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact hgm
  have : CharP (IsLocalRing.ResidueField O) g := (CharP.charP_iff_prime_eq_zero hg).mpr hgk
  have hfix : IsLocalRing.residue O (σ x) ^ g = IsLocalRing.residue O (σ x) := by
    have h := (IsLocalRing.residue_eq_zero_iff _).mpr (hspan hy)
    rwa [map_sub, map_pow, sub_eq_zero] at h
  obtain ⟨a, ha⟩ : ∃ a : ZMod g,
      IsLocalRing.residue O (σ x) = ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O) a := by
    by_contra hno
    simp only [not_exists] at hno
    classical
    have hpoly : (Polynomial.X ^ g - Polynomial.X : Polynomial (IsLocalRing.ResidueField O)) ≠ 0 :=
      Polynomial.X_pow_sub_X_ne_zero hg.one_lt
    have hnot : IsLocalRing.residue O (σ x) ∉
        Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)) := by
      intro h
      obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h
      exact hno b hb.symm
    have hsub : (insert (IsLocalRing.residue O (σ x))
        (Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)))).val ⊆
        (Polynomial.X ^ g - Polynomial.X : Polynomial (IsLocalRing.ResidueField O)).roots := by
      intro z hz
      have hz' : z ∈ insert (IsLocalRing.residue O (σ x))
        (Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O))) := hz
      rw [Polynomial.mem_roots hpoly, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, sub_eq_zero]
      rcases Finset.mem_insert.mp hz' with h | h
      · rw [h]; exact hfix
      · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp h
        rw [← map_pow, ZMod.pow_card]
    have hcard := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Polynomial.natDegree_X_pow_sub_X hg.one_lt, Finset.card_insert_of_notMem hnot,
      Finset.card_image_of_injective _ (RingHom.injective _), Finset.card_univ, ZMod.card] at hcard
    omega
  have ha' : IsLocalRing.residue O (σ x) = IsLocalRing.residue O ((a.val : ℕ) : O) := by
    rw [ha, map_natCast, ← map_natCast (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)),
      ZMod.natCast_zmod_val]
  have hnu : ¬ IsUnit (σ x - ((a.val : ℕ) : O)) := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, ha', sub_self]
  have hne : Ideal.span {(g : O)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hgu
  have : Nontrivial (O ⧸ Ideal.span {(g : O)}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : CharP (O ⧸ Ideal.span {(g : O)}) g := (CharP.charP_iff_prime_eq_zero hg).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _)
  have hyQ : Ideal.Quotient.mk (Ideal.span {(g : O)}) (σ x) ^ g
      - Ideal.Quotient.mk (Ideal.span {(g : O)}) (σ x) = 0 := by
    rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]; exact hy
  have hnQ : ((a.val : ℕ) : O ⧸ Ideal.span {(g : O)}) ^ g = ((a.val : ℕ) : O ⧸ Ideal.span {(g : O)}) := by
    rw [← map_natCast (ZMod.castHom (dvd_refl g) (O ⧸ Ideal.span {(g : O)})), ← map_pow, ZMod.pow_card]
  have hsh : (σ x - ((a.val : ℕ) : O)) ^ g - (σ x - ((a.val : ℕ) : O)) ∈ Ideal.span {(g : O)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_sub, map_natCast, sub_pow_char, hnQ]
    linear_combination hyQ
  refine ⟨(a.val : ℤ), ?_⟩
  rw [Int.cast_natCast]
  exact mem_span_prime_of_not_isUnit_of_pow_sub_mem g hg _ hsh hnu

end GlobalTheory
end

section

open MeasureTheory Filter Topology

namespace GlobalTheory

noncomputable def snocMeasurableEquiv (n : ℕ) : ((Fin n → ℂ) × ℂ) ≃ᵐ (Fin (n + 1) → ℂ) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n)).symm

lemma snocMeasurableEquiv_apply (n : ℕ) (p : (Fin n → ℂ) × ℂ) :
    snocMeasurableEquiv n p = Fin.snoc (α := fun _ => ℂ) p.1 p.2 := by
  simp [snocMeasurableEquiv, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
    Fin.insertNthEquiv, Fin.insertNth_last']

lemma measurePreserving_snocMeasurableEquiv (n : ℕ) :
    MeasurePreserving (snocMeasurableEquiv n)
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) volume := by
  have h1 := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n)).symm
  have h2 : MeasurePreserving (MeasurableEquiv.prodComm : ((Fin n → ℂ) × ℂ) ≃ᵐ (ℂ × (Fin n → ℂ)))
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ))
      ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ))) :=
    Measure.measurePreserving_swap
  exact h2.trans h1

lemma ae_coords_ne_zero (n : ℕ) : ∀ᵐ c : Fin n → ℂ, ∀ i, c i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  exact Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℂ)) i 0

theorem iterated_integral_eq_integral_pi :
    ∀ (n : ℕ) (W : ℕ → ℂ → ℝ) (R : (j : ℕ) → (Fin j → ℂ) → ℝ), (∀ j t, 0 ≤ W j t) → (∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) → 0 ≤ R n c) → AEMeasurable (fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c) → (∀ j, j < n → ∀ c : Fin j → ℂ, (∀ i, c i ≠ 0) → Integrable (fun t : ℂ => W (j + 1) t * R (j + 1) (Fin.snoc c t)) ∧ R j c = ∫ t : ℂ, W (j + 1) t * R (j + 1) (Fin.snoc c t)) → Integrable (fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c) ∧ R 0 (fun i => i.elim0) = ∫ c : Fin n → ℂ, (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c := by
  intro n W R hW
  induction n with
  | zero =>
    intro _ _ _
    refine ⟨Integrable.of_finite, ?_⟩
    rw [integral_unique]
    have : (volume : Measure (Fin 0 → ℂ)).real Set.univ = 1 := by
      simp [Measure.real, volume_pi, Measure.pi_univ]
    rw [this]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, smul_eq_mul]
    exact congrArg _ (Subsingleton.elim _ _)
  | succ n ih =>
    intro hR hm hstep
    have hmp := measurePreserving_snocMeasurableEquiv n
    set T : (Fin (n + 1) → ℂ) → ℝ :=
      fun c => (∏ i : Fin (n + 1), W ((i : ℕ) + 1) (c i)) * R (n + 1) c with hT
    set F : (Fin n → ℂ) × ℂ → ℝ := fun p => T (snocMeasurableEquiv n p) with hF
    have hFm : AEStronglyMeasurable F
        ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) :=
      (hm.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving).aestronglyMeasurable
    have hFeq : ∀ (c : Fin n → ℂ) (t : ℂ), F (c, t) =
        (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) *
          (W (n + 1) t * R (n + 1) (Fin.snoc (α := fun _ => ℂ) c t)) := by
      intro c t
      simp only [hF, hT, snocMeasurableEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, Fin.val_castSucc, Fin.val_last, mul_assoc]
    have hpos : ∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) → ∀ᵐ t : ℂ,
        0 ≤ W (n + 1) t * R (n + 1) (Fin.snoc (α := fun _ => ℂ) c t) := by
      intro c hc
      have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
        simp [ae_iff]
      filter_upwards [h0] with t ht
      refine mul_nonneg (hW _ _) (hR _ ?_)
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using ht
      · simpa using hc i
    have hslice : ∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) →
        ∫ t, F (c, t) = (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c := by
      intro c hc
      simp only [hFeq]
      rw [integral_const_mul, (hstep n (Nat.lt_succ_self n) c hc).2]
    have hae : (fun c => ∫ t, F (c, t)) =ᵐ[volume]
        fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c := by
      filter_upwards [ae_coords_ne_zero n] with c hc using hslice c hc
    obtain ⟨hint, heq⟩ := ih
      (fun c hc => by
        rw [(hstep n (Nat.lt_succ_self n) c hc).2]
        exact integral_nonneg_of_ae (hpos c hc))
      (hFm.integral_prod_right'.aemeasurable.congr hae)
      (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    have hFi : Integrable F ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [integrable_prod_iff hFm]
      constructor
      · filter_upwards [ae_coords_ne_zero n] with c hc
        simp only [hFeq]
        exact (hstep n (Nat.lt_succ_self n) c hc).1.const_mul _
      · refine hint.congr ?_
        filter_upwards [ae_coords_ne_zero n] with c hc
        rw [← hslice c hc]
        refine integral_congr_ae ?_
        filter_upwards [hpos c hc] with t ht
        rw [Real.norm_of_nonneg]
        rw [hFeq]
        exact mul_nonneg (Finset.prod_nonneg fun i _ => hW _ _) ht
    refine ⟨?_, ?_⟩
    · exact (hmp.integrable_comp_emb (snocMeasurableEquiv n).measurableEmbedding).1 hFi
    · rw [heq, ← hmp.integral_comp' T, ← integral_congr_ae hae]
      exact (integral_prod F hFi).symm

end GlobalTheory
end

section

open NumberField TensorProduct

namespace GlobalTheory.IntSepElement

variable (E : Type) [Field E] [NumberField E]


open scoped Classical in
noncomputable def dualB : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)

theorem sum_dualB (z : E) :
    ∑ i, Algebra.trace ℚ E (z * integralBasis E i) • dualB E i = z := by
  classical
  conv_rhs => rw [← (dualB E).sum_repr z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dualB, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]

theorem repr_eq_trace (z : E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).repr z i = Algebra.trace ℚ E (dualB E i * z) := by
  classical
  have h : ∀ j, Algebra.trace ℚ E (dualB E i * integralBasis E j) = if j = i then 1 else 0 := by
    intro j
    have h := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E)
      (integralBasis E) i j
    rw [Algebra.traceForm_apply] at h
    convert h
    rfl
  conv_rhs => rw [← (integralBasis E).sum_repr z]

  rw [Finset.mul_sum, map_sum]
  simp_rw [mul_smul_comm, LinearMap.map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem trace_dualB_int (c : 𝓞 E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (dualB E i * (c : E)) = ((RingOfIntegers.basis E).repr c i : ℚ) := by
  rw [← repr_eq_trace]
  exact integralBasis_repr_apply E c i

theorem sum_mul_dualB : ∑ i, integralBasis E i * dualB E i = 1 := by
  classical
  have key : ∀ z : E, Algebra.trace ℚ E ((∑ i, integralBasis E i * dualB E i) * z) = Algebra.trace ℚ E z := by
    intro z

    rw [Finset.sum_mul, map_sum, Algebra.trace_eq_matrix_trace (integralBasis E) z, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, repr_eq_trace]
    congr 1
    ring
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun z => ?_
  rw [Algebra.traceForm_apply, sub_mul, map_sub, key, one_mul, sub_self]

theorem discr_mul_dualB (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∃ y : 𝓞 E, (y : E) = ((discr E : ℤ) : E) * dualB E i := by
  classical
  have hmem : dualB E i ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    rw [Submodule.mem_one] at ha
    obtain ⟨a, rfl⟩ := ha
    refine ⟨(RingOfIntegers.basis E).repr a i, ?_⟩
    rw [Algebra.traceForm_apply]
    exact (trace_dualB_int E a i).symm
  have := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) (b := integralBasis E) (fun i => by
      rw [integralBasis_apply]; exact (RingOfIntegers.isIntegral_coe _)) (Submodule.one_le.mp le_rfl) hmem
  rw [← coe_discr, Algebra.smul_def, mul_one, map_intCast] at this
  exact ⟨⟨_, this⟩, rfl⟩

theorem exists_sep_discr :
    ∃ x y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E, ∑ i, x i * y i = ((discr E : ℤ) : 𝓞 E) ∧
      ∀ a : 𝓞 E, (∑ i, (a * x i) ⊗ₜ[ℤ] y i : 𝓞 E ⊗[ℤ] 𝓞 E) = ∑ i, x i ⊗ₜ[ℤ] (a * y i) := by
  choose y hy using discr_mul_dualB E
  have hy' : ∀ i, algebraMap (𝓞 E) E (y i) = ((discr E : ℤ) : E) * dualB E i := hy
  refine ⟨RingOfIntegers.basis E, y, ?_, fun a => ?_⟩
  · apply RingOfIntegers.coe_injective

    rw [map_sum, map_intCast]
    simp only [map_mul, hy', ← integralBasis_apply]
    calc ∑ i, integralBasis E i * (((discr E : ℤ) : E) * dualB E i)
        = ((discr E : ℤ) : E) * ∑ i, integralBasis E i * dualB E i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [sum_mul_dualB, mul_one]
  · have h1 : ∀ k, ∑ i, (RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i = a * y k := by
      intro k
      apply RingOfIntegers.coe_injective

      rw [map_sum, map_mul, hy']
      have h2 := sum_dualB E (dualB E k * algebraMap (𝓞 E) E a)
      calc ∑ i, algebraMap (𝓞 E) E ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i)
          = ((discr E : ℤ) : E) * ∑ i, Algebra.trace ℚ E
              (dualB E k * algebraMap (𝓞 E) E a * integralBasis E i) • dualB E i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            have h3 := trace_dualB_int E (a * RingOfIntegers.basis E i) k
            have h4 : ((a * RingOfIntegers.basis E i : 𝓞 E) : E) = algebraMap (𝓞 E) E a * integralBasis E i := by
              rw [integralBasis_apply, ← map_mul]
            rw [h4, ← mul_assoc] at h3
            rw [h3, map_zsmul, hy', Int.cast_smul_eq_zsmul, mul_smul_comm]
        _ = _ := by rw [h2]; ring
    calc (∑ i, (a * RingOfIntegers.basis E i) ⊗ₜ[ℤ] y i : 𝓞 E ⊗[ℤ] 𝓞 E)
        = ∑ i, ∑ k, RingOfIntegers.basis E k ⊗ₜ[ℤ]
            ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E i)]
          rw [TensorProduct.sum_tmul]
          exact Finset.sum_congr rfl fun k _ => TensorProduct.smul_tmul _ _ _
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => by rw [← TensorProduct.tmul_sum, h1]

end GlobalTheory.IntSepElement
end

section

open Cardinal
namespace GlobalTheory.MomOne.Inh

theorem mk_le {A X : Type} [MetricSpace X] (f : A → X) (hf : DenseRange f) (hA : #A ≤ 𝔠) :
    #X ≤ 𝔠 := by
  have h : ∀ x : X, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := fun x => by
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa only [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (by rw [hxy]; exact hs y)
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right hA).trans_eq Cardinal.continuum_power_aleph0

theorem nonempty_iso (p : ℕ) [Fact p.Prime] : Nonempty (ℂ ≃+* ℂ_[p]) := by
  have h1 : #ℚ_[p] ≤ 𝔠 := mk_le _ (Padic.denseRange_ratCast p)
    (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
  have h2 : #(PadicAlgCl p) ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans (max_le h1 Cardinal.aleph0_le_continuum)
  have h3 : #(ℂ_[p]) ≤ 𝔠 := mk_le (X := PadicComplex p) _
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) h2
  have h4 : 𝔠 ≤ #(ℂ_[p]) := continuum_le_cardinal_of_nontriviallyNormedField _
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) ?_
  exact Cardinal.eq.1 (by rw [Cardinal.mk_complex]; exact le_antisymm h4 h3)

end GlobalTheory.MomOne.Inh
end
