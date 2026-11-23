module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle048
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private lemma nu_mul' (x y : ℂ) : nu ι (x * y) = nu ι x * nu ι y := by
  simp [nu]

private lemma nu_nonneg' (x : ℂ) : 0 ≤ nu ι x := norm_nonneg _

private lemma nu_pos' {x : ℂ} (h : x ≠ 0) : 0 < nu ι x := by
  unfold nu
  exact norm_pos_iff.mpr (by simpa using h)

private lemma nu_sum_le' {α : Type*} (t : Finset α) (f : α → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x ∈ t, nu ι (f x) ≤ b) : nu ι (∑ x ∈ t, f x) ≤ b := by
  unfold nu

  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb (fun x hx => h x hx)

private lemma nu_mulVec_le {I : Type} [Fintype I] (A : Matrix I I ℂ) (v : I → ℂ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hA : ∀ i j, nu ι (A i j) ≤ p) (hv : ∀ j, nu ι (v j) ≤ q) (i : I) :
    nu ι ((A *ᵥ v) i) ≤ p * q := by
  simp only [Matrix.mulVec, dotProduct]
  refine nu_sum_le' ι _ _ _ (mul_nonneg hp hq) fun j _ => ?_
  rw [nu_mul']
  exact mul_le_mul (hA i j) (hv j) (nu_nonneg' ι _) hp

end SlopeTestRemainingChoices

theorem absBound :
    UpperTheory.V.Z.Int.AbsBound := by
  intro l _ ι G _ Γ K I _ R F s a c C hc hfin hF hΓ hK heig hRK hRL
  set Nf : G → I → ℂ := fun g => R g⁻¹ *ᵥ F g with hN
  have Rinv : ∀ g, R g⁻¹ * R g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have Rinv' : ∀ g, R g * R g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hNΓ : ∀ γ ∈ Γ, ∀ g, Nf (γ * g) = Nf g := by
    intro γ hγ g
    simp only [hN, hΓ γ hγ g, _root_.mul_inv_rev, map_mul, mulVec_mulVec]
    rw [mul_assoc, Rinv, mul_one]
  have hNK : ∀ k ∈ K, ∀ g, Nf (g * k) = R k⁻¹ *ᵥ Nf g := by
    intro k hk g
    simp only [hN, hK k hk g, _root_.mul_inv_rev, map_mul, mulVec_mulVec]
  have hNeig : ∀ h, a • Nf h = ∑ x ∈ s, R x *ᵥ Nf (h * x) := by
    intro h
    have h1 : ∀ x, R x *ᵥ Nf (h * x) = R h⁻¹ *ᵥ F (h * x) := by
      intro x
      simp only [hN, _root_.mul_inv_rev, map_mul, mulVec_mulVec]
      rw [← mul_assoc, Rinv', one_mul]
    simp only [h1]
    simp only [hN]
    rw [← Matrix.mulVec_smul, ← heig h, Matrix.mulVec_sum]

  obtain ⟨g0, i0, h0⟩ : ∃ g i, Nf g i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hF
    funext g
    have : F g = R g *ᵥ Nf g := by
      simp only [hN, mulVec_mulVec, Rinv', one_mulVec]
    rw [this, show Nf g = 0 from funext (hcon g)]
    simp
  have hC : 0 ≤ C := (nu_nonneg' ι _).trans (hRK 1 K.one_mem i0 i0)

  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ g i, nu ι (Nf g i) ≤ B := by
    haveI := hfin
    letI := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))
    set B0 : ℝ := ∑ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), ∑ i, nu ι (Nf q.out i) with hB0
    have hB0n : 0 ≤ B0 := Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun i _ => nu_nonneg' ι _
    have hle : ∀ (q : DoubleCoset.Quotient (Γ : Set G) (K : Set G)) j, nu ι (Nf q.out j) ≤ B0 := by
      intro q j
      calc nu ι (Nf q.out j) ≤ ∑ i, nu ι (Nf q.out i) :=
            Finset.single_le_sum (f := fun i => nu ι (Nf q.out i)) (fun i _ => nu_nonneg' ι _) (Finset.mem_univ j)
        _ ≤ B0 := Finset.single_le_sum (f := fun q : DoubleCoset.Quotient (Γ : Set G) (K : Set G) => ∑ i, nu ι (Nf q.out i))
            (fun q _ => Finset.sum_nonneg fun i _ => nu_nonneg' ι _) (Finset.mem_univ q)
    refine ⟨C * B0, mul_nonneg hC hB0n, fun g i => ?_⟩
    obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
    have hg : g = h⁻¹ * ((DoubleCoset.mk Γ K g).out * k⁻¹) := by
      rw [e]; group
    have hNg : Nf g = R (k⁻¹)⁻¹ *ᵥ Nf (DoubleCoset.mk Γ K g).out := by
      conv_lhs => rw [hg]
      rw [hNΓ _ (Γ.inv_mem hh), hNK _ (K.inv_mem hk)]
    rw [hNg]
    exact nu_mulVec_le ι _ _ C B0 hC hB0n (hRK _ (K.inv_mem (K.inv_mem hk))) (hle _) i

  have hstep : ∀ (L : List G), a • (R L.prod *ᵥ Nf (g0 * L.prod)) =
      ∑ x ∈ s, R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod) := by
    intro L
    rw [← Matrix.mulVec_smul, hNeig, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [List.prod_append, List.prod_singleton, map_mul, mulVec_mulVec, mul_assoc]
  have hit : ∀ (n : ℕ) (L : List G), (∀ x ∈ L, x ∈ s) → ∀ i,
      nu ι a ^ n * nu ι ((R L.prod *ᵥ Nf (g0 * L.prod)) i) ≤ C * B * c ^ (L.length + n) := by
    intro n
    induction n with
    | zero =>
      intro L hL i
      have := nu_mulVec_le ι (R L.prod) (Nf (g0 * L.prod)) (C * c ^ L.length) B
        (mul_nonneg hC (pow_nonneg hc _)) hB0 (hRL L hL) (hB _) i
      simp only [pow_zero, one_mul, add_zero]
      calc _ ≤ _ := this
        _ = _ := by ring
    | succ n ih =>
      intro L hL i
      have e : a * (R L.prod *ᵥ Nf (g0 * L.prod)) i =
          ∑ x ∈ s, (R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod)) i := by
        have := congrFun (hstep L) i
        simpa [Finset.sum_apply] using this
      have hD : 0 ≤ C * B * c ^ (L.length + (n + 1)) :=
        mul_nonneg (mul_nonneg hC hB0) (pow_nonneg hc _)
      calc nu ι a ^ (n + 1) * nu ι ((R L.prod *ᵥ Nf (g0 * L.prod)) i)
          = nu ι a ^ n * nu ι (a * (R L.prod *ᵥ Nf (g0 * L.prod)) i) := by
            rw [nu_mul']; ring
        _ = nu ι a ^ n * nu ι (∑ x ∈ s, (R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod)) i) := by rw [e]
        _ ≤ C * B * c ^ (L.length + (n + 1)) := by
            by_cases hz : nu ι a ^ n = 0
            · rw [hz, zero_mul]; exact hD
            have hp : 0 < nu ι a ^ n := lt_of_le_of_ne (pow_nonneg (nu_nonneg' ι _) _) (Ne.symm hz)
            rw [← le_div_iff₀' hp]
            refine nu_sum_le' ι _ _ _ (div_nonneg hD hp.le) fun x hx => ?_
            rw [le_div_iff₀' hp]
            have := ih (L ++ [x]) (fun y hy => by
              rcases List.mem_append.mp hy with h | h
              · exact hL y h
              · simp at h; exact h ▸ hx) i
            simpa [List.length_append, add_assoc, add_comm 1 n] using this
  have hfinal : ∀ n : ℕ, nu ι a ^ n * nu ι (Nf g0 i0) ≤ C * B * c ^ n := by
    intro n
    have := hit n [] (by simp) i0
    simpa [hN] using this
  have hd : 0 < nu ι (Nf g0 i0) := nu_pos' ι h0
  by_contra hlt
  push_neg at hlt
  rcases hc.eq_or_lt with h0c | hcpos
  · have := hfinal 1
    rw [← h0c] at this hlt
    simp only [pow_one, mul_zero] at this
    have : 0 < nu ι a * nu ι (Nf g0 i0) := mul_pos hlt hd
    linarith
  · have hr : 1 < nu ι a / c := (one_lt_div hcpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C * B / nu ι (Nf g0 i0)) hr
    rw [div_lt_iff₀ hd, div_pow, div_mul_eq_mul_div, lt_div_iff₀ (pow_pos hcpos n)] at hn
    linarith [hfinal n]

end UpperTheory.V.Z.Int
end

section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

theorem UpperTheory.V.Z.Int.rootBound :
    UpperTheory.V.Z.Int.RootBound := by
  intro l _ ι S c hc h b hb
  by_contra hlt
  have hlt' : c < ‖ι.symm b‖ := not_le.mp hlt
  have hroot : Polynomial.eval b (S.map fun t => Polynomial.X - Polynomial.C t).prod = 0 := by
    rw [Polynomial.eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨Polynomial.X - Polynomial.C b, Multiset.mem_map.mpr ⟨b, hb, rfl⟩, by simp⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, Polynomial.eval_finsetSum, Finset.sum_range_succ'] at hroot
  have hn : 0 < S.card := Multiset.card_pos_iff_exists_mem.mpr ⟨b, hb⟩
  have h0 : S.esymm 0 = 1 := by simp [Multiset.esymm]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, pow_zero, one_mul, Nat.sub_zero, h0] at hroot
  have hK := congrArg ι.symm hroot

  simp only [map_add (f := _), map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at hK
  have heq : ‖ι.symm b‖ ^ S.card = ‖∑ j ∈ Finset.range S.card, (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1)))‖ := by
    rw [eq_neg_of_add_eq_zero_left hK, norm_neg, norm_pow]
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hn.ne')
    (fun j => (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1))))
  have hi' : i + 1 ≤ S.card := Finset.mem_range.mp hi
  have hj := h (i + 1) (by omega) hi'
  have hj' : ‖ι.symm (S.esymm (i + 1))‖ ≤ c ^ (i + 1) := hj
  have hpos : 0 < ‖ι.symm b‖ := lt_of_le_of_lt hc hlt'
  have hcp : c ^ (i + 1) < ‖ι.symm b‖ ^ (i + 1) := pow_lt_pow_left₀ hlt' hc (by omega)
  have hterm : ‖(-1 : PadicAlgCl l) ^ (i + 1) * (ι.symm (S.esymm (i + 1)) * ι.symm b ^ (S.card - (i + 1)))‖
      < ‖ι.symm b‖ ^ S.card := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow]
    calc ‖ι.symm (S.esymm (i + 1))‖ * ‖ι.symm b‖ ^ (S.card - (i + 1))
        < ‖ι.symm b‖ ^ (i + 1) * ‖ι.symm b‖ ^ (S.card - (i + 1)) :=
          mul_lt_mul_of_pos_right (lt_of_le_of_lt hj' hcp) (pow_pos hpos _)
      _ = ‖ι.symm b‖ ^ S.card := by rw [← pow_add]; congr 1; omega
  exact absurd (heq.le.trans hle) (not_le.mpr hterm)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace UpperTheory.V.Z.Int

private theorem val_le_one_iff {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* Qbar l) (u : HeightOneSpectrum (𝓞 E))
    (hu : ∀ x : E, u.valuation E x < 1 ↔ ‖c x‖ < 1) (x : E) :
    u.valuation E x ≤ 1 ↔ ‖c x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : 0 < u.valuation E x := zero_lt_iff.2 ((map_ne_zero _).2 hx)
  have h1 : 0 < ‖c x‖ := norm_pos_iff.2 ((map_ne_zero c).2 hx)
  have h := hu x⁻¹
  rw [map_inv₀, map_inv₀, norm_inv, inv_lt_one₀ h0, inv_lt_one₀ h1] at h
  rw [← not_lt, ← not_lt, h]

theorem placeHom : PlaceHom := by
  intro l _ ι E _ _ τ
  let c : E →+* Qbar l := ι.symm.toRingHom.comp τ
  have hc : ∀ x, c x = ι.symm (τ x) := fun _ => rfl
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l c
  obtain ⟨j, hj, hjE⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l c u hu
  have hjx : ∀ x : E, j (algebraMap E (u.adicCompletion E) x) = c x :=
    fun x => DFunLike.congr_fun hjE x
  refine ⟨u, ι.toRingHom.comp j, fun x => ?_, fun x => ?_, fun w => ?_⟩
  · change ι (j (algebraMap E (u.adicCompletion E) x)) = τ x
    rw [hjx, hc, RingEquiv.apply_symm_apply]
  · have hnu : ∀ y, nu ι ((ι.toRingHom.comp j) y) = ‖j y‖ := fun y => by
      change ‖ι.symm (ι (j y))‖ = _
      rw [RingEquiv.symm_apply_apply]
    rw [hnu]
    have hB : IsClopen {y : u.adicCompletion E | ‖j y‖ ≤ 1} := by
      have := (IsUltrametricDist.isClopen_closedBall (0 : Qbar l) one_ne_zero).preimage hj
      simpa [Set.preimage, Metric.closedBall] using this
    have hC : IsClopen {y : u.adicCompletion E | Valued.v y ≤ 1} :=
      Valued.isClopen_integer (u.adicCompletion E)
    have hT : IsClosed {y : u.adicCompletion E | ‖j y‖ ≤ 1 ↔ Valued.v y ≤ 1} := by
      have : {y : u.adicCompletion E | ‖j y‖ ≤ 1 ↔ Valued.v y ≤ 1} =
          ({y | ‖j y‖ ≤ 1} ∩ {y | Valued.v y ≤ 1}) ∪
            ({y | ‖j y‖ ≤ 1}ᶜ ∩ {y | Valued.v y ≤ 1}ᶜ) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      rw [this]
      exact (hB.isClosed.inter hC.isClosed).union (hB.compl.isClosed.inter hC.compl.isClosed)
    refine (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) (K := E) u).induction_on
      (p := fun y => ‖j y‖ ≤ 1 ↔ Valued.v y ≤ 1) x hT fun a => ?_
    have hv : Valued.v (algebraMap E (u.adicCompletion E) a) = u.valuation E a :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u a
    rw [hjx, hv, val_le_one_iff c u hu a]
  · have hw : ∀ a : 𝓞 E, nu ι (τ a) = ‖c a‖ := fun _ => rfl
    have hmem : ∀ a : 𝓞 E, a ∈ u.asIdeal ↔ ‖c a‖ < 1 := fun a => by
      rw [← hu, HeightOneSpectrum.valuation_lt_one_iff_mem]
    simp only [Ov, Finset.mem_filter, Finset.mem_univ, true_and, hw]
    constructor
    · intro h
      exact HeightOneSpectrum.ext (Ideal.ext fun a => (h a).trans (hmem a).symm)
    · rintro rfl
      exact hmem

end UpperTheory.V.Z.Int
end
end

section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

private theorem conj_mem_Ov {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {v : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (h : τ ∈ UpperTheory.V.Z.Int.Ov ι v) :
    ComplexEmbedding.conjugate τ ∈ UpperTheory.V.Z.Int.Ov ι (conjSrc (GlobalTheory.SplitPts.conjE E) v) := by
  have hv := (Finset.mem_filter.1 h).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => ?_⟩
  have hI := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) v)
  have e : τ ((RingOfIntegers.mapRingEquiv (GlobalTheory.SplitPts.conjE E) x : 𝓞 E) : E) =
      ComplexEmbedding.conjugate τ (x : E) := by
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact IsCMField.complexEmbedding_complexConj E τ x
  rw [hI, Ideal.mem_comap]
  refine (hv _).trans ?_
  rw [e]

private theorem eq_of_mem_Ov {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E]
    {u v : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (h₁ : τ ∈ UpperTheory.V.Z.Int.Ov ι u) (h₂ : τ ∈ UpperTheory.V.Z.Int.Ov ι v) :
    u = v :=
  HeightOneSpectrum.ext (Ideal.ext fun x =>
    ((Finset.mem_filter.1 h₁).2 x).trans ((Finset.mem_filter.1 h₂).2 x).symm)

theorem UpperTheory.V.Z.Int.placeConj :
    UpperTheory.V.Z.Int.PlaceConj := by
  intro l _ ι E _ _ _ w hw τ
  obtain ⟨hne, -, hover⟩ := GlobalTheory.SplitPts.over_split hw
  refine ⟨fun h hc => hne (eq_of_mem_Ov ι (conj_mem_Ov ι h) hc), fun u hu huw hunder => ?_⟩
  have hcu : u = conjSrc (GlobalTheory.SplitPts.conjE E) w := (hover u hunder).resolve_left huw
  have h := conj_mem_Ov ι hu
  rwa [hcu, GlobalTheory.SplitPts.conjSrc_conjSrc_cm] at h
end
