module

public import ReciprocityTheory.SemistableReduction.Bundle002
public import Lemmata.IterateZero.IterZero
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
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
public import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.NormOrdLengthResidue
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

@[expose] public section

section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

noncomputable def gaussRed {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    MvPolynomial σ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) :=
  ∑ α ∈ p.support, monomial α (IsLocalRing.residue _ ⟨p.coeff α, hc α⟩)

theorem gaussRed_coeff {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) (α : σ →₀ ℕ) :
    (gaussRed V p hc).coeff α = IsLocalRing.residue _ ⟨p.coeff α, hc α⟩ := by
  classical
  unfold gaussRed
  rw [MvPolynomial.coeff_sum]
  by_cases h : α ∈ p.support
  · rw [Finset.sum_eq_single α]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg hb]
    · intro h'
      exact absurd h h'
  · have h0 : p.coeff α = 0 := by simpa [MvPolynomial.mem_support_iff] using h
    have hz : (⟨p.coeff α, hc α⟩ : V.comap (algebraMap Ω U)) = 0 := Subtype.ext h0
    rw [Finset.sum_eq_zero, hz, map_zero]
    intro b hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    rintro rfl
    exact h hb

theorem gaussRed_eval {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    letI := residueAlgebra V (algebraMap Ω U)
    ∃ h : aeval t p ∈ V, IsLocalRing.residue V ⟨aeval t p, h⟩ =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V p hc) := by
  try dsimp only
  letI := residueAlgebra V (algebraMap Ω U)
  classical
  obtain ⟨y, hydef⟩ : ∃ y : V, y = ∑ α ∈ p.support,
      comapInclusion V (algebraMap Ω U) ⟨p.coeff α, hc α⟩ *
        ∏ s ∈ α.support, (⟨t s, ht s⟩ : V) ^ α s := ⟨_, rfl⟩
  have hy : (y : U) = aeval t p := by
    change V.subtype y = _
    rw [hydef, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]

    simp only [map_sum, map_mul, map_prod, map_pow]
    rfl
  have hmem : aeval t p ∈ V := by
    rw [← hy]
    exact y.2
  refine ⟨hmem, ?_⟩
  have hyy : (⟨aeval t p, hmem⟩ : V) = y := Subtype.ext hy.symm

  rw [hyy, hydef, map_sum]
  unfold gaussRed

  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.aeval_monomial]
  simp only [map_mul, map_prod, map_pow]
  congr 1

end ReciprocityTheory.MultiplicativeHeights
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Module UniqueFactorizationMonoid

theorem normValuation_eq_factorization (hC1 : NormLengthStatement) : NormOrdStatement := by
  classical
  intro O B _ _ _ _ _ _ _ _ _ g hg
  rw [hC1 O B g hg]
  set I : Ideal B := Ideal.span {g} with hIdef
  have hI : I ≠ ⊥ := by rwa [Ne, hIdef, Ideal.span_singleton_eq_bot]
  have hfac : UniqueFactorizationMonoid.factors I = normalizedFactors I :=
    UniqueFactorizationMonoid.factors_eq_normalizedFactors I
  have hmax : ∀ P ∈ UniqueFactorizationMonoid.factors I, P.IsMaximal ∧ P ≠ ⊥ := by
    intro P hP
    have hpr : Prime P := UniqueFactorizationMonoid.prime_of_factor P hP
    exact ⟨(Ideal.isPrime_of_prime hpr).isMaximal hpr.ne_zero, hpr.ne_zero⟩
  let φ := IsDedekindDomain.quotientEquivPiFactors hI
  let ψ : (B ⧸ I) ≃ₗ[O] ((P : (UniqueFactorizationMonoid.factors I).toFinset) →
      B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors I)) :=
    { φ with
      map_smul' := by
        intro o x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        change φ (Ideal.Quotient.mk I (o • b)) = o • φ (Ideal.Quotient.mk I b)
        rw [IsDedekindDomain.quotientEquivPiFactors_mk, IsDedekindDomain.quotientEquivPiFactors_mk]
        rfl }
  rw [ψ.length_eq, Module.length_pi_of_fintype]
  have hterm : ∀ P : (UniqueFactorizationMonoid.factors I).toFinset,
      Module.length O (B ⧸ (P : Ideal B) ^
        Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors I)) =
      ((Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors I) *
        (P : Ideal B).inertiaDeg O : ℕ) : ℕ∞) := by
    intro P
    obtain ⟨hPm, hP0⟩ := hmax P (Multiset.mem_toFinset.mp P.2)
    rw [normOrd_length_pow O B _ hP0, normOrd_length_residue O B]
    norm_cast
  rw [Finset.sum_congr rfl (fun P _ => hterm P), ← Nat.cast_sum]
  congr 1
  rw [← hfac, Finset.sum_coe_sort (UniqueFactorizationMonoid.factors I).toFinset
    (fun P => Multiset.count P (UniqueFactorizationMonoid.factors I) * P.inertiaDeg O)]
  rw [finsum_eq_sum_of_support_subset (s := (UniqueFactorizationMonoid.factors I).toFinset.subtype
    (fun Q : Ideal B => Q.IsMaximal)) _ ?sup]
  · rw [Finset.sum_subtype_eq_sum_filter (fun Q : Ideal B =>
        Q.inertiaDeg O * Multiset.count Q (UniqueFactorizationMonoid.factors I)),
      Finset.filter_true_of_mem]
    · exact Finset.sum_congr rfl fun P _ => mul_comm _ _
    · intro P hP
      exact (hmax P (Multiset.mem_toFinset.mp hP)).1
  case sup =>
    intro Q hQ
    rw [Function.mem_support] at hQ
    rw [Finset.mem_coe, Finset.mem_subtype, Multiset.mem_toFinset]
    by_contra hn
    exact hQ (by rw [Multiset.count_eq_zero.mpr hn, mul_zero])

end ReciprocityTheory.MultiplicativeHeights
end

section

namespace ReciprocityTheory.MultiplicativeHeights

theorem integralClosureRank (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L] :
    IsDedekindDomain (integralClosure O L) ∧ Module.Finite O (integralClosure O L) ∧
      Module.Free O (integralClosure O L) ∧
      Module.finrank O (integralClosure O L) = Module.finrank F L ∧
      {Q : Ideal (integralClosure O L) | Q.IsMaximal}.Finite ∧
      ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
          Q.1.ramificationIdx O * Q.1.inertiaDeg O = Module.finrank F L := by
  set C := integralClosure O L
  haveI hD : IsDedekindDomain C := integralClosure.isDedekindDomain O F L
  haveI hFin : Module.Finite O C := IsIntegralClosure.finite O F L C
  haveI : Module.IsTorsionFree O L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  haveI : Module.IsTorsionFree O C := inferInstance
  haveI hFr : Module.Free O C := Module.free_of_finite_type_torsion_free'
  haveI : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension O F L C
  set m := IsLocalRing.maximalIdeal O
  have hm : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have key : ∀ Q : Ideal C, Q.IsMaximal ↔ Q ∈ IsDedekindDomain.primesOverFinset m C := by
    intro Q
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C]
    constructor
    · intro hQ
      have hu : (Q.under O).IsMaximal := Ideal.IsMaximal.under O Q
      refine ⟨hQ.isPrime, ⟨?_⟩⟩
      exact (IsLocalRing.eq_maximalIdeal hu).symm
    · rintro ⟨hP, hl⟩
      refine hP.isMaximal ?_
      rintro rfl
      apply hm
      rw [hl.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O C)
  refine ⟨hD, hFin, hFr, IsIntegralClosure.rank O F L C, ?_, ?_⟩
  · exact (IsDedekindDomain.primesOverFinset m C).finite_toSet.subset fun Q hQ => (key Q).1 hQ
  · rw [← Ideal.sum_ramification_inertia C F L hm]
    rw [← finsum_comp_equiv (Equiv.subtypeEquivRight key).symm, finsum_eq_sum_of_fintype,
      ← Finset.sum_coe_sort (IsDedekindDomain.primesOverFinset m C)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hP := P.2
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C] at hP
    haveI := hP.1
    haveI := hP.2
    haveI : P.1.IsMaximal := ((key P.1).2 P.2)
    simp only [Equiv.subtypeEquivRight_symm_apply_coe]
    rw [Ideal.ramificationIdx_eq_ramificationIdx' m P.1 hm, Ideal.inertiaDeg_eq_inertiaDeg' m P.1]

open MvPolynomial

theorem algebraicIndependent_of_residue_lift {F₁ F₂ : Type} [Field F₁] [Field F₂] [Algebra F₁ F₂]
    (V : ValuationSubring F₂) {ι : Type*} (y : ι → V)
    (hx : letI := residueAlgebra V (algebraMap F₁ F₂)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (fun i => IsLocalRing.residue V (y i))) :
    AlgebraicIndependent F₁ (fun i => ((y i : V) : F₂)) := by
  classical
  letI := residueAlgebra V (algebraMap F₁ F₂)
  rw [algebraicIndependent_iff] at hx ⊢
  intro p hp
  by_contra hne
  have hS : p.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m₀, hm₀, hmax⟩ := p.support.exists_max_image
    (fun m => (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)) hS
  have hc : p.coeff m₀ ≠ 0 := MvPolynomial.mem_support_iff.1 hm₀
  have hvc : (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hc

  have hle : ∀ m, (p.coeff m₀)⁻¹ * p.coeff m ∈ V.comap (algebraMap F₁ F₂) := by
    intro m
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hm : m ∈ p.support
    · calc ((V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀))⁻¹ *
            (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)
          ≤ ((V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀))⁻¹ *
            (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) := by
            gcongr
            exact hmax m hm
        _ = 1 := inv_mul_cancel₀ hvc
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      simp
  have hpp : MvPolynomial.C (p.coeff m₀)⁻¹ * p ∈
      Set.range (MvPolynomial.map (V.comap (algebraMap F₁ F₂)).subtype) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 ha
    exact ⟨⟨_, hle m⟩, by simp [MvPolynomial.coeff_C_mul]⟩
  obtain ⟨qV, hqV⟩ := hpp
  have hcoeff : qV.coeff m₀ = 1 := by
    have e := congrArg (AddMonoidAlgebra.coeff · m₀) hqV
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc] at e
    exact Subtype.ext e
  have h0 : MvPolynomial.eval₂ (comapInclusion V (algebraMap F₁ F₂)) y qV = 0 := by
    apply Subtype.ext
    have e1 : MvPolynomial.aeval (fun i => ((y i : V) : F₂))
        (MvPolynomial.C (p.coeff m₀)⁻¹ * p) = 0 := by
      rw [map_mul, hp, mul_zero]
    rw [MvPolynomial.aeval_def, ← hqV, MvPolynomial.eval₂_map] at e1
    have e2 := MvPolynomial.eval₂_comp_left V.subtype (comapInclusion V (algebraMap F₁ F₂)) y qV
    have e3 : V.subtype.comp (comapInclusion V (algebraMap F₁ F₂)) =
        (algebraMap F₁ F₂).comp (V.comap (algebraMap F₁ F₂)).subtype := RingHom.ext fun _ => rfl
    rw [e3] at e2
    exact e2.trans e1

  have h1 : MvPolynomial.aeval (fun i => IsLocalRing.residue V (y i))
      (MvPolynomial.map (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) qV) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e4 := MvPolynomial.eval₂_comp_left (IsLocalRing.residue V)
      (comapInclusion V (algebraMap F₁ F₂)) y qV
    rw [h0, map_zero] at e4
    have e5 : (algebraMap (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (IsLocalRing.ResidueField V)).comp (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) =
        (IsLocalRing.residue V).comp (comapInclusion V (algebraMap F₁ F₂)) :=
      RingHom.ext fun r => IsLocalRing.ResidueField.map_residue _ r
    rw [e5]
    exact e4.symm
  have e6 := congrArg (AddMonoidAlgebra.coeff · m₀) (hx _ h1)
  rw [MvPolynomial.coeff_map, hcoeff, map_one, MvPolynomial.coeff_zero] at e6
  exact one_ne_zero e6

theorem residueTrdegLe : TRStatement := by
  intro F₁ F₂ _ _ _ V
  letI := residueAlgebra V (algebraMap F₁ F₂)
  unfold Algebra.trdeg
  refine ciSup_le' fun s => ?_
  have hy : ∀ a : s.1, ∃ v : V, IsLocalRing.residue V v = a :=
    fun a => IsLocalRing.residue_surjective (a : IsLocalRing.ResidueField V)
  choose y hy using hy
  have hs : AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
      (fun a => IsLocalRing.residue V (y a)) := by
    have : (fun a => IsLocalRing.residue V (y a)) = ((↑) : s.1 → IsLocalRing.ResidueField V) :=
      funext hy
    rw [this]
    exact s.2
  exact (algebraicIndependent_of_residue_lift V y hs).cardinalMk_le_trdeg

theorem integralClosureRank_and_residueTrdegLe : DedekindRankStatement ∧ TRStatement :=
  ⟨by intro O F L; intros; exact integralClosureRank O F L, residueTrdegLe⟩

end ReciprocityTheory.MultiplicativeHeights
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Filter Topology Function Metric Polynomial

theorem entire_poly_of_growth (k : ℕ) : ∀ (g : ℂ → ℂ) (A : ℝ), Differentiable ℂ g →
    (∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t, g t = P.eval t := by
  first | exact Bl.IterateZero.goal1 .. | (apply Bl.IterateZero.goal1 <;> assumption) | (intros; apply Bl.IterateZero.goal1 <;> assumption)

theorem exists_entire_of_finite_growth (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ) (hB : B.Finite)
    (hf : DifferentiableOn ℂ f Bᶜ) (hb : ∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ t ∉ B, g t = f t := by
  classical
  let g : ℂ → ℂ := fun t => if t ∈ B then limUnder (𝓝[≠] t) f else f t
  refine ⟨g, fun c => ?_, fun t ht => if_neg ht⟩
  by_cases hc : c ∈ B
  · have hU : IsOpen (B \ {c})ᶜ := (hB.sdiff).isClosed.isOpen_compl
    set s : Set ℂ := (B \ {c})ᶜ ∩ ball c 1 with hs
    have hsn : s ∈ 𝓝 c := inter_mem (hU.mem_nhds (fun h => h.2 rfl)) (ball_mem_nhds c one_pos)
    have hsub : s \ {c} ⊆ Bᶜ := by
      rintro t ⟨⟨h1, -⟩, h2⟩ htB
      exact h1 ⟨htB, h2⟩
    have hbdd : BddAbove (norm ∘ f '' (s \ {c})) := by
      refine ⟨|A| * (2 + ‖c‖) ^ k, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have htc : ‖t‖ ≤ ‖c‖ + 1 := by
        have h := ht.1.2
        rw [mem_ball, dist_eq_norm] at h
        have := norm_le_norm_add_norm_sub' t c
        linarith [norm_sub_rev t c]
      calc ‖f t‖ ≤ A * (1 + ‖t‖) ^ k := hb t (hsub ht)
        _ ≤ |A| * (1 + ‖t‖) ^ k := mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ |A| * (2 + ‖c‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k)
              (abs_nonneg A)
    have hdiff := Complex.differentiableOn_update_limUnder_of_bddAbove hsn
      (hf.mono hsub) hbdd
    refine (hdiff.differentiableAt hsn).congr_of_eventuallyEq ?_
    filter_upwards [hsn] with t ht
    by_cases htc : t = c
    · subst htc
      simp [g, hc]
    · have htB : t ∉ B := fun h => ht.1 ⟨h, htc⟩
      simp [g, htB, update_of_ne htc]
  · have hO : IsOpen Bᶜ := hB.isClosed.isOpen_compl
    refine (hf.differentiableAt (hO.mem_nhds hc)).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hc] with t ht
    exact if_neg ht

theorem onePolyGrowth_holds : OnePolyGrowthStatement := by
  intro f B A k hB hf hb
  obtain ⟨g, hg, hgf⟩ := exists_entire_of_finite_growth f B A k hB hf hb
  have hclosed : IsClosed {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} :=
    isClosed_le (continuous_norm.comp hg.continuous)
      (continuous_const.mul ((continuous_const.add continuous_norm).pow k))
  have hsub : Bᶜ ⊆ {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} := fun t ht => by
    simpa [hgf t ht] using hb t ht
  have hall : ∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k := by
    have hd : Dense Bᶜ := hB.countable.dense_compl ℂ
    intro t
    have : t ∈ closure Bᶜ := by rw [hd.closure_eq]; trivial
    exact closure_minimal hsub hclosed this
  obtain ⟨P, hPd, hP⟩ := entire_poly_of_growth k g A hg hall
  exact ⟨P, hPd, fun t ht => by rw [← hgf t ht, hP t]⟩

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def UnipotentStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r g : ℕ) (γ : Matrix (Fin r) (Fin r) K)
    (Q : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
    (∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 K, (γ ^ n).trace - r = (g : K) * z) →
    (Real.exp (1 / 3) + 1) * r < g → (∀ σ, (Q σ).det ≠ 0) →
    (∀ σ (u : Fin r → ℂ), normSq ((Q σ * γ.map σ * (Q σ)⁻¹) *ᵥ u) ≤
      Real.exp (2 / (3 * (r : ℝ))) * normSq u) →
    (γ - 1) ^ r = 0 ∧ ∀ σ, ∑ a, ∑ b, ‖(Q σ * (γ.map σ - 1) * (Q σ)⁻¹) a b‖ ^ 2 < 1

def hq {r : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) : ℝ := (star u ⬝ᵥ (H *ᵥ u)).re

structure Majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) where

  H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ
  posDef : ∀ σ, (H σ).PosDef
  major : ∀ σ, H σ * (S.G.map σ)⁻¹ * H σ = S.G.map σ
  conj_compat : ∀ σ, H ((starRingEnd ℂ).comp σ) = (H σ).map (starRingEnd ℂ)

def gramC {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => star (embVec σ (b i)) ⬝ᵥ (H *ᵥ embVec σ (b j))

def IsKBasisIn {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) : Prop :=
  (∀ i, b i ∈ B) ∧ LinearIndependent K b ∧ ∀ x ∈ B, x ∈ Submodule.span K (Set.range b)

def latDeg {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : ℝ :=
  Real.log ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup : ℝ) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ b).det.re

def IsSemistableZero {K : Type} [Field K] [NumberField K] {r : ℕ} (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  (∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn L b → latDeg H L b = 0) ∧
  ∀ B : Submodule (𝓞 K) (Fin r → K), B ≤ L →
    ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg H B b ≤ 0

def gramX {K : Type} [Field K] [NumberField K] {r k m : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : Matrix (Fin k) (Fin m) ℂ :=
  Matrix.of fun i j => star (embVec σ (b i)) ⬝ᵥ (H *ᵥ embVec σ (c j))

def quotGramC {K : Type} [Field K] [NumberField K] {r k m : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : Matrix (Fin m) (Fin m) ℂ :=
  gramC H σ c - gramX H σ c b * (gramC H σ b)⁻¹ * gramX H σ b c

def satSub {K : Type} [Field K] [NumberField K] {r k : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : Submodule (𝓞 K) (Fin r → K) :=
  L ⊓ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)

def quotDeg {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : ℝ :=
  Real.log ((satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
      L.toAddSubgroup : ℝ) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (quotGramC (H σ) σ b c).det.re

def DegAddStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k m : ℕ) (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K),
    (∀ σ, (H σ).PosDef) → L.FG → (∀ i, b i ∈ L) → (∀ j, c j ∈ L) →
    LinearIndependent K (Fin.append b c) →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range (Fin.append b c))) →
    latDeg H L (Fin.append b c) = latDeg H (satSub L b) b + quotDeg H L b c

def SemiPointStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)),
    IsLattice L → IsSelfDual S L → ∃ M : Majorant S, IsSemistableZero M.H L

def SemistableStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)),
    IsLattice L → IsSelfDual S L → ∃ M : Majorant S, IsSemistableZero M.H L ∧
      ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
        (∀ σ (u : Fin r → ℂ), u ≠ 0 → hq (M.H σ) (N.map σ *ᵥ u) < hq (M.H σ) u) → N = 0

end ReciprocityTheory.MultiplicativeHeights
end
end
