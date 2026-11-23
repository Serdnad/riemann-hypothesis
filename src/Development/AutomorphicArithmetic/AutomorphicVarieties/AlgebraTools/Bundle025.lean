module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Equiv
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.dim_quot_le_of_primes {P : Type} [CommRing P] (I J : Ideal P)
    (h : ∀ p : Ideal P, p.IsPrime → J ≤ p → I ≤ p) :
    ringKrullDim (P ⧸ J) ≤ ringKrullDim (P ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  have hsub : PrimeSpectrum.zeroLocus (R := P) (J : Set P) ⊆ PrimeSpectrum.zeroLocus (I : Set P) := by
    intro q hq
    rw [PrimeSpectrum.mem_zeroLocus] at hq ⊢
    exact h q.asIdeal q.isPrime hq
  exact Order.krullDim_le_of_strictMono (Set.inclusion hsub) (fun a b hab => hab)

theorem UpperTheory.V.AlgebraTools.dim_relIdeal_le :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ringKrullDim (P ⧸ relIdeal z m) + (Fintype.card ι : ℕ) ≤ ringKrullDim P := by
  classical
  intro P _ _ ι _ _ z m hx
  set x : ι × ι ⊕ ι → P := Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m with hxdef
  let K : Ideal P := Ideal.span (Set.range x)
  let g : ι × ι → P := fun ij => z ij.1 ij.2 - if ij.1 = ij.2 then m ij.1 else 0
  let G : Ideal P := Ideal.span (Set.range g)
  have hreg := (regular_quotient_cotInd P (ι × ι ⊕ ι) x hx).2.1
  rw [Fintype.card_sum, Fintype.card_prod] at hreg
  have hA : ringKrullDim (P ⧸ relIdeal z m ⊔ G) ≤ ringKrullDim (P ⧸ K) := by
    apply dim_quot_le_of_primes
    intro q hq hle
    have hrel : relIdeal z m ≤ q := le_trans le_sup_left hle
    have hG : G ≤ q := le_trans le_sup_right hle
    have hg : ∀ ij, g ij ∈ q := fun ij => hG (Ideal.subset_span ⟨ij, rfl⟩)
    have hm : ∀ i, m i ∈ q := by
      intro i
      have h1 : z.mulVec m i ∈ q := hrel (Ideal.subset_span ⟨i, rfl⟩)
      have h2 : m i * m i = z.mulVec m i - ∑ j, g (i, j) * m j := by
        simp only [g, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring
      have h3 : m i * m i ∈ q := by
        rw [h2]
        exact q.sub_mem h1 (q.sum_mem fun j _ => q.mul_mem_right _ (hg (i, j)))
      rcases hq.mem_or_mem h3 with h | h <;> exact h
    rw [Ideal.span_le]
    rintro _ ⟨(⟨i, j⟩ | i), rfl⟩
    · have h4 : z i j = g (i, j) + (if i = j then m i else 0) := by simp [g]
      show z i j ∈ q
      rw [h4]
      refine q.add_mem (hg _) ?_
      split_ifs
      · exact hm i
      · exact q.zero_mem
    · exact hm i
  have hB : ringKrullDim (P ⧸ relIdeal z m) ≤
      ringKrullDim (P ⧸ K) + ((Fintype.card ι * Fintype.card ι : ℕ) : WithBot ℕ∞) := by
    let Gb : Ideal (P ⧸ relIdeal z m) := G.map (Ideal.Quotient.mk _)
    have hsf : Gb.spanFinrank ≤ Fintype.card ι * Fintype.card ι := by
      have e : Gb = Ideal.span (Set.range (Ideal.Quotient.mk (relIdeal z m) ∘ g)) := by
        simp only [Gb, G, Ideal.map_span, Set.range_comp]
      rw [e]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
      rw [← Set.image_univ, ← Finset.coe_univ]
      exact (Set.ncard_coe_finset _ ▸ Set.ncard_image_le (Finset.finite_toSet _)).trans (by simp)
    have hdim : ringKrullDim (P ⧸ relIdeal z m) ≤
        ringKrullDim ((P ⧸ relIdeal z m) ⧸ Gb) + Gb.spanFinrank := by
      rw [ringKrullDim_le_iff_isMaximal_height_le]
      intro M hM
      apply height_le_ringKrullDim_quotient_add_spanFinrank
      rw [Ideal.map_le_iff_le_comap]
      have hc : Ideal.comap (Ideal.Quotient.mk (relIdeal z m)) M = maximalIdeal P :=
        IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [hc, Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have hz : z i j ∈ maximalIdeal P := hx.mem (Sum.inl (i, j))
      have hmi : m i ∈ maximalIdeal P := hx.mem (Sum.inr i)
      show z i j - (if i = j then m i else 0) ∈ maximalIdeal P
      refine (maximalIdeal P).sub_mem hz ?_
      split_ifs
      · exact hmi
      · exact (maximalIdeal P).zero_mem
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup (relIdeal z m) G)] at hdim
    exact hdim.trans (add_le_add hA (by exact_mod_cast hsf))
  rw [← hreg]
  refine (add_le_add hB le_rfl).trans (le_of_eq ?_)
  rw [add_assoc]
  norm_cast
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.chartIdeal_localization_isPrime :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (c : ι) (Q : Ideal (MvPolynomial ι P)) [Q.IsPrime],
      (maximalIdeal P).map (MvPolynomial.C : P →+* MvPolynomial ι P) ≤ Q →
      ((chartIdeal z m c).map (algebraMap _ (Localization.AtPrime Q))).IsPrime := by
  intro P _ _ ι _ _ z m hx c Q _ hQ
  obtain ⟨_, hcot⟩ := regular_polynomial_localization P ι Q hQ
  let φ : MvPolynomial ι P →+* Localization.AtPrime Q := algebraMap _ _
  let w : ι → Localization.AtPrime Q := fun j => φ (MvPolynomial.C (m j))
  let l : ι → Localization.AtPrime Q := fun j => φ (lam P c j)
  let y : Matrix ι ι (Localization.AtPrime Q) := z.map (φ.comp MvPolynomial.C)
  have h1 : CotInd (Localization.AtPrime Q) (Sum.elim (fun ij : ι × ι => y ij.1 ij.2) w) := by
    have h := hcot _ _ hx
    convert h using 1
    funext k
    rcases k with k | k <;> rfl
  have hl : l c = 1 := by
    simp [l, lam]
  have h2 := chartGen_cotInd (Localization.AtPrime Q) ι y w l c h1 hl
  have h3 := (regular_quotient_cotInd (Localization.AtPrime Q) _ _ h2).2.2
  have hf : ⇑φ ∘ chartGen z m c = Sum.elim (y.mulVec l) fun j : {j : ι // j ≠ c} => w j - l j * w c := by
    funext k
    rcases k with k | k
    · simp only [Function.comp, chartGen, Sum.elim_inl]
      rw [RingHom.map_mulVec, Matrix.map_map]
      rfl
    · simp [chartGen, w, l]
  have key : (chartIdeal z m c).map φ =
      Ideal.span (Set.range (Sum.elim (y.mulVec l) fun j : {j : ι // j ≠ c} => w j - l j * w c)) := by
    rw [chartIdeal, Ideal.map_span, ← Set.range_comp, hf]
  exact key ▸ h3
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem prime_sub (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) : (Ideal.span (x '' (s : Set κ))).IsPrime := by
  have h := (regular_quotient_cotInd R s (x ∘ ((↑) : s → κ)) (hx.comp _ Subtype.val_injective)).2.2
  have e : Set.range (x ∘ ((↑) : s → κ)) = x '' (s : Set κ) := by
    rw [Set.range_comp]
    congr 1
    ext a
    simp
  rwa [e] at h

private theorem not_mem_sub (R : Type) [CommRing R] [IsLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) (a : κ) (ha : a ∉ s) :
    x a ∉ Ideal.span (x '' (s : Set κ)) := by
  classical
  intro hmem
  obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).mp hmem
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul R (x i))] at hlx
  simp only [smul_eq_mul] at hlx
  let b : κ → R := Pi.single a 1
  have h0 : ∑ k, (b k - l k) * x k ∈ maximalIdeal R ^ 2 := by
    have hz : ∑ k, (b k - l k) * x k = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, hlx]
      simp [b, Pi.single_apply]
    rw [hz]
    exact zero_mem _
  have h1 := hx.indep _ h0 a
  rw [(Finsupp.mem_supported' R l).mp hl a ha, sub_zero] at h1
  simp only [b, Pi.single_eq_same] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem height_sub (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) :
    (s.card : ℕ∞) ≤ (Ideal.span (x '' (s : Set κ))).height := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    haveI := prime_sub R κ x hx s
    haveI := prime_sub R κ x hx (insert a s)
    have hlt : Ideal.span (x '' (s : Set κ)) < Ideal.span (x '' ((insert a s : Finset κ) : Set κ)) := by
      refine lt_of_le_of_ne (Ideal.span_mono (Set.image_mono (by simp))) fun e => ?_
      apply not_mem_sub R κ x hx s a ha
      rw [e]
      exact Ideal.subset_span ⟨a, by simp, rfl⟩
    have h1 := Ideal.height_strict_mono_of_isPrime hlt
    rw [Finset.card_insert_of_notMem ha, Nat.cast_succ]
    exact Order.add_one_le_of_lt (ih.trans_lt h1)

theorem UpperTheory.V.AlgebraTools.regular_localization_cotInd :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      ∀ (p : Ideal R) [p.IsPrime], p = Ideal.span (Set.range x) →
      p.height = (Fintype.card κ : ℕ) ∧ IsRegularLocalRing (Localization.AtPrime p) := by
  classical
  intro R _ _ κ _ x hx p _ hp
  have hge : ((Fintype.card κ : ℕ) : ℕ∞) ≤ p.height := by
    have h1 := height_sub R κ x hx Finset.univ
    rwa [Finset.card_univ, Finset.coe_univ, Set.image_univ, ← hp] at h1
  have hle : p.height ≤ ((Fintype.card κ : ℕ) : ℕ∞) := by
    have e : Ideal.span ((Finset.univ.image x : Finset R) : Set R) = p := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hp]
    have hmin : p ∈ (Ideal.span ((Finset.univ.image x : Finset R) : Set R)).minimalPrimes := by
      rw [e, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton p
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans ?_
    exact_mod_cast Finset.card_image_le
  have heq : p.height = ((Fintype.card κ : ℕ) : ℕ∞) := le_antisymm hle hge
  refine ⟨heq, ?_⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl,
    IsLocalization.AtPrime.under_maximalIdeal _ p, heq, ← Localization.AtPrime.map_eq_maximalIdeal]
  have hmap : Ideal.map (algebraMap R (Localization.AtPrime p)) p =
      Ideal.map (algebraMap R (Localization.AtPrime p)) (Ideal.span (Set.range x)) := congrArg _ hp
  rw [hmap, Ideal.map_span, ← Set.range_comp]
  have h3 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Localization.AtPrime p)
    (Set.finite_range (algebraMap R (Localization.AtPrime p) ∘ x))
  have h4 : (Set.range (algebraMap R (Localization.AtPrime p) ∘ x)).ncard ≤ Fintype.card κ := by
    rw [← Set.image_univ, ← Finset.coe_univ]
    exact (Set.ncard_coe_finset _ ▸ Set.ncard_image_le (Finset.finite_toSet _)).trans (by simp)
  exact_mod_cast h3.trans h4
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem mem_span_variables_of_coeff {O σ : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0) →
      f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X s

theorem UpperTheory.V.AlgebraTools.mvPowerSeries_cotInd :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
      ∀ (σ : Type) [Fintype σ], IsRegularLocalRing (MvPowerSeries σ O) ∧
        ringKrullDim (MvPowerSeries σ O) = ((Fintype.card σ + 1 : ℕ) : WithBot ℕ∞) ∧
        CotInd (MvPowerSeries σ O) (fun o : Option σ => o.elim (MvPowerSeries.C ϖ) MvPowerSeries.X) := by
  intro O _ _ _ ϖ hϖ σ _
  have hreg : IsRegularLocalRing (MvPowerSeries σ O) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O σ
  have hdim : ringKrullDim (MvPowerSeries σ O) = ((Fintype.card σ + 1 : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
      Nat.card_eq_fintype_card, add_comm]
    push_cast
    rfl
  have hm : maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  refine ⟨hreg, hdim, cotInd_of_span _ _ _ ?_ ?_⟩
  · apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨o, rfl⟩
      refine GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 ?_
      cases o with
      | none => simpa using hϖ.not_isUnit
      | some i => simp
    · intro f hf
      have h0 := GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hf
      rw [hm, Ideal.mem_span_singleton] at h0
      obtain ⟨c, hc⟩ := h0
      have h1 : f - MvPowerSeries.C (ϖ * c) ∈
          Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) := by
        refine mem_span_variables_of_coeff Finset.univ _ fun n hn => ?_
        have : n = 0 := Finsupp.ext fun i => hn i (Finset.mem_univ i)
        subst this
        simp [hc]
      have h2 : f = (f - MvPowerSeries.C (ϖ * c)) + MvPowerSeries.C ϖ * MvPowerSeries.C c := by
        rw [map_mul]; ring
      rw [h2]
      refine add_mem (Ideal.span_mono ?_ h1)
        (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨none, rfl⟩))
      rintro _ ⟨i, rfl⟩
      exact ⟨some i, rfl⟩
  · have h := hreg.spanFinrank_maximalIdeal
    rw [hdim] at h
    rw [Fintype.card_option]
    have h' : (maximalIdeal (MvPowerSeries σ O)).spanFinrank = Fintype.card σ + 1 := by
      exact_mod_cast h
    exact h'.ge
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem card_le_dim (R : Type) [CommRing R] [IsRegularLocalRing R] (r : ℕ) (x : Fin r → R)
    (hx : CotInd R x) : (r : WithBot ℕ∞) ≤ ringKrullDim R := by
  obtain ⟨s, y, -, -, hc⟩ := cotInd_extend R _ x hx
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hc, Fintype.card_fin]
  exact_mod_cast Nat.le_add_right r s

private theorem exists_max (R : Type) [CommRing R] [IsRegularLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) :
    ∃ (r : ℕ) (x : Fin r → R), CotInd R x ∧ (∀ k, x k ∈ I) ∧
      I ≤ Ideal.span (Set.range x) ⊔ maximalIdeal R ^ 2 := by
  classical
  let P : ℕ → Prop := fun r => ∃ x : Fin r → R, CotInd R x ∧ ∀ k, x k ∈ I
  have h0 : P 0 := ⟨Fin.elim0, ⟨fun k => k.elim0, fun _ _ k => k.elim0⟩, fun k => k.elim0⟩
  have hb : ∀ r, P r → r ≤ (maximalIdeal R).spanFinrank := by
    rintro r ⟨x, hx, -⟩
    have := card_le_dim R r x hx
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal] at this
    exact_mod_cast this
  obtain ⟨x, hx, hxI⟩ : P (Nat.findGreatest P (maximalIdeal R).spanFinrank) :=
    Nat.findGreatest_spec (Nat.zero_le _) h0
  refine ⟨_, x, hx, hxI, fun t ht => ?_⟩
  by_contra hn
  have h1 : P (Nat.findGreatest P (maximalIdeal R).spanFinrank + 1) := by
    refine ⟨Fin.cons t x, ⟨?_, ?_⟩, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact hI ht
      · exact hx.mem j
    · intro a ha
      rw [Fin.sum_univ_succ] at ha
      simp only [Fin.cons_zero, Fin.cons_succ] at ha
      have ha0 : a 0 ∈ maximalIdeal R := by
        by_contra hu
        have hu' : IsUnit (a 0) := by simpa using hu
        apply hn
        rw [← Ideal.unit_mul_mem_iff_mem _ hu']
        have h2 : ∑ i, a i.succ * x i ∈ Ideal.span (Set.range x) :=
          Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
        have h3 := sub_mem (Ideal.mem_sup_right (S := Ideal.span (Set.range x)) ha)
          (Ideal.mem_sup_left h2)
        simpa using h3
      have h4 : a 0 * t ∈ maximalIdeal R ^ 2 := by
        rw [sq]
        exact Ideal.mul_mem_mul ha0 (hI ht)
      have h5 : ∑ i, a i.succ * x i ∈ maximalIdeal R ^ 2 := by
        simpa using sub_mem ha h4
      intro k
      exact Fin.cases ha0 (fun j => hx.indep (fun i => a i.succ) h5 j) k
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact ht
      · exact hxI j
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hb _ h1) h1

theorem UpperTheory.V.AlgebraTools.exists_cotInd_of_regular_quotient :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (I : Ideal R) [IsRegularLocalRing (R ⧸ I)],
      ∃ (r : ℕ) (x : Fin r → R), CotInd R x ∧ Ideal.span (Set.range x) = I := by
  intro R _ _ I _
  have hne : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hI : I ≤ maximalIdeal R := le_maximalIdeal hne
  obtain ⟨r, x, hx, hxI, hle⟩ := exists_max R I hI
  refine ⟨r, x, hx, ?_⟩
  have hJ : Ideal.span (Set.range x) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hxI k
  obtain ⟨s, y, hxy, -, hc⟩ := cotInd_extend R _ x hx
  obtain ⟨-, hd, hp⟩ := regular_quotient_cotInd R _ x hx
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hy : CotInd (R ⧸ I) (fun j => Ideal.Quotient.mk I (y j)) := by
    refine ⟨fun j => hmax ▸ Ideal.mem_map_of_mem _ (hxy.mem (Sum.inr j)), fun a ha => ?_⟩
    choose b hb using fun j => Ideal.Quotient.mk_surjective (a j)
    have h1 : Ideal.Quotient.mk I (∑ j, b j * y j) ∈
        Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R ^ 2) := by
      rw [Ideal.map_pow, hmax]
      simpa [hb] using ha
    rw [Ideal.mem_quotient_iff_mem_sup] at h1
    have h2 : ∑ j, b j * y j ∈ Ideal.span (Set.range x) ⊔ maximalIdeal R ^ 2 :=
      sup_le le_sup_right hle h1
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h2
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hu
    have h3 : ∑ k, Sum.elim (fun i => - c i) b k * Sum.elim x y k ∈ maximalIdeal R ^ 2 := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, ← huv, neg_mul, Finset.sum_neg_distrib]
      simpa using hv
    intro j
    rw [← hb j, ← hmax]
    exact Ideal.mem_map_of_mem _ (hxy.indep _ h3 (Sum.inr j))
  have hs := card_le_dim _ s _ hy
  refine le_antisymm hJ fun t ht => ?_
  by_contra hn
  have : IsDomain (R ⧸ Ideal.span (Set.range x)) := (Ideal.Quotient.isDomain_iff_prime _).2 hp
  have h0 : Ideal.Quotient.mk (Ideal.span (Set.range x)) t ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h4 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hJ)
    (Ideal.Quotient.factor_surjective hJ) (mem_nonZeroDivisors_of_ne_zero h0)
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact ht)
  have h5 : ((s : WithBot ℕ∞) + 1) + (Fintype.card (Fin r) : ℕ) ≤ ringKrullDim R := by
    rw [← hd]
    gcongr
    exact le_trans (by gcongr) h4
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hc] at h5
  have h6 : s + 1 + Fintype.card (Fin r) ≤ Fintype.card (Fin r) + s := by exact_mod_cast h5
  omega
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem finOrb_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K K' L : Subgroup G} (hL : IsCompact (L : Set G)) (hK : K ≤ L) (hK' : IsOpen (K' : Set G)) (x : G) :
    FinOrb K K' x := by
  haveI : DiscreteTopology (G ⧸ K') := QuotientGroup.discreteTopology hK'
  have hc : Continuous fun g : G => ((g * x : G) : G ⧸ K') :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hL.image hc).finite_of_discrete).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨g, hK g.2, rfl⟩

private theorem iwC_le_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ KO k (Fin n) := by
  refine sup_le (sup_le GlobalTheory.StepData.KOne_le_KO inf_le_right) ?_
  rintro _ ⟨t, ht, rfl⟩
  refine iwahori_le_KO k (Fin n) (diagT_mem_iwahori fun i => ?_)
  obtain ⟨u, -, hu⟩ := ht i trivial
  rw [← hu]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit u)

theorem UpperTheory.V.AlgebraTools.heckePairIwC :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ), HeckePair (iwC k n C) ∧ HeckePair (KO k (Fin n)) ∧ ∀ (C' : Subgroup 𝓀[k]ˣ), FinOrb (iwC k n C') (iwC k n C) 1 ∧ FinOrb (KO k (Fin n)) (iwC k n C) 1 := by
  intro k _ _ _ _ n C
  have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO
  have ho : IsOpen (iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  exact ⟨fun x => finOrb_of_compact hc (iwC_le_KO k n C) ho x,
    fun x => finOrb_of_compact hc le_rfl GlobalTheory.SplitFlip.isOpen_KO x,
    fun C' => ⟨finOrb_of_compact hc (iwC_le_KO k n C') ho 1, finOrb_of_compact hc le_rfl ho 1⟩⟩
end
