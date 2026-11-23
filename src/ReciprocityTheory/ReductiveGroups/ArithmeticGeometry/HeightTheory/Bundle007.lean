module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Mathlib.RingTheory.Length
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle003
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Jacobson.Artinian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle004
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre

open IsLocalRing

theorem avoid {B : Type*} [CommRing B] [IsNoetherianRing B] (M q : Ideal B) [hM : M.IsMaximal] (w : B)
    (hchain : ∀ P : Ideal B, P.IsPrime → q ≤ P → P ≤ M → w ∈ P → P = M) :
    ∃ s ∉ M, ∀ P : Ideal B, P.IsPrime → q ≤ P → w ∈ P → s ∉ P → P = M := by
  classical
  haveI := hM.isPrime
  set I : Ideal B := q ⊔ Ideal.span {w} with hI
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
  have hprop : ∀ p ∈ I.minimalPrimes, p.IsPrime ∧ I ≤ p := fun p hp => hp.1
  have hnot : ∀ p ∈ I.minimalPrimes, p ≠ M → ¬ p ≤ M := by
    intro p hp hne hle
    obtain ⟨hpp, hIp⟩ := hprop p hp
    exact hne (hchain p hpp (le_trans le_sup_left hIp) hle
      (hIp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))
  have hex : ∀ p ∈ I.minimalPrimes, p ≠ M → ∃ x ∈ p, x ∉ M :=
    fun p hp hne => SetLike.not_le_iff_exists.mp (hnot p hp hne)
  let f : Ideal B → B := fun p =>
    if h : p ∈ I.minimalPrimes ∧ p ≠ M then (hex p h.1 h.2).choose else 1
  let T := hfin.toFinset.filter (· ≠ M)
  refine ⟨∏ p ∈ T, f p, ?_, ?_⟩
  · intro hmem
    obtain ⟨p, hpT, hpM⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset] at hpT
    have h1 := (hex p hpT.1 hpT.2).choose_spec.2
    simp only [f, dif_pos hpT] at hpM
    exact h1 hpM
  · intro P hP hqP hwP hsP
    have hIP : I ≤ P := sup_le hqP ((Ideal.span_singleton_le_iff_mem P).mpr hwP)
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le hIP
    by_cases hpM : p = M
    · rw [hpM] at hpP
      exact (hM.eq_of_le hP.ne_top hpP).symm
    · exfalso
      apply hsP
      apply Ideal.IsPrime.prod_mem_iff.mpr
      refine ⟨p, ?_, ?_⟩
      · simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨hp, hpM⟩
      · simp only [f, dif_pos (And.intro hp hpM)]
        exact hpP (hex p hp hpM).choose_spec.1

theorem finite_of_fibre {O T : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing T] [IsDomain T] [IsNoetherianRing T] [Algebra O T]
    [Algebra.FiniteType O T] (ϖ : O) (hϖ : Irreducible ϖ)
    (hex : ∃ P : Ideal T, P.IsPrime ∧ algebraMap O T ϖ ∈ P)
    (huniq : ∀ P P' : Ideal T, P.IsPrime → P'.IsPrime → algebraMap O T ϖ ∈ P → algebraMap O T ϖ ∈ P' →
      P = P') : Module.Finite O T := by
  classical
  set w := algebraMap O T ϖ with hw
  set J : Ideal T := Ideal.span {w} with hJ
  obtain ⟨P0, hP0, hwP0⟩ := hex
  have hJtop : J ≠ ⊤ := fun h => hP0.ne_top (eq_top_iff.2 (h ▸ (Ideal.span_singleton_le_iff_mem P0).2 hwP0))

  have hdim : Ring.KrullDimLE 0 (T ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    obtain ⟨N, hN, hIN⟩ := Ideal.exists_le_maximal I hI.ne_top
    have hwI : w ∈ Ideal.comap (Ideal.Quotient.mk J) I := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self w)]
      exact I.zero_mem
    have hwN : w ∈ Ideal.comap (Ideal.Quotient.mk J) N := Ideal.comap_mono hIN hwI
    have e := huniq _ _ (Ideal.comap_isPrime _ I) (Ideal.comap_isPrime _ N) hwI hwN
    have : I = N := by
      have h1 := congrArg (Ideal.map (Ideal.Quotient.mk J)) e
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    rw [this]; exact hN
  have hart : IsArtinianRing (T ⧸ J) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

  have hmJ : maximalIdeal O ≤ Ideal.comap (algebraMap O T) J := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_span_singleton_self w
  let _ : Algebra (O ⧸ maximalIdeal O) (T ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hmJ
  have hmk : ∀ c : O, algebraMap (O ⧸ maximalIdeal O) (T ⧸ J) (Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk J (algebraMap O T c) := fun c => rfl
  have : IsScalarTower O (O ⧸ maximalIdeal O) (T ⧸ J) := IsScalarTower.of_algebraMap_eq fun c => (hmk c).symm
  have : Algebra.FiniteType O (T ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O J) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType (O ⧸ maximalIdeal O) (T ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  have : IsJacobsonRing (O ⧸ maximalIdeal O) := by
    let _ := Ideal.Quotient.field (maximalIdeal O); infer_instance
  have : Module.Finite (O ⧸ maximalIdeal O) (T ⧸ J) := Module.finite_of_isArtinianRing _ _
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := O ⧸ maximalIdeal O) (M := T ⧸ J)
  choose S hS using fun i => Ideal.Quotient.mk_surjective (g i)
  have hgen : ∀ x : T, ∃ c : Fin n → O, ∃ y : T, x = ∑ i, c i • S i + ϖ • y := by
    intro x
    have hx : Ideal.Quotient.mk J x ∈ Submodule.span (O ⧸ maximalIdeal O) (Set.range g) := by
      rw [hg]; trivial
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    choose c hc using fun i => Ideal.Quotient.mk_surjective (cb i)
    have hmem : x - ∑ i, c i • S i ∈ J := by

      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, ← hcb, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc i, ← hS i, Algebra.smul_def, Algebra.smul_def, map_mul, hmk]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨c, y, ?_⟩
    rw [Algebra.smul_def, ← hw, mul_comm, hy]
    abel
  have hsep : ∀ x : T, (∀ k : ℕ, ∃ y : T, x = ϖ ^ k • y) → x = 0 := by
    intro x hx
    have h0 := Ideal.iInf_pow_eq_bot_of_isDomain J hJtop
    have : x ∈ ⨅ k : ℕ, J ^ k := by
      rw [Ideal.mem_iInf]
      intro k
      obtain ⟨y, rfl⟩ := hx k
      rw [hJ, Ideal.span_singleton_pow, Algebra.smul_def, map_pow, ← hw]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [h0] at this
    exact (Submodule.mem_bot T).1 this
  have : IsAdicComplete (Ideal.span {ϖ}) O := hϖ.maximalIdeal_eq ▸ inferInstance
  have htop := SpanTopOfComplete.span_eq_top_of_complete ϖ hsep S hgen
  exact ⟨Submodule.fg_def.2 ⟨Set.range S, Set.finite_range S, htop⟩⟩

end ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound

open IsLocalRing

lemma le_dim_quot {R : Type*} [CommRing R] (p P m : Ideal R) [hp : p.IsPrime] [hP : P.IsPrime]
    [hm : m.IsPrime] (h1 : p < P) (h2 : P < m) : (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  rw [ringKrullDim_quotient]
  let a : PrimeSpectrum.zeroLocus (p : Set R) := ⟨⟨p, hp⟩, fun x hx => hx⟩
  let b : PrimeSpectrum.zeroLocus (p : Set R) := ⟨⟨P, hP⟩, fun x hx => h1.le hx⟩
  let c : PrimeSpectrum.zeroLocus (p : Set R) := ⟨⟨m, hm⟩, fun x hx => (h1.trans h2).le hx⟩
  have hab : a < b := h1
  have hbc : b < c := h2
  have hs : ((2 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) :=
    Order.LTSeries.length_le_krullDim (((RelSeries.singleton _ a).snoc b
      (by first | exact hab | exact ⟨_, _, rfl, hab⟩ | simpa using hab)).snoc c
      (by first | exact hbc | exact ⟨_, _, rfl, hbc⟩ | (simp only [RelSeries.last_snoc]; exact hbc) | simpa using hbc))
  exact_mod_cast hs

lemma one_le_dim {R : Type*} [CommRing R] (p m : Ideal R) [p.IsPrime] [m.IsPrime] (h : p < m) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
  let a : PrimeSpectrum R := ⟨p, inferInstance⟩
  let b : PrimeSpectrum R := ⟨m, inferInstance⟩
  have hab : a < b := h
  have hs : ((1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R) :=
    Order.LTSeries.length_le_krullDim ((RelSeries.singleton _ a).snoc b hab)
  exact_mod_cast hs

theorem local_step {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] (M : Ideal B) [hM : M.IsMaximal]
    (w e : B) (hw : w ∈ M) (hw0 : w ≠ 0) (he : e ≠ 0) :
    ∃ q : Ideal B, q.IsPrime ∧ q ≤ M ∧ e ∉ q ∧ w ∉ q ∧
      ∀ P : Ideal B, P.IsPrime → q ≤ P → P ≤ M → w ∈ P → P = M := by
  classical
  let R := Localization.AtPrime M
  haveI : IsDomain R := IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors M)
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors M)
  have hcm : (IsLocalRing.maximalIdeal R).comap (algebraMap B R) = M :=
    Localization.AtPrime.under_maximalIdeal (I := M)
  have hh : algebraMap B R (e * w) ≠ 0 := by
    intro h
    exact mul_ne_zero he hw0 (hinj (by rw [h, map_zero]))
  have hmax : (⊥ : Ideal R) < IsLocalRing.maximalIdeal R := by
    rw [bot_lt_iff_ne_bot]
    intro h
    have hw' : algebraMap B R w ∈ IsLocalRing.maximalIdeal R := by
      rw [← Ideal.mem_comap, hcm]; exact hw
    rw [h, Ideal.mem_bot] at hw'
    exact hw0 (hinj (by rw [hw', map_zero]))
  have hdim : 1 ≤ ringKrullDim R := one_le_dim ⊥ (IsLocalRing.maximalIdeal R) hmax
  obtain ⟨p, hp, hpd, hpn⟩ := ReciprocityTheory.ChartRestriction.G.T0.av_prime_dim_one hdim _ hh
  haveI := hp
  refine ⟨p.comap (algebraMap B R), Ideal.comap_isPrime _ _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hcm]
    exact IsLocalRing.le_maximalIdeal hp.ne_top hx
  · intro he'
    apply hpn
    rw [map_mul]
    exact p.mul_mem_right _ he'
  · intro hw'
    apply hpn
    rw [map_mul]
    exact p.mul_mem_left _ hw'
  · intro P hP hqP hPM hwP
    by_contra hne
    have hdisj : Disjoint (M.primeCompl : Set B) P := by
      rw [Set.disjoint_left]
      intro x hx hxP
      exact hx (hPM hxP)
    haveI hP' : (P.map (algebraMap B R)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M.primeCompl R P hP hdisj
    have hcomap : (P.map (algebraMap B R)).comap (algebraMap B R) = P :=
      IsLocalization.under_map_of_isPrime_disjoint M.primeCompl R hP hdisj
    have h1 : p < P.map (algebraMap B R) := by
      refine lt_of_le_of_ne ?_ ?_
      · have hpe : (p.comap (algebraMap B R)).map (algebraMap B R) = p :=
          IsLocalization.map_under M.primeCompl R p
        rw [← hpe]
        exact Ideal.map_mono hqP
      · intro heq
        apply hpn
        rw [heq, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hwP)
    have h2 : P.map (algebraMap B R) < IsLocalRing.maximalIdeal R := by
      refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP'.ne_top) ?_
      intro heq
      apply hne
      rw [← hcomap, heq, hcm]
    have h3 := le_dim_quot p (P.map (algebraMap B R)) (IsLocalRing.maximalIdeal R) h1 h2
    rw [hpd] at h3
    exact absurd h3 (by decide)

end ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

abbrev OT (K : Type) [Field K] [NumberField K] (D N : ℕ) : Type :=
  MvPolynomial (TVar D N) (𝓞 K)

abbrev KTp (K : Type) [Field K] (D N : ℕ) : Type := MvPolynomial (TVar D N) K

abbrev KTf (K : Type) [Field K] (D N : ℕ) : Type := FractionRing (KTp K D N)

noncomputable def laT {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Ideal (OT K D N) :=
  Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) la.asIdeal

instance laT_isPrime {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : (laT D N la).IsPrime := by
  have e := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := TVar D N) la.asIdeal
  have : IsDomain (OT K D N ⧸ laT D N la) := MulEquiv.isDomain _ e.toRingEquiv.symm.toMulEquiv
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

abbrev Op {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Type :=
  Localization.AtPrime (laT D N la)

noncomputable def OTtoKT (K : Type) [Field K] [NumberField K] (D N : ℕ) : OT K D N →+* KTp K D N :=
  MvPolynomial.map (algebraMap (𝓞 K) K)

noncomputable def OpToKT {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Op D N la →+* KTf K D N :=
  IsLocalization.lift (M := (laT D N la).primeCompl) (S := Op D N la)
    (g := (algebraMap (KTp K D N) (KTf K D N)).comp (OTtoKT K D N)) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      intro h
      have hy : (y : OT K D N) ≠ 0 := fun h0 => y.2 (by rw [h0]; exact (laT D N la).zero_mem)
      apply hy
      have h2 : OTtoKT K D N (y : OT K D N) = 0 :=
        (IsFractionRing.injective (KTp K D N) (KTf K D N)) (by simpa using h)
      exact MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
        (by simpa [OTtoKT] using h2))

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

def S1 : Prop := ∀ c, Function.Injective (d.sH c)

noncomputable def KTtoS (h : d.S1) (c : ι) : KTf K d.D d.N →+* OmS (Ω c) d.D d.N :=
  IsFractionRing.lift (A := KTp K d.D d.N) (g := (d.sH c).toRingHom) (h c)

noncomputable def OpToS (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    Op d.D d.N la →+* OmS (Ω c) d.D d.N :=
  (d.KTtoS h c).comp (OpToKT d.D d.N la)

noncomputable def OTtoS (c : ι) : OT K d.D d.N →+* OmS (Ω c) d.D d.N :=
  (d.sH c).toRingHom.comp (OTtoKT K d.D d.N)

def PlOver (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    Set (AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ x : OT K d.D d.N, 0 ≤ w (d.OTtoS c x) ∧
    (0 < w (d.OTtoS c x) ↔ x ∈ laT d.D d.N la)}

noncomputable def Wres (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) :
    AddValuation (Ω c) (WithTop ℤ) :=
  w.comap (algebraMap (Ω c) (OmS (Ω c) d.D d.N))

noncomputable def fze (h : d.S1) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) : ℕ :=
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI := resAlg (F := KTf K d.D d.N) w
  Module.finrank (IsLocalRing.ResidueField ((vRing w).comap (algebraMap (KTf K d.D d.N)
    (OmS (Ω c) d.D d.N)))) (IsLocalRing.ResidueField (vRing w))

end Data

namespace Data

variable (d : Data K ι Ω WT A)

open scoped TensorProduct

noncomputable abbrev algOp (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) :=
  (d.OpToS h la c).toAlgebra

noncomputable def bvecG (sel : Fin d.del → Fin d.np) (e : ∀ c, A c) (k : Fin d.del) :
    ∀ c, OmS (Ω c) d.D d.N :=
  fun c => algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c))

def AdmissibleOmegaFamiliesAtPrimeOfSection (e : ∀ c, A c) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Set (∀ c, OmS (Ω c) d.D d.N) :=
  {y | ∀ c, ∀ w ∈ d.PlOver la c,
    0 ≤ w (y c) + ((d.ord c (d.Wres c w) d.wF (e c) : ℤ) : WithTop ℤ)}

noncomputable def IL (h : d.S1) (sel : Fin d.del → Fin d.np) (e : ∀ c, A c)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
  let A0 := Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection e la)
  let B := Submodule.span (Op d.D d.N la) (Set.range (d.bvecG sel e))
  ((Module.length (Op d.D d.N la) (A0 ⧸ B.comap A0.subtype)).toNat : ℝ)

noncomputable def Nl (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ c, ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (d.ord c (d.Wres c w) (d.n1 • d.wde) (d.et c) : ℝ)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
