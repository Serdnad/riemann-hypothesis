module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem aG_frame_nonneg (hd : d.AxH 𝒜) (h : d.S1) : 0 ≤ d.aG h d.wF hd.a4.choose := by
  classical
  have hespec := hd.a4.choose_spec
  unfold aG
  refine Finset.sum_nonneg fun c _ => ?_
  have hec : hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hespec.1 c
  have hk : ∃ k, d.thp (hd.sel k) c ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨q, hq, p, hp⟩ := hespec.2.2 (fun _ => 1)
    have e1 := hp c
    simp only [mul_one] at e1
    apply hq c
    rw [e1]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hno k, ratio_eq_of_eq_smul hec.2 (zero_smul (Ω c) (hd.a4.choose c)).symm, map_zero, mul_zero]
  obtain ⟨k, hk⟩ := hk
  have htm : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  have hr := eq_ratio_smul_on_line d (hd := hd) htm hec.1 hec.2
  have hr0 : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) ≠ 0 := by
    intro h0
    apply hk
    rw [hr, h0, zero_smul]
  have hthpmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  have hord : ∀ v, d.admitted c v → 0 ≤ d.ord c v d.wF (d.thp (hd.sel k) c) :=
    fun v hv => hd.ord_nonneg_Thp c v hv _ hthpmem hk
  have x2 := d.good_primes_properties hd h c
  have hsplit : ∀ p ∈ d.HtOne, d.nP h c d.wF (d.thp (hd.sel k) c) p =
      d.nP h c d.wF (hd.a4.choose c) p +
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) *
          WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c))) := by
    intro p hp
    have e2 := d.nP_smul hd h c hec.1 hec.2 hr0 hp
    rw [← hr] at e2
    exact e2
  have hkey := d.key_degree hd h c _ hr0
  have hfe := x2.2.2.1 _ _ hec.1 hec.2
  have hfm := d.use₈ hd h c _ hr0
  have eq1 : (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c d.wF (d.thp (hd.sel k) c) p * (d.dg (d.gen p) : ℤ)) =
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c d.wF (hd.a4.choose c) p * (d.dg (d.gen p) : ℤ)) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          (d.fze h c w : ℤ) *
            WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c)))) *
          (d.dg (d.gen p) : ℤ) := by
    rw [← finsum_mem_add_distrib' ?_ ?_]
    · exact finsum_mem_congr rfl fun p hp => by rw [hsplit p hp, add_mul]
    · refine hfe.subset ?_
      rintro p ⟨hp, hne⟩
      exact ⟨hp, fun h0 => hne (by simp [h0])⟩
    · refine hfm.subset ?_
      rintro p ⟨hp, hne⟩
      exact ⟨hp, fun h0 => hne (by simp [h0])⟩
  have hnn : 0 ≤ ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      d.nP h c d.wF (d.thp (hd.sel k) c) p * (d.dg (d.gen p) : ℤ) :=
    finsum_nonneg fun p => finsum_nonneg fun hp =>
      mul_nonneg (d.nP_nonneg hd h c hp _ _ hord) (Nat.cast_nonneg _)
  rw [eq1, hkey, add_zero] at hnn
  exact hnn

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem substRowZero_fix_of_degree_zero (x : Fin (d.N + 1) → K) (q : KTp K d.D d.N)
    (hq : ∀ s ∈ q.support, ∑ j, s (0, j) = 0) : d.sub0 x q = q := by
  conv_lhs => rw [q.as_sum]

  rw [map_sum]
  conv_rhs => rw [q.as_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h0 : ∀ j, s (0, j) = 0 := fun j =>
    (Finset.sum_eq_zero_iff.mp (hq s hs)) j (Finset.mem_univ _)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun v hv => ?_
  have hv0 : v.1 ≠ 0 := by
    intro h1
    apply Finsupp.mem_support_iff.mp hv
    have e : ((0 : Fin (d.D + 1)), v.2) = v := Prod.ext h1.symm rfl
    rw [← e]
    exact h0 v.2
  simp [hv0]

theorem pi_free (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (f : A c) :
    ∃ Pp Pm : KTp K d.D d.N, Pm ≠ 0 ∧ (∀ x, d.sub0 x Pp = Pp) ∧ (∀ x, d.sub0 x Pm = Pm) ∧
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pp =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c f p := by
  classical
  have hfix : ∀ p ∈ d.HtOne, d.nPMM h c f p ≠ 0 → ∀ x, d.sub0 x (d.gen p) = d.gen p := by
    intro p hp hn x
    have hw : ∃ w, w ∈ d.GoodP c p := by
      by_contra hno
      push_neg at hno
      exact hn (by simp [Data.nPMM, hno])
    have hm := d.GeneratorMultiHomogeneous hd h c p hp hw
    refine d.substRowZero_fix_of_degree_zero x (d.gen p) fun s hs => ?_
    simpa using hm s hs 0
  rw [finprod_mem_def, finprod_def]
  split_ifs with hfin
  · set T := hfin.toFinset with hT
    have hTmem : ∀ p ∈ T, p ∈ d.HtOne ∧ d.nPMM h c f p ≠ 0 := by
      intro p hpT
      have hpT' : p ∈ Function.mulSupport (d.HtOne.mulIndicator fun p =>
          (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)) (d.gen p) ^ d.nPMM h c f p) :=
        (Set.Finite.mem_toFinset (hs := hfin)).mp hpT
      rw [Function.mem_mulSupport] at hpT'
      by_cases hp : p ∈ d.HtOne
      · refine ⟨hp, fun h0 => hpT' ?_⟩
        simp [Set.mulIndicator_of_mem hp, h0]
      · simp [hp] at hpT'
    refine ⟨∏ p ∈ T, d.gen p ^ (d.nPMM h c f p).toNat,
      ∏ p ∈ T, d.gen p ^ (-d.nPMM h c f p).toNat, ?_, ?_, ?_, ?_⟩
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (d.generator_ne_zero_of_height p (hTmem p hp).1)
    · intro x
      rw [map_prod]
      exact Finset.prod_congr rfl fun p hp => by
        rw [map_pow, hfix p (hTmem p hp).1 (hTmem p hp).2 x]
    · intro x
      rw [map_prod]
      exact Finset.prod_congr rfl fun p hp => by
        rw [map_pow, hfix p (hTmem p hp).1 (hTmem p hp).2 x]
    · rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Set.mulIndicator_of_mem (hTmem p hp).1]
      have ha : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)),
          (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)).eq_iff]
        exact d.generator_ne_zero_of_height p (hTmem p hp).1
      rw [map_pow, map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
      congr 1
      omega
  · exact ⟨1, 1, one_ne_zero, fun x => map_one _, fun x => map_one _, by simp⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
