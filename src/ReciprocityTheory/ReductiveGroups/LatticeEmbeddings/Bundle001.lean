module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.SetTheory.Cardinal.Rat
public import Mathlib.Topology.MetricSpace.Perfect

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain

namespace ReciprocityTheory.ChartRestriction.B3.IotaPl

theorem norm_le_one_of_isIntegral_int {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨f, hf, hfx⟩ := hx
  set n := f.natDegree with hn
  have hsum := hf.as_sum
  rw [hsum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hfx
  have key : x ^ n = -∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap ℤ ℂ_[p]) x (Polynomial.C (f.coeff i) * Polynomial.X ^ i) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hfx
  have hx1 : 1 ≤ ‖x‖ := hlt.le
  have bound : ‖∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap ℤ ℂ_[p]) x (Polynomial.C (f.coeff i) * Polynomial.X ^ i)‖ ≤
        ‖x‖ ^ (n - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖(algebraMap ℤ ℂ_[p]) (f.coeff i)‖ ≤ 1 := by
      have h := IsUltrametricDist.norm_intCast_le_one ℂ_[p] (f.coeff i)
      first
        | (simpa using h)
        | (rw [algebraMap_int_eq, eq_intCast]; exact h)
        | (convert h using 2; exact (algebraMap ℤ ℂ_[p]).eq_intCast _)
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖(algebraMap ℤ ℂ_[p]) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hx1 hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (n - 1) := one_mul _
  have h2 : ‖x‖ ^ n ≤ ‖x‖ ^ (n - 1) := by
    rw [← norm_pow, key, norm_neg]
    exact bound
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at key
    simp at key
  · have h3 : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ hlt (by omega)
    linarith

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_int_le (ι : K →+* ℂ_[p]) (y : 𝓞 K) : ‖ι (y : K)‖ ≤ 1 := by
  obtain ⟨f, hf, hfy⟩ := NumberField.RingOfIntegers.isIntegral_coe y
  refine norm_le_one_of_isIntegral_int ⟨f, hf, ?_⟩
  have e : (algebraMap ℤ ℂ_[p]) = ι.comp (algebraMap ℤ K) := RingHom.ext_int _ _
  rw [e, ← Polynomial.hom_eval₂, hfy, map_zero]

def smallIdeal (ι : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {y | ‖ι (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ι ((a + b : 𝓞 K) : K) = ι (a : K) + ι (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : ι ((c • a : 𝓞 K) : K) = ι (c : K) * ι (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le ι c
    nlinarith [norm_nonneg (ι (c : K)), norm_nonneg (ι (a : K))]

theorem mem_smallIdeal (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : 𝓞 K) ∈ smallIdeal ι := (Ideal.eq_top_iff_one _).mp h
    rw [mem_smallIdeal] at h1
    simp at h1
  · intro a b hab
    simp only [mem_smallIdeal] at hab ⊢
    have e : ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K) := by simp
    rw [e, norm_mul] at hab
    by_contra hc
    push_neg at hc
    obtain ⟨ha, hb⟩ := hc
    nlinarith [norm_int_le ι a, norm_int_le ι b]

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have e : (p : ℂ_[p]) = (((algebraMap ℚ_[p] (PadicAlgCl p)) (p : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    first
      | simp
      | (rw [map_natCast]; exact (map_natCast UniformSpace.Completion.coeRingHom p).symm)
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  first
    | exact Padic.norm_p_lt_one
    | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
    | (rw [padicNormE.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))

end ReciprocityTheory.ChartRestriction.B3.IotaPl

namespace ReciprocityTheory.ChartRestriction.B3

end ReciprocityTheory.ChartRestriction.B3
end
end

section

noncomputable section
open Cardinal Filter Topology

namespace ReciprocityTheory.ChartRestriction.T1

theorem lat_mk_le_of_denseRange {D X : Type} [TopologicalSpace X] [FirstCountableTopology X] [T2Space X]
    (f : D → X) (hf : DenseRange f) : #X ≤ #D ^ ℵ₀ := by
  classical
  have hseq : ∀ x : X, ∃ u : ℕ → D, Tendsto (f ∘ u) atTop (𝓝 x) := by
    intro x
    have hx : x ∈ closure (Set.range f) := by rw [hf.closure_range]; exact Set.mem_univ x
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hx
    choose u hu using hv
    refine ⟨u, ?_⟩
    have hfu : f ∘ u = v := funext hu
    rw [hfu]
    exact hlim
  choose g hg using hseq

  have hinj : Function.Injective g := by
    intro x y hxy
    have h' : Tendsto (f ∘ g x) atTop (𝓝 y) := by rw [hxy]; exact hg y
    exact tendsto_nhds_unique (hg x) h'
  calc Cardinal.mk X ≤ Cardinal.mk (ℕ → D) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.mk D ^ ℵ₀ := by rw [← Cardinal.mk_nat, Cardinal.power_def]

theorem lat_mk_Cp (p : ℕ) [Fact p.Prime] : #ℂ_[p] = 𝔠 := by
  apply le_antisymm
  · have h1 : Cardinal.mk ℚ_[p] ≤ 𝔠 := by
      calc Cardinal.mk ℚ_[p] ≤ Cardinal.mk ℚ ^ ℵ₀ :=
            lat_mk_le_of_denseRange ((↑) : ℚ → ℚ_[p]) (Padic.denseRange_ratCast p)
        _ = 𝔠 := by rw [Cardinal.mkRat, Cardinal.aleph0_power_aleph0]
    have h2 : Cardinal.mk (PadicAlgCl p) ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans
        (max_le h1 Cardinal.aleph0_le_continuum)
    calc Cardinal.mk ℂ_[p] ≤ Cardinal.mk (PadicAlgCl p) ^ ℵ₀ :=
          lat_mk_le_of_denseRange ((↑) : PadicAlgCl p → ℂ_[p]) UniformSpace.Completion.denseRange_coe
      _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right h2
      _ = 𝔠 := Cardinal.continuum_power_aleph0
  ·
    obtain ⟨g, -, -, hg⟩ := Perfect.exists_nat_bool_injection (C := (Set.univ : Set ℂ_[p]))
      ⟨isClosed_univ, PerfectSpace.univ_preperfect⟩ ⟨0, trivial⟩
    calc 𝔠 = Cardinal.mk (ℕ → Bool) := by
          rw [← Cardinal.two_power_aleph0, ← Cardinal.mk_nat, ← Cardinal.mk_bool, Cardinal.power_def]
      _ ≤ Cardinal.mk ℂ_[p] := Cardinal.mk_le_of_injective hg

end ReciprocityTheory.ChartRestriction.T1

namespace ReciprocityTheory.ChartRestriction.B3

theorem iop_extEmb {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  letI : Algebra R K := f.toAlgebra
  letI : Algebra R L := g.toAlgebra
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 f.injective
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 g.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L

  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hR hK
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hR (hKL ▸ hK)
  simp only [Cardinal.lift_id] at h1 h2
  have hst : Cardinal.mk s = Cardinal.mk t := by rw [← h1, ← h2, hKL]
  obtain ⟨e⟩ := Cardinal.eq.1 hst
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let eA : Algebra.adjoin R (Set.range (Subtype.val : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range (Subtype.val : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L eA.toRingEquiv, fun r => ?_⟩
  have e1 : f r = algebraMap (Algebra.adjoin R (Set.range (Subtype.val : s → K))) K
      (algebraMap R _ r) := rfl
  have e2 : g r = algebraMap (Algebra.adjoin R (Set.range (Subtype.val : t → L))) L
      (algebraMap R _ r) := rfl
  rw [e1, IsAlgClosure.equivOfEquiv_algebraMap, e2]
  congr 1
  exact eA.commutes r

end ReciprocityTheory.ChartRestriction.B3
end
end
