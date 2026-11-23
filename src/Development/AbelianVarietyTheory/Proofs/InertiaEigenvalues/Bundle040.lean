module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Semigroup
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Algebra.Polynomial.Monomial

@[expose] public section

section

namespace GlobalTheory

open Polynomial in
private lemma norm_le_one_of_monic_root_lemma {K : Type*} [NormedField K] [IsUltrametricDist K]
    {p : K[X]} (hp : p.Monic) (hc : ∀ i, ‖p.coeff i‖ ≤ 1) {x : K} (hx : p.eval x = 0) :
    ‖x‖ ≤ 1 := by
  by_contra h
  push_neg at h
  rw [hp.as_sum] at hx
  simp only [eval_add, eval_pow, eval_X, Polynomial.eval_finsetSum, eval_mul, eval_C] at hx
  set n := p.natDegree
  have hxn : x ^ n = -∑ i ∈ Finset.range n, p.coeff i * x ^ i := eq_neg_of_add_eq_zero_left hx
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at hxn
    simp at hxn
  have hle : ‖x ^ n‖ ≤ ‖x‖ ^ (n - 1) := by
    rw [hxn, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖p.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) := by
          gcongr
          · exact hc i
          · exact h.le
      _ = ‖x‖ ^ (n - 1) := one_mul _
  rw [norm_pow] at hle
  have hlt : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ h (by omega)
  linarith


open Polynomial in
theorem _root_.GlobalTheory.padicAlgCl_embedding_bounded_continuous (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [TopologicalSpace O] [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O))
    (ι : O →+* PadicAlgCl l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) :
    (∀ a, ‖ι a‖ ≤ 1) ∧ (∀ a ∈ IsLocalRing.maximalIdeal O, ‖ι a‖ < 1) ∧ Continuous ι := by
  set g : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom
  have hg : ι.comp (algebraMap ℤ_[l] O) = g := by
    ext z
    exact hι z
  have h1 : ∀ a, ‖ι a‖ ≤ 1 := by
    intro a
    obtain ⟨p, hpm, hpa⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a
    have hroot : (p.map g).eval (ι a) = 0 := by
      rw [eval_map, ← hg, ← hom_eval₂]
      rw [hpa, map_zero]
    refine norm_le_one_of_monic_root_lemma (hpm.map g) (fun i => ?_) hroot
    rw [coeff_map]
    change ‖algebraMap ℚ_[l] (PadicAlgCl l) ((p.coeff i : ℤ_[l]) : ℚ_[l])‖ ≤ 1
    rw [PadicAlgCl.norm_extends]
    exact PadicInt.norm_le_one _
  have hunit : ∀ u : Oˣ, ‖ι u‖ = 1 := by
    intro u
    have hprod : ‖ι u‖ * ‖ι ↑u⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have ha := h1 u
    have hb := h1 ↑u⁻¹
    have ha0 := norm_nonneg (ι u)
    have hb0 := norm_nonneg (ι ↑u⁻¹)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖlt : ‖ι ϖ‖ < 1 := by
    refine lt_of_le_of_ne (h1 ϖ) fun heq => ?_
    set x := algebraMap ℤ_[l] O (l : ℤ_[l])
    have hx : ‖ι x‖ = ‖(l : ℚ_[l])‖ := by
      rw [hι, PadicAlgCl.norm_extends]
      push_cast
      rfl
    have hlt : ‖ι x‖ < 1 := hx ▸ Padic.norm_p_lt_one
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, map_zero, norm_zero] at hx
      have : (0 : ℝ) < ‖(l : ℚ_[l])‖ := by
        rw [Padic.norm_p]
        have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
        positivity
      linarith
    obtain ⟨n, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [hxu, map_mul, norm_mul, map_pow, norm_pow, heq, one_pow, mul_one, hunit] at hlt
    exact lt_irrefl _ hlt
  have hpow : ∀ n : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal O ^ n, ‖ι a‖ ≤ ‖ι ϖ‖ ^ n := by
    intro n a ha
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, norm_mul, map_pow, norm_pow]
    calc ‖ι b‖ * ‖ι ϖ‖ ^ n ≤ 1 * ‖ι ϖ‖ ^ n := by gcongr; exact h1 b
      _ = ‖ι ϖ‖ ^ n := one_mul _
  refine ⟨h1, fun a ha => ?_, ?_⟩
  · have := hpow 1 a (by rwa [pow_one])
    rw [pow_one] at this
    exact this.trans_lt hϖlt
  · refine continuous_of_continuousAt_zero ι ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖlt
    have hopen := (isAdic_iff.mp hO).1 n
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with a ha
    rw [dist_zero_right]
    exact (hpow n a ha).trans_lt hn

end GlobalTheory
end

section

namespace GlobalTheory.UnitBallBasis

theorem exists_basis_mem_iff_norm_le_one {l : ℕ} [inst : Fact (Nat.Prime l)] {L O V : Type}
    [inst_1 : Field L] [inst_2 : Algebra ℚ_[l] L] [inst_3 : CommRing O] [inst_4 : Algebra O L]
    [inst_5 : Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (hc : ∀ (a : ℤ_[l]), algebraMap O L (algebraMap ℤ_[l] O a) = algebraMap ℚ_[l] L (a : ℚ_[l]))
    (hd : ∀ (a : L), ∃ (y : ℤ_[l]), y ≠ 0 ∧ ∃ (o : O),
      algebraMap O L o = algebraMap ℚ_[l] L (y : ℚ_[l]) * a)
    [inst_8 : AddCommGroup V] [inst_9 : Module L V] [inst_10 : Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] L V] [inst_12 : Module O V] [IsScalarTower O L V]
    (S : Submodule O V) (hfg : S.FG) (hfree : Module.Free O S)
    (hspan : Submodule.span L (S : Set V) = ⊤) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] V), ∀ (x : V),
      x ∈ S ↔ ∀ (i : Fin n), ‖w.repr x i‖ ≤ (1 : ℝ) := by
  classical
  have := hfree
  have : Module.Finite O S := Module.Finite.iff_fg.mpr hfg
  let b := Module.Free.chooseBasis O S
  let c := Module.Free.chooseBasis ℤ_[l] O

  have hsm : ∀ (a : ℤ_[l]) (v : V), (algebraMap ℤ_[l] O a) • v = (a : ℚ_[l]) • v := by
    intro a v
    rw [← algebraMap_smul L (algebraMap ℤ_[l] O a) v, hc, algebraMap_smul]

  let J := Module.Free.ChooseBasisIndex ℤ_[l] O × Module.Free.ChooseBasisIndex O S
  let e : J → V := fun j => c j.1 • (b j.2 : V)
  have he : ∀ j, e j ∈ S := fun j => S.smul_mem _ (b j.2).2
  have hin : ∀ a : J → ℤ_[l], ∑ j, (a j : ℚ_[l]) • e j ∈ S := by
    intro a
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← hsm]
    exact S.smul_mem _ (he j)

  have hrep : ∀ s : S, ∃ a : J → ℤ_[l], (s : V) = ∑ j, (a j : ℚ_[l]) • e j := by
    intro s
    refine ⟨fun j => c.repr (b.repr s j.2) j.1, ?_⟩
    rw [Fintype.sum_prod_type_right]
    conv_lhs => rw [← b.sum_repr s]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul]
    conv_lhs => rw [← c.sum_repr (b.repr s i)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_smul, hsm]

  have hind : ∀ a : J → ℤ_[l], ∑ j, (a j : ℚ_[l]) • e j = 0 → a = 0 := by
    intro a ha
    have h1 : ((∑ i, (∑ k, a (k, i) • c k) • b i : S) : V) = 0 := by
      rw [← ha, Fintype.sum_prod_type_right, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, mul_smul, hsm]
    have h3 := Fintype.linearIndependent_iff.mp b.linearIndependent _ (Submodule.coe_eq_zero.mp h1)
    funext j
    exact Fintype.linearIndependent_iff.mp c.linearIndependent _ (h3 j.2) j.1

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hli : LinearIndependent ℚ_[l] e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ j, ‖g j‖) hl1
    have hsmall : ∀ j, ‖(l : ℚ_[l]) ^ N * g j‖ ≤ 1 := by
      intro j
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
      exact (Finset.single_le_sum (fun j _ => norm_nonneg (g j)) (Finset.mem_univ j)).trans hN.le
    have h0 := hind (fun j => ⟨(l : ℚ_[l]) ^ N * g j, hsmall j⟩) (by
      change ∑ j, ((l : ℚ_[l]) ^ N * g j) • e j = 0
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, hg, smul_zero])
    intro j
    have hj : (l : ℚ_[l]) ^ N * g j = 0 := congrArg Subtype.val (congrFun h0 j)
    exact (mul_eq_zero.mp hj).resolve_left (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))

  let P := Submodule.span ℚ_[l] (Set.range e)
  have hSP : ∀ s : S, (s : V) ∈ P := by
    intro s
    obtain ⟨a, ha⟩ := hrep s
    rw [ha]
    exact Submodule.sum_mem _ fun j _ => P.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hLS : ∀ (x : L) (s : V), s ∈ S → x • s ∈ P := by
    intro x s hs
    obtain ⟨y, hy, o, ho⟩ := hd x
    have hy' : (y : ℚ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
    have ho' : o • s = (y : ℚ_[l]) • (x • s) := by
      rw [← algebraMap_smul L o s, ho, mul_smul, algebraMap_smul]
    have hx : x • s = ((y : ℚ_[l]))⁻¹ • (o • s) := by
      rw [ho', inv_smul_smul₀ hy']
    rw [hx]
    exact P.smul_mem _ (hSP ⟨_, S.smul_mem o hs⟩)
  have hLP : ∀ (x : L) (v : V), v ∈ P → x • v ∈ P := by
    intro x v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact hLS x _ (he j)
    | zero => rw [smul_zero]; exact P.zero_mem
    | add u w _ _ hu hw => rw [smul_add]; exact P.add_mem hu hw
    | smul q u _ hu => rw [smul_comm]; exact P.smul_mem q hu
  have hsp : ⊤ ≤ P := by
    rintro v -
    have hv : v ∈ Submodule.span L (S : Set V) := by rw [hspan]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem v hv => exact hSP ⟨v, hv⟩
    | zero => exact P.zero_mem
    | add u w _ _ hu hw => exact P.add_mem hu hw
    | smul x u _ hu => exact hLP x u hu
  let b0 : Module.Basis J ℚ_[l] V := Module.Basis.mk hli hsp
  have hb0 : ∀ j, b0 j = e j := fun j => Module.Basis.mk_apply hli hsp j
  refine ⟨Fintype.card J, b0.reindex (Fintype.equivFin J), fun x => ?_⟩
  simp only [Module.Basis.repr_reindex_apply]
  constructor
  · intro hx i
    obtain ⟨a, ha⟩ := hrep ⟨x, hx⟩
    have hx0 : x = ∑ j, (a j : ℚ_[l]) • b0 j := by simpa only [hb0] using ha
    rw [hx0, congrFun (b0.repr_sum_self fun j => (a j : ℚ_[l]))]
    exact PadicInt.norm_le_one _
  · intro hx
    have hx' : ∀ j, ‖b0.repr x j‖ ≤ 1 := fun j => by simpa using hx (Fintype.equivFin J j)
    have hxs := hin fun j => ⟨b0.repr x j, hx' j⟩
    have hsum : ∑ j, ((⟨b0.repr x j, hx' j⟩ : ℤ_[l]) : ℚ_[l]) • e j = x := by
      simp_rw [← hb0]
      exact b0.sum_repr x
    rwa [hsum] at hxs

end GlobalTheory.UnitBallBasis
end

section

namespace GlobalTheory

private theorem isClosed_submodule_padicInt_finite (l : ℕ) [Fact l.Prime] {N : Type} [AddCommGroup N]
    [Module ℤ_[l] N] [Module.Finite ℤ_[l] N] [TopologicalSpace N] [IsModuleTopology ℤ_[l] N]
    (M : Submodule ℤ_[l] N) : IsClosed (M : Set N) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] N
  have hq := IsModuleTopology.isQuotientMap_of_surjective (R := ℤ_[l]) hπ
  rw [← hq.isClosed_preimage]
  obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' ℤ_[l] (M.comap π)
  have hc : Continuous (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) :=
    IsModuleTopology.continuous_of_linearMap ((M.comap π).subtype ∘ₗ φ)
  have hrange : Set.range (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) = π ⁻¹' (M : Set N) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (φ x).2
    · intro hy
      obtain ⟨x, hx⟩ := hφ ⟨y, hy⟩
      exact ⟨x, by simp [hx]⟩
  rw [← hrange]
  exact (isCompact_range hc).isClosed

theorem exists_idempotent_sub_mem_of_pow_sub_mem (l : ℕ) [Fact l.Prime] {R : Type} [Ring R]
    [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R] (b : R) :
    ∃ E : R, E * E = E ∧ ∀ (M : Submodule ℤ_[l] R) (c : R),
      (∀ n : ℕ, b ^ (n + 1) - c ∈ M) → E - c ∈ M := by
  letI : TopologicalSpace R := moduleTopology ℤ_[l] R
  haveI : IsModuleTopology ℤ_[l] R := ⟨rfl⟩
  haveI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing ℤ_[l] R
  have hcl : ∀ M : Submodule ℤ_[l] R, IsClosed (M : Set R) := fun M => isClosed_submodule_padicInt_finite l M
  haveI : T2Space R := by
    rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
    simpa using hcl ⊥
  haveI : CompactSpace R := by
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] R
    have hc : Continuous π := IsModuleTopology.continuous_of_linearMap π
    exact ⟨by simpa [hπ.range_eq] using isCompact_range hc⟩
  obtain ⟨E, hES, hE⟩ := exists_idempotent_in_compact_subsemigroup (fun r => continuous_mul_const r)
    (closure (Set.range fun n : ℕ => b ^ (n + 1))) ⟨b ^ (0 + 1), subset_closure ⟨0, rfl⟩⟩
    isClosed_closure.isCompact (by
      intro x hx y hy
      refine map_mem_closure₂ (f := fun x y : R => x * y) continuous_mul hx hy ?_
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      refine ⟨i + j + 1, ?_⟩
      show b ^ (i + j + 1 + 1) = b ^ (i + 1) * b ^ (j + 1)
      rw [← pow_add]
      congr 1
      omega)
  refine ⟨E, hE, fun M c h => ?_⟩
  have hC : IsClosed {x : R | x - c ∈ M} := (hcl M).preimage (continuous_id.sub continuous_const)
  exact closure_minimal (by rintro _ ⟨n, rfl⟩; exact h n) hC hES

end GlobalTheory
end

section

namespace GlobalTheory.PadicLte

theorem norm_pow_prime_sub_one (l : ℕ) [Fact l.Prime] (u : ℤ_[l])
    (h : ‖u - 1‖ < ‖((l : ℕ) : ℤ_[l])‖) :
    ‖u ^ l - 1‖ = ‖u - 1‖ * ‖((l : ℕ) : ℤ_[l])‖ := by
  have hl1 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
    intro i
    rw [← mul_geom_sum, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
  have hsum : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, (u ^ i - 1)‖ ≤ ‖u - 1‖ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      exact (PadicInt.nonarchimedean _ _).trans (max_le ih (hpow m))
  have hsplit : ∑ i ∈ Finset.range l, u ^ i
      = ((l : ℕ) : ℤ_[l]) + ∑ i ∈ Finset.range l, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hgeom : ‖∑ i ∈ Finset.range l, u ^ i‖ = ‖((l : ℕ) : ℤ_[l])‖ := by
    rw [hsplit, PadicInt.norm_add_eq_max_of_ne]
    · exact max_eq_left ((hsum l).trans h.le)
    · exact ((hsum l).trans_lt h).ne'
  rw [← mul_geom_sum, norm_mul, hgeom]

theorem norm_pow_prime_pow_sub_one (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (k : ℕ) (hk : 2 ≤ k)
    (hu : ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k) (n : ℕ) :
    ‖u ^ l ^ n - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := by
  have hl1 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : 0 ≤ ‖((l : ℕ) : ℤ_[l])‖ := norm_nonneg _
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    have hlt : ‖u ^ l ^ n - 1‖ < ‖((l : ℕ) : ℤ_[l])‖ := by
      rw [ih]
      calc ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ 2 :=
            pow_le_pow_of_le_one hl0 hl1.le (by omega)
        _ < ‖((l : ℕ) : ℤ_[l])‖ ^ 1 := by
            have hpos : 0 < ‖((l : ℕ) : ℤ_[l])‖ := by
              rw [PadicInt.norm_p]
              exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)
            exact pow_lt_pow_right_of_lt_one₀ hpos hl1 (by norm_num)
        _ = ‖((l : ℕ) : ℤ_[l])‖ := pow_one _
    rw [pow_succ, pow_mul, norm_pow_prime_sub_one l _ hlt, ih, ← pow_succ, ← add_assoc]

end GlobalTheory.PadicLte
end

section

namespace GlobalTheory.UltrametricPowerBound

variable {l : ℕ} [Fact (Nat.Prime l)]

lemma ultra (q r : ℚ_[l]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := Padic.nonarchimedean q r

lemma pow_sub_one_le (w : ℚ_[l]) (hw : ‖w‖ ≤ 1) (k : ℕ) : ‖w ^ k - 1‖ ≤ ‖w - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : w ^ (k + 1) - 1 = w * (w ^ k - 1) + (w - 1) := by ring
    rw [e]
    refine (ultra _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    calc ‖w‖ * ‖w ^ k - 1‖ ≤ 1 * ‖w ^ k - 1‖ := by gcongr
      _ ≤ ‖w - 1‖ := by rw [one_mul]; exact ih

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (w : ℚ_[l]), ‖w‖ ≤ (1 : ℝ) → ∀ (k : ℕ),
    ‖w ^ k - (1 : ℚ_[l]) - (↑k : ℚ_[l]) * (w - (1 : ℚ_[l]))‖ ≤ ‖w - (1 : ℚ_[l])‖ ^ (2 : ℕ) := by
  intro l _ w hw k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : w ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℚ_[l]) * (w - 1)
        = (w ^ k - 1 - (k : ℚ_[l]) * (w - 1)) + (w - 1) * (w ^ k - 1) := by push_cast; ring
    rw [e]
    refine (ultra _ _).trans (max_le ih ?_)
    rw [norm_mul, sq]
    exact mul_le_mul_of_nonneg_left (pow_sub_one_le w hw k) (norm_nonneg _)

end GlobalTheory.UltrametricPowerBound
end

section

namespace GlobalTheory

theorem exists_padicInt_of_compatible_zmod_pow :
    ∀ (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n)),
      (∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) →
      ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n := by
  intro p _ c hc
  let f : ∀ n : ℕ, Polynomial ℤ →+* ZMod (p ^ n) := fun n =>
    Polynomial.eval₂RingHom (Int.castRingHom _) (c n)
  have hf : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁))).comp (f k₂) = f k₁ := by
    intro k₁ k₂ hk
    apply Polynomial.ringHom_ext
    · intro a
      simp [f]
    · simpa [f] using hc k₁ k₂ hk
  refine ⟨PadicInt.lift hf Polynomial.X, fun n => ?_⟩
  have h := congrArg (fun g : Polynomial ℤ →+* ZMod (p ^ n) => g Polynomial.X)
    (PadicInt.lift_spec hf n)
  simpa [f] using h

end GlobalTheory
end
