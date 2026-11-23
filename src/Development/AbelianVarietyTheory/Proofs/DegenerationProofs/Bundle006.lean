module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

namespace GlobalTheory.ResidueSpanScale

theorem exists_scale {O K J : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite J] (c : J → K) (j : J) (hj : c j ≠ 0) :
    ∃ (j₀ : J) (d : J → O), c j₀ ≠ 0 ∧ d j₀ = 1 ∧ ∀ i, c i = c j₀ * algebraMap O K (d i) := by
  classical
  haveI : Nonempty J := ⟨j⟩
  obtain ⟨j₀, h₀⟩ := Finite.exists_max (fun i => ValuationRing.valuation O K (c i))
  have hv : ValuationRing.valuation O K (c j₀) ≠ 0 := by
    intro h
    have h1 := h₀ j
    rw [h, le_zero_iff] at h1
    exact hj ((Valuation.zero_iff _).1 h1)
  have hc : c j₀ ≠ 0 := fun h => hv (by rw [h, map_zero])
  have hex : ∀ i, ∃ a : O, algebraMap O K a = c i / c j₀ := by
    intro i
    rw [← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (h₀ i) zero_le
  choose d hd using hex
  refine ⟨j₀, d, hc, ?_, fun i => ?_⟩
  · apply IsFractionRing.injective O K
    rw [hd, div_self hc, map_one]
  · rw [hd]; field_simp

theorem finrank_span_residue_le {O K I A B : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] [Finite I] (f : I → A → K)
    (g : I → B → IsLocalRing.ResidueField O)
    (h : ∀ b : B, ∃ (a : A) (w : I → O), ∀ i : I,
      f i a = algebraMap O K (w i) ∧ g i b = IsLocalRing.residue O (w i)) :
    Module.finrank (IsLocalRing.ResidueField O)
        (Submodule.span (IsLocalRing.ResidueField O) (Set.range g)) ≤
      Module.finrank K (Submodule.span K (Set.range f)) := by
  classical
  obtain ⟨κ, e, he, hsp, hli⟩ := exists_linearIndependent' (IsLocalRing.ResidueField O) g
  haveI : Finite κ := Finite.of_injective e he
  haveI : Fintype κ := Fintype.ofFinite κ
  have hf : LinearIndependent K (f ∘ e) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    obtain ⟨j, hj⟩ := hne
    obtain ⟨j₀, d, hc₀, hd₀, hd⟩ := exists_scale (O := O) c j hj
    have hz : ∑ i, IsLocalRing.residue O (d i) • (g ∘ e) i = 0 := by
      funext b
      obtain ⟨a, w, hw⟩ := h b
      have h1 := congrFun hc a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply] at h1 ⊢
      have h2 : c j₀ * algebraMap O K (∑ i, d i * w (e i)) = 0 := by

        rw [← h1, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, (hw (e i)).1, ← mul_assoc, ← hd i]
      have h3 : ∑ i, d i * w (e i) = 0 := by
        apply IsFractionRing.injective O K
        rw [map_zero]
        exact (mul_eq_zero.1 h2).resolve_left hc₀
      have h4 := congrArg (IsLocalRing.residue O) h3

      rw [map_sum, map_zero] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, (hw (e i)).2]
    have := Fintype.linearIndependent_iff.1 hli _ hz j₀
    rw [hd₀, map_one] at this
    exact one_ne_zero this
  haveI : Module.Finite K (Submodule.span K (Set.range f)) :=
    Module.Finite.span_of_finite K (Set.finite_range f)
  rw [← hsp, finrank_span_eq_card hli, ← finrank_span_eq_card hf]
  exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range e f))

end GlobalTheory.ResidueSpanScale
end

section

open Module

namespace GlobalTheory

theorem exists_eq_add_nsmul_of_torsion_characters_eq (k X : Type) [Field k] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k) (hN : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) (α β : X)
    (h : ∀ t : Multiplicative X →* kˣ, t ^ N = 1 →
      t (Multiplicative.ofAdd α) = t (Multiplicative.ofAdd β)) :
    ∃ w, α = β + N • w := by
  classical
  have hu : IsUnit ζ := hζ.isUnit hN.ne'
  obtain ⟨u, rfl⟩ := hu
  have hu' : IsPrimitiveRoot u N := IsPrimitiveRoot.coe_units_iff.mp hζ
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, (N : ℤ) ∣ b.repr (α - β) i := by
    intro i
    let t : Multiplicative X →* kˣ :=
      { toFun := fun x => u ^ (b.repr (Multiplicative.toAdd x) i)
        map_one' := by simp
        map_mul' := by
          intro x y
          simp [zpow_add] }
    have ht : t ^ N = 1 := by
      refine MonoidHom.ext fun x => ?_
      have : (u ^ (b.repr (Multiplicative.toAdd x) i)) ^ N = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu'.pow_eq_one,
          one_zpow]
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact this
    have h1 : u ^ (b.repr α i) = u ^ (b.repr β i) := h t ht
    rw [← hu'.zpow_eq_one_iff_dvd, map_sub, Finsupp.sub_apply, zpow_sub, h1, mul_inv_cancel]
  choose d hd using key
  refine ⟨∑ i, d i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (α - β), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i, mul_smul, natCast_zsmul]

theorem finsupp_eq_zero_of_sum_torsion_characters_eq_zero :
    ∀ (k X : Type) [Field k] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k), 0 < N → IsPrimitiveRoot ζ N → ∀ (M : Type) [AddCommGroup M] [Module k M] (c : X →₀ M), (∀ α ∈ c.support, ∀ β ∈ c.support, (∃ w, α = β + N • w) → α = β) → (∀ t : Multiplicative X →* kˣ, t ^ N = 1 → c.sum (fun α m => (t (Multiplicative.ofAdd α) : k) • m) = 0) → c = 0 := by
  intro k X _ _ _ _ N ζ hN hζ M _ _ c hc hsum
  classical
  let G : Subgroup (Multiplicative X →* kˣ) := (powMonoidHom N).ker
  let ev : c.support → (G →* k) := fun α =>
    { toFun := fun t => ((t : Multiplicative X →* kˣ) (Multiplicative.ofAdd (α : X)) : k)
      map_one' := by simp
      map_mul' := by
        intro s t
        simp }
  have hinj : Function.Injective ev := by
    intro α β hαβ
    apply Subtype.ext
    refine hc _ α.2 _ β.2
      (exists_eq_add_nsmul_of_torsion_characters_eq k X N ζ hN hζ _ _ fun t ht => ?_)
    exact Units.ext (DFunLike.congr_fun hαβ (⟨t, ht⟩ : G))
  have hli : LinearIndependent k (fun α : c.support => (ev α : G → k)) :=
    (linearIndependent_monoidHom G k).comp ev hinj
  ext α
  by_contra hα
  have hmem : α ∈ c.support := Finsupp.mem_support_iff.mpr hα
  apply hα
  rw [Finsupp.zero_apply, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  refine Fintype.linearIndependent_iff.mp hli (fun β => φ (c β)) ?_ ⟨α, hmem⟩
  funext t
  have h0 := congrArg φ (hsum t t.2)

  rw [Finsupp.sum, map_sum, map_zero, ← Finset.sum_coe_sort] at h0
  rw [Finset.sum_apply, Pi.zero_apply, ← h0]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory
end

section

namespace GlobalTheory.PadicVal

variable {p : ℕ} [Fact p.Prime]

theorem exists_rat_log (x : PadicAlgCl p) (hx : x ≠ 0) : ∃ q : ℚ, Real.log ‖x‖ = q * Real.log p := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  have hn : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (minpoly ℚ_[p] x).natDegree : ℝ) := by
    rw [← PadicAlgCl.spectralNorm_eq]
    exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) x
  refine ⟨((-((minpoly ℚ_[p] x).coeff 0).valuation : ℤ) : ℚ) / ((minpoly ℚ_[p] x).natDegree : ℚ), ?_⟩
  rw [hn, Real.log_rpow (norm_pos_iff.2 hc), Padic.norm_eq_zpow_neg_valuation hc, Real.log_zpow]
  push_cast
  ring


open Classical in
theorem exists_addValuation (π : PadicAlgCl p) (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1) :
    ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), ∀ x, x ≠ 0 →
      ∃ q : ℚ, v x = (q : WithTop ℚ) ∧ Real.log ‖x‖ = q * Real.log ‖π‖ := by
  classical
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  have hex : ∀ x : PadicAlgCl p, x ≠ 0 → ∃ q : ℚ, Real.log ‖x‖ = q * Real.log ‖π‖ := by
    intro x hx
    obtain ⟨a, ha⟩ := exists_rat_log x hx
    obtain ⟨b, hb⟩ := exists_rat_log π (norm_pos_iff.1 h0)
    have hb0 : (b : ℝ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hb
      exact hL.ne hb
    have hlp : Real.log p ≠ 0 := by
      intro h
      rw [h, mul_zero] at hb
      exact hL.ne hb
    refine ⟨a / b, ?_⟩
    rw [ha, hb]
    push_cast
    field_simp
  let r : PadicAlgCl p → ℚ := fun x => if hx : x = 0 then 0 else Classical.choose (hex x hx)
  have hr : ∀ x, x ≠ 0 → Real.log ‖x‖ = r x * Real.log ‖π‖ := by
    intro x hx
    simp only [r, dif_neg hx]
    exact Classical.choose_spec (hex x hx)
  have hr' : ∀ x, x ≠ 0 → (r x : ℝ) = Real.log ‖x‖ / Real.log ‖π‖ := by
    intro x hx
    rw [hr x hx, mul_div_cancel_right₀ _ hL.ne]
  let f : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ)
  have f_ne : ∀ x, x ≠ 0 → f x = (r x : WithTop ℚ) := fun x hx => if_neg hx
  have f_zero : f 0 = ⊤ := if_pos rfl
  refine ⟨AddValuation.of f f_zero ?_ ?_ ?_, ?_⟩
  · have h : (r 1 : ℝ) = 0 := by
      rw [hr' 1 one_ne_zero, norm_one, Real.log_one, zero_div]
    rw [f_ne 1 one_ne_zero, Rat.cast_eq_zero.1 h]
    rfl
  · intro x y
    by_cases hx : x = 0
    · subst hx
      rw [f_zero, zero_add]
      exact min_le_right _ _
    by_cases hy : y = 0
    · subst hy
      rw [f_zero, add_zero]
      exact min_le_left _ _
    by_cases hxy : x + y = 0
    · rw [hxy, f_zero]
      exact le_top
    rw [f_ne x hx, f_ne y hy, f_ne _ hxy, ← WithTop.coe_min, WithTop.coe_le_coe,
      ← Rat.cast_le (K := ℝ), Rat.cast_min, hr' x hx, hr' y hy, hr' _ hxy]
    have hle : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
    have hpos : 0 < ‖x + y‖ := norm_pos_iff.2 hxy
    rcases le_total ‖y‖ ‖x‖ with h | h
    · rw [max_eq_left h] at hle
      exact (min_le_left _ _).trans
        (div_le_div_of_nonpos_of_le hL.le (Real.log_le_log hpos hle))
    · rw [max_eq_right h] at hle
      exact (min_le_right _ _).trans
        (div_le_div_of_nonpos_of_le hL.le (Real.log_le_log hpos hle))
  · intro x y
    by_cases hx : x = 0
    · subst hx
      rw [zero_mul, f_zero, top_add]
    by_cases hy : y = 0
    · subst hy
      rw [mul_zero, f_zero, add_top]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    rw [f_ne x hx, f_ne y hy, f_ne _ hxy, ← WithTop.coe_add, WithTop.coe_eq_coe]
    have h : (r (x * y) : ℝ) = r x + r y := by
      rw [hr' _ hxy, hr' x hx, hr' y hy, norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), add_div]
    exact_mod_cast h
  · intro x hx
    exact ⟨r x, f_ne x hx, hr x hx⟩

theorem tendsto_of_null {π : PadicAlgCl p} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    {v : AddValuation (PadicAlgCl p) (WithTop ℚ)}
    (hv : ∀ x, x ≠ 0 → ∃ q : ℚ, v x = (q : WithTop ℚ) ∧ Real.log ‖x‖ = q * Real.log ‖π‖)
    {I : Type} {x : I → PadicAlgCl p} (hx : ∀ q : ℚ, {i | v (x i) < (q : WithTop ℚ)}.Finite) :
    Filter.Tendsto x Filter.cofinite (nhds 0) := by
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨q, hq⟩ := exists_rat_gt (Real.log ε / Real.log ‖π‖)
  rw [Filter.eventually_cofinite]
  refine (hx q).subset ?_
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  by_contra hlt
  apply hi
  rw [dist_zero_right, norm_norm]
  by_cases hxi : x i = 0
  · rw [hxi, norm_zero]
    exact hε
  obtain ⟨q', hv', hlog⟩ := hv (x i) hxi
  have hqq : q ≤ q' := by
    rw [hv', not_lt, WithTop.coe_le_coe] at hlt
    exact hlt
  have h2 : (q' : ℝ) * Real.log ‖π‖ ≤ q * Real.log ‖π‖ :=
    mul_le_mul_of_nonpos_right (by exact_mod_cast hqq) hL.le
  have h3 : (q : ℝ) * Real.log ‖π‖ < Real.log ε := (div_lt_iff_of_neg hL).1 hq
  have h4 : Real.log ‖x i‖ < Real.log ε := by linarith
  exact (Real.log_lt_log_iff (norm_pos_iff.2 hxi) hε).1 h4

theorem summable_of_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {I : Type} {x : I → PadicAlgCl p} (hK : ∀ i, x i ∈ K) (hx : Filter.Tendsto x Filter.cofinite (nhds 0)) :
    Summable x := by
  have : CompleteSpace K := FiniteDimensional.complete ℚ_[p] K
  let y : I → K := fun i => ⟨x i, hK i⟩
  have hy : Filter.Tendsto y Filter.cofinite (nhds 0) := by
    rw [tendsto_subtype_rng]
    exact hx
  have hs : Summable y := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hy
  exact hs.map K.val continuous_subtype_val

end GlobalTheory.PadicVal
end

section

namespace GlobalTheory

open IsLocalRing in
private lemma exists_pow_maximalIdeal_eq_span {V V' : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [Algebra V V'] [IsLocalHom (algebraMap V V')] (hinj : Function.Injective (algebraMap V V'))
    {ϖ : V} (hϖ : Irreducible ϖ) :
    ∃ e : ℕ, 0 < e ∧ ∀ n, maximalIdeal V' ^ (e * n) = Ideal.span {algebraMap V V' ϖ ^ n} := by
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V'
  have h0 : algebraMap V V' ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V V')]
    exact fun h => hϖ.ne_zero (hinj h)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ'
  have hnu : ¬ IsUnit (algebraMap V V' ϖ) := fun h => hϖ.not_isUnit (isUnit_of_map_unit _ _ h)
  refine ⟨e, Nat.pos_of_ne_zero fun he => hnu ?_, fun n => ?_⟩
  · rw [hu, he, pow_zero, mul_one]; exact u.isUnit
  · rw [hϖ'.maximalIdeal_eq, Ideal.span_singleton_pow, hu, mul_pow, ← pow_mul,
      ← Units.val_pow_eq_pow_val, Ideal.span_singleton_mul_left_unit (u ^ n).isUnit]

open IsLocalRing in
private lemma mem_span_pow_iff_repr {V V' : Type} [CommRing V] [CommRing V'] [Algebra V V']
    {ι : Type} [Fintype ι] (b : Module.Basis ι V V') (ϖ : V) (j : ℕ) (x : V') :
    x ∈ Ideal.span {algebraMap V V' ϖ ^ j} ↔ ∀ i, b.repr x i ∈ Ideal.span {ϖ ^ j} := by
  simp only [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩ i
    refine ⟨b.repr y i, ?_⟩
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
      smul_eq_mul, mul_comm]
  · intro h
    choose c hc using h
    refine ⟨∑ i, c i • b i, ?_⟩
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, Finset.smul_sum]
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i, smul_smul, mul_comm (ϖ ^ j)]


open IsLocalRing in
theorem _root_.GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr :
    ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CommRing V'] [IsDomain V']
      [IsDiscreteValuationRing V'] [Algebra V V'], Module.Finite V V' →
      Function.Injective (algebraMap V V') →
      IsLocalHom (algebraMap V V') ∧ IsAdicComplete (IsLocalRing.maximalIdeal V') V' := by
  intro V V' _ _ _ _ _ _ _ _ hfin hinj
  have hloc : IsLocalHom (algebraMap V V') :=
    RingHom.IsIntegral.isLocalHom (fun x => Algebra.IsIntegral.isIntegral x) hinj
  refine ⟨hloc, ?_⟩
  haveI : FaithfulSMul V V' := (faithfulSMul_iff_algebraMap_injective V V').2 hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨e, he, hpow⟩ := exists_pow_maximalIdeal_eq_span hinj hϖ
  let b := Module.Free.chooseBasis V V'
  have hV : ∀ j, (maximalIdeal V ^ j • ⊤ : Submodule V V) = Ideal.span {ϖ ^ j} := by
    intro j
    rw [smul_eq_mul, Ideal.mul_top, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hV' : ∀ n, (maximalIdeal V' ^ n • ⊤ : Submodule V' V') = maximalIdeal V' ^ n := by
    intro n
    rw [smul_eq_mul, Ideal.mul_top]
  haveI hH : IsHausdorff (maximalIdeal V') V' :=
    IsHausdorff.of_isLocalRing (maximalIdeal V') V' (IsLocalRing.maximalIdeal.isMaximal V').ne_top
  have hP : IsPrecomplete (maximalIdeal V') V' := by
    rw [isPrecomplete_iff]
    intro f hf
    have hcoord : ∀ i : Module.Free.ChooseBasisIndex V V', ∀ {m n : ℕ}, m ≤ n →
        b.repr (f (e * m)) i ≡ b.repr (f (e * n)) i
          [SMOD maximalIdeal V ^ m • (⊤ : Submodule V V)] := by
      intro i m n hmn
      have h := hf (Nat.mul_le_mul_left e hmn)
      rw [hV', SModEq.sub_mem, hpow, mem_span_pow_iff_repr b] at h
      rw [hV, SModEq.sub_mem, ← Finsupp.sub_apply, ← map_sub]
      exact h i
    choose L hL using fun i =>
      (isPrecomplete_iff.1 (inferInstance : IsPrecomplete (maximalIdeal V) V)) _ (hcoord i)
    refine ⟨b.equivFun.symm L, fun n => ?_⟩
    have h1 : f n ≡ f (e * n) [SMOD maximalIdeal V' ^ n • (⊤ : Submodule V' V')] :=
      hf (Nat.le_mul_of_pos_left n he)
    have h2 : f (e * n) ≡ b.equivFun.symm L [SMOD maximalIdeal V' ^ n • (⊤ : Submodule V' V')] := by
      rw [hV', SModEq.sub_mem]
      refine Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n he) ?_
      rw [hpow, mem_span_pow_iff_repr b]
      intro i
      have hi := hL i n
      rw [hV, SModEq.sub_mem] at hi
      rw [map_sub, Finsupp.sub_apply, ← b.equivFun_apply (b.equivFun.symm L),
        LinearEquiv.apply_symm_apply]
      exact hi
    exact h1.trans h2
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

end GlobalTheory
end
