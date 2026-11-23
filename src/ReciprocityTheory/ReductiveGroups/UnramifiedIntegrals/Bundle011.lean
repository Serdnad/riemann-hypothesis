module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle003
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle007
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Mathlib.Algebra.Algebra.Hom.Rat
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem IsMF.qExp_eq {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) {s : PowerSeries ℂ} (hs : Conv s)
    (h : ∀ τ, ev s (qm 1 τ) = f τ) : qExpansion 1 f = s := by
  have hq : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ∃ τ : ℍ, qm 1 τ = x := by
    intro x hx0 hx1
    have hx : x ≠ 0 := norm_pos_iff.mp hx0
    refine ⟨⟨Function.Periodic.invQParam 1 x,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hx1 hx⟩, ?_⟩
    have h1 := Function.Periodic.qParam_right_inv one_ne_zero hx
    unfold Function.Periodic.qParam at h1
    unfold qm
    simpa using h1
  have hsum : ∀ τ : ℍ, HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ) :=
    fun τ => hf.hasSum τ
  have hconv : Conv (qExpansion 1 f) := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (‖x‖ + 1) / 2 := ⟨_, rfl⟩
    have hy0 : 0 < y := by rw [hy]; positivity
    have hy1 : y < 1 := by linarith
    have hxy : ‖x‖ < y := by linarith
    have hyn : ‖(y : ℂ)‖ = y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    obtain ⟨τ, hτ⟩ := hq (y : ℂ) (by rw [hyn]; exact hy0) (by rw [hyn]; exact hy1)
    have hs := hsum τ
    rw [hτ] at hs
    have ht : Filter.Tendsto (fun n => ‖PowerSeries.coeff n (qExpansion 1 f) * (y : ℂ) ^ n‖)
        Filter.atTop (nhds 0) := by
      simpa using hs.summable.tendsto_atTop_zero.norm
    obtain ⟨C, hC⟩ := ht.bddAbove_range
    have hr0 : 0 ≤ ‖x‖ / y := by positivity
    have hr1 : ‖x‖ / y < 1 := (div_lt_one hy0).mpr hxy
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
    have hb := hC ⟨n, rfl⟩
    have he : ‖PowerSeries.coeff n (qExpansion 1 f)‖ * ‖x‖ ^ n =
        ‖PowerSeries.coeff n (qExpansion 1 f) * (y : ℂ) ^ n‖ * (‖x‖ / y) ^ n := by
      rw [norm_mul, norm_pow, hyn, div_pow]
      field_simp <;> ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  refine eq_of_ev_eq hconv hs fun x hx0 hx1 => ?_
  obtain ⟨τ, rfl⟩ := hq x hx0 hx1
  rw [h τ]
  exact (hsum τ).tsum_eq

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_of_ratRoot {Ω M : Type*} [Field Ω] [IsAlgClosed Ω] [Field M] (e : Ω →+* M)
    (f₀ : ℚ →+* Ω) (f : ℚ →+* M) {p : Polynomial ℚ} (hp : p ≠ 0) {y : M}
    (hy : p.eval₂ f y = 0) : ∃ a : Ω, e a = y := by
  have hP : p.map f₀ ≠ 0 := (Polynomial.map_ne_zero_iff f₀.injective).2 hp
  have hr : ((p.map f₀).map e).roots = (p.map f₀).roots.map e :=
    (IsAlgClosed.splits _).roots_map e
  have hf : e.comp f₀ = f := Subsingleton.elim _ _
  have hmem : y ∈ ((p.map f₀).map e).roots := by
    rw [Polynomial.mem_roots ((Polynomial.map_ne_zero_iff e.injective).2 hP), Polynomial.map_map, hf,
      Polynomial.IsRoot.def, Polynomial.eval_map]
    exact hy
  rw [hr, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩

theorem exists_e_eq {d l : ℕ} [Fact l.Prime] (e : Om d →+* PadicAlgCl l)
    (r : PadicAlgCl l →+* PadicAlgCl l) (x : Om d) : ∃ y : Om d, e y = r (e x) := by
  obtain ⟨p, hp, hpx⟩ := Om_isAlgebraic d x
  have : IsAlgClosed (Om d) :=
    (IsAlgClosed.algebraicClosure_eq_bot_iff (Om d) ℂ).mp (algebraicClosure.algebraicClosure_eq_bot (KQ d) ℂ)
  let f₀ : ℚ →+* Om d := algebraMap ℚ (Om d)
  have h0 : p.eval₂ f₀ x = 0 := by
    apply (algebraMap (Om d) ℂ).injective
    rw [Polynomial.hom_eval₂, map_zero]
    have : (algebraMap (Om d) ℂ).comp f₀ = algebraMap ℚ ℂ := Subsingleton.elim _ _
    rw [this]
    exact hpx
  refine exists_of_ratRoot e f₀ ((r.comp e).comp f₀) hp ?_
  have := congrArg (r.comp e) h0
  rw [Polynomial.hom_eval₂, map_zero] at this
  exact this

theorem norm_lt_of_res {l : ℕ} [Fact l.Prime] {r : PadicAlgCl l → PadicAlgCl l}
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) {z : PadicAlgCl l} (hz : ‖z‖ < 1) : ‖r z‖ < 1 := by
  have h := PadicAlgCl.isNonarchimedean l (r z - z) z
  rw [sub_add_cancel] at h
  exact lt_of_le_of_lt h (max_lt (hr z hz.le) hz)

theorem norm_le_of_res {l : ℕ} [Fact l.Prime] {r : PadicAlgCl l → PadicAlgCl l}
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) {z : PadicAlgCl l} (hz : ‖z‖ ≤ 1) : ‖r z‖ ≤ 1 := by
  have h := PadicAlgCl.isNonarchimedean l (r z - z) z
  rw [sub_add_cancel] at h
  exact le_trans h (max_le (hr z hz).le hz)

theorem norm_le_iff_of_res {l : ℕ} [Fact l.Prime] (r : PadicAlgCl l →+* PadicAlgCl l)
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) (z : PadicAlgCl l) : ‖r z‖ ≤ 1 ↔ ‖z‖ ≤ 1 := by
  refine ⟨fun h => ?_, fun h => norm_le_of_res hr h⟩
  by_contra hz
  push Not at hz
  have h1 : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  have h2 := norm_lt_of_res hr h1
  rw [map_inv₀, norm_inv] at h2
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
    linarith
  have h3 : 0 < ‖r z‖ := norm_pos_iff.2 ((map_ne_zero r).2 hz0)
  have h4 : 1 ≤ ‖r z‖⁻¹ := (one_le_inv₀ h3).2 h
  linarith

theorem fix_KQ {d l : ℕ} [Fact l.Prime] (e : Om d →+* PadicAlgCl l)
    (ρ : PadicAlgCl l ≃ₐ[IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))}] PadicAlgCl l)
    (k : KQ d) : ρ (e (algebraMap (KQ d) (Om d) k)) = e (algebraMap (KQ d) (Om d) k) := by
  let φ₁ : KQ d →ₐ[ℚ] PadicAlgCl l := (e.comp (algebraMap (KQ d) (Om d))).toRatAlgHom
  let φ₂ : KQ d →ₐ[ℚ] PadicAlgCl l :=
    ((ρ : PadicAlgCl l →+* PadicAlgCl l).comp (e.comp (algebraMap (KQ d) (Om d)))).toRatAlgHom
  have h : φ₂ = φ₁ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (s := {sqD d}) rfl ?_
    intro x hx
    have hx' : x = sqD d := hx
    subst hx'
    have hm : e (algebraMap (KQ d) (Om d) (sqK d)) ∈
        IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    exact ρ.commutes ⟨_, hm⟩
  exact DFunLike.congr_fun h k

theorem locLift {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (e : Om d →+* PadicAlgCl l)
    (he : ∀ x : Om d, algebraMap (PadicAlgCl l) ℂ_[l] (e x) = ι (x : ℂ))
    (ρ : PadicAlgCl l ≃ₐ[IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))}] PadicAlgCl l)
    (hρ : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖ρ z - z‖ < 1) :
    ∃ σ : Om d ≃ₐ[KQ d] Om d, InertiaEl (Aio d l ι) σ ∧ ∀ x : Om d, e (σ x) = ρ (e x) := by
  have hinj : Function.Injective e := e.injective
  choose g hg using exists_e_eq e (ρ : PadicAlgCl l →+* PadicAlgCl l)
  choose g' hg' using exists_e_eq e (ρ.symm : PadicAlgCl l →+* PadicAlgCl l)
  have hg1 : ∀ x, e (g x) = ρ (e x) := hg
  have hg2 : ∀ x, e (g' x) = ρ.symm (e x) := hg'
  let σ : Om d ≃ₐ[KQ d] Om d :=
    { toFun := g
      invFun := g'
      left_inv := fun x => hinj (by rw [hg2, hg1, AlgEquiv.symm_apply_apply])
      right_inv := fun x => hinj (by rw [hg1, hg2, AlgEquiv.apply_symm_apply])
      map_mul' := fun x y => hinj (by rw [hg1, map_mul, map_mul, map_mul, hg1, hg1])
      map_add' := fun x y => hinj (by rw [hg1, map_add (f := _), map_add (f := _), map_add (f := _), hg1, hg1])
      commutes' := fun k => hinj (by rw [hg1, fix_KQ]) }
  have hσ : ∀ x, e (σ x) = ρ (e x) := hg1
  have hn : ∀ x : Om d, ‖ι (x : ℂ)‖ = ‖e x‖ := fun x => by
    rw [← he, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  have hiff : ∀ x : Om d, σ x ∈ Aio d l ι ↔ x ∈ Aio d l ι := fun x => by
    rw [mem_Aio, mem_Aio, hn, hn, hσ]
    exact norm_le_iff_of_res (ρ : PadicAlgCl l →+* PadicAlgCl l) hρ (e x)
  refine ⟨σ, ⟨?_, ?_⟩, hσ⟩
  · show σ • Aio d l ι = Aio d l ι
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hiff]
    have : σ (σ⁻¹ • x) = x := σ.apply_symm_apply x
    rw [this]
  · intro x hx
    rw [mem_nonunits_Aio]
    rw [hn, map_sub, hσ]
    exact hρ _ (by rw [← hn]; exact (mem_Aio ι x).1 hx)

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_padicAlgCl {l : ℕ} [Fact l.Prime] {z : ℂ_[l]} (hz : IsAlgebraic ℚ_[l] z) :
    ∃ y : PadicAlgCl l, algebraMap (PadicAlgCl l) ℂ_[l] y = z := by

  have hsplit : ((minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l))).Splits :=
    IsAlgClosed.splits _
  have hne : (minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l)) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hz.isIntegral)
  have hroot : (((minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l))).map
      (algebraMap (PadicAlgCl l) ℂ_[l])).IsRoot z := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    exact (Polynomial.eval_map_algebraMap _ _).trans (minpoly.aeval _ _)
  obtain ⟨y, hy⟩ := hsplit.mem_range_of_isRoot hne hroot
  exact ⟨y, hy⟩

theorem isAlgebraic_padic_map {l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) {x : ℂ}
    (hx : IsAlgebraic ℚ x) : IsAlgebraic ℚ_[l] (ι x) := by
  have h : IsAlgebraic ℚ (ι x) := hx.algHom (ι : ℂ →+* ℂ_[l]).toRatAlgHom
  exact h.tower_top ℚ_[l]

theorem locEmb (d l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) :
    ∃ e : Om d →+* PadicAlgCl l, ∀ x : Om d, algebraMap (PadicAlgCl l) ℂ_[l] (e x) = ι (x : ℂ) := by
  set j : PadicAlgCl l →+* ℂ_[l] := algebraMap (PadicAlgCl l) ℂ_[l] with hj

  let J : PadicAlgCl l ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => j.injective (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  have hmem : ∀ x : Om d, (ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ) x ∈ j.range := by
    intro x
    obtain ⟨y, hy⟩ := exists_padicAlgCl (isAlgebraic_padic_map ι (Om_isAlgebraic d x))
    exact ⟨y, hy⟩
  refine ⟨J.symm.toRingHom.comp (((ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ)).codRestrict j.range hmem),
    fun x => ?_⟩
  have h := congrArg Subtype.val (J.apply_symm_apply
    ((((ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ)).codRestrict j.range hmem) x))
  exact h

end ReciprocityTheory.ChartRestriction.L1
end
end
