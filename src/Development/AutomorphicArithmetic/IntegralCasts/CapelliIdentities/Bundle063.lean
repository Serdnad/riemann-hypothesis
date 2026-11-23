module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.GroupTheory.Coset.Card

@[expose] public section

section

open Polynomial

private lemma integral_of_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) :
    IsIntegral ℤ_[l] x := by
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hx
  have hl : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  have h0 := minpoly.aeval ℚ_[l] x
  rw [← hq, aeval_def, eval₂_map] at h0
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact h0

private lemma norm_of_integral {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l)
    (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hc : spectralValue (minpoly ℚ_[l] x) ≤ 1 := by
    rw [spectralValue_le_one_iff (minpoly.monic h.tower_top)]
    intro n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  exact hc

private lemma isUnit_of_inv_integral {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (a : R) (ha : algebraMap R K a ≠ 0)
    (h : IsIntegral R (algebraMap R K a)⁻¹) : IsUnit a := by
  obtain ⟨p, hp, he⟩ := h
  letI := invertibleOfNonzero (inv_ne_zero ha)
  have h1 := eval₂_reverse_mul_pow (algebraMap R K) ((algebraMap R K a)⁻¹) p
  rw [he, invOf_eq_inv, inv_inv] at h1
  have h2 : eval₂ (algebraMap R K) (algebraMap R K a) p.reverse = 0 := by
    simpa [ha] using h1
  have h3 : eval a p.reverse = 0 := by
    apply hinj
    rw [map_zero, ← h2, eval₂_at_apply]
  have h5 : p.reverse.coeff 0 = 1 := by
    simp [coeff_zero_reverse, hp.leadingCoeff]
  have h4 := divX_mul_X_add p.reverse
  rw [← h4, h5] at h3
  simp only [eval_add, eval_mul, eval_X, eval_C] at h3
  exact isUnit_iff_exists_inv.2 ⟨-(eval a p.reverse.divX), by linear_combination -h3⟩

theorem UpperTheory.integral_dvr_norm :
    ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O]
        [Module.Finite ℤ_[l] O],
        (∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → IsIntegral O x) ∧ (∀ a : O, ‖(a : PadicAlgCl l)‖ ≤ 1) ∧
          ∀ a : O, ¬ IsUnit a → ‖(a : PadicAlgCl l)‖ < 1 := by
  intro l _ O _ _
  have hfin : ∀ a : O, IsIntegral ℤ_[l] (a : PadicAlgCl l) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map O.val
  refine ⟨fun x hx => (integral_of_norm x hx).tower_top, fun a => norm_of_integral _ (hfin a),
    fun a ha => lt_of_le_of_ne (norm_of_integral _ (hfin a)) fun h1 => ha ?_⟩
  have ha0 : (a : PadicAlgCl l) ≠ 0 := by
    intro h
    simp [h] at h1
  have hinv : IsIntegral O (a : PadicAlgCl l)⁻¹ :=
    (integral_of_norm _ (by rw [norm_inv, h1, inv_one])).tower_top
  exact isUnit_of_inv_integral (K := PadicAlgCl l) Subtype.val_injective a ha0 hinv
end

section

theorem UpperTheory.dvr_of_norm_integral :
    ∀ {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], (∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → IsIntegral ℤ_[l] x) → IsDiscreteValuationRing (integralClosure ℤ_[l] K) := by
  intro l _ K _ h
  have hded : IsDedekindDomain (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K _
  have hfr : IsFractionRing (integralClosure ℤ_[l] K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[l] ℚ_[l] K _
  have key : ∀ x : K, ‖(x : PadicAlgCl l)‖ ≤ 1 →
      IsLocalization.IsInteger (integralClosure ℤ_[l] K) x := by
    intro x hx
    have hi : IsIntegral ℤ_[l] x :=
      (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective).mp (h _ hx)
    exact ⟨⟨x, hi⟩, rfl⟩
  have hval : ValuationRing (integralClosure ℤ_[l] K) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _ K]
    intro x
    rcases le_total ‖(x : PadicAlgCl l)‖ 1 with hx | hx
    · exact Or.inl (key x hx)
    · refine Or.inr (key _ ?_)
      rw [IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ hx
  have hinjK : Function.Injective (algebraMap ℤ_[l] K) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K, RingHom.coe_comp]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K)) := by
    intro a b hab
    exact hinjK (congrArg Subtype.val hab)
  have hnf : ¬ IsField (integralClosure ℤ_[l] K) := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l]
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hf)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[l] K) hnf).out 1 2).mpr hval
end

section

namespace UpperTheory.Reformulated.B.CoboundaryOfGenerator

noncomputable def ContAction.{u_1, u_2, u_3}
    {R : Type u_1} [CommRing R] {G : Type u_2} [Group G] [TopologicalSpace G]
    {M : Type u_3} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (rho : Representation R G M) : Prop :=
  Continuous fun p : G × M => rho p.1 p.2

theorem aux2.{u_1, u_2, u_3}
    {R : Type u_3} [CommRing R] {G : Type u_1} [Group G] [TopologicalSpace G]
    {M : Type u_2} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (rho : Representation R G M) {f f' : G → M}
    (hf : Continuous f ∧ ∀ g h : G, f (g * h) = f g + rho g (f h))
    (hf' : Continuous f' ∧ ∀ g h : G, f' (g * h) = f' g + rho g (f' h)) :
    Continuous (f + f') ∧ ∀ g h : G, (f + f') (g * h) = (f + f') g + rho g ((f + f') h) := by
  obtain ⟨hc, hf⟩ := hf
  obtain ⟨hc', hf'⟩ := hf'
  refine ⟨hc.add hc', fun g h => ?_⟩
  simp only [Pi.add_apply, hf g h, hf' g h, map_add]
  abel

theorem aux3.{u_1, u_2, u_3}
    {R : Type u_3} [CommRing R] {G : Type u_1} [Group G] [TopologicalSpace G]
    {M : Type u_2} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (rho : Representation R G M) :
    Continuous (0 : G → M) ∧ ∀ g h : G, (0 : G → M) (g * h) = (0 : G → M) g + rho g ((0 : G → M) h) :=
  ⟨continuous_const, fun _ _ => by simp⟩

theorem aux4.{u_1, u_2, u_3}
    {R : Type u_3} [CommRing R] {G : Type u_1} [Group G] [TopologicalSpace G]
    {M : Type u_2} [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousConstSMul R M]
    (rho : Representation R G M) (c : R) (f : G → M)
    (hf : Continuous f ∧ ∀ g h : G, f (g * h) = f g + rho g (f h)) :
    Continuous (c • f) ∧ ∀ g h : G, (c • f) (g * h) = (c • f) g + rho g ((c • f) h) := by
  obtain ⟨hc, hf⟩ := hf
  refine ⟨hc.const_smul c, fun g h => ?_⟩
  simp only [Pi.smul_apply, hf g h, map_smul, smul_add]

noncomputable def Z1.{u_1, u_2, u_3}
    {R : Type u_1} [CommRing R] {G : Type u_2} [Group G] [TopologicalSpace G]
    {M : Type u_3} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (rho : Representation R G M) : Submodule R (G → M) where
  carrier := {f : G → M | Continuous f ∧ ∀ g h : G, f (g * h) = f g + rho g (f h)}
  add_mem' := aux2 rho
  zero_mem' := aux3 rho
  smul_mem' := aux4 rho

theorem aux6.{u_1, u_2}
    {R : Type u_1} {M : Type u_2} [SMul R M] [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousConstSMul R M :=
  ⟨fun _ => continuous_of_discreteTopology⟩

theorem aux7.{u_1} {R : Type u_1} [CommRing R] : RingHomSurjective (RingHom.id R) :=
  ⟨Function.surjective_id⟩

noncomputable def d0.{u_1, u_2, u_3}
    {R : Type u_1} [CommRing R] {G : Type u_2} [Group G]
    {M : Type u_3} [AddCommGroup M] [Module R M]
    (rho : Representation R G M) : M →ₗ[R] (G → M) :=
  LinearMap.pi fun g => rho g - LinearMap.id

noncomputable def B1.{u_1, u_2, u_3}
    {R : Type u_1} [CommRing R] {G : Type u_2} [Group G]
    {M : Type u_3} [AddCommGroup M] [Module R M]
    (rho : Representation R G M) : Submodule R (G → M) :=
  LinearMap.range (d0 rho)

theorem cobOfGen
    (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (χ : Γ →* ℤ_[l]ˣ)
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (γ : Γ)
    (hχ : Continuous χ) (hρ : ContAction ρ)
    (hker : ∀ g, χ g = 1 → ∀ m, ρ g m = m)
    (hgen : ∀ g, χ g ∈ (Subgroup.zpowers (χ γ)).topologicalClosure)
    (hsurj : Function.Surjective fun m => ρ γ m - m)
    (z : Γ → M) (hz : z ∈ @Z1 R _ Γ _ _ M _ _ _ inferInstance aux6 ρ)
    (hz0 : ∀ g, χ g = 1 → z g = 0) :
    z ∈ B1 ρ := by
  have hzc : Continuous z := hz.1
  have hzm : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := hz.2
  obtain ⟨m, hm⟩ := hsurj (z γ)
  have hone : z 1 = 0 := hz0 1 (map_one χ)
  -- The cocycle agrees with the coboundary on a closed subgroup containing γ.
  let S : Subgroup Γ :=
    { carrier := {g | z g = ρ g m - m}
      one_mem' := by
        change z 1 = ρ 1 m - m
        simp [hone]
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = ρ a m - m := ha
        have hb' : z b = ρ b m - m := hb
        change z (a * b) = ρ (a * b) m - m
        rw [hzm, ha', hb', map_mul, map_sub, mul_apply_eq_comp]
        abel
      inv_mem' := by
        intro a ha
        have ha' : z a = ρ a m - m := ha
        change z a⁻¹ = ρ a⁻¹ m - m
        have h1 := hzm a⁻¹ a
        have h2 : ρ a⁻¹ (ρ a m) = m := by
          rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
        rw [inv_mul_cancel, hone, ha', map_sub, h2] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm, neg_sub] }
  have hρm : Continuous fun g : Γ => ρ g m :=
    Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) (f := fun g : Γ => (g, m)) hρ
      (continuous_id.prodMk continuous_const)
  have hSc : IsClosed (S : Set Γ) := isClosed_eq hzc (hρm.sub continuous_const)
  have himg : IsClosed ((S.map χ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hSc.isCompact.image hχ).isClosed
  have hle : (Subgroup.zpowers (χ γ)).topologicalClosure ≤ S.map χ :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.zpowers_le).2 ⟨γ, hm.symm, rfl⟩) himg
  have hall : ∀ g : Γ, g ∈ S := by
    intro g
    obtain ⟨s, hs, hsg⟩ := hle (hgen g)
    have hk : χ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
    have hmem : s⁻¹ * g ∈ S := by
      change z (s⁻¹ * g) = ρ (s⁻¹ * g) m - m
      rw [hz0 _ hk, hker _ hk, sub_self]
    simpa using S.mul_mem hs hmem
  refine ⟨m, funext fun g => ?_⟩
  exact (hall g).symm

end UpperTheory.Reformulated.B.CoboundaryOfGenerator
end

section

theorem UpperTheory.Reformulated.B.CoboundaryCriterion.isCoboundary_of_coprime :
    ∀ {R G M : Type} [inst : CommRing R]
    [inst_1 : Group G] [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (ρ : Representation R G M) {l : ℕ}
    {H C : Type} [inst_4 : Group H] [inst_5 : Group C] [Finite C] (i : H →* G) (f : H →* C),
    (Nat.card C).Coprime l →
      (∀ (m : M), l • m = (0 : M)) →
        ∀ (z : G → M),
          (∀ (g h : G), z (g * h) = z g + ((ρ : G → M →ₗ[R] M) g : M → M) (z h)) →
            (∀ (u : H), (f : H → C) u = (1 : C) → z ((i : H → G) u) = (0 : M)) →
              ∃ (b : M), ∀ (u : H), z ((i : H → G) u) = ((ρ : G → M →ₗ[R] M) ((i : H → G) u) : M → M) b - b := by
  intro R G M _ _ _ _ ρ l H C _ _ _ i f hcop hl z hz hker
  classical
  have hfac : ∀ u v : H, f u = f v → z (i u) = z (i v) := by
    intro u v huv
    have h1 : z (i (v⁻¹ * u)) = 0 := hker _ (by simp [huv])
    have h2 : i u = i v * i (v⁻¹ * u) := by simp
    rw [h2, hz, h1, map_zero, add_zero]
  haveI : Fintype f.range := Fintype.ofFinite _
  obtain ⟨s, hs⟩ : ∃ s : f.range → H, ∀ q, f (s q) = (q : C) :=
    ⟨fun q => q.2.choose, fun q => q.2.choose_spec⟩
  have hcop' : (Nat.card f.range).Coprime l :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card f.range) hcop
  set n := Nat.card f.range with hn
  set S : M := ∑ q : f.range, z (i (s q)) with hS
  have key : ∀ u : H, S = n • z (i u) + ρ (i u) S := by
    intro u
    have h1 : S = ∑ q : f.range, z (i (s (f.rangeRestrict u * q))) :=
      (Equiv.sum_comp (Equiv.mulLeft (f.rangeRestrict u)) (fun q => z (i (s q)))).symm
    have h2 : ∀ q : f.range,
        z (i (s (f.rangeRestrict u * q))) = z (i u) + ρ (i u) (z (i (s q))) := by
      intro q
      rw [← hz, ← map_mul]
      apply hfac
      simp [hs]
    calc S = ∑ q : f.range, (z (i u) + ρ (i u) (z (i (s q)))) := by
          rw [h1]; exact Finset.sum_congr rfl fun q _ => h2 q
      _ = n • z (i u) + ρ (i u) S := by

          rw [Finset.sum_add_distrib, Finset.sum_const, hS, map_sum, hn, Nat.card_eq_fintype_card,
          Finset.card_univ]
  obtain ⟨a, c, hac⟩ : IsCoprime (n : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop'
  refine ⟨-(a • S), fun u => ?_⟩
  have h3 : (n : ℤ) • z (i u) = S - ρ (i u) S := by
    rw [natCast_zsmul, eq_sub_iff_add_eq]; exact (key u).symm
  have h4 : (l : ℤ) • z (i u) = 0 := by rw [natCast_zsmul, hl]
  calc z (i u) = (a * n + c * l) • z (i u) := by rw [hac, one_smul]
    _ = a • (S - ρ (i u) S) := by rw [add_smul, mul_smul, mul_smul, h3, h4, smul_zero, add_zero]
    _ = ρ (i u) (-(a • S)) - -(a • S) := by
        rw [map_neg, map_zsmul, smul_sub]; abel
end

section

noncomputable def UpperTheory.Reformulated.B.CyclicSubtraction.cycSub.{u_1, u_2} :
    {G : Type u_1} → {M : Type u_2} → [inst : Group G] → [inst_1 : AddCommGroup M] → Representation ℤ G M → G → M →+ M :=
    fun {G : Type u_1} {M : Type u_2} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) (σ : G) ↦
      ((ρ : G → M →ₗ[ℤ] M) σ - LinearMap.id).toAddMonoidHom

theorem UpperTheory.Reformulated.B.CyclicSubtraction.apply_eq_of_cycSub_eq_zero.{u_1, u_2} :
    ∀ {G : Type u_1} {M : Type u_2} [inst : Group G] [inst_1 : AddCommGroup M] (ρ : Representation ℤ G M) {σ : G},
      (∀ (g : G), g ∈ Subgroup.zpowers σ) →
        ∀ {x : M}, (UpperTheory.Reformulated.B.CyclicSubtraction.cycSub ρ σ : M → M) x = (0 : M) → ∀ (g : G), ((ρ : G → M →ₗ[ℤ] M) g : M → M) x = x := by
  intro G M _ _ ρ σ hσ x hx g
  have h0 : ρ σ x - x = 0 := hx
  have h1 : ρ σ x = x := sub_eq_zero.mp h0
  let H : Subgroup G :=
    { carrier := {g | ρ g x = x}
      one_mem' := by
        show ρ 1 x = x
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha']
          _ = ρ (a⁻¹ * a) x := by rw [map_mul, Module.End.mul_apply]
          _ = x := by
            rw [inv_mul_cancel, map_one]
            rfl }
  have hle : Subgroup.zpowers σ ≤ H := (Subgroup.zpowers_le).mpr h1
  exact hle (hσ g)
end

section

noncomputable def UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd :
    {A H M : Type} →
      [inst : CommRing A] →
        [inst_1 : Group H] →
          [inst_2 : AddCommGroup M] → [inst_3 : _root_.Module A M] → Representation A H M → Subgroup H → Submodule A M :=
  fun {_A _H _M} _ _ _ _ ρ K =>
    { carrier := {v | ∀ k ∈ K, ρ k v = v}
      add_mem' := fun {a b} ha hb k hk => by
        rw [map_add (f := _), ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero (ρ k)
      smul_mem' := fun c v hv k hk => by
        rw [map_smul, hv k hk] }
end

section

noncomputable def UpperTheory.Reformulated.B.Rb1.Zc :
    {D N : Type} → [inst : Group D] → [TopologicalSpace D] → [inst_2 : AddCommGroup N] → Representation ℤ D N → Set (D → N) :=
    fun {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) ↦
      {z : D → N | IsLocallyConstant z ∧ ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t)}

theorem UpperTheory.Reformulated.B.Rb1.ul_zero :
    ∀ {D N : Type} [inst : Group D] [inst_1 : TopologicalSpace D] [inst_2 : IsTopologicalGroup D] [inst_3 : AddCommGroup N]
      (ρ : Representation ℤ D N) (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
        ∀ z ∈ UpperTheory.Reformulated.B.Rb1.Zc ρ, (∀ s ∈ I, z s = (0 : N)) → z φ = (0 : N) → ∀ (s : D), z s = (0 : N) := by
  intro D N _ _ _ _ ρ I φ hcl z hz hI hφ s
  have hlc : IsLocallyConstant z := hz.1
  have hco : ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t) := hz.2
  have h1 : z 1 = 0 := by
    have h := hco 1 1
    rw [mul_one, map_one] at h
    simpa using h
  let K : Subgroup D :=
    { carrier := z ⁻¹' {0}
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = 0 := ha
        have hb' : z b = 0 := hb
        show z (a * b) = 0
        rw [hco, ha', hb', map_zero, add_zero]
      one_mem' := h1
      inv_mem' := by
        intro a ha
        have ha' : z a = 0 := ha
        show z a⁻¹ = 0
        have h := hco a⁻¹ a
        rw [inv_mul_cancel, h1, ha', map_zero, add_zero] at h
        exact h.symm }
  have hK : IsClosed (K : Set D) := hlc.isClosed_fiber 0
  have hle : I ⊔ Subgroup.zpowers φ ≤ K :=
    sup_le hI (by
      rw [Subgroup.zpowers_le]
      exact hφ)
  have htop : (⊤ : Subgroup D) ≤ K := by
    rw [← hcl]
    exact Subgroup.topologicalClosure_minimal _ hle hK
  exact htop (Subgroup.mem_top s)
end

section

namespace PrecompleteLimitOfPowDvd

private lemma memPow {R : Type*} [CommRing R] (π x : R) (m : ℕ) :
    x ∈ ((Ideal.span {π}) ^ m • (⊤ : Submodule R R)) ↔ π ^ m ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private lemma tele {R : Type*} [CommRing R] (π : R) (f : ℕ → R)
    (h : ∀ n : ℕ, π ^ n ∣ f (n + 1) - f n) (m : ℕ) : ∀ k : ℕ, π ^ m ∣ f (m + k) - f m := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : π ^ m ∣ f (m + k + 1) - f (m + k) :=
      (pow_dvd_pow π (Nat.le_add_right m k)).trans (h (m + k))
    have : f (m + (k + 1)) - f m = (f (m + k + 1) - f (m + k)) + (f (m + k) - f m) := by
      rw [← add_assoc]; ring
    rw [this]; exact dvd_add h2 ih

end PrecompleteLimitOfPowDvd

theorem UpperTheory.Reformulated.B.Yra6.main.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] {π : R},
      IsPrecomplete (Ideal.span {π}) R →
        ∀ (f : ℕ → R), (∀ (n : ℕ), π ^ n ∣ f (n + (1 : ℕ)) - f n) → ∃ (L : R), ∀ (n : ℕ), π ^ n ∣ f n - L := by
  intro R _ π hP f h
  obtain ⟨L, hL⟩ := hP.prec' f (by
    intro m n hmn
    rw [SModEq.sub_mem, PrecompleteLimitOfPowDvd.memPow]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have := PrecompleteLimitOfPowDvd.tele π f h m k
    rw [← neg_sub]; exact (dvd_neg).2 this)
  refine ⟨L, fun n => ?_⟩
  have := hL n
  rw [SModEq.sub_mem, PrecompleteLimitOfPowDvd.memPow] at this
  exact this
end
