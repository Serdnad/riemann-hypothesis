module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle001
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

section

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter

section CosMeas

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem isOpen_thick (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x; simp [thick]
  rw [this]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)

theorem measure_thick_eq (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  classical
  have hC : ∀ y, IsOpen {z : X | z - y ∈ Λ} := fun y =>
    hΛ.preimage (continuous_id.sub continuous_const)
  have hfin : ∀ t : Finset X,
      m1 (⋃ s ∈ t, {z | z - s ∈ Λ}) = m2 (⋃ s ∈ t, {z | z - s ∈ Λ}) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert s0 t hs0 ih =>
      rw [Finset.set_biUnion_insert]
      by_cases hex : ∃ s ∈ t, s0 - s ∈ Λ
      · obtain ⟨s, hs, hss⟩ := hex
        have hsub : {z : X | z - s0 ∈ Λ} ⊆ ⋃ s ∈ t, {z | z - s ∈ Λ} := by
          intro z hz
          simp only [Set.mem_iUnion, Set.mem_setOf_eq]
          exact ⟨s, hs, by simpa [sub_add_sub_cancel] using Λ.add_mem hz hss⟩
        rw [Set.union_eq_right.2 hsub, ih]
      · push_neg at hex
        have hdisj : Disjoint {z : X | z - s0 ∈ Λ} (⋃ s ∈ t, {z | z - s ∈ Λ}) := by
          rw [Set.disjoint_left]
          intro z hz hz'
          simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz'
          obtain ⟨s, hs, hzs⟩ := hz'
          apply hex s hs
          simpa [sub_sub_sub_cancel_left] using Λ.sub_mem hzs hz
        have hmeas : MeasurableSet (⋃ s ∈ t, {z : X | z - s ∈ Λ}) :=
          (isOpen_biUnion fun s _ => hC s).measurableSet
        rw [measure_union hdisj hmeas, measure_union hdisj hmeas, h, ih]
  obtain ⟨t, htS, hcov⟩ := hS.elim_nhds_subcover (fun x => {z : X | z - x ∈ Λ})
    (fun x _ => (hC x).mem_nhds (by simp [Λ.zero_mem]))
  have heq : thick S Λ = ⋃ s ∈ t, {z : X | z - s ∈ Λ} := by
    ext x
    simp only [thick, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨u, hu, hsu⟩ := Set.mem_iUnion₂.1 (hcov hs)
      exact ⟨u, hu, by simpa [sub_add_sub_cancel] using Λ.add_mem hxs hsu⟩
    · rintro ⟨u, hu, hxu⟩
      exact ⟨u, htS u hu, hxu⟩
  rw [heq]
  exact hfin t


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem iInter_thick (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [Set.mem_iInter, thick, Set.mem_setOf_eq]
  constructor
  · intro hx
    by_contra hxS
    have hc : Continuous fun d : X => x - d := continuous_const.sub continuous_id
    have hN : (fun d : X => x - d) ⁻¹' Sᶜ ∈ 𝓝 (0 : X) :=
      hc.continuousAt.preimage_mem_nhds (hSc.isOpen_compl.mem_nhds (by simpa using hxS))
    obtain ⟨n, hn⟩ := hb _ hN
    obtain ⟨s, hs, hxs⟩ := hx n
    have h1 := hn hxs
    simp only [Set.mem_preimage, sub_sub_cancel, Set.mem_compl_iff] at h1
    exact h1 hs
  · intro hx n
    exact ⟨x, hx, by simp [(Λ n).zero_mem]⟩

theorem measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hmono : Antitone fun n => thick S (Λ n) := by
    intro i j hij x hx
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hs, hanti hij hxs⟩
  have hmeas : ∀ n, MeasurableSet (thick S (Λ n)) := fun n =>
    (isOpen_thick S (Λ n) (hΛo n)).measurableSet
  have heq : ∀ n, m1 (thick S (Λ n)) = m2 (thick S (Λ n)) := fun n =>
    measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS
  rw [← iInter_thick S hSc Λ hb,
    hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩,
    hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet)
      ⟨0, by rw [← heq 0]; exact measure_ne_top _ _⟩]
  simp_rw [heq]

end CosMeas

theorem cosDens_holds : CosDens := by
  intro X _ _ _ _ _ _ ν m _ hν H hHo hHc hanti hb c0 κ hm0 hcos S hS
  have hC : ∀ (n : ℕ) (y : X), IsOpen {z : X | z - y ∈ H n} := fun n y =>
    (hHo n).preimage (continuous_id.sub continuous_const)
  have hC0 : MeasurableSet {z : X | z - c0 ∈ H 0} := (hC 0 c0).measurableSet
  have hback : ∀ n y z, y - c0 ∉ H 0 → z - y ∈ H n → z - c0 ∉ H 0 := by
    intro n y z hy hz hz0
    apply hy
    have hz' : z - y ∈ H 0 := hanti (Nat.zero_le n) hz
    simpa [sub_sub_sub_cancel_left] using (H 0).sub_mem hz0 hz'
  have key := measure_eq_of_cos m (κ • ν.restrict {z : X | z - c0 ∈ H 0}) H hHo hanti hb ?_
    S hS hS.isClosed
  · rw [key, Measure.smul_apply, Measure.restrict_apply' hC0, smul_eq_mul]
  · intro n y
    rw [Measure.smul_apply, Measure.restrict_apply' hC0, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z : X | z - y ∈ H n} ⊆ {z : X | z - c0 ∈ H 0} := by
        intro z hz
        have hz0 : z - y ∈ H 0 := hanti (Nat.zero_le n) hz
        simpa [sub_add_sub_cancel] using (H 0).add_mem hz0 hy
      rw [Set.inter_eq_left.2 hsub]
      exact hcos n y hy
    · have hdisj : {z : X | z - y ∈ H n} ∩ {z : X | z - c0 ∈ H 0} = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        exact hback n y z hy
      rw [hdisj, measure_empty, mul_zero]
      exact measure_mono_null (fun z hz => hback n y z hy hz) hm0

end PI.VolStabSW
end
end

section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace PI.VolStabSW

private theorem addHom_eq_zero_of_integralBasis_mul {F : Type} [Field F] [NumberField F] (g : F →+ ℂ)
    {y : F} (hy : y ≠ 0) (h0 : ∀ i, g (integralBasis F i * y) = 0) (w : F) : g w = 0 := by
  have hw : w = (∑ i, (integralBasis F).repr (w * y⁻¹) i • integralBasis F i) * y := by
    rw [(integralBasis F).sum_repr, mul_assoc, inv_mul_cancel₀ hy, mul_one]

  rw [hw, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [smul_mul_assoc, map_rat_smul, h0 i, smul_zero]

private theorem exists_mul_integers_of_fg {F : Type} [Field F] [NumberField F]
    (Λ : Submodule (𝓞 F) F) (hfg : (Λ.restrictScalars ℤ).FG) :
    ∃ c : F, c ≠ 0 ∧ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r := by
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (M := (𝓞 F)⁰) (S := F) s
  have hB0 : algebraMap (𝓞 F) F b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  let T : Submodule ℤ F :=
    { carrier := {a | ∃ r : 𝓞 F, algebraMap (𝓞 F) F b * a = algebraMap (𝓞 F) F r}
      add_mem' := by
        rintro a a' ⟨r, hr⟩ ⟨r', hr'⟩
        exact ⟨r + r', by rw [mul_add, hr, hr', map_add (f := _)]⟩
      zero_mem' := ⟨0, by rw [mul_zero, map_zero]⟩
      smul_mem' := by
        rintro n a ⟨r, hr⟩
        exact ⟨n • r, by rw [mul_smul_comm, hr, map_zsmul]⟩ }
  have hsT : Submodule.span ℤ (s : Set F) ≤ T := by
    rw [Submodule.span_le]
    intro a ha
    obtain ⟨r, hr⟩ := hb a ha
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  refine ⟨(algebraMap (𝓞 F) F b)⁻¹, inv_ne_zero hB0, fun a ha => ?_⟩
  have has : a ∈ Submodule.span ℤ (s : Set F) := by rw [hs]; exact ha
  obtain ⟨r, hr⟩ := hsT has
  refine ⟨r, ?_⟩
  have hrr : ((r : 𝓞 F) : F) = algebraMap (𝓞 F) F r := by
    rfl
  rw [hrr, ← hr, ← mul_assoc, inv_mul_cancel₀ hB0, one_mul]

private theorem fg_of_addHom_intValued {F : Type} [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F)
    (g : F →+ ℂ) (hg : ∀ a ∈ Λ, ∃ n : ℤ, g a = n) (hne : ∃ w, g w ≠ 0) :
    (Λ.restrictScalars ℤ).FG := by
  classical
  let φ : F →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ) :=
    { toFun := fun y i => g (integralBasis F i * y)
      map_add' := fun y y' => by funext i; simp only [mul_add, map_add (f := _), Pi.add_apply]
      map_smul' := fun n y => by
        funext i; simp only [mul_smul_comm, map_zsmul, RingHom.id_apply, Pi.smul_apply] }
  let ψ : (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ) →ₗ[ℤ]
      (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ) :=
    { toFun := fun z i => (z i : ℂ)
      map_add' := fun z z' => by funext i; simp only [Pi.add_apply, Int.cast_add]
      map_smul' := fun n z => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply, zsmul_eq_mul] }
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    obtain ⟨w, hw⟩ := hne
    exact hw (addHom_eq_zero_of_integralBasis_mul g hy0 (fun i => congrFun hy i) w)
  have hrange : (Λ.restrictScalars ℤ).map φ ≤ LinearMap.range ψ := by
    rintro _ ⟨y, hy, rfl⟩
    have hmem : ∀ i, integralBasis F i * y ∈ Λ := fun i => by
      have h := Λ.smul_mem (RingOfIntegers.basis F i) hy
      rwa [Algebra.smul_def, ← integralBasis_apply] at h
    choose n hn using fun i => hg _ (hmem i)
    exact ⟨n, funext fun i => (hn i).symm⟩
  have hQ : (((Λ.restrictScalars ℤ).map φ).comap ψ).FG := IsNoetherian.noetherian _
  have hmap : (((Λ.restrictScalars ℤ).map φ).comap ψ).map ψ = (Λ.restrictScalars ℤ).map φ := by
    apply le_antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact hz
    · intro x hx
      obtain ⟨z, rfl⟩ := hrange hx
      exact ⟨z, hx, rfl⟩
  have hfg := hQ.map ψ
  rw [hmap] at hfg
  exact Submodule.fg_of_fg_map_injective φ hφ hfg

theorem addIntF_holds : AddIntF := by
  intro F _ _ Λ _ hnp g hg
  by_contra hall
  obtain ⟨c, hc0, hc⟩ := exists_mul_integers_of_fg Λ (fg_of_addHom_intValued Λ g hg (not_forall.mp hall))
  exact hnp c hc0 hc

theorem chInf_of_lift (hL : ChLift) : ChInf :=
  chInf_of hL addIntF_holds

end PI.VolStabSW
end
end

section

noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem perp_sub_mem {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  rw [mem_perp, hs.sub_right, hs.smul_right, mul_right_comm, inv_mul_cancel₀ he, one_mul, sub_self]

theorem card_decomp {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  classical
  let T : V → K := fun x => (h e e)⁻¹ * h e x
  have hTe : ∀ (t : K) (w : perp hs e), T ((t • e) + (w : V)) = t := by
    intro t w
    simp only [T]
    rw [hs.add_right, hs.smul_right, (mem_perp hs e w).1 w.2, add_zero, ← mul_assoc,
      mul_comm ((h e e)⁻¹) t, mul_assoc, inv_mul_cancel₀ he, mul_one]
  let eqv : {x : V // h x x = c} ≃ Σ t : K, {w : perp hs e // h w w = c - σ t * t * h e e} :=
    { toFun := fun x => ⟨T x.1, ⟨⟨x.1 - T x.1 • e, perp_sub_mem hs e x.1 he⟩, by
        have h1 := decomp_val hs e (x.1 - T x.1 • e)
          ((mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)) (T x.1)
        have hx : T x.1 • e + (x.1 - T x.1 • e) = x.1 := by abel
        rw [hx, x.2] at h1
        show h (x.1 - T x.1 • e) (x.1 - T x.1 • e) = c - σ (T x.1) * T x.1 * h e e
        rw [eq_sub_iff_add_eq, add_comm]
        exact h1.symm⟩⟩
      invFun := fun p => ⟨p.1 • e + (p.2.1 : V), by
        rw [decomp_val hs e p.2.1 ((mem_perp hs e _).1 p.2.1.2) p.1]
        have h2 : h (p.2.1 : V) (p.2.1 : V) = c - σ p.1 * p.1 * h e e := p.2.2
        rw [h2]
        ring⟩
      left_inv := fun x => Subtype.ext (by
        show T x.1 • e + (x.1 - T x.1 • e) = x.1
        abel)
      right_inv := fun p => by
        refine Sigma.subtype_ext (hTe p.1 p.2.1) (Subtype.ext ?_)
        show p.1 • e + (p.2.1 : V) - T (p.1 • e + (p.2.1 : V)) • e = (p.2.1 : V)
        rw [hTe]
        abel }
  rw [Nat.card_congr eqv, Nat.card_sigma]

end PI.VolStabSW.FFHS
end
end

section

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set

theorem densCos_of_filt (hP1 : HenselCount) (hP2 : CosDens) {V X Y : Type} [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X)
    (hG : Continuous G) (hfG : ∀ v, f v = ι (G v)) (y : V) (Λ : ℕ → AddSubgroup V)
    (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V)) (hΛc : ∀ n, IsCompact (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (hHb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n)
    (hyp : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ 0}.indicator (fun _ => (1 : ℝ)) v ∂μ =
        ∫ b in S, g b ∂ν := by
  classical
  have hHa : Antitone H := by
    intro a b hab
    rw [← hD a, ← hD b]
    exact AddSubgroup.map_mono (hΛa hab)
  have hΦ : Continuous (fun Z : V => G (y + Z)) := hG.comp (continuous_const.add continuous_id)
  have hΦm : Measurable (fun Z : V => G (y + Z)) := hΦ.measurable
  have hΛ0m : MeasurableSet (Λ 0 : Set V) := (hΛo 0).measurableSet
  set m : Measure X := (μ.restrict (Λ 0 : Set V)).map (fun Z : V => G (y + Z)) with hm
  haveI : IsFiniteMeasure (μ.restrict (Λ 0 : Set V)) :=
    isFiniteMeasure_restrict.mpr (hΛc 0).measure_lt_top.ne
  haveI : IsFiniteMeasure m := by rw [hm]; infer_instance
  have hmT : ∀ T : Set X, MeasurableSet T → m T = μ {Z | Z ∈ Λ 0 ∧ G (y + Z) ∈ T} := by
    intro T hT
    rw [hm, Measure.map_apply hΦm hT, Measure.restrict_apply' hΛ0m]
    congr 1
    ext Z
    simp [and_comm]
  have hopen : ∀ (h : X) (k : ℕ), IsOpen {z : X | z - h ∈ H k} := fun h k =>
    (hHo k).preimage (continuous_sub_right h)
  have hν0 : ν (H 0 : Set X) ≠ 0 := ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
  have hνt : ν (H 0 : Set X) ≠ ⊤ := (hHc 0).measure_lt_top.ne
  have htrans : ∀ (h : X) (k : ℕ), ν {z : X | z - h ∈ H k} = ν (H k : Set X) := by
    intro h k
    have he : {z : X | z - h ∈ H k} = (fun z => -h + z) ⁻¹' (H k : Set X) := by
      ext z
      simp [sub_eq_neg_add]
    rw [he, measure_preimage_add]
  set κ : ENNReal := μ (Λ 0 : Set V) / ν (H 0 : Set X) with hκ
  have hdens : ∀ k (h : X), h - G y ∈ H 0 →
      m {z | z - h ∈ H k} = κ * ν {z | z - h ∈ H k} := by
    intro k h hh
    have hH := hP1 V X μ ν inferInstance inferInstance Λ H hΛo hΛc hΛa hHo hHc D hD G y hyp k h hh
    rw [hmT _ (hopen h k).measurableSet, htrans, hκ, div_eq_mul_inv, mul_right_comm,
      ← div_eq_mul_inv, ENNReal.eq_div_iff hν0 hνt, mul_comm]
    exact hH
  have hcompl : m {z | z - G y ∈ H 0}ᶜ = 0 := by
    rw [hmT _ (hopen (G y) 0).measurableSet.compl]
    refine (congrArg (fun s : Set V => μ s) (Set.ext fun Z => ?_)).trans measure_empty
    constructor
    · rintro ⟨hZ, hZ'⟩
      have h1 := hyp 0 0 (Λ 0).zero_mem Z hZ
      simp only [add_zero, zero_add] at h1
      have h2 : D Z ∈ H 0 := by
        rw [← hD 0]
        exact AddSubgroup.mem_map_of_mem D hZ
      have hmem : G (y + Z) - G y ∈ H 0 := by
        simpa using (H 0).add_mem (hHa (Nat.zero_le 1) h1) h2
      exact hZ' hmem
    · intro hZ
      exact False.elim hZ
  have hcos := hP2 X ν m inferInstance H hHo hHc hHa hHb (G y) κ hcompl hdens
  set C : Set X := {z | z - G y ∈ H 0} with hC
  have hCo : IsOpen C := hopen (G y) 0
  have hCc : IsClosed C := (hHc 0).isClosed.preimage (continuous_sub_right (G y))
  refine ⟨C.indicator (fun _ => κ.toReal), ?_, ?_⟩
  · refine continuous_indicator ?_ continuousOn_const
    intro a ha
    rw [hCc.frontier_eq, hCo.interior_eq, Set.diff_self] at ha
    simp at ha
  · intro S hS
    have hSm : MeasurableSet S := hS.isClosed.measurableSet
    have hpre : f ⁻¹' (ι '' S) = G ⁻¹' S := by
      ext v
      simp [hfG, hι.mem_set_image]
    have hCV : MeasurableSet {z : V | z - y ∈ Λ 0} :=
      ((hΛo 0).preimage (continuous_sub_right y)).measurableSet
    have key : m S = μ ({z : V | z - y ∈ Λ 0} ∩ G ⁻¹' S) := by
      rw [hmT S hSm, ← measure_preimage_add μ y ({z : V | z - y ∈ Λ 0} ∩ G ⁻¹' S)]
      congr 1
      ext Z
      simp
    rw [hpre, integral_indicator_const _ hCV, integral_indicator_const _ hCo.measurableSet]
    simp only [Measure.real, smul_eq_mul, mul_one]
    rw [Measure.restrict_apply hCV, Measure.restrict_apply hCo.measurableSet, ← key, hcos S hS,
      ENNReal.toReal_mul, Set.inter_comm, mul_comm]

end PI.VolStabSW
end
end
