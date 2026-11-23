module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Topology Filter Set
open scoped Classical

noncomputable section

namespace GlobalTheory.SBProd

theorem exists_compact_clopen_nhd {H : Type} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] {x : H} {U : Set H} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set H, IsClopen V ∧ IsCompact V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU hx
  obtain ⟨V, hV, hxV, hVs⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 (isOpen_interior.mem_nhds xs)
  exact ⟨V, hV, comp.of_isClosed_subset hV.1 (hVs.trans interior_subset), hxV,
    (hVs.trans interior_subset).trans sU⟩

theorem isLocallyConstant_filter {H ι : Type} [TopologicalSpace H] (F : Finset ι) (U : ι → Set H)
    (hU : ∀ i, IsClopen (U i)) : IsLocallyConstant fun a => F.filter (fun i => a ∈ U i) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ i ∈ F, ∀ᶠ y in 𝓝 x, (y ∈ U i ↔ x ∈ U i) := by
    intro i _
    by_cases h : x ∈ U i
    · filter_upwards [(hU i).isOpen.mem_nhds h] with y hy
      exact iff_of_true hy h
    · filter_upwards [(hU i).compl.isOpen.mem_nhds h] with y hy
      exact iff_of_false hy h
  filter_upwards [(Filter.eventually_all_finset F).2 this] with y hy
  exact Finset.filter_congr fun i hi => hy i hi

theorem exists_sum_box (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] (κ κ' : Type) [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → X) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (κ ⊕ κ' → X)) :
    ∃ (ι : Type) (_ : Fintype ι) (g₁ : ι → (κ → X) → ℂ) (g₂ : ι → (κ' → X) → ℂ),
      (∀ i, g₁ i ∈ GlobalTheory.WeilM.SB (κ → X)) ∧ (∀ i, g₂ i ∈ GlobalTheory.WeilM.SB (κ' → X)) ∧
      g = ∑ i, fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr) := by
  obtain ⟨hlc, hcs⟩ := hg
  let e : (κ ⊕ κ' → X) ≃ₜ (κ → X) × (κ' → X) := Homeomorph.sumArrowHomeomorphProdArrow
  let h : (κ → X) × (κ' → X) → ℂ := g ∘ e.symm
  have hgh : ∀ z, g z = h (z ∘ Sum.inl, z ∘ Sum.inr) := fun z => by
    have : (z ∘ Sum.inl, z ∘ Sum.inr) = e z := rfl
    simp [h, this]
  have hlc' : IsLocallyConstant h := hlc.comp_continuous e.symm.continuous
  have hcs' : HasCompactSupport h := hcs.comp_homeomorph e.symm
  have key : ∀ p : (κ → X) × (κ' → X), ∃ U : Set (κ → X), ∃ V : Set (κ' → X), IsClopen U ∧ IsCompact U ∧
      IsClopen V ∧ IsCompact V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧ ∀ a ∈ U, ∀ b ∈ V, h (a, b) = h p := by
    rintro ⟨a₀, b₀⟩
    obtain ⟨u, v, hu, hv, hpu, hpv, huv⟩ :=
      isOpen_prod_iff.1 (hlc'.isOpen_fiber (h (a₀, b₀))) a₀ b₀ rfl
    obtain ⟨U, hU, hUc, haU, hUu⟩ := exists_compact_clopen_nhd hu hpu
    obtain ⟨V, hV, hVc, hbV, hVv⟩ := exists_compact_clopen_nhd hv hpv
    exact ⟨U, V, hU, hUc, hV, hVc, haU, hbV, fun a ha b hb => huv (mk_mem_prod (hUu ha) (hVv hb))⟩
  choose U V hU hUc hV hVc hpU hpV hconst using key
  obtain ⟨F, hF⟩ := hcs'.isCompact.elim_finite_subcover (fun p => U p ×ˢ V p)
    (fun p => (hU p).isOpen.prod (hV p).isOpen) (fun q _ => mem_iUnion.2 ⟨q, hpU q, hpV q⟩)
  let σ : (κ → X) → Finset F := fun a => Finset.univ.filter (fun i : F => a ∈ U i)
  let τ : (κ' → X) → Finset F := fun b => Finset.univ.filter (fun i : F => b ∈ V i)
  have hσ : IsLocallyConstant σ := isLocallyConstant_filter _ (fun i : F => U i) fun i => hU i
  have hτ : IsLocallyConstant τ := isLocallyConstant_filter _ (fun i : F => V i) fun i => hV i
  let c : Finset F → Finset F → ℂ := fun S T =>
    if hx : (S ∩ T).Nonempty then h (hx.choose : (κ → X) × (κ' → X)) else 0
  refine ⟨Finset F × Finset F, inferInstance,
    fun x a => if σ a = x.1 ∧ x.1.Nonempty then c x.1 x.2 else 0,
    fun x b => if τ b = x.2 ∧ x.2.Nonempty then 1 else 0, ?_, ?_, ?_⟩
  · intro x
    refine ⟨hσ.comp fun s => if s = x.1 ∧ x.1.Nonempty then c x.1 x.2 else 0, ?_⟩
    by_cases hx : x.1.Nonempty
    · obtain ⟨i, hi⟩ := hx
      refine HasCompactSupport.intro (hUc i) fun a ha => if_neg fun hs => ha ?_
      rw [← hs.1] at hi
      simpa [σ] using hi
    · exact HasCompactSupport.intro isCompact_empty fun a _ => if_neg fun hs => hx hs.2
  · intro x
    refine ⟨hτ.comp fun s => if s = x.2 ∧ x.2.Nonempty then (1 : ℂ) else 0, ?_⟩
    by_cases hx : x.2.Nonempty
    · obtain ⟨i, hi⟩ := hx
      refine HasCompactSupport.intro (hVc i) fun b hb => if_neg fun hs => hb ?_
      rw [← hs.1] at hi
      simpa [τ] using hi
    · exact HasCompactSupport.intro isCompact_empty fun b _ => if_neg fun hs => hx hs.2
  · funext z
    rw [Finset.sum_apply, hgh z]
    generalize z ∘ Sum.inl = a
    generalize z ∘ Sum.inr = b
    rw [Fintype.sum_eq_single (σ a, τ b)]
    · by_cases hst : (σ a ∩ τ b).Nonempty
      · have hs : (σ a).Nonempty := hst.mono Finset.inter_subset_left
        have ht : (τ b).Nonempty := hst.mono Finset.inter_subset_right
        have hmem := Finset.mem_inter.1 hst.choose_spec
        simp only [σ, τ, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        have hc : c (σ a) (τ b) = h (hst.choose : (κ → X) × (κ' → X)) := dif_pos hst
        simp only [true_and, hs, ht, and_self, if_true, hc, mul_one]
        exact hconst _ a hmem.1 b hmem.2
      · have hc : c (σ a) (τ b) = 0 := dif_neg hst
        simp only [hc, ite_self, zero_mul]
        by_contra hne
        obtain ⟨i, hi, hab⟩ := mem_iUnion₂.1 (hF (subset_tsupport h hne))
        exact hst ⟨⟨i, hi⟩, Finset.mem_inter.2 ⟨by simpa [σ] using hab.1, by simpa [τ] using hab.2⟩⟩
    · intro x hx
      by_cases h1 : σ a = x.1
      · have h2 : τ b ≠ x.2 := fun h2 => hx (Prod.ext h1.symm h2.symm)
        simp [h2]
      · simp [h1]

end GlobalTheory.SBProd
end
end

section

open GlobalTheory.WeilM

noncomputable section

open scoped Classical Topology

namespace GlobalTheory.CharForm

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

def cosetInd (U : AddSubgroup X) (q : X ⧸ U) : X → ℂ := fun x => if (x : X ⧸ U) = q then 1 else 0

theorem cosetInd_mem_SB (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X)) (q : X ⧸ U) :
    cosetInd U q ∈ SB X := by
  haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo
  refine ⟨?_, ?_⟩
  · exact (IsLocallyConstant.of_discrete (fun q' : X ⧸ U => if q' = q then (1 : ℂ) else 0)).comp_continuous
      QuotientAddGroup.continuous_mk
  · have hK : IsCompact ((fun u => q.out + u) '' (U : Set X)) := hUc.image (continuous_const.add continuous_id)
    have hKc : IsClosed ((fun u => q.out + u) '' (U : Set X)) :=
      (Homeomorph.addLeft q.out).isClosedMap _ (AddSubgroup.isClosed_of_isOpen U hUo)
    refine HasCompactSupport.intro' hK hKc fun x hx => ?_
    simp only [cosetInd, ite_eq_right_iff, one_ne_zero, imp_false]
    intro hxq
    apply hx
    refine ⟨-q.out + x, ?_, by simp⟩
    rw [← QuotientAddGroup.out_eq' q] at hxq
    exact QuotientAddGroup.eq.mp hxq.symm

theorem exists_periodic {C : Set (X → ℂ)}
    (H : ∀ N ∈ 𝓝 (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) {V : Set X} (hV : V ∈ 𝓝 (0 : X)) :
    ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ V ∧
      (∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) ∧ ∀ x, ∀ u ∈ U, g (x + u) = g x := by
  have hN : ∀ x, {y | g (x + y) = g x} ∈ 𝓝 (0 : X) := fun x =>
    ((hg.1.isOpen_fiber (g x)).preimage (continuous_const_add x)).mem_nhds (by simp)
  choose W hWo _ hWN _ using fun x => H _ (hN x)
  obtain ⟨t, -, hcov⟩ := hg.2.isCompact.elim_nhds_subcover (fun x => {y | y - x ∈ W x}) fun x _ =>
    ((hWo x).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  have hNm : V ∩ ⋂ x ∈ t, (W x : Set X) ∈ 𝓝 (0 : X) :=
    Filter.inter_mem hV ((Filter.biInter_finset_mem t).2 fun x _ => (hWo x).mem_nhds (W x).zero_mem)
  obtain ⟨U, hUo, hUc, hUN, hUk⟩ := H _ hNm
  refine ⟨U, hUo, hUc, fun u hu => (hUN hu).1, hUk, ?_⟩
  have hA : ∀ y ∈ tsupport g, ∀ u ∈ U, g (y + u) = g y := by
    intro y hy u hu
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcov hy)
    have hu' : u ∈ W x := Set.mem_iInter₂.mp (hUN hu).2 x hxt
    have h1 : g (x + (y - x)) = g x := hWN x hyx
    have h2 : g (x + (y - x + u)) = g x := hWN x ((W x).add_mem hyx hu')
    rw [add_sub_cancel] at h1
    rw [← add_assoc, add_sub_cancel] at h2
    rw [h1, h2]
  intro y u hu
  by_cases hy : y ∈ tsupport g
  · exact hA y hy u hu
  by_cases hyu : y + u ∈ tsupport g
  · have := hA _ hyu (-u) (U.neg_mem hu)
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

theorem apply_eq_of_periodic {C : Set (X → ℂ)} (a : (X → ℂ) →ₗ[ℂ] ℂ)
    (ha : ∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g)
    (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X))
    (hUk : ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) (hper : ∀ x, ∀ u ∈ U, g (x + u) = g x) :
    a g = g 0 * a (cosetInd U 0) := by
  haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo
  have hout : ∀ x : X, g ((x : X ⧸ U).out) = g x := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add U x
    rw [hh]; exact hper x h h.2
  have hfin : (QuotientAddGroup.mk '' tsupport g : Set (X ⧸ U)).Finite :=
    (hg.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T : Finset (X ⧸ U) := insert 0 hfin.toFinset with hT
  have hsum : g = ∑ q ∈ T, g q.out • cosetInd U q := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cosetInd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · exact (hout x).symm
    · apply image_eq_zero_of_notMem_tsupport
      intro hxs
      exact hx (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr ⟨x, hxs, rfl⟩))
  have hkill : ∀ q : X ⧸ U, q ≠ 0 → a (cosetInd U q) = 0 := by
    intro q hq
    have hx₀ : q.out ∉ U := by
      intro hm
      apply hq
      rw [← QuotientAddGroup.out_eq' q]
      exact (QuotientAddGroup.eq_zero_iff _).mpr hm
    obtain ⟨χ, hχC, hχU, hχ1⟩ := hUk _ hx₀
    have hmul : (fun x => χ x * cosetInd U q x) = χ q.out • cosetInd U q := by
      funext x
      simp only [cosetInd, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      split_ifs with hxq
      · have hm : -q.out + x ∈ U := by
          rw [← QuotientAddGroup.out_eq' q] at hxq
          exact QuotientAddGroup.eq.mp hxq.symm
        have := hχU _ hm
        rwa [add_neg_cancel_left] at this
      · rfl
    have e := ha χ hχC _ (cosetInd_mem_SB U hUo hUc q)
    rw [hmul, map_smul, smul_eq_mul] at e
    have : (χ q.out - 1) * a (cosetInd U q) = 0 := by rw [sub_mul, e, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hχ1)
  conv_lhs => rw [hsum]

  rw [map_sum, Finset.sum_eq_single (0 : X ⧸ U)]
  · rw [map_smul, smul_eq_mul, ← QuotientAddGroup.mk_zero, hout]
  · intro q _ hq
    rw [map_smul, hkill q hq, smul_zero]
  · intro h
    exact absurd (Finset.mem_insert_self _ _) h

theorem exists_eq_mul_apply_zero : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (C : Set (X → ℂ)),
    (∀ N ∈ nhds (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) →
    ∀ (a : (X → ℂ) →ₗ[ℂ] ℂ), (∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g) →
      ∃ c : ℂ, ∀ g ∈ SB X, a g = c * g 0 := by
  intro X _ _ _ C H a ha
  obtain ⟨U₀, hU₀o, hU₀c, -, hU₀k⟩ := H Set.univ Filter.univ_mem
  refine ⟨a (cosetInd U₀ 0), fun g hg => ?_⟩
  obtain ⟨U, hUo, hUc, hUV, hUk, hper⟩ := exists_periodic H hg (hU₀o.mem_nhds U₀.zero_mem)
  have h1 := apply_eq_of_periodic a ha U hUo hUc hUk hg hper
  have h2 := apply_eq_of_periodic a ha U hUo hUc hUk (cosetInd_mem_SB U₀ hU₀o hU₀c 0) fun x u hu => by
    have : ((u : X) : X ⧸ U₀) = 0 := (QuotientAddGroup.eq_zero_iff u).mpr (hUV hu)
    simp only [cosetInd, QuotientAddGroup.mk_add, this, add_zero]
  have h0 : cosetInd U₀ (0 : X ⧸ U₀) 0 = 1 := by simp [cosetInd]
  rw [h0, one_mul] at h2
  rw [h1, h2, mul_comm]

end GlobalTheory.CharForm
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix

namespace GlobalTheory.WeilTr

open GlobalTheory.WeilM

variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]

def trRep {G : Type} [Group G] (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) (om : G →* Module.End ℂ ((κ → R) → ℂ)) :
    G →* Module.End ℂ ((κ → R) → ℂ) where
  toFun g := T.toLinearMap ∘ₗ om g ∘ₗ T.symm.toLinearMap
  map_one' := by
    ext φ x
    simp
  map_mul' g h := by
    ext φ x
    simp

theorem trRep_apply {G : Type} [Group G] (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) (om : G →* Module.End ℂ ((κ → R) → ℂ))
    (g : G) (φ : (κ → R) → ℂ) : trRep T om g φ = T (om g (T.symm φ)) := rfl

variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}

def IsGoodInt [TopologicalSpace R] (C : TestClass R) (ψ : AddChar R ℂ) (d d₁ : Darboux B κ)
    (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : Prop :=
  (∀ φ, φ ∈ C.sp κ ↔ T φ ∈ C.sp κ) ∧
  (∀ w, ∀ φ ∈ C.sp κ, T (d.rho ψ w φ) = d₁.rho ψ w (T φ)) ∧
  (∀ l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ, l ∈ C.adm κ ↔ l ∘ₗ T.toLinearMap ∈ C.adm κ) ∧
  ∀ μ : @Measure (κ → R) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ c : ℝ≥0∞, ∀ φ ∈ C.sp κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

section Dbl

variable {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

def HasDbl [TopologicalSpace R] (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (d d₁ : Darboux (symp c ξ JA JB) κ) (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : Prop :=
  ∀ dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ), IsDblCoord c ξ JA JB d dd →
    ∃ (dd₁ : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) (Td : ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ))
      (S : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)), IsDblCoord c ξ JA JB d₁ dd₁ ∧ IsGoodInt C ψ dd dd₁ Td ∧
      (∀ φ, φ ∈ C.sp κ ↔ S φ ∈ C.sp κ) ∧
      ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ, Td (boxFun φ₁ φ₂) = boxFun (T φ₁) (S φ₂)

end Dbl

theorem isUSplitting_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] {C : TestClass R} {ψ : AddChar R ℂ} {d d₁ : Darboux B κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T)
    {G : Type} [Group G] [TopologicalSpace G] {act : G → W → W} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUSplitting C ψ d act om) : IsUSplitting C ψ d₁ act (trRep T om) := by
  obtain ⟨hsp, hheis, hadm, hunit⟩ := hT
  have hinv : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hsp _).2 (by simpa using hφ)
  have hrho : ∀ w, ∀ φ ∈ C.sp κ, T.symm (d₁.rho ψ w φ) = d.rho ψ w (T.symm φ) := fun w φ hφ => by
    rw [LinearEquiv.symm_apply_eq, hheis w _ (hinv φ hφ), LinearEquiv.apply_symm_apply]
  refine ⟨⟨fun g φ hφ => ?_, fun g w φ hφ => ?_, fun g l hl => ?_⟩, fun μ hμ g φ hφ => ?_, fun l hl φ hφ => ?_⟩
  · rw [trRep_apply]
    exact (hsp _).1 (h.pres g _ (hinv φ hφ))
  · rw [trRep_apply, trRep_apply, hrho w φ hφ, h.impl g w _ (hinv φ hφ), hheis _ _ (h.pres g _ (hinv φ hφ))]
  · have h1 : l ∘ₗ T.toLinearMap ∈ C.adm κ := (hadm l).1 hl
    have h2 := h.adm g _ h1
    have h3 : (l ∘ₗ T.toLinearMap ∘ₗ om g) ∘ₗ T.symm.toLinearMap ∈ C.adm κ := by
      rw [hadm]
      convert h2 using 1
      ext φ
      simp
    convert h3 using 1
    ext φ
    simp [trRep_apply]
  · obtain ⟨c, hc⟩ := hunit μ hμ
    rw [trRep_apply, hc _ (h.pres g _ (hinv φ hφ)), h.unit μ hμ g _ (hinv φ hφ)]
    conv_rhs => rw [← LinearEquiv.apply_symm_apply T φ]
    rw [hc _ (hinv φ hφ)]
  · have := h.cont _ ((hadm l).1 hl) _ (hinv φ hφ)
    simpa [trRep_apply] using this

theorem siegelRule_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T)
    {χ : Eˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy : Matrix β ν E} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : SiegelRule c C ψ ξ JA JB d χ Cy om) : SiegelRule c C ψ ξ JA JB d₁ χ Cy (trRep T om) := by
  obtain ⟨hsp, hheis, hadm, -⟩ := hT
  have hinv : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hsp _).2 (by simpa using hφ)
  intro l hl hinvl p t hpt φ hφ
  have key := h (l ∘ₗ T.toLinearMap) ((hadm l).1 hl) (fun z φ' hφ' => by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [hheis _ _ hφ', hinvl z _ ((hsp _).1 hφ')]) p t hpt (T.symm φ) (hinv φ hφ)
  simpa [trRep_apply] using key

theorem isUWeilB_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    [TopologicalSpace E] [IsModuleTopology R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T) (hD : HasDbl c C ψ ξ JA JB d d₁ T)
    {χ : Eˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilB c C ψ ξ JA JB d χ om) : IsUWeilB c C ψ ξ JA JB d₁ χ (trRep T om) := by
  obtain ⟨hs, dd, omd, hdd, ⟨hL, hsd, hsg⟩, hbox⟩ := h
  obtain ⟨dd₁, Td, S, hdd₁, hTd, hS, hTbox⟩ := hD dd hdd
  have hinvT : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hT.1 _).2 (by simpa using hφ)
  have hinvS : ∀ φ ∈ C.sp κ, S.symm φ ∈ C.sp κ := fun φ hφ => (hS _).2 (by simpa using hφ)
  refine ⟨isUSplitting_trRep hT hs, dd₁, trRep Td omd, hdd₁, ⟨hL, isUSplitting_trRep hTd hsd, siegelRule_trRep hTd hsg⟩, fun g gd hg φ₁ hφ₁ φ₂ hφ₂ => ?_⟩
  have hb : Td.symm (boxFun φ₁ φ₂) = boxFun (T.symm φ₁) (S.symm φ₂) := by
    rw [LinearEquiv.symm_apply_eq, hTbox _ (hinvT φ₁ hφ₁) _ (hinvS φ₂ hφ₂), LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  rw [trRep_apply, hb, hbox g gd hg _ (hinvT φ₁ hφ₁) _ (hinvS φ₂ hφ₂),
    hTbox _ (hs.pres g _ (hinvT φ₁ hφ₁)) _ (hinvS φ₂ hφ₂), LinearEquiv.apply_symm_apply, trRep_apply]

theorem symp_transpose {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [Fintype β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix β α E) :
    symp c ξ JB JA x y = symp c ξ JA JB xᵀ yᵀ := by
  unfold symp hTens
  congr 2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  ring

def transpCoord {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {α β : Type} [Fintype α] [Fintype β] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    (d : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans d.e
  form w w' := by
    rw [symp_transpose, d.form]
    rfl

theorem transpCoord_e {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {α β : Type} [Fintype α] [Fintype β] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    (d : Darboux (symp c ξ JA JB) κ) (x : Matrix α β E) : (transpCoord d).e xᵀ = d.e x := rfl

theorem isUWeilPair_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    [TopologicalSpace E] [IsModuleTopology R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T) (hD : HasDbl c C ψ ξ JA JB d d₁ T)
    (hD' : ∀ d' d₁' : Darboux (symp c ξ JB JA) κ, (∀ x : Matrix α β E, d'.e xᵀ = d.e x) → (∀ x : Matrix α β E, d₁'.e xᵀ = d₁.e x) →
      HasDbl c C ψ ξ JB JA d' d₁' T)
    {χA χB : Eˣ →* Circle} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilPair c C ψ ξ JA JB d χA χB om) : IsUWeilPair c C ψ ξ JA JB d₁ χA χB (trRep T om) := by
  have hsplit := isUSplitting_trRep hT h.isUSplitting
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  have hT' : IsGoodInt C ψ d' (transpCoord d₁) T := by
    obtain ⟨h1, h2, h3, h4⟩ := hT
    refine ⟨h1, fun w φ hφ => ?_, h3, h4⟩
    have e1 : d'.e w = d.e wᵀ := by rw [← hd', Matrix.transpose_transpose]
    have e2 : (transpCoord d₁).e w = d₁.e wᵀ := by rw [← transpCoord_e d₁ wᵀ, Matrix.transpose_transpose]
    have := h2 wᵀ φ hφ
    simp only [Darboux.rho] at this ⊢
    rw [e1, e2, this]
  exact ⟨isUWeilB_trRep hT hD hB, ⟨transpCoord d₁, transpCoord_e d₁, isUWeilB_trRep hT' (hD' d' _ hd' (transpCoord_e d₁)) hA⟩, hsplit.cont⟩

end GlobalTheory.WeilTr

end
end

section

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

def frobKerIdeal (p : ℕ) (R H : Type) [CommRing R] [CommRing H] [Bialgebra R H] : Ideal H :=
  Ideal.span ((fun a : H => a ^ p) '' (augIdeal R H : Set H))

theorem pow_mem_frobKerIdeal {p : ℕ} {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H] {a : H}
    (ha : a ∈ augIdeal R H) : a ^ p ∈ frobKerIdeal p R H :=
  Ideal.subset_span ⟨a, ha, rfl⟩

theorem frobKerIdeal_le_augIdeal {p : ℕ} (hp : p ≠ 0) (R H : Type) [CommRing R] [CommRing H]
    [Bialgebra R H] : frobKerIdeal p R H ≤ augIdeal R H :=
  Ideal.span_le.2 fun _ ⟨a, ha, e⟩ => e ▸ Ideal.pow_mem_of_mem _ ha p (Nat.pos_of_ne_zero hp)

end GlobalTheory.PDiv
end
end
