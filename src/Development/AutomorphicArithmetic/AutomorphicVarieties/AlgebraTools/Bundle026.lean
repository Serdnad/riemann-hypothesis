module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle022
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem double_coset_operator_sum {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M)
    (K K' : Subgroup G) (x : G) (h : (MulAction.orbit K (x : G ⧸ K')).Finite) (v : fixd ρ K') :
    (hk2 ρ K K' x v : M) = ∑ q ∈ Set.Finite.toFinset h, ρ q.out v := by
  rw [(hkApply A G M ρ K K' x h).1 v, dc,
    finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ K' => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ h,
    LinearMap.sum_apply]

private theorem mem_orb {G : Type} [Group G] (K K' : Subgroup G) (x g : G) :
    (g : G ⧸ K') ∈ MulAction.orbit K (x : G ⧸ K') ↔ ∃ a ∈ K, ∃ b ∈ K', g = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (((a : G) * x : G) : G ⧸ K') = g := ha
    exact ⟨a, a.2, _, QuotientGroup.eq.1 ha', by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    change ((a * x : G) : G ⧸ K') = _
    exact (QuotientGroup.mk_mul_of_mem _ hb).symm

theorem UpperTheory.V.AlgebraTools.hkTrace :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I K : Subgroup G) (h : I ≤ K) (ι : Type) [Fintype ι] (w : ι → G), HeckePair I → (∀ i, w i ∈ K) → (∀ g ∈ K, ∃! i, ∃ a ∈ I, ∃ b ∈ I, g = a * w i * b) → FinOrb K I 1 ∧ ∑ i, hk ρ I (w i) = inc ρ h ∘ₗ trc ρ K I ∧ ∀ v : fixd ρ K, trc ρ K I (inc ρ h v) = (I.relIndex K : A) • v := by
  intro A G M _ _ _ _ ρ I K h ι _ w hI hw hu
  classical
  replace hI : ∀ x : G, (MulAction.orbit I (x : G ⧸ I)).Finite := hI
  have hK : ∀ g : G, (g : G ⧸ I) ∈ MulAction.orbit K ((1 : G) : G ⧸ I) ↔ g ∈ K := fun g => by
    rw [mem_orb]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => e ▸ mul_mem (mul_mem ha (one_mem _)) (h hb),
      fun hg => ⟨g, hg, 1, one_mem _, by simp⟩⟩
  have hU : MulAction.orbit K ((1 : G) : G ⧸ I) = ⋃ i, MulAction.orbit I (w i : G ⧸ I) := by
    ext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [Set.mem_iUnion, hK, mem_orb]
    exact ⟨fun hg => (hu g hg).exists,
      fun ⟨i, a, ha, b, hb, e⟩ => e ▸ mul_mem (mul_mem (h ha) (hw i)) (h hb)⟩
  have hF : (MulAction.orbit K ((1 : G) : G ⧸ I)).Finite := by
    rw [hU]
    exact Set.finite_iUnion fun i => hI (w i)
  refine ⟨hF, ?_, fun v => ?_⟩
  · ext v
    change _ = (hk2 ρ K I 1 v : M)
    rw [LinearMap.sum_apply, Submodule.coe_sum, double_coset_operator_sum ρ K I 1 hF]
    have e : Set.Finite.toFinset hF = Finset.univ.biUnion fun i => Set.Finite.toFinset (hI (w i)) := by
      ext q
      simp [hU]
    rw [e, Finset.sum_biUnion]
    · exact Finset.sum_congr rfl fun i _ => double_coset_operator_sum ρ I I (w i) (hI _) v
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro q hi hj
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [Set.Finite.mem_toFinset] at hi hj
      have hg : g ∈ K := (hK g).1 (hU ▸ Set.mem_iUnion.2 ⟨i, hi⟩)
      exact hij ((hu g hg).unique ((mem_orb _ _ _ _).1 hi) ((mem_orb _ _ _ _).1 hj))
  · ext
    change (hk2 ρ K I 1 (inc ρ h v) : M) = _
    rw [double_coset_operator_sum ρ K I 1 hF, Finset.sum_congr rfl (g := fun _ => (v : M))]
    · have hs : MulAction.stabilizer K ((1 : G) : G ⧸ I) = I.subgroupOf K := by
        ext k
        rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
        change (((k : G) * 1 : G) : G ⧸ I) = _ ↔ _
        rw [eq_comm, QuotientGroup.eq]
        simp
      rw [Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hF, ← MulAction.index_stabilizer, hs,
        Submodule.coe_smul, Nat.cast_smul_eq_nsmul]
      rfl
    · intro q hq
      rw [Set.Finite.mem_toFinset, ← q.out_eq'] at hq
      exact v.2 _ ((hK _).1 hq)
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hkMul_out {G : Type} [Group G] (I : Subgroup G) (g : G) :
    ∃ i ∈ I, (g : G ⧸ I).out = g * i := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I g
  exact ⟨h, h.2, hh⟩

private theorem hkMul_mem {G : Type} [Group G] (I : Subgroup G) (x : G) (p : G ⧸ I) :
    p ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, p = ((a * x : G) : G ⧸ I) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem UpperTheory.V.AlgebraTools.hkMul :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (x y : G), HeckePair I → (∀ b ∈ I, ∃ a ∈ I, ∃ c ∈ I, x * b * y = a * (x * y) * c) → (MulAction.orbit I ((x * y : G) : G ⧸ I)).ncard = (MulAction.orbit I (x : G ⧸ I)).ncard * (MulAction.orbit I (y : G ⧸ I)).ncard → hk ρ I x * hk ρ I y = hk ρ I (x * y) := by
  intro A G M _ _ _ _ ρ I x y hI hb hc
  classical
  haveI fx : Fintype (MulAction.orbit I (x : G ⧸ I)) := (hI x).fintype
  haveI fy : Fintype (MulAction.orbit I (y : G ⧸ I)) := (hI y).fintype
  haveI fxy : Fintype (MulAction.orbit I ((x * y : G) : G ⧸ I)) := (hI (x * y)).fintype
  have hmem : ∀ (p : MulAction.orbit I (x : G ⧸ I)) (q : MulAction.orbit I (y : G ⧸ I)),
      (((p : G ⧸ I).out * (q : G ⧸ I).out : G) : G ⧸ I) ∈ MulAction.orbit I ((x * y : G) : G ⧸ I) := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨a, ha, rfl⟩ := (hkMul_mem I x p).1 hp
    obtain ⟨b, hb', rfl⟩ := (hkMul_mem I y q).1 hq
    obtain ⟨i, hi, e1⟩ := hkMul_out I (a * x)
    obtain ⟨j, hj, e2⟩ := hkMul_out I (b * y)
    obtain ⟨a', ha', c, hc', e3⟩ := hb (i * b) (mul_mem hi hb')
    refine (hkMul_mem I _ _).2 ⟨a * a', mul_mem ha ha', ?_⟩
    simp only [e1, e2]
    have : a * x * i * (b * y * j) = a * a' * (x * y) * (c * j) := by
      calc a * x * i * (b * y * j) = a * (x * (i * b) * y) * j := by group
        _ = _ := by rw [e3]; group
    rw [this]
    exact QuotientGroup.mk_mul_of_mem _ (mul_mem hc' hj)
  let f : MulAction.orbit I (x : G ⧸ I) × MulAction.orbit I (y : G ⧸ I) →
      MulAction.orbit I ((x * y : G) : G ⧸ I) := fun pq => ⟨_, hmem pq.1 pq.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨a, ha, rfl⟩ := (hkMul_mem I _ r).1 hr
    obtain ⟨i, hi, e1⟩ := hkMul_out I (a * x)
    obtain ⟨j, hj, e2⟩ := hkMul_out I (i⁻¹ * y)
    refine ⟨(⟨_, (hkMul_mem I _ _).2 ⟨a, ha, rfl⟩⟩, ⟨_, (hkMul_mem I _ _).2 ⟨i⁻¹, inv_mem hi, rfl⟩⟩), Subtype.ext ?_⟩
    simp only [f, e1, e2]
    have : a * x * i * (i⁻¹ * y * j) = a * (x * y) * j := by group
    rw [this]
    exact QuotientGroup.mk_mul_of_mem _ hj
  have hbij : Function.Bijective f := by
    refine (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, ?_⟩
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, hc]
  refine LinearMap.ext fun v => Subtype.ext ?_
  have h1 := (hkApply A G M ρ I I x (hI x)).1
  have h2 := (hkApply A G M ρ I I y (hI y)).1
  have h3 := (hkApply A G M ρ I I (x * y) (hI _)).1
  rw [Module.End.mul_apply]
  unfold hk
  rw [h1, h2, h3]

  simp only [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum]
  rw [← hbij.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨i, hi, e⟩ := hkMul_out I ((p : G ⧸ I).out * (q : G ⧸ I).out)
  simp only [f, e, map_mul, Module.End.mul_apply]
  rw [v.2 i hi]
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem leviLevel_reps {G : Type} [Group G] {K K' : Subgroup G} (S : Subgroup G) {m : G} (hS : S ≤ K)
    (hfin : FinOrb K K' m) :
    ∃ r : Finset G, (∀ u ∈ r, u ∈ S) ∧ ∀ x ∈ S, ∃! u, u ∈ r ∧ (u * m)⁻¹ * (x * m) ∈ K' := by
  classical
  let φ : G → G ⧸ K' := fun x => ((x * m : G) : G ⧸ K')
  have h1 : (φ '' (S : Set G)).Finite := by
    refine Set.Finite.subset hfin ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hS hx⟩, rfl⟩
  obtain ⟨t, ht, hb⟩ := Set.exists_subset_bijOn (S : Set G) φ
  have h2 : t.Finite := (hb.finite_iff_finite).2 h1
  refine ⟨h2.toFinset, fun u hu => ht (h2.mem_toFinset.1 hu), fun x hx => ?_⟩
  obtain ⟨u, hu, e⟩ := hb.surjOn ⟨x, hx, rfl⟩
  refine ⟨u, ⟨h2.mem_toFinset.2 hu, QuotientGroup.eq.1 e⟩, ?_⟩
  rintro u' ⟨hu', e'⟩
  exact hb.injOn (h2.mem_toFinset.1 hu') hu ((QuotientGroup.eq.2 e').trans e.symm)

private theorem leviLevel_sum {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) {K K' : Subgroup G} (S : Subgroup G) {m : G} (hS : S ≤ K) (hfin : FinOrb K K' m)
    (hg : ∀ g ∈ K, ∃ x ∈ S, (x * m)⁻¹ * (g * m) ∈ K') (r : Finset G) (f : G → G) (hf : ∀ u ∈ r, f u ∈ S)
    (hr : ∀ x ∈ S, ∃! u, u ∈ r ∧ (f u * m)⁻¹ * (x * m) ∈ K') (v : fixd ρ K') :
    (hk2 ρ K K' m v : M) = ∑ u ∈ r, ρ (f u * m) v := by
  classical
  have hinj : ∀ u ∈ r, ∀ u' ∈ r, ((f u * m : G) : G ⧸ K') = ((f u' * m : G) : G ⧸ K') → u = u' :=
    fun u hu u' hu' e => (hr _ (hf u' hu')).unique ⟨hu, QuotientGroup.eq.1 e⟩ ⟨hu', by simp⟩
  rw [(UpperTheory.V.AlgebraTools.hkApply A G M ρ K K' m hfin).2.1 (r.image fun u => f u * m) ?_ ?_ v, Finset.sum_image]
  · intro u hu u' hu' e
    exact hinj u hu u' hu' (congrArg _ e)
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨⟨f u, hS (hf u hu)⟩, rfl⟩
  · rintro _ ⟨⟨g, hgK⟩, rfl⟩
    obtain ⟨x, hx, e⟩ := hg g hgK
    obtain ⟨u, ⟨hu, e'⟩, -⟩ := hr x hx
    have e2 : ((f u * m : G) : G ⧸ K') = ((g * m : G) : G ⧸ K') :=
      (QuotientGroup.eq.2 e').trans (QuotientGroup.eq.2 e)
    refine ⟨f u * m, ⟨Finset.mem_image.2 ⟨u, hu, rfl⟩, e2⟩, ?_⟩
    rintro y ⟨hy, e3⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
    rw [hinj u' hu' u hu (e3.trans e2.symm)]

private theorem leviLevel_cover {G : Type} [Group G] {K : Subgroup G} (F : LeviFact K) {m : G}
    (hL : ∀ l ∈ F.Lf ⊓ K, m⁻¹ * l * m ∈ K) (hJ : ∀ j ∈ F.Mf ⊓ K, m * j = j * m) :
    ∀ g ∈ K, ∃ x ∈ F.Uf ⊓ K, (x * m)⁻¹ * (g * m) ∈ K := by
  intro g hg
  obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact g hg
  refine ⟨u, hu, ?_⟩
  have e : (u * m)⁻¹ * (u * j * l * m) = m⁻¹ * (j * m) * (m⁻¹ * l * m) := by group
  rw [e, ← hJ j hj, inv_mul_cancel_left]
  exact mul_mem hj.2 (hL l hl)

theorem UpperTheory.V.AlgebraTools.leviLevel :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I I' : Subgroup G) (h : I' ≤ I) (F : LeviFact I) (F' : LeviFact I') (m : G), HeckePair I → HeckePair I' → FinOrb I I' 1 → F'.Uf = F.Uf → F'.Mf = F.Mf → F'.Lf = F.Lf → F.Uf ⊓ I ≤ I' → F.Lf ⊓ I ≤ I' → (∀ a ∈ I, ∀ b ∈ I', a * b * a⁻¹ ∈ I') → F.Pos m → (∀ j ∈ F.Mf ⊓ I, m * j = j * m) → hk ρ I' m ∘ₗ inc ρ h = inc ρ h ∘ₗ hk ρ I m ∧ trc ρ I I' ∘ₗ hk ρ I' m = hk ρ I m ∘ₗ trc ρ I I' := by
  intro A G M _ _ _ _ ρ I I' h F F' m hI hI' h1 eU eM eL hU hL hn hm hJ
  obtain ⟨r, hr, hr2⟩ := leviLevel_reps (F.Uf ⊓ I) inf_le_right (hI m)
  obtain ⟨t, ht, ht2⟩ := leviLevel_reps (F.Mf ⊓ I) inf_le_right h1
  have cI := leviLevel_cover F hm.2.2 hJ
  have cI' : ∀ g ∈ I', ∃ x ∈ F.Uf ⊓ I, (x * m)⁻¹ * (g * m) ∈ I' := by
    intro g hg
    obtain ⟨x, hx, e⟩ := leviLevel_cover F' (m := m) (fun l hl => by
      have hl1 : l ∈ F.Lf := eL ▸ hl.1
      refine hL ⟨?_, hm.2.2 l ⟨hl1, h hl.2⟩⟩
      simpa using F.M_L _ (inv_mem hm.1) l hl1) (fun j hj => hJ j ⟨eM ▸ hj.1, h hj.2⟩) g hg
    exact ⟨x, ⟨eU ▸ hx.1, h hx.2⟩, e⟩
  have cJ : ∀ g ∈ I, ∃ x ∈ F.Mf ⊓ I, (x * 1)⁻¹ * (g * 1) ∈ I' := by
    intro g hg
    obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact g hg
    refine ⟨j, hj, ?_⟩
    have := mul_mem (hn _ (I.inv_mem hj.2) _ (hU hu)) (hL hl)
    convert this using 1
    group
  have hr3 : ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ r ∧ (u * m)⁻¹ * (x * m) ∈ I' := by
    intro x hx
    obtain ⟨u, ⟨hu, e⟩, huq⟩ := hr2 x hx
    refine ⟨u, ⟨hu, hU ⟨?_, e⟩⟩, fun u' hu' => huq u' ⟨hu'.1, h hu'.2⟩⟩
    have := F.M_U _ (inv_mem hm.1) _ (mul_mem (inv_mem (hr u hu).1) hx.1)
    convert this using 1
    show _ ∈ F.Uf ↔ _
    congr! 1
    group
  have sI := leviLevel_sum ρ (F.Uf ⊓ I) inf_le_right (hI m) cI r id hr hr2
  have sJ := leviLevel_sum ρ (F.Mf ⊓ I) inf_le_right h1 cJ t id ht ht2
  have sI' : ∀ j ∈ F.Mf ⊓ I, ∀ v : fixd ρ I',
      (hk2 ρ I' I' m v : M) = ∑ u ∈ r, ρ (j⁻¹ * u * j * m) v := by
    intro j hj
    have hc : ∀ a ∈ F.Mf ⊓ I, ∀ x ∈ F.Uf ⊓ I, a * x * a⁻¹ ∈ F.Uf ⊓ I := fun a ha x hx =>
      ⟨F.M_U a ha.1 x hx.1, I.mul_mem (I.mul_mem ha.2 hx.2) (I.inv_mem ha.2)⟩
    refine leviLevel_sum ρ (F.Uf ⊓ I) hU (hI' m) cI' r (fun u => j⁻¹ * u * j) (fun u hu => ?_) (fun x hx => ?_)
    · simpa using hc _ (inv_mem hj) u (hr u hu)
    · refine (existsUnique_congr fun u => and_congr_right fun _ => ?_).1 (hr3 _ (hc j hj x hx))
      have e : j * ((j⁻¹ * u * j * m)⁻¹ * (x * m)) * j⁻¹ = (u * m)⁻¹ * (j * x * j⁻¹ * m) := by
        have e1 : j * m⁻¹ * j⁻¹ = m⁻¹ := by
          rw [mul_assoc, ← _root_.mul_inv_rev, ← hJ j hj]; group
        have e2 : m * j⁻¹ = j⁻¹ * m := hJ _ (inv_mem hj)
        calc _ = (j * m⁻¹ * j⁻¹) * u⁻¹ * j * x * (m * j⁻¹) := by group
          _ = _ := by rw [e1, e2]; group
      rw [← e]
      refine ⟨fun hx => ?_, hn _ hj.2 _⟩
      have := hn _ (I.inv_mem hj.2) _ hx
      convert this using 1
      group
  refine ⟨LinearMap.ext fun v => Subtype.ext ?_, LinearMap.ext fun v => Subtype.ext ?_⟩
  · show (hk2 ρ I' I' m (inc ρ h v) : M) = hk2 ρ I I m v
    rw [sI' 1 (one_mem _), sI]
    simp only [inv_one, one_mul, mul_one, id]
    rfl
  · show (hk2 ρ I I' 1 (hk2 ρ I' I' m v) : M) = hk2 ρ I I m (hk2 ρ I I' 1 v)
    rw [sJ, sI, sJ]

    simp only [id, mul_one, map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_

    rw [sI' j (ht j hj), map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc u, hJ j (ht j hj)]
    congr 2
    group
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hkNorm_mem {G : Type} [Group G] (I : Subgroup G) (x y : G) :
    (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, y = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have h : (((a : G) * x : G) : G ⧸ I) = (y : G ⧸ I) := ha
    rw [QuotientGroup.eq] at h
    exact ⟨a, a.2, _, h, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [QuotientGroup.mk_mul_of_mem _ hb]
    rfl

private theorem hkNorm_reps {G : Type} [Group G] (I : Subgroup G) (x : G) (h : FinOrb I I x) :
    ∃ s : Finset G, (∀ y ∈ s, (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I)) ∧
      ∀ q ∈ MulAction.orbit I (x : G ⧸ I), ∃! y, y ∈ s ∧ (y : G ⧸ I) = q := by
  classical
  refine ⟨(Set.Finite.toFinset h).image Quotient.out, fun y hy => ?_, fun q hq => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    rw [QuotientGroup.out_eq']
    exact (Set.Finite.mem_toFinset h).1 hq
  · refine ⟨q.out, ⟨Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset h).2 hq), QuotientGroup.out_eq' q⟩, ?_⟩
    rintro y ⟨hy, rfl⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [QuotientGroup.out_eq']

private theorem hkNorm_tr {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (x u w : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (hw : w ∈ Subgroup.normalizer (I : Set G))
    (s : Finset G) (h1 : ∀ y ∈ s, (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I))
    (h2 : ∀ q ∈ MulAction.orbit I (x : G ⧸ I), ∃! y, y ∈ s ∧ (y : G ⧸ I) = q) (v : fixd ρ I) :
    (hk ρ I (u * x * w) v : M) = ∑ y ∈ s, ρ (u * y * w) v := by
  classical
  have cu : ∀ a ∈ I, u * a * u⁻¹ ∈ I := fun a ha => (Subgroup.mem_normalizer_iff.1 hu a).1 ha
  have cu' : ∀ a ∈ I, u⁻¹ * a * u ∈ I := fun a ha => (Subgroup.mem_normalizer_iff''.1 hu a).1 ha
  have cw : ∀ a ∈ I, w * a * w⁻¹ ∈ I := fun a ha => (Subgroup.mem_normalizer_iff.1 hw a).1 ha
  have cw' : ∀ a ∈ I, w⁻¹ * a * w ∈ I := fun a ha => (Subgroup.mem_normalizer_iff''.1 hw a).1 ha
  have key := (hkApply A G M ρ I I (u * x * w) (hI _)).2.1 (s.image fun y => u * y * w) ?_ ?_ v
  · rw [Finset.sum_image (fun a _ b _ h => by simpa using h)] at key
    exact key
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I x z).1 (h1 z hz)
    exact (hkNorm_mem I _ _).2 ⟨_, cu a ha, _, cw' b hb, by group⟩
  · intro q hq
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I _ z).1 hq
    obtain ⟨y, ⟨hy, hyq⟩, huniq⟩ := h2 ((u⁻¹ * a * u * x : G) : G ⧸ I)
      ((hkNorm_mem I _ _).2 ⟨_, cu' a ha, 1, one_mem _, by group⟩)
    refine ⟨u * y * w, ⟨Finset.mem_image_of_mem _ hy, ?_⟩, ?_⟩
    · rw [QuotientGroup.eq] at hyq ⊢
      convert mul_mem (cw' _ hyq) hb using 1
      group
    · rintro y' ⟨hy', h⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy'
      rw [huniq z ⟨hz, ?_⟩]
      rw [QuotientGroup.eq] at h ⊢
      convert cw _ (mul_mem h (inv_mem hb)) using 1
      group

private theorem hkNorm_one {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (v : fixd ρ I) : (hk ρ I u v : M) = ρ u v := by
  have h := hkNorm_tr ρ I hI 1 u 1 hu (one_mem _) {1} (by simp) (fun q hq => by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I _ z).1 hq
    refine ⟨1, ⟨by simp, ?_⟩, fun y hy => by simpa using hy.1⟩
    rw [QuotientGroup.eq]
    simpa using mul_mem ha hb) v
  simpa using h

private theorem hkNorm_mul {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (x : G) :
    hk ρ I (u * x) = hk ρ I u * hk ρ I x ∧ hk ρ I (x * u) = hk ρ I x * hk ρ I u := by
  obtain ⟨s, h1, h2⟩ := hkNorm_reps I x (hI x)
  have h0 := hkNorm_tr ρ I hI x 1 1 (one_mem _) (one_mem _) s h1 h2
  have hl := hkNorm_tr ρ I hI x u 1 hu (one_mem _) s h1 h2
  have hr := hkNorm_tr ρ I hI x 1 u (one_mem _) hu s h1 h2
  simp only [one_mul, mul_one] at h0 hl hr
  constructor
  · ext v

    rw [hl, Module.End.mul_apply, hkNorm_one ρ I hI u hu, h0, map_sum]
    simp only [map_mul, Module.End.mul_apply]
  · ext v
    rw [hr, Module.End.mul_apply, h0, hkNorm_one ρ I hI u hu]
    simp only [map_mul, Module.End.mul_apply]

theorem UpperTheory.V.AlgebraTools.hkNorm :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (u : G), HeckePair I → u ∈ Subgroup.normalizer (I : Set G) → (∀ v : fixd ρ I, (hk ρ I u v : M) = ρ u v) ∧ hk ρ I 1 = 1 ∧ IsUnit (hk ρ I u) ∧ ∀ x : G, hk ρ I (u * x) = hk ρ I u * hk ρ I x ∧ hk ρ I (x * u) = hk ρ I x * hk ρ I u := by
  intro A G M _ _ _ _ ρ I u hI hu
  have h1 : hk ρ I 1 = 1 := by
    ext v
    rw [hkNorm_one ρ I hI 1 (one_mem _)]
    simp
  refine ⟨hkNorm_one ρ I hI u hu, h1, ⟨⟨hk ρ I u, hk ρ I u⁻¹, ?_, ?_⟩, rfl⟩, hkNorm_mul ρ I hI u hu⟩
  · rw [← (hkNorm_mul ρ I hI u hu u⁻¹).1, mul_inv_cancel, h1]
  · rw [← (hkNorm_mul ρ I hI u hu u⁻¹).2, inv_mul_cancel, h1]
end
