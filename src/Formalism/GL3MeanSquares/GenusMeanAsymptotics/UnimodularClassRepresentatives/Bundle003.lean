module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.LinearAlgebra.Matrix.Adjugate
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

section

open Module MeasureTheory Filter Topology Bornology Pointwise ZLattice

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LatSum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι]

theorem map_equivFun (μ : Measure E) [μ.IsAddHaarMeasure] (b : Basis ι ℤ L) :
    μ.map (b.ofZLatticeBasis ℝ L).equivFunL = ENNReal.ofReal (covolume L μ) • volume := by
  classical
  set e := (b.ofZLatticeBasis ℝ L).equivFunL with he
  have h := Measure.addHaarMeasure_unique (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι)
  rw [addHaarMeasure_eq_volume_pi] at h
  have hF := ZLattice.isAddFundamentalDomain b μ
  have hc : (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι) = ENNReal.ofReal (covolume L μ) := by
    have h1 : (μ.map e) (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) =
        (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι) := by
      conv_lhs => rw [h]
      rw [Measure.smul_apply, Real.volume_pi_Ico]
      simp
    rw [← h1, Measure.map_apply e.continuous.measurable
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico),
      covolume_eq_measure_fundamentalDomain L μ hF, measureReal_def,
      ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne]
    congr 1
    ext x
    simp [ZSpan.mem_fundamentalDomain, Set.mem_pi, he]
  rw [h, hc]

theorem tendsto_tsum_div_pow (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : μ (frontier s) = 0) {G : E → ℝ} (hG : Continuous G) :
    Tendsto (fun n : ℕ ↦ (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • (L : Set E)), G x) / (n : ℝ) ^ finrank ℝ E)
      atTop (𝓝 ((∫ x in s, G x ∂μ) / covolume L μ)) := by
  classical

  let b := Module.Free.chooseBasis ℤ L
  let e := (b.ofZLatticeBasis ℝ L).equivFunL
  let eM := e.toHomeomorph.toMeasurableEquiv
  have heM : ∀ x, eM x = e x := fun _ => rfl
  have hcov : 0 < covolume L μ := ZLattice.covolume_pos L μ
  have hne : ENNReal.ofReal (covolume L μ) ≠ 0 := by simpa using hcov
  have hmap : μ.map eM = ENNReal.ofReal (covolume L μ) • volume := map_equivFun L μ b
  have hL : e '' (L : Set E) =
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
        Set (Module.Free.ChooseBasisIndex ℤ L → ℝ)) := by
    have hspan := b.ofZLatticeBasis_span ℝ L
    have hstep : e '' (L : Set E) = e '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E) := by
      rw [hspan]
    rw [hstep]
    have hm := Submodule.map_coe (e.toLinearEquiv.toLinearMap.restrictScalars ℤ)
      (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)))
    rw [Submodule.map_span] at hm
    rw [show e '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E) =
      ((e.toLinearEquiv.toLinearMap.restrictScalars ℤ) '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E))
      from rfl, ← hm, ← Set.range_comp]
    have hfun : ⇑(e.toLinearEquiv.toLinearMap.restrictScalars ℤ) ∘ ⇑(b.ofZLatticeBasis ℝ L) =
        ⇑(Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L)) := by
      funext i
      ext j
      by_cases h : j = i
      · subst h
        simp [e]
      · simp [e, h, Ne.symm h]
    rw [hfun]
  have himg : ∀ n : ℕ, e '' (s ∩ (n : ℝ)⁻¹ • (L : Set E)) =
      e '' s ∩ (n : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
        Set (Module.Free.ChooseBasisIndex ℤ L → ℝ)) := by
    intro n
    rw [Set.image_inter e.injective, ← hL]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨e a, ⟨a, ha, rfl⟩, (e.map_smul _ a).symm⟩
    · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_ • a, ⟨a, ha, rfl⟩, e.map_smul _ a⟩
  have hsum : ∀ n : ℕ, (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • (L : Set E)), G x) =
      ∑' y : ↑(e '' s ∩ (n : ℝ)⁻¹ • (Submodule.span ℤ
        (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
          Set (Module.Free.ChooseBasisIndex ℤ L → ℝ))), G (e.symm y) := by
    intro n
    rw [← himg n, tsum_image (fun y => G (e.symm y)) e.injective.injOn]
    simp
  have hdim : finrank ℝ E = Fintype.card (Module.Free.ChooseBasisIndex ℤ L) := by
    rw [← ZLattice.rank ℝ L]
    exact Module.finrank_eq_card_chooseBasisIndex ℤ L
  have hpre : eM ⁻¹' (e '' s) = s := Set.preimage_image_eq s e.injective
  have hint : (∫ y in e '' s, G (e.symm y)) = (∫ x in s, G x ∂μ) / covolume L μ := by
    have h1 := setIntegral_map_equiv (μ := μ) eM (fun y => G (e.symm y)) (e '' s)
    rw [hpre, hmap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hcov.le] at h1
    simp only [heM, ContinuousLinearEquiv.symm_apply_apply] at h1
    rw [← h1, smul_eq_mul, mul_div_cancel_left₀ _ hcov.ne']
  have hfr : volume (frontier (e '' s)) = 0 := by
    have h2 := MeasurableEquiv.map_apply (μ := μ) eM (frontier (e '' s))
    have h3 : eM ⁻¹' frontier (e '' s) = frontier s := by
      have hfe : frontier (e '' s) = e '' frontier s := (e.toHomeomorph.image_frontier s).symm
      rw [hfe]
      exact Set.preimage_image_eq _ e.injective
    rw [h3, hs₃, hmap, Measure.smul_apply, smul_eq_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left hne
  have hlim := tendsto_tsum_div_pow_atTop_integral (e '' s) (fun y => G (e.symm y))
    (hG.comp e.symm.continuous) (e.lipschitzWith.isBounded_image hs₁)
    (eM.measurableSet_image.2 hs₂) hfr
  rw [hint] at hlim
  refine hlim.congr fun n => ?_
  rw [hsum n, hdim]

end Formalism.HermitianLattices.Ext.L3.LatSum
end
end

section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

open Subgroup

variable {G : Type*} [Group G]

private theorem ncard_orbit_in_stabilizer_eq_relIndex {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  have h1 : MulAction.stabilizer (MulAction.stabilizer G y) t =
      (MulAction.stabilizer G t).subgroupOf (MulAction.stabilizer G y) := by
    ext g
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have h2 : MulAction.orbit (MulAction.stabilizer G y) t = {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [Subgroup.relIndex, ← h1, MulAction.index_stabilizer, h2]

theorem relIndex_eq_of_cover (S C H' : Subgroup G) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) : C.relIndex S = C.relIndex H' := by
  have hS := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ S)
  have hH := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ H')
  rw [MulAction.stabilizer_quotient, MulAction.stabilizer_quotient] at hS hH
  rw [← hS, ← hH]
  have hmem : ∀ (K : Subgroup G) (g : G), g • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ g ∈ K :=
    fun K g => by rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, hmem]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, ht, htg⟩ := h2 g hg
    refine ⟨t⁻¹, H'.inv_mem ht, ?_⟩
    rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa using htg
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, h1 hg, rfl⟩

theorem index_tube (H S C H' : Subgroup G) (hS : S ≤ H) (hC : C ≤ H) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) :
    S.relIndex H * C.relIndex H' = C.relIndex H * S.relIndex C := by
  rw [← relIndex_eq_of_cover S C H' h1 h2, ← inf_relIndex_right C S, ← inf_relIndex_right S C, mul_comm,
    relIndex_mul_relIndex _ _ _ inf_le_right hS, mul_comm, relIndex_mul_relIndex _ _ _ inf_le_right hC, inf_comm]

theorem relIndex_cocycle (A B C : Subgroup G) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hCB : B.relIndex C ≠ 0) :
    B.relIndex A * C.relIndex B * A.relIndex C = A.relIndex B * B.relIndex C * C.relIndex A := by
  have hBA' : B.relIndex A ≠ 0 := relIndex_ne_zero_trans hCB hAC
  have hAC' : A.relIndex C ≠ 0 := relIndex_ne_zero_trans hBA hCB
  have orbitMap_conj_smul_one := relIndex_inf_mul_relIndex C B A
  have orbitMap_conj_smul_two := relIndex_inf_mul_relIndex B C A
  have eB1 := relIndex_inf_mul_relIndex A C B
  have eB2 := relIndex_inf_mul_relIndex C A B
  have eC1 := relIndex_inf_mul_relIndex B A C
  have eC2 := relIndex_inf_mul_relIndex A B C
  have EA : C.relIndex (A ⊓ B) * B.relIndex A = B.relIndex (A ⊓ C) * C.relIndex A := by
    rw [inf_comm A B, inf_comm A C, orbitMap_conj_smul_one, orbitMap_conj_smul_two, inf_comm]
  have EB : A.relIndex (B ⊓ C) * C.relIndex B = C.relIndex (A ⊓ B) * A.relIndex B := by
    rw [inf_comm B C, eB1, eB2, inf_comm]
  have EC : B.relIndex (A ⊓ C) * A.relIndex C = A.relIndex (B ⊓ C) * B.relIndex C := by
    rw [eC1, eC2, inf_comm]
  have hu : C.relIndex (A ⊓ B) ≠ 0 := by
    rw [inf_comm]
    exact left_ne_zero_of_mul (by rw [orbitMap_conj_smul_one]; exact relIndex_inf_ne_zero hAC hBA')
  have hv : B.relIndex (A ⊓ C) ≠ 0 :=
    left_ne_zero_of_mul (by rw [eC1]; exact relIndex_inf_ne_zero hCB hAC')
  have hw : A.relIndex (B ⊓ C) ≠ 0 :=
    left_ne_zero_of_mul (by rw [eC2]; exact relIndex_inf_ne_zero hAC' hCB)
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hu hv) hw))
  calc C.relIndex (A ⊓ B) * B.relIndex (A ⊓ C) * A.relIndex (B ⊓ C) *
        (B.relIndex A * C.relIndex B * A.relIndex C)
      = (C.relIndex (A ⊓ B) * B.relIndex A) * (A.relIndex (B ⊓ C) * C.relIndex B) *
          (B.relIndex (A ⊓ C) * A.relIndex C) := by ring
    _ = (B.relIndex (A ⊓ C) * C.relIndex A) * (C.relIndex (A ⊓ B) * A.relIndex B) *
          (A.relIndex (B ⊓ C) * B.relIndex C) := by rw [EA, EB, EC]
    _ = _ := by ring

theorem ncard_biUnion_finset {ι X : Type*} (s : Finset ι) (f : ι → Set X)
    (hf : ∀ i ∈ s, (f i).Finite) (hd : (s : Set ι).PairwiseDisjoint f) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  revert hf hd
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih hf hd
  have hfa : (f a).Finite := hf a (Finset.mem_insert_self a s)
  have hfs : (⋃ i ∈ s, f i).Finite :=
    Set.Finite.biUnion s.finite_toSet fun i hi => hf i (Finset.mem_insert_of_mem hi)
  have hdisj : Disjoint (f a) (⋃ i ∈ s, f i) := by
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
  rw [Finset.set_biUnion_insert, Finset.sum_insert ha, Set.ncard_union_eq hdisj hfa hfs,
    ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (hd.subset (Finset.coe_subset.2 (Finset.subset_insert a s)))]

theorem ncard_orb {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  exact ncard_orbit_in_stabilizer_eq_relIndex t y

theorem sum_relIndex_fibre {X Y : Type*} [MulAction G X] [MulAction G Y] (π : X → Y)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ x ∈ sX, x ∈ A ∧ π x ∈ sY)
    (hX : ∀ x ∈ A, ∃! t, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ sY, ∀ y' ∈ sY, (∃ g : G, g • y = y') → y = y')
    (hfin : ∀ x ∈ sX, (MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) ≠ 0)
    (w : Y → ℝ) :
    ∑ x ∈ sX, ((MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) : ℝ) * w (π x) =
      ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y := by
  classical
  have hcard : ∀ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) =
      ∑ t ∈ sX.filter (fun t => π t = y),
        ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ) := by
    intro y hy
    have hfib : {x | x ∈ A ∧ π x = y} =
        ⋃ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · rintro ⟨hxA, hxy⟩
        obtain ⟨t, ⟨ht, g, hgt⟩, -⟩ := hX x hxA
        have h1 : π t = y := hY (π t) (hsX t ht).2 y hy ⟨g, by rw [← hπ, hgt, hxy]⟩
        refine ⟨t, ⟨ht, h1⟩, g, ?_, hgt⟩
        rw [← h1, ← hπ, hgt, hxy, h1]
      · rintro ⟨t, ⟨ht, h1⟩, g, hg, rfl⟩
        refine ⟨hA g t (hsX t ht).1, ?_⟩
        rw [hπ, h1, hg]
    have hfin' : ∀ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x}.Finite := by
      intro t ht
      rw [Finset.mem_filter] at ht
      apply Set.finite_of_ncard_ne_zero
      rw [ncard_orb, ← ht.2]
      exact hfin t ht.1
    have hdisj : (↑(sX.filter (fun t => π t = y)) : Set X).PairwiseDisjoint
        (fun t => {x : X | ∃ g : G, g • y = y ∧ g • t = x}) := by
      intro t ht t' ht' hne
      refine Set.disjoint_left.2 ?_
      rintro x ⟨g, -, rfl⟩ ⟨g', -, hg'⟩
      rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
      obtain ⟨t0, -, huniq⟩ := hX (g • t) (hA g t (hsX t ht.1).1)
      exact hne ((huniq t ⟨ht.1, g, rfl⟩).trans (huniq t' ⟨ht'.1, g', hg'⟩).symm)
    have hnc : Nat.card {x // x ∈ A ∧ π x = y} = ({x | x ∈ A ∧ π x = y} : Set X).ncard :=
      by exact (Set.ncard_ofPred _).symm
    rw [hnc, hfib, ncard_biUnion_finset _ _ hfin' hdisj]
    push_cast
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_filter] at ht
    rw [ncard_orb, ht.2]
  symm
  calc ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y
      = ∑ y ∈ sY, ∑ t ∈ sX.filter (fun t => π t = y),
          ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ) * w (π t) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hcard y hy, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [(Finset.mem_filter.1 ht).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun t ht => (hsX t ht).2) _

end Formalism.HermitianLattices.Ext.L3.LIOrb
end

section

open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K]

structure IsLocUnif (S : Subring K) (ϖ : K) : Prop where
  star_mem : ∀ a ∈ S, star a ∈ S
  mem : ϖ ∈ S
  fix : star ϖ = ϖ
  ne : ϖ ≠ 0
  tr : ∃ τ ∈ S, τ + star τ = 1
  skew : ∃ θ ∈ S, star θ = -θ ∧ θ ≠ 0
  dv : ∀ f ∈ S, star f = f → f⁻¹ ∈ S ∨ f * ϖ⁻¹ ∈ S
  rad : ∀ s ∈ S, 1 + ϖ * s ≠ 0 ∧ (1 + ϖ * s)⁻¹ ∈ S
  arch : ∀ a : K, ∃ l : ℕ, ϖ ^ l * a ∈ S

def Ent (S : Subring K) {m n : Type*} (M : Matrix m n K) : Prop := ∀ i j, M i j ∈ S

variable {S : Subring K} {m n o : Type*}

theorem Ent.add {M N : Matrix m n K} (hM : Ent S M) (hN : Ent S N) : Ent S (M + N) := by
  exact fun i j => S.add_mem (hM i j) (hN i j)

theorem Ent.sub {M N : Matrix m n K} (hM : Ent S M) (hN : Ent S N) : Ent S (M - N) := by
  exact fun i j => S.sub_mem (hM i j) (hN i j)

theorem Ent.neg {M : Matrix m n K} (hM : Ent S M) : Ent S (-M) := by
  exact fun i j => S.neg_mem (hM i j)

theorem Ent.zero : Ent S (0 : Matrix m n K) := by
  exact fun _ _ => S.zero_mem

theorem Ent.smul {a : K} (ha : a ∈ S) {M : Matrix m n K} (hM : Ent S M) : Ent S (a • M) := by
  exact fun i j => S.mul_mem ha (hM i j)

theorem Ent.mul [Fintype n] {M : Matrix m n K} {N : Matrix n o K} (hM : Ent S M) (hN : Ent S N) :
    Ent S (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => S.mul_mem (hM i k) (hN k j)

theorem Ent.one [DecidableEq n] : Ent S (1 : Matrix n n K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem Ent.conjTranspose (hS : ∀ a ∈ S, star a ∈ S) {M : Matrix m n K} (hM : Ent S M) : Ent S Mᴴ := by
  exact fun i j => hS _ (hM j i)

theorem Ent.exists_map {M : Matrix m n K} (hM : Ent S M) :
    ∃ M₀ : Matrix m n S, M₀.map S.subtype = M := by
  refine ⟨fun i j => ⟨M i j, hM i j⟩, ?_⟩
  ext i j
  rfl

theorem Ent.det [Fintype n] [DecidableEq n] {M : Matrix n n K} (hM : Ent S M) : M.det ∈ S := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  have h := RingHom.map_det S.subtype M₀
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact (M₀.det).2

theorem Ent.adjugate [Fintype n] [DecidableEq n] {M : Matrix n n K} (hM : Ent S M) :
    Ent S M.adjugate := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  have h := RingHom.map_adjugate S.subtype M₀
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [← h]
  intro i j
  exact (M₀.adjugate i j).2

theorem pow_mem {ϖ : K} (hS : IsLocUnif S ϖ) (k : ℕ) : ϖ ^ k ∈ S := by
  exact S.pow_mem hS.mem k

end Formalism.HermitianLattices.Ext.L3.HU
end
