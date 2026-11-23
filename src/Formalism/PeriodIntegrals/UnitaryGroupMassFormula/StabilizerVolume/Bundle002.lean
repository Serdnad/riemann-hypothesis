module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem
public import Mathlib.Topology.MetricSpace.Polish
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle001
public import Mathlib.Algebra.Module.LinearMap.Rat
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Metrizable.Urysohn
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.KummerPolynomial

@[expose] public section

section

noncomputable section

namespace PI.VolStabS.TopoPolish

open Topology TopologicalSpace Set

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  apply PI.AprimeInfA.polish_of_lcsc <;> assumption

end PI.VolStabS.TopoPolish
end
end

section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter

section CosMeas

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem isOpen_thick (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have e : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x
    simp [thick]
  rw [e]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)

theorem measure_thick_eq (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  classical

  have hfib : ∀ c : X ⧸ Λ, m1 (((↑) : X → X ⧸ Λ) ⁻¹' {c}) = m2 (((↑) : X → X ⧸ Λ) ⁻¹' {c}) ∧
      MeasurableSet (((↑) : X → X ⧸ Λ) ⁻¹' {c}) := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    have e : ((↑) : X → X ⧸ Λ) ⁻¹' {(y : X ⧸ Λ)} = {z | z - y ∈ Λ} := by
      ext z
      simp [QuotientAddGroup.eq_iff_sub_mem]
    rw [e]
    exact ⟨h y, (hΛ.preimage (continuous_id.sub continuous_const)).measurableSet⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : S => {z : X | z - (s : X) ∈ Λ})
    (fun s => hΛ.preimage (continuous_id.sub continuous_const))
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, by simp⟩)
  have hT : thick S Λ = ⋃ c ∈ t.image (fun s : S => ((s : X) : X ⧸ Λ)),
      ((↑) : X → X ⧸ Λ) ⁻¹' {c} := by
    ext x
    simp only [thick, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_singleton_iff,
      Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨s', hs't, hss'⟩ := mem_iUnion₂.mp (ht hs)
      refine ⟨((s' : X) : X ⧸ Λ), ⟨s', hs't, rfl⟩, ?_⟩
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have e : x - (s' : X) = (x - s) + (s - s') := by abel
      rw [e]
      exact Λ.add_mem hxs hss'
    · rintro ⟨c, ⟨s', _, rfl⟩, hx⟩
      exact ⟨s', s'.2, (QuotientAddGroup.eq_iff_sub_mem).mp hx⟩
  rw [hT, measure_biUnion_finset, measure_biUnion_finset]
  · exact Finset.sum_congr rfl fun c _ => (hfib c).1
  all_goals first
    | exact fun c _ c' _ hne => (Set.disjoint_singleton.mpr hne).preimage _
    | exact fun c _ => (hfib c).2


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem iInter_thick (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx
    by_contra hxS
    have hN : (fun u => x - u) ⁻¹' Sᶜ ∈ 𝓝 (0 : X) := by
      apply (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
      simpa using hSc.isOpen_compl.mem_nhds hxS
    obtain ⟨n, hn⟩ := hb _ hN
    obtain ⟨s, hs, hxs⟩ := hx n
    have hmem := hn hxs
    simp only [mem_preimage, mem_compl_iff, sub_sub_cancel] at hmem
    exact hmem hs
  · intro hx n
    exact ⟨x, hx, by simp⟩

theorem measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hmono : Antitone fun n => thick S (Λ n) := by
    intro a c hac x hx
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hs, hanti hac hxs⟩
  have hnull : ∀ (μ : Measure X) n, NullMeasurableSet (thick S (Λ n)) μ := fun μ n =>
    (isOpen_thick S (Λ n) (hΛo n)).measurableSet.nullMeasurableSet
  have heq : ∀ n, m1 (thick S (Λ n)) = m2 (thick S (Λ n)) := fun n =>
    measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS
  rw [← iInter_thick S hSc Λ hb, hmono.measure_iInter (hnull m1) ⟨0, measure_ne_top _ _⟩,
    hmono.measure_iInter (hnull m2) ⟨0, by rw [← heq 0]; exact measure_ne_top _ _⟩]
  simp only [heq]

end CosMeas

theorem cosDens_holds : CosDens := by
  unfold CosDens
  intro X _ _ _ _ _ _ ν m _ _ H hHo _ hanti hb c0 κ hm0 hcos S hS
  have hle : ∀ n, H n ≤ H 0 := fun n => hanti (Nat.zero_le n)
  have hcos' : ∀ n y, m {z | z - y ∈ H n} = ((κ • ν).restrict {z | z - c0 ∈ H 0}) {z | z - y ∈ H n} := by
    intro n y
    have hmeas : MeasurableSet {z : X | z - y ∈ H n} :=
      ((hHo n).preimage (continuous_id.sub continuous_const)).measurableSet
    rw [Measure.restrict_apply hmeas, Measure.smul_apply, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z : X | z - y ∈ H n} ∩ {z | z - c0 ∈ H 0} = {z | z - y ∈ H n} := by
        apply inter_eq_left.mpr
        intro z hz
        have e : z - c0 = (z - y) + (y - c0) := by abel
        show z - c0 ∈ H 0
        rw [e]
        exact (H 0).add_mem (hle n hz) hy
      rw [hsub]
      exact hcos n y hy
    ·
      have hout : ∀ z, z - y ∈ H n → z - c0 ∉ H 0 := by
        intro z hz hz0
        apply hy
        have e : y - c0 = (z - c0) - (z - y) := by abel
        rw [e]
        exact (H 0).sub_mem hz0 (hle n hz)
      have hempty : {z : X | z - y ∈ H n} ∩ {z | z - c0 ∈ H 0} = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact hout z
      rw [hempty, measure_empty, mul_zero]
      exact measure_mono_null (fun z hz => hout z hz) hm0
  rw [measure_eq_of_cos m _ H hHo hanti hb hcos' S hS hS.isClosed,
    Measure.restrict_apply hS.isClosed.measurableSet, Measure.smul_apply, smul_eq_mul]

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Polynomial

private theorem bijective_algebraMap_add_mul_of_finrank_two {k K : Type} [Field k] [CommRing K]
    [Algebra k K] [Module.Finite k K] (hK : Module.finrank k K = 2) (r : K)
    (h0 : ∀ a b : k, algebraMap k K a + algebraMap k K b * r = 0 → a = 0 ∧ b = 0) :
    Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  let L : (k × k) →ₗ[k] K :=
    (LinearMap.fst k k k).smulRight (1 : K) + (LinearMap.snd k k k).smulRight r
  have hL : ∀ p : k × k, L p = algebraMap k K p.1 + algebraMap k K p.2 * r := by
    intro p
    simp [L, Algebra.smul_def]
  have hfun : (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) = ⇑L :=
    funext fun p => (hL p).symm
  rw [hfun]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL] at hp
    obtain ⟨h1, h2⟩ := h0 p.1 p.2 hp
    exact Prod.ext h1 h2
  have H : Module.finrank k (k × k) = Module.finrank k K := by
    rw [hK]
    simp
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank H).mp hinj⟩

private theorem exists_algEquiv_prod_swap (k : Type) [Field k] :
    ∃ σ : (k × k) ≃ₐ[k] (k × k), ∀ x, σ x = x.swap :=
  ⟨{ toFun := Prod.swap
     invFun := Prod.swap
     left_inv := fun x => Prod.swap_swap x
     right_inv := fun x => Prod.swap_swap x
     map_mul' := fun x y => rfl
     map_add' := fun x y => rfl
     commutes' := fun c => rfl }, fun x => rfl⟩

private theorem isQuadInv_and_bijective_of_not_isSquare (k K : Type) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) (hsq : ¬ IsSquare D)
    (hK : Module.finrank k K = 2) (r : K) (hr : r * r = algebraMap k K D)
    (σ' : K ≃ₐ[k] K) (hσ : σ' r = -r) (hinv : ∀ x, σ' (σ' x) = x) :
    IsQuadInv k K σ' ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h11 : algebraMap k K (1 + 1) = 0 := by
      rw [map_add (f := _), map_one]
      linear_combination h
    have h11' : (1 + 1 : k) = 0 := (algebraMap k K).injective (h11.trans (map_zero _).symm)
    exact h2 (by linear_combination h11')
  refine ⟨⟨hinv, Or.inl ⟨Field.toIsField K, hK, ?_⟩⟩, ?_⟩
  · intro hσr
    have h1 : r = -r := by
      simpa [hσr] using hσ
    have hr0 : r = 0 := by
      have h2r : (2 : K) * r = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2r).resolve_left h2K
    apply hD
    apply (algebraMap k K).injective
    rw [← hr, hr0, mul_zero, map_zero]
  · apply bijective_algebraMap_add_mul_of_finrank_two hK r
    intro a b h
    by_cases hb : b = 0
    · subst hb
      simp only [map_zero, zero_mul, add_zero] at h
      refine ⟨?_, rfl⟩
      apply (algebraMap k K).injective
      rw [h, map_zero]
    · exfalso
      apply hsq
      refine ⟨-a / b, ?_⟩
      apply (algebraMap k K).injective
      have hbK : algebraMap k K b ≠ 0 := (_root_.map_ne_zero _).mpr hb
      have hrc : r = algebraMap k K (-a / b) := by
        rw [map_div₀, map_neg, eq_div_iff hbK]
        linear_combination h
      rw [← hr, hrc, map_mul]

theorem exists_quadAlg (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K) (r : K),
      IsQuadInv k K σ' ∧ r * r = algebraMap k K D ∧ σ' r = -r ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  by_cases hsq : IsSquare D
  · obtain ⟨s, hs⟩ := hsq
    have hs0 : s ≠ 0 := fun h => hD (by rw [hs, h, mul_zero])
    obtain ⟨σ, hσ⟩ := exists_algEquiv_prod_swap k
    refine ⟨k × k, inferInstance, inferInstance, σ, (s, -s), ?_, ?_, ?_, ?_⟩
    · refine ⟨fun x => by rw [hσ, hσ, Prod.swap_swap], Or.inr ⟨AlgEquiv.refl, fun x => ?_⟩⟩
      rw [hσ]
      rfl
    · ext <;> simp [hs]
    · rw [hσ]
      ext <;> simp
    · apply bijective_algebraMap_add_mul_of_finrank_two
      · simp
      · intro a b h
        have e1 : a + b * s = 0 := by
          exact congrArg Prod.fst h
        have e2 : a + b * -s = 0 := by
          exact congrArg Prod.snd h
        have hb : (2 * s) * b = 0 := by linear_combination e1 - e2
        have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_left (mul_ne_zero h2 hs0)
        refine ⟨?_, hb0⟩
        linear_combination e1 - s * hb0
  · have hroot : ∀ b : k, b ^ 2 ≠ D := fun b hb => hsq ⟨b, by rw [← hb, sq]⟩
    have hirr : Irreducible (X ^ 2 - C D : k[X]) := by
      exact X_pow_sub_C_irreducible_of_prime Nat.prime_two hroot
    have : Fact (Irreducible (X ^ 2 - C D : k[X])) := ⟨hirr⟩
    have hf0 : (X ^ 2 - C D : k[X]) ≠ 0 := hirr.ne_zero
    have hfin : Module.finrank k (AdjoinRoot (X ^ 2 - C D : k[X])) = 2 := by
      rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]
    have : Module.Finite k (AdjoinRoot (X ^ 2 - C D : k[X])) := (AdjoinRoot.powerBasis hf0).finite
    have hr : AdjoinRoot.root (X ^ 2 - C D : k[X]) * AdjoinRoot.root (X ^ 2 - C D : k[X]) =
        algebraMap k (AdjoinRoot (X ^ 2 - C D : k[X])) D := by
      have h0 : aeval (AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      simp only [map_sub, aeval_X_pow, aeval_C] at h0
      linear_combination h0
    have hneg : aeval (-AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
      simp only [map_sub, aeval_X_pow, aeval_C]
      linear_combination hr
    have hneg' : eval₂ (algebraMap k (AdjoinRoot (X ^ 2 - C D : k[X])))
        (-AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
      rw [← aeval_def]
      exact hneg
    obtain ⟨τ, hτr⟩ : ∃ τ : AdjoinRoot (X ^ 2 - C D : k[X]) →ₐ[k] AdjoinRoot (X ^ 2 - C D : k[X]),
        τ (AdjoinRoot.root _) = -AdjoinRoot.root (X ^ 2 - C D : k[X]) := by
      exact ⟨{ AdjoinRoot.lift (algebraMap k _) (-AdjoinRoot.root _) hneg' with
          commutes' := fun c => by simp [AdjoinRoot.algebraMap_eq] }, AdjoinRoot.lift_root hneg'⟩
    have hττ : τ.comp τ = AlgHom.id k _ := by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, hτr, map_neg, hτr, neg_neg, AlgHom.id_apply]
    let σ' := AlgEquiv.ofAlgHom τ τ hττ hττ
    have hσ : σ' (AdjoinRoot.root (X ^ 2 - C D : k[X])) = -AdjoinRoot.root (X ^ 2 - C D : k[X]) :=
      hτr
    have hinv : ∀ x, σ' (σ' x) = x := fun x => DFunLike.congr_fun hττ x
    obtain ⟨hq, hbij⟩ := isQuadInv_and_bijective_of_not_isSquare k (AdjoinRoot (X ^ 2 - C D : k[X])) h2 D hD hsq hfin
      (AdjoinRoot.root _) hr σ' hσ hinv
    exact ⟨AdjoinRoot (X ^ 2 - C D : k[X]), inferInstance, inferInstance, σ',
      AdjoinRoot.root _, hq, hr, hσ, hbij⟩

end PI.VolStabS
end
end

section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace PI.VolStabS

private theorem exists_trace_mul_eq_linearMap (F : Type) [Field F] [NumberField F] (f : F →ₗ[ℚ] ℚ) :
    ∃ β : F, ∀ y : F, f y = Algebra.trace ℚ F (β * y) := by
  have hnd := traceForm_nondegenerate ℚ F
  obtain ⟨β, hβ⟩ : ∃ β, (LinearMap.BilinForm.toDual (Algebra.traceForm ℚ F) hnd) β = f :=
    ⟨_, LinearEquiv.apply_symm_apply _ f⟩
  refine ⟨β, fun y => ?_⟩
  rw [← hβ, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]

theorem addIntF_holds : AddIntF := by
  intro F _ _ Λ ⟨c0, hc0, hc0Λ⟩ hnot g hg
  have hmul : ∀ (r : 𝓞 F) (x : F), x ∈ Λ → algebraMap (𝓞 F) F r * x ∈ Λ := by
    intro r x hx
    have h1 := Λ.smul_mem r hx
    rw [Algebra.smul_def] at h1
    exact h1
  obtain ⟨bb, hbb⟩ : ∃ bb, bb = NumberField.integralBasis F := ⟨_, rfl⟩
  have hmem : ∀ i, c0 * bb i ∈ Λ := by
    intro i
    rw [hbb, NumberField.integralBasis_apply, mul_comm]
    exact hmul _ _ hc0Λ
  choose n hn using fun i => hg _ (hmem i)
  let h0 : F →ₗ[ℚ] ℚ := bb.constr ℚ (fun i => (n i : ℚ))
  have hh0 : ∀ y : F, g (c0 * y) = ((h0 y : ℚ) : ℂ) := by
    let L1 : F →+ ℂ := g.comp (AddMonoidHom.mulLeft c0)
    let L2 : F →+ ℂ := (Rat.castHom ℂ).toAddMonoidHom.comp h0.toAddMonoidHom
    have hL : L1.toRatLinearMap = L2.toRatLinearMap := by
      refine bb.ext (fun i => ?_)
      simp [L1, L2, h0, hn i]
    intro y
    have h1 := congrArg (fun L : F →ₗ[ℚ] ℂ => L y) hL
    simpa [L1, L2] using h1
  obtain ⟨β, hβ⟩ := exists_trace_mul_eq_linearMap F h0
  have hgx : ∀ x : F, g x = ((Algebra.trace ℚ F (β * c0⁻¹ * x) : ℚ) : ℂ) := by
    intro x
    have h1 := hh0 (c0⁻¹ * x)
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h1
    rw [h1, hβ, mul_assoc]
  intro a
  by_contra ha
  have hβ0 : β * c0⁻¹ ≠ 0 := by
    intro h0'
    apply ha
    rw [hgx, h0', zero_mul, map_zero, Rat.cast_zero]
  have h10 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    intro h
    have h1 : (1 : F) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨1, map_one _⟩
    rw [h, FractionalIdeal.mem_zero_iff] at h1
    exact one_ne_zero h1
  have hdual : ∀ x ∈ Λ,
      β * c0⁻¹ * x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    intro x hx
    rw [FractionalIdeal.mem_dual h10]
    intro b hb
    rw [FractionalIdeal.mem_one_iff] at hb
    obtain ⟨r, rfl⟩ := hb
    obtain ⟨m, hm⟩ := hg _ (hmul r x hx)
    rw [RingHom.mem_range]
    refine ⟨m, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast]
    have h1 := hgx (algebraMap (𝓞 F) F r * x)
    have h2 : ((Algebra.trace ℚ F (β * c0⁻¹ * (algebraMap (𝓞 F) F r * x)) : ℚ) : ℂ)
        = ((m : ℚ) : ℂ) := by
      rw [← h1, hm, Rat.cast_intCast]
    rw [Rat.cast_inj] at h2
    rw [← h2]
    congr 1
    ring
  obtain ⟨d, hd, hdint⟩ :=
    (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).isFractional
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  apply hnot ((algebraMap (𝓞 F) F d * (β * c0⁻¹))⁻¹) (inv_ne_zero (mul_ne_zero hd0 hβ0))
  intro x hx
  obtain ⟨r, hr⟩ := hdint _ (hdual x hx)
  refine ⟨r, ?_⟩
  rw [Algebra.smul_def] at hr
  have hr' : (r : F) = algebraMap (𝓞 F) F r := rfl
  rw [hr', hr, show algebraMap (𝓞 F) F d * (β * c0⁻¹ * x)
      = algebraMap (𝓞 F) F d * (β * c0⁻¹) * x by ring,
    inv_mul_cancel_left₀ (mul_ne_zero hd0 hβ0)]

theorem chInf_of_lift (hL : ChLift) : ChInf :=
  chInf_of hL addIntF_holds

end PI.VolStabS
end
end
