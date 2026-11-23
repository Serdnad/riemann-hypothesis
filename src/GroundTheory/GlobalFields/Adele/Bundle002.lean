module

public import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import GroundTheory.GlobalFields.IdeleGroups.Bundle001
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle065
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import GroundTheory.GlobalFields.Adele.Bundle001
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Filter Topology TopologicalSpace NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing

namespace GroundTheory.Global

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)}

theorem isOpen_setOf_forall_mem (hAopen : ∀ i, IsOpen (A i)) {V : ∀ i, Set (R i)}
    (hV : ∀ i, IsOpen (V i)) (hVA : ∀ᶠ i in cofinite, V i = A i) :
    IsOpen {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ V i} := by
  set S : Set ι := {i | V i = A i}
  have hSf : Sᶜ.Finite := hVA
  have hEq : {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ V i} =
      {x : Πʳ i, [R i, A i] | ∀ i, i ∈ S → x.1 i ∈ A i} ∩
        ⋂ i ∈ Sᶜ, (fun x : Πʳ i, [R i, A i] ↦ x i) ⁻¹' V i := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨fun i hi ↦ (show V i = A i from hi) ▸ h i, fun i _ ↦ h i⟩
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ S
      · rw [show V i = A i from hi]
        exact h1 i hi
      · exact h2 i hi
  rw [hEq]
  exact (_root_.RestrictedProduct.isOpen_forall_imp_mem hAopen).inter
    (hSf.isOpen_biInter fun i _ ↦ (hV i).preimage (_root_.RestrictedProduct.continuous_eval i))

theorem isTopologicalBasis (hAopen : ∀ i, IsOpen (A i)) :
    IsTopologicalBasis {s : Set (Πʳ i, [R i, A i]) | ∃ V : ∀ i, Set (R i),
      (∀ i, IsOpen (V i)) ∧ (∀ᶠ i in cofinite, V i = A i) ∧ s = {x | ∀ i, x i ∈ V i}} := by
  classical
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨V, hV, hVA, rfl⟩
    exact isOpen_setOf_forall_mem hAopen hV hVA
  · intro x u hxu hu
    set T : Set ι := {i | x i ∈ A i}
    have hT : cofinite ≤ 𝓟 T := le_principal_iff.mpr x.2
    obtain ⟨x', hxx'⟩ :=
      _root_.RestrictedProduct.exists_inclusion_eq_of_eventually R A hT (fun i hi ↦ hi)
    have hu' : IsOpen (_root_.RestrictedProduct.inclusion R A hT ⁻¹' u) :=
      hu.preimage (_root_.RestrictedProduct.continuous_inclusion hT)
    rw [_root_.RestrictedProduct.isEmbedding_coe_of_principal.isInducing.isOpen_iff] at hu'
    obtain ⟨t, ht, htu⟩ := hu'
    have hx't : (x' : ∀ i, R i) ∈ t := by
      have : x' ∈ _root_.RestrictedProduct.inclusion R A hT ⁻¹' u := by
        rw [Set.mem_preimage, hxx']
        exact hxu
      rw [← htu] at this
      exact this
    obtain ⟨I, W, hW, hIW⟩ := isOpen_pi_iff.1 ht _ hx't
    let V : ∀ i, Set (R i) := fun i ↦
      (if i ∈ I then W i else Set.univ) ∩ (if i ∈ T then A i else Set.univ)
    refine ⟨{y | ∀ i, y i ∈ V i}, ⟨V, fun i ↦ ?_, ?_, rfl⟩, ?_, ?_⟩
    · refine IsOpen.inter ?_ ?_
      · split_ifs with h
        exacts [(hW i h).1, isOpen_univ]
      · split_ifs
        exacts [hAopen i, isOpen_univ]
    · filter_upwards [x.2, I.finite_toSet.compl_mem_cofinite] with i hi hiI
      have hiI' : i ∉ I := hiI
      have hiT : i ∈ T := hi
      simp only [V, if_neg hiI', if_pos hiT, Set.univ_inter]
    · intro i
      rw [← hxx']
      refine ⟨?_, ?_⟩
      · split_ifs with h
        exacts [(hW i h).2, Set.mem_univ _]
      · split_ifs with h
        exacts [eventually_principal.1 x'.2 i h, Set.mem_univ _]
    · intro y hy
      let y' : Πʳ i, [R i, A i]_[𝓟 T] := ⟨y.1, eventually_principal.2 fun i hi ↦ by
        have := (hy i).2
        simp only [if_pos hi] at this
        exact this⟩
      have hy' : y' ∈ _root_.RestrictedProduct.inclusion R A hT ⁻¹' u := by
        rw [← htu]
        refine hIW fun i hi ↦ ?_
        have := (hy i).1
        simp only [if_pos (Finset.mem_coe.1 hi)] at this
        exact this
      exact hy'

end RestrictedProduct

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

theorem finiteProj_eq (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    finiteProj v x = (prodRestrictedEquiv K x).2 v :=
  Units.ext rfl

theorem infiniteProj_eq (w : InfinitePlace K) (x : IdeleGroup K) :
    infiniteProj w x = ContinuousMulEquiv.piUnits (prodRestrictedEquiv K x).1 w :=
  Units.ext rfl

theorem isTopologicalBasis :
    IsTopologicalBasis {s : Set (IdeleGroup K) |
      ∃ (U : ∀ w : InfinitePlace K, Set (w.Completion)ˣ)
        (V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ),
        (∀ w, IsOpen (U w)) ∧ (∀ v, IsOpen (V v)) ∧
        (∀ᶠ v in cofinite, V v =
          ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)) ∧
        s = {x | (∀ w, infiniteProj w x ∈ U w) ∧ ∀ v, finiteProj v x ∈ V v}} := by
  set e := prodRestrictedEquiv K
  set p := (ContinuousMulEquiv.piUnits :
    (InfiniteAdeleRing K)ˣ ≃ₜ* ∀ w : InfinitePlace K, (w.Completion)ˣ)
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨U, V, hU, hV, hVO, rfl⟩
    have h1 : IsOpen {x : IdeleGroup K | ∀ w, infiniteProj w x ∈ U w} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun w ↦ (hU w).preimage (continuous_infiniteProj w)
    have h2 : IsOpen {x : IdeleGroup K | ∀ v, finiteProj v x ∈ V v} := by
      simp only [finiteProj_eq]
      exact (RestrictedProduct.isOpen_setOf_forall_mem
        (fun v ↦ isOpen_units_adicCompletionIntegers K v) hV hVO).preimage
          (continuous_snd.comp e.continuous)
    exact h1.inter h2
  · intro x u hxu hu
    have hu' : IsOpen (e.symm ⁻¹' u) := hu.preimage e.symm.continuous
    have hxu' : e x ∈ e.symm ⁻¹' u := by simpa using hxu
    obtain ⟨a, b, ha, hb, hxa, hxb, hab⟩ := isOpen_prod_iff.1 hu' (e x).1 (e x).2 hxu'
    obtain ⟨_, ⟨V, hV, hVO, rfl⟩, hxV, hVb⟩ :=
      (RestrictedProduct.isTopologicalBasis
        (fun v ↦ isOpen_units_adicCompletionIntegers K v)).exists_subset_of_mem_open hxb hb
    have ha' : IsOpen (p.symm ⁻¹' a) := ha.preimage p.symm.continuous
    have hxa' : p (e x).1 ∈ p.symm ⁻¹' a := by
      change p.symm (p (e x).1) ∈ a
      exact (congrArg (fun z : (InfiniteAdeleRing K)ˣ ↦ z ∈ a)
        (p.symm_apply_apply (e x).1)).mpr hxa
    obtain ⟨U, hU, hUa⟩ := isOpen_pi_iff'.1 ha' _ hxa'
    refine ⟨{y | (∀ w, infiniteProj w y ∈ U w) ∧ ∀ v, finiteProj v y ∈ V v},
      ⟨U, V, fun w ↦ (hU w).1, hV, hVO, rfl⟩, ⟨fun w ↦ ?_, fun v ↦ ?_⟩, ?_⟩
    · rw [infiniteProj_eq]
      exact (hU w).2
    · rw [finiteProj_eq]
      exact hxV v
    · rintro y ⟨hyU, hyV⟩
      have hya : (e y).1 ∈ a := by
        have : p (e y).1 ∈ p.symm ⁻¹' a := hUa fun w _ ↦ by
          rw [← infiniteProj_eq]
          exact hyU w
        change p.symm (p (e y).1) ∈ a at this
        exact (congrArg (fun z : (InfiniteAdeleRing K)ˣ ↦ z ∈ a)
          (p.symm_apply_apply (e y).1)).mp this
      have hyb : (e y).2 ∈ b := hVb fun v ↦ by
        rw [← finiteProj_eq]
        exact hyV v
      have := hab (Set.mk_mem_prod hya hyb)
      simpa using this

end IdeleGroup

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped _root_.RestrictedProduct

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_valuation_sub_le_one (S : Finset (HeightOneSpectrum R))
    (x : HeightOneSpectrum R → K) :
    ∃ k : K, (∀ v ∈ S, v.valuation K (k - x v) ≤ 1) ∧ (∀ v ∉ S, v.valuation K k ≤ 1) :=
  _root_.UpperTheory.Reformulated.B.ExistsValuationSubLeOne.exists_valuation_sub_le_one S x

def integralFiniteAdeles (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Subring (FiniteAdeleRing R K) where
  carrier := {a | ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v := Subring.mul_mem _ (ha v) (hb v)
  one_mem' _ := Subring.one_mem _
  add_mem' ha hb v := Subring.add_mem _ (ha v) (hb v)
  zero_mem' _ := Subring.zero_mem _
  neg_mem' ha v := Subring.neg_mem _ (ha v)

theorem mem_integralFiniteAdeles {a : FiniteAdeleRing R K} :
    a ∈ integralFiniteAdeles R K ↔ ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem isOpen_integralFiniteAdeles :
    IsOpen (integralFiniteAdeles R K : Set (FiniteAdeleRing R K)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun _ => Valued.isOpen_valuationSubring _)

theorem coe_mem_adicCompletionIntegers_iff (v : HeightOneSpectrum R) (k : K) :
    (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ v.valuation K k ≤ 1 := by
  rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']

theorem exists_sub_mem_integralFiniteAdeles (a : FiniteAdeleRing R K) :
    ∃ k : K, a - algebraMap K (FiniteAdeleRing R K) k ∈ integralFiniteAdeles R K := by
  classical
  have hS : {v : HeightOneSpectrum R | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2
  have hx : ∀ v : HeightOneSpectrum R, ∃ z : K,
      a v - (z : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    intro v
    have hU : IsOpen {w : v.adicCompletion K | a v - w ∈ v.adicCompletionIntegers K} :=
      (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
        (continuous_const.sub continuous_id)
    obtain ⟨z, hz⟩ := (denseRange_algebraMap (K := K) v).exists_mem_open hU
      ⟨a v, by simp⟩
    exact ⟨z, hz⟩
  choose x hx using hx
  obtain ⟨k, hkS, hkn⟩ := exists_valuation_sub_le_one hS.toFinset x
  refine ⟨k, fun v => ?_⟩
  change a v - (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K
  by_cases hv : v ∈ hS.toFinset
  · have h1 := (coe_mem_adicCompletionIntegers_iff v (k - x v)).mpr (hkS v hv)
    have h2 : a v - (k : v.adicCompletion K) =
        (a v - (x v : v.adicCompletion K)) - ((k - x v : K) : v.adicCompletion K) := by
      have hc : ∀ z : K, (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z :=
        fun z => by simp [algebraMap_adicCompletion]
      rw [hc, hc, hc, map_sub]
      ring
    rw [h2]
    exact Subring.sub_mem _ (hx v) h1
  · have hav : a v ∈ v.adicCompletionIntegers K := by
      simpa using hv
    exact Subring.sub_mem _ hav ((coe_mem_adicCompletionIntegers_iff v k).mpr (hkn v hv))

instance : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

instance (F : Type*) [Field F] : T2Space (NumberField.InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))

instance : T2Space (NumberField.AdeleRing R K) :=
  inferInstanceAs (T2Space (NumberField.InfiniteAdeleRing K × FiniteAdeleRing R K))

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open IsDedekindDomain NumberField Topology

variable {K : Type*} [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))

theorem denseRange_units_prod_pi :
    DenseRange (fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a))) := by
  classical
  set f := fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a)) with hf
  set E : ((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ) →
      ((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion) :=
    Prod.map (Pi.map fun _ ↦ Units.val) (Pi.map fun _ ↦ Units.val) with hE
  have hEi : IsInducing E :=
    (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing).prodMap
      (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing)
  let W : Set (((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion)) :=
    {z | (∀ v, z.1 v ≠ 0) ∧ ∀ w, z.2 w ≠ 0}
  have hW : IsOpen W := by
    have : W = (⋂ v, {z | z.1 v ≠ 0}) ∩ ⋂ w, {z | z.2 w ≠ 0} := by
      ext z; simp [W]
    rw [this]
    exact (isOpen_iInter_of_finite fun v ↦
      isOpen_ne_fun ((continuous_apply v).comp continuous_fst) continuous_const).inter
      (isOpen_iInter_of_finite fun w ↦
        isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const)
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ ↦ ?_
  obtain ⟨V, hV, rfl⟩ := hEi.isOpen_iff.1 hU
  have hEu : E u ∈ W := ⟨fun v ↦ (u.1 v).ne_zero, fun w ↦ (u.2 w).ne_zero⟩
  obtain ⟨x, hxV, hxW⟩ := (denseRange_algebraMap_prod_pi S T).exists_mem_open (hV.inter hW)
    ⟨E u, hu, hEu⟩
  by_cases hx : x = 0
  · have hS : IsEmpty S := ⟨fun v ↦ hxW.1 v (by rw [hx]; exact map_zero _)⟩
    have hT : IsEmpty T := ⟨fun w ↦ hxW.2 w (by rw [hx]; exact map_zero _)⟩
    refine ⟨f 1, ?_, 1, rfl⟩
    show E (f 1) ∈ V
    convert hxV using 1
    exact Prod.ext (funext fun v ↦ isEmptyElim v) (funext fun w ↦ isEmptyElim w)
  · refine ⟨f (Units.mk0 x hx), ?_, _, rfl⟩
    exact hxV

end GroundTheory.Global
end
