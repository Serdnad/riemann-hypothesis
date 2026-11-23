module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Mathlib.Algebra.Module.SpanRankOperations
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem prec_of_surj {B C : Type} [CommRing B] [CommRing C] (g : B →+* C)
    (I : Ideal B) [hB : IsPrecomplete I B] (hg : Function.Surjective g) :
    IsPrecomplete (I.map g) C := by
  refine ⟨fun f hf => ?_⟩
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  have h1 : ∀ n, ∃ d ∈ I ^ n, g d = f (n + 1) - f n := by
    intro n
    have := (((I.map g) ^ n).neg_mem (hf (Nat.le_succ n)))
    rw [neg_sub, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective g hg] at this
    exact this
  choose d hd hgd using h1
  obtain ⟨b0, hb0⟩ := hg (f 0)
  let u : ℕ → B := fun n => b0 + ∑ i ∈ Finset.range n, d i
  have hu : ∀ n, g (u n) = f n := by
    intro n

    simp only [u, map_add (f := _), map_sum, hgd, hb0, Finset.sum_range_sub]
    ring
  have hc : ∀ {m n}, m ≤ n → u m ≡ u n [SMOD (I ^ m • ⊤ : Submodule B B)] := by
    intro m n hmn
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have e : u m - u (k + 1) = (u m - u k) - d k := by
        simp only [u, Finset.sum_range_succ]; ring
      rw [e]
      exact Ideal.sub_mem _ ih (Ideal.pow_le_pow_right hk (hd k))
  obtain ⟨L, hL⟩ := hB.prec hc
  refine ⟨g L, fun n => ?_⟩
  have := hL n
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  rw [← hu, ← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ this

private theorem approx_map {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) (I : Ideal R) (n : ℕ) (x : B)
    (hx : x ∈ I.map (algebraMap R B)) :
    ∃ i ∈ I, ∃ s : R, s ∉ p ∧ algebraMap R B s * x - algebraMap R B i ∈ maximalIdeal B ^ n := by
  have hp := h.isPrime
  have h1 : (1 : R) ∉ p := (Ideal.ne_top_iff_one _).1 hp.ne_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, hi, 1, h1, by simp⟩
  | zero => exact ⟨0, I.zero_mem, 1, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi, s, hs, hx⟩ := hx
    obtain ⟨j, hj, t, ht, hy⟩ := hy
    refine ⟨t * i + s * j, I.add_mem (I.mul_mem_left _ hi) (I.mul_mem_left _ hj), s * t,
      fun hst => (hp.mem_or_mem hst).elim hs ht, ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R B t) hx)
      (Ideal.mul_mem_left _ (algebraMap R B s) hy)
    convert this using 1
    simp only [map_add (f := _), map_mul]; ring
  | smul b x _ hx =>
    obtain ⟨i, hi, s, hs, hx⟩ := hx
    obtain ⟨a, t, ht, hb⟩ := h.dense n b
    refine ⟨a * i, I.mul_mem_left _ hi, s * t, fun hst => (hp.mem_or_mem hst).elim hs ht, ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R B t * b) hx)
      (Ideal.mul_mem_left _ (algebraMap R B i) hb)
    convert this using 1
    simp only [map_mul, smul_eq_mul]; ring

theorem UpperTheory.V.AlgebraTools.IsCplAt.quotient :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (S : Type) [CommRing S] [Algebra R S] (q : Ideal S) (C : Type) [CommRing C] [IsLocalRing C]
      [Algebra S C] [Algebra B C] [Algebra R C] [IsScalarTower R S C] [IsScalarTower R B C],
      IsCplAt R p B → Function.Surjective (algebraMap R S) → q.comap (algebraMap R S) = p →
      Function.Surjective (algebraMap B C) →
      RingHom.ker (algebraMap B C) = (RingHom.ker (algebraMap R S)).map (algebraMap R B) → IsCplAt S q C := by
  intro R _ _ p B _ _ _ S _ _ q C _ _ _ _ _ _ _ h hRS hq hBC hker
  haveI := h.noeth
  haveI := h.complete
  have hp := h.isPrime
  have hN : IsNoetherianRing C := isNoetherianRing_of_surjective B C (algebraMap B C) hBC
  haveI hloc : IsLocalHom (algebraMap B C) := IsLocalHom.of_surjective _ hBC
  have hm : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hBC
  have hsq : ∀ r : R, algebraMap S C (algebraMap R S r) = algebraMap B C (algebraMap R B r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hqp : ∀ r : R, algebraMap R S r ∈ q ↔ r ∈ p := by
    intro r; rw [← hq, Ideal.mem_comap]
  have hpre : IsPrecomplete (maximalIdeal C) C := hm ▸ prec_of_surj (algebraMap B C) _ hBC
  refine ⟨hN, {}, ?_, ?_, ?_⟩
  · ext x
    obtain ⟨r, rfl⟩ := hRS x
    rw [hqp, ← h.comap_eq, Ideal.mem_comap, Ideal.mem_comap, hsq, mem_maximalIdeal,
      mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]
  · intro n c
    obtain ⟨b, rfl⟩ := hBC c
    obtain ⟨a, s, hs, hab⟩ := h.dense n b
    refine ⟨algebraMap R S a, algebraMap R S s, fun hh => hs ((hqp s).1 hh), ?_⟩
    rw [hsq, hsq, ← map_mul, ← map_sub, ← hm, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hab
  · intro n x hx
    obtain ⟨a, rfl⟩ := hRS x
    rw [hsq, ← hm, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hBC] at hx
    obtain ⟨y, hy, hya⟩ := hx
    have hk : algebraMap R B a - y ∈ RingHom.ker (algebraMap B C) := by
      rw [RingHom.mem_ker, map_sub, hya, sub_self]
    rw [hker] at hk
    obtain ⟨i, hi, s, hs, hsi⟩ := approx_map h _ n _ hk
    have h2 : algebraMap R B (s * a - i) ∈ maximalIdeal B ^ n := by
      have := Ideal.add_mem _ hsi (Ideal.mul_mem_left _ (algebraMap R B s) hy)
      convert this using 1
      simp only [map_sub, map_mul]; ring
    obtain ⟨t, ht, hta⟩ := h.strict n _ h2
    refine ⟨algebraMap R S (t * s), fun hh => (hp.mem_or_mem ((hqp _).1 hh)).elim ht hs, ?_⟩
    have h3 : algebraMap R S (t * (s * a - i)) ∈ q ^ n := by
      have := Ideal.mem_map_of_mem (algebraMap R S) hta
      rw [Ideal.map_pow] at this
      refine Ideal.pow_right_mono ?_ n this
      rw [Ideal.map_le_iff_le_comap, hq]
    rw [RingHom.mem_ker] at hi
    convert h3 using 1
    simp only [map_sub, map_mul, hi]; ring
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem limKer_key {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) (O : OpenNormalSubgroup G) (x : G) :
    (∀ᶠ i in (U : Filter ι), x ∈ K i ⊔ O.toSubgroup) ↔
      x ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup := by
  haveI := O.isNormal'
  constructor
  · intro h
    have hex : ∀ᶠ i in (U : Filter ι), ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup := by
      refine h.mono fun i hi => ?_
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hi
      refine ⟨y, hy, ?_⟩
      rw [← hyz]
      simpa using hz
    classical
    obtain ⟨k, hk⟩ : ∃ k : ι → G, ∀ᶠ i in (U : Filter ι), k i ∈ K i ∧ (k i)⁻¹ * x ∈ O.toSubgroup := by
      refine ⟨fun i => if hi : ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup then hi.choose else 1, ?_⟩
      refine hex.mono fun i hi => ?_
      simp only [dif_pos hi]
      exact hi.choose_spec
    obtain ⟨l, hl⟩ : ∃ l : G, Tendsto k (U : Filter ι) (nhds l) := by
      refine ⟨(U.map k).lim, ?_⟩
      have h' := (U.map k).le_nhds_lim
      rw [Ultrafilter.coe_map] at h'
      exact h'
    have hlL : l ∈ limKer (U : Filter ι) K := by
      rw [mem_limKer]
      intro O'
      have hopen : IsOpen {y : G | l⁻¹ * y ∈ O'.toSubgroup} :=
        O'.toOpenSubgroup.isOpen.preimage (continuous_const_mul _)
      filter_upwards [hl.eventually (hopen.mem_nhds (by simp)), hk] with i h1 h2
      have heq : l = k i * (l⁻¹ * k i)⁻¹ := by group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h2.1) (Subgroup.mem_sup_right (Subgroup.inv_mem _ h1))
    have hC : IsClosed {y : G | y⁻¹ * x ∈ O.toSubgroup} :=
      O.toOpenSubgroup.isClosed.preimage (continuous_inv.mul continuous_const)
    have hlx : l⁻¹ * x ∈ O.toSubgroup := hC.mem_of_tendsto hl (hk.mono fun i h => h.2)
    have heq : x = l * (l⁻¹ * x) := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right hlx)
  · intro h
    let S : Subgroup G :=
      { carrier := {g | ∀ᶠ i in (U : Filter ι), g ∈ K i ⊔ O.toSubgroup}
        mul_mem' := fun ha hb =>
          Filter.Eventually.mono (Filter.Eventually.and ha hb) fun i hi => Subgroup.mul_mem _ hi.1 hi.2
        one_mem' := Filter.Eventually.of_forall fun i => Subgroup.one_mem _
        inv_mem' := fun ha => Filter.Eventually.mono ha fun i hi => Subgroup.inv_mem _ hi }
    have hle : limKer (U : Filter ι) K ⊔ O.toSubgroup ≤ S :=
      sup_le (fun g hg => (mem_limKer.1 hg) O)
        (fun g hg => Filter.Eventually.of_forall fun i => Subgroup.mem_sup_right hg)
    exact hle h

theorem UpperTheory.V.AlgebraTools.limKer_sup :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal],
      IsClosed (limKer (U : Filter ι) K : Set G) ∧
      (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup) ∧
      (∀ O : OpenNormalSubgroup G, limKer (U : Filter ι) K ≤ O.toSubgroup ↔ ∀ᶠ i in (U : Filter ι), K i ≤ O.toSubgroup) := by
  intro G ι _ _ _ _ _ U K _
  have h2 : ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι),
      K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup := by
    intro O
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
      (fun g : G => {y : G | g⁻¹ * y ∈ O.toSubgroup})
      (fun g => O.toOpenSubgroup.isOpen.preimage (continuous_const_mul _))
      (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
    have hev : ∀ᶠ i in (U : Filter ι), ∀ t ∈ T,
        (t ∈ K i ⊔ O.toSubgroup ↔ t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup) := by
      refine (Filter.eventually_all_finset T).2 (fun t _ => ?_)
      by_cases ht : t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup
      · exact ((limKer_key U K O t).2 ht).mono fun i hi => iff_of_true hi ht
      · have hn : ¬ ∀ᶠ i in (U : Filter ι), t ∈ K i ⊔ O.toSubgroup :=
          fun h => ht ((limKer_key U K O t).1 h)
        exact (Ultrafilter.eventually_not.2 hn).mono fun i hi => iff_of_false hi ht
    filter_upwards [hev] with i hi
    ext g
    obtain ⟨t, htT, hgt⟩ : ∃ t ∈ T, t⁻¹ * g ∈ O.toSubgroup := by
      have := hT (Set.mem_univ g)
      simp only [Set.mem_iUnion] at this
      obtain ⟨t, htT, hgt⟩ := this
      exact ⟨t, htT, hgt⟩
    have mem_iff : ∀ M : Subgroup G, O.toSubgroup ≤ M → (g ∈ M ↔ t ∈ M) := by
      intro M hM
      have hg : g = t * (t⁻¹ * g) := by group
      rw [hg]
      exact mul_mem_cancel_right (hM hgt)
    rw [mem_iff _ le_sup_right, mem_iff _ le_sup_right]
    exact hi t htT
  have hclosed : IsClosed (limKer (U : Filter ι) K : Set G) := by
    have hset : (limKer (U : Filter ι) K : Set G) =
        ⋂ O : OpenNormalSubgroup G, ((limKer (U : Filter ι) K ⊔ O.toSubgroup : Subgroup G) : Set G) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_iInter]
      constructor
      · intro hx O
        exact Subgroup.mem_sup_left hx
      · intro hx
        rw [mem_limKer]
        intro O
        exact (limKer_key U K O x).2 (hx O)
    rw [hset]
    exact isClosed_iInter fun O =>
      Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right O.toOpenSubgroup.isOpen)
  refine ⟨hclosed, h2, fun O => ⟨fun h => ?_, fun h => ?_⟩⟩
  · filter_upwards [h2 O] with i hi
    rw [sup_eq_right.2 h] at hi
    exact sup_eq_right.1 hi
  · intro x hx
    obtain ⟨i, hi1, hi2⟩ := ((mem_limKer.1 hx O).and h).exists
    exact (sup_le hi2 le_rfl) hi1
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_lim_hom_out :
    ∀ (G Z ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z], TopFG G → ∀ (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal] (f : ι → G →* Z),
      (∀ i, Continuous (f i)) → (∀ i, K i ≤ (f i).ker) →
      ∃ F : G →* Z, Continuous F ∧ limKer (U : Filter ι) K ≤ F.ker ∧
        (∀ V : OpenNormalSubgroup Z, ∀ᶠ i in (U : Filter ι), ∀ g, (F g)⁻¹ * f i g ∈ V.toSubgroup) ∧
        ((∀ i, Function.Surjective (f i)) → Function.Surjective F) := by
  intro G Z ι _ _ _ _ _ _ _ _ _ _ hG U K _ f hf hK
  obtain ⟨s, hsfin, hsgen⟩ := hG
  obtain ⟨F0, hF0⟩ : ∃ F0 : G → Z, ∀ g, Tendsto (fun i => f i g) (U : Filter ι) (nhds (F0 g)) := by
    refine ⟨fun g => (U.map (fun i => f i g)).lim, fun g => ?_⟩
    have h := (U.map (fun i => f i g)).le_nhds_lim
    rw [Ultrafilter.coe_map] at h
    exact h
  have hone : F0 1 = 1 :=
    tendsto_nhds_unique (hF0 1) (by simp only [map_one]; exact tendsto_const_nhds)
  have hmul : ∀ a b, F0 (a * b) = F0 a * F0 b := fun a b =>
    tendsto_nhds_unique (hF0 (a * b)) (by simp only [map_mul]; exact (hF0 a).mul (hF0 b))
  obtain ⟨F, hF⟩ : ∃ F : G →* Z, ∀ g, Tendsto (fun i => f i g) (U : Filter ι) (nhds (F g)) :=
    ⟨{ toFun := F0, map_one' := hone, map_mul' := hmul }, hF0⟩
  have agree : ∀ (V : OpenNormalSubgroup Z) (i j : ι),
      (∀ x ∈ s, (F x)⁻¹ * f i x ∈ V.toSubgroup) → (∀ x ∈ s, (F x)⁻¹ * f j x ∈ V.toSubgroup) →
      ∀ g, (f j g)⁻¹ * f i g ∈ V.toSubgroup := by
    intro V i j hi hj g
    let H : Subgroup G :=
      { carrier := {g | (f j g)⁻¹ * f i g ∈ V.toSubgroup}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul] at *
          have := V.toSubgroup.mul_mem (V.isNormal'.conj_mem _ ha (f j b)⁻¹) hb
          convert this using 1
          group
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq, map_inv] at *
          have := V.isNormal'.conj_mem _ (V.toSubgroup.inv_mem ha) (f j a)
          convert this using 1
          group }
    have hHc : IsClosed (H : Set G) :=
      V.toOpenSubgroup.isClosed.preimage (((hf j).inv).mul (hf i))
    have hsH : Subgroup.closure s ≤ H := by
      rw [Subgroup.closure_le]
      intro x hx
      show (f j x)⁻¹ * f i x ∈ V.toSubgroup
      have := V.toSubgroup.mul_mem (V.toSubgroup.inv_mem (hj x hx)) (hi x hx)
      convert this using 1
      group
    have hg : g ∈ (Subgroup.closure s).topologicalClosure := by
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, hsgen.closure_eq]
      trivial
    exact Subgroup.topologicalClosure_minimal _ hsH hHc hg
  have key : ∀ V : OpenNormalSubgroup Z, ∀ᶠ i in (U : Filter ι), ∀ g, (F g)⁻¹ * f i g ∈ V.toSubgroup := by
    intro V
    have hs : ∀ᶠ i in (U : Filter ι), ∀ x ∈ s, (F x)⁻¹ * f i x ∈ V.toSubgroup := by
      refine (Filter.eventually_all_finite hsfin).2 (fun x _ => ?_)
      have hopen : IsOpen {z : Z | (F x)⁻¹ * z ∈ V.toSubgroup} :=
        V.toOpenSubgroup.isOpen.preimage (continuous_const_mul _)
      exact (hF x).eventually (hopen.mem_nhds (by simp))
    obtain ⟨j, hj⟩ := hs.exists
    filter_upwards [hs] with i hi g
    have hC : IsClosed {z : Z | (f j g)⁻¹ * z ∈ V.toSubgroup} :=
      V.toOpenSubgroup.isClosed.preimage (continuous_const_mul _)
    have h1 : (f j g)⁻¹ * F g ∈ V.toSubgroup :=
      hC.mem_of_tendsto (hF g) (hs.mono fun k hk => agree V k j hk hj g)
    have h2 := agree V i j hi hj g
    have := V.toSubgroup.mul_mem (V.toSubgroup.inv_mem h1) h2
    convert this using 1
    group
  have hFc : Continuous F := by
    apply continuous_of_continuousAt_one F
    rw [ContinuousAt, map_one]
    intro W hW
    obtain ⟨t, htW, hto, h1t⟩ := mem_nhds_iff.1 hW
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hto h1t
    obtain ⟨i, hi⟩ := (key V).exists
    have hmem : {g : G | f i g ∈ V.toSubgroup} ∈ nhds (1 : G) :=
      (V.toOpenSubgroup.isOpen.preimage (hf i)).mem_nhds (by simp)
    refine Filter.mem_map.2 (Filter.mem_of_superset hmem (fun g hg => ?_))
    apply htW
    apply hV
    have := V.toSubgroup.mul_mem hg (V.toSubgroup.inv_mem (hi g))
    change F g ∈ V.toSubgroup
    convert this using 1
    group
  refine ⟨F, hFc, ?_, key, ?_⟩
  · intro g hg
    rw [MonoidHom.mem_ker]
    have hall : ∀ V : OpenNormalSubgroup Z, F g ∈ V.toSubgroup := by
      intro V
      let O : OpenNormalSubgroup G :=
        { toSubgroup := V.toSubgroup.comap F
          isOpen' := V.toOpenSubgroup.isOpen.preimage hFc
          isNormal' := V.isNormal'.comap F }
      rw [mem_limKer] at hg
      obtain ⟨i, hi1, hi2⟩ := ((hg O).and (key V)).exists
      have hle : K i ⊔ (O.toOpenSubgroup : Subgroup G) ≤ V.toSubgroup.comap (f i) := by
        refine sup_le ?_ ?_
        · intro x hx
          have hx' := hK i hx
          rw [MonoidHom.mem_ker] at hx'
          show f i x ∈ V.toSubgroup
          rw [hx']
          exact one_mem _
        · intro x hx
          have hx' : F x ∈ V.toSubgroup := hx
          show f i x ∈ V.toSubgroup
          have := V.toSubgroup.mul_mem hx' (hi2 x)
          convert this using 1
          group
      have hfg : f i g ∈ V.toSubgroup := hle hi1
      have := V.toSubgroup.mul_mem hfg (V.toSubgroup.inv_mem (hi2 g))
      convert this using 1
      group
    by_contra hne
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isOpen_compl_singleton (x := F g)) (Set.mem_compl_singleton_iff.2 (Ne.symm hne))
    exact hV (hall V) rfl
  · intro hsurj z
    have hcl : IsClosed (Set.range F) := (isCompact_range hFc).isClosed
    have hz : z ∈ closure (Set.range F) := by
      rw [mem_closure_iff_nhds]
      intro t ht
      have hW : (fun y => z * y) ⁻¹' t ∈ nhds (1 : Z) :=
        (continuous_const_mul z).continuousAt.preimage_mem_nhds (by rwa [mul_one])
      obtain ⟨u, huW, huo, h1u⟩ := mem_nhds_iff.1 hW
      obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one huo h1u
      obtain ⟨i, hi⟩ := (key V).exists
      obtain ⟨g, hg⟩ := hsurj i z
      refine ⟨F g, ?_, g, rfl⟩
      have hv : z⁻¹ * F g ∈ V.toSubgroup := by
        have := V.toSubgroup.inv_mem (hi g)
        rw [hg] at this
        convert this using 1
        group
      have := huW (hV hv)
      simpa using this
    rw [hcl.closure_eq] at hz
    exact hz
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_lim_elt :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal],
      (∀ a : ι → G, ∃ b : G, ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b⁻¹ * a i ∈ O.toSubgroup) ∧
      (∀ (a : ι → G) (b b' : G), (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b⁻¹ * a i ∈ K i ⊔ O.toSubgroup) →
        (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b'⁻¹ * a i ∈ K i ⊔ O.toSubgroup) → b⁻¹ * b' ∈ limKer (U : Filter ι) K) := by
  intro G ι _ _ _ _ _ U K _
  refine ⟨fun a => ?_, fun a b b' hb hb' => ?_⟩
  · obtain ⟨b, hl⟩ : ∃ b : G, Tendsto a (U : Filter ι) (nhds b) := by
      refine ⟨(U.map a).lim, ?_⟩
      have h' := (U.map a).le_nhds_lim
      rw [Ultrafilter.coe_map] at h'
      exact h'
    refine ⟨b, fun O => ?_⟩
    have hopen : IsOpen {y : G | b⁻¹ * y ∈ O.toSubgroup} :=
      O.toOpenSubgroup.isOpen.preimage (continuous_const_mul _)
    exact hl.eventually (hopen.mem_nhds (by simp))
  · rw [mem_limKer]
    intro O
    filter_upwards [hb O, hb' O] with i h1 h2
    have heq : b⁻¹ * b' = (b⁻¹ * a i) * (b'⁻¹ * a i)⁻¹ := by group
    rw [heq]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.cotInd_of_span :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (κ : Type) [Fintype κ] (x : κ → R),
      Ideal.span (Set.range x) = maximalIdeal R → Fintype.card κ ≤ (maximalIdeal R).spanFinrank → CotInd R x := by
  intro R _ _ _ κ _ x hx hcard
  have hm : ∀ k, x k ∈ maximalIdeal R := fun k => hx ▸ Ideal.subset_span ⟨k, rfl⟩
  refine (cotInd_iff R x).mpr ⟨hm, ?_⟩
  let g : κ → maximalIdeal R := fun k => ⟨x k, hm k⟩
  have hg : Submodule.span R (Set.range g) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hx
  have hV : Submodule.span (ResidueField R) (Set.range ((maximalIdeal R).toCotangent ∘ g)) = ⊤ := by
    rw [Set.range_comp, CotangentSpace.span_image_eq_top_iff]
    exact hg
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  have hle := finrank_range_le_card (R := ResidueField R) ((maximalIdeal R).toCotangent ∘ g)
  rw [Set.finrank, hV, finrank_top] at hle
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg] at hcard
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hV.ge (le_antisymm hcard hle)
end
