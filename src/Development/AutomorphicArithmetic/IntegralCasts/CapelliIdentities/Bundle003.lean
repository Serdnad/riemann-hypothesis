module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

section

theorem UpperTheory.semilinear_lattice_mem :
    ∀ (R K C V W : Type) [CommRing R] [Field K] [Field C] [Algebra R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup W] [Module C W] (e : K →+* C) (U : Submodule K V) (Φ : U →ₛₗ[e] W) (A : Set C) (L : AddSubgroup W) (G : Set V), (∀ a ∈ A, ∀ y ∈ L, a • y ∈ L) → (∀ r : R, e (algebraMap R K r) ∈ A) → (∀ g ∈ G, ∃ h : g ∈ U, Φ ⟨g, h⟩ ∈ L) → ∀ (s : R), algebraMap R K s ≠ 0 → e (algebraMap R K s)⁻¹ ∈ A → ∀ v : U, s • (v : V) ∈ Submodule.span R G → Φ v ∈ L := by
  intro R K C V W _ _ _ _ _ _ _ _ _ _ e U Φ A L G hA hR hG s hs hsA v hv
  have key : ∀ x ∈ Submodule.span R G, ∃ h : x ∈ U, Φ ⟨x, h⟩ ∈ L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hG x hx
    | zero =>
      refine ⟨U.zero_mem, ?_⟩
      have h0 : (⟨0, U.zero_mem⟩ : U) = 0 := rfl
      rw [h0, map_zero]
      exact L.zero_mem
    | add x y _ _ hx hy =>
      obtain ⟨hxU, hx⟩ := hx
      obtain ⟨hyU, hy⟩ := hy
      refine ⟨U.add_mem hxU hyU, ?_⟩
      have h0 : (⟨x + y, U.add_mem hxU hyU⟩ : U) = ⟨x, hxU⟩ + ⟨y, hyU⟩ := rfl
      rw [h0, map_add (f := _)]
      exact L.add_mem hx hy
    | smul r x _ hx =>
      obtain ⟨hxU, hx⟩ := hx
      have hm : r • x ∈ U := by
        rw [← algebraMap_smul K r x]
        exact U.smul_mem _ hxU
      refine ⟨hm, ?_⟩
      have h0 : (⟨r • x, hm⟩ : U) = algebraMap R K r • (⟨x, hxU⟩ : U) :=
        Subtype.ext (algebraMap_smul K r x).symm
      rw [h0, LinearMap.map_smulₛₗ]
      exact hA _ (hR r) _ hx
  obtain ⟨hU, hL⟩ := key _ hv
  have h1 : v = (algebraMap R K s)⁻¹ • (⟨s • (v : V), hU⟩ : U) := by
    apply Subtype.ext
    change (v : V) = (algebraMap R K s)⁻¹ • (s • (v : V))
    rw [← algebraMap_smul K s (v : V), inv_smul_smul₀ hs]
  rw [h1, LinearMap.map_smulₛₗ]
  exact hA _ hsA _ hL
end

section

theorem UpperTheory.Reformulated.B.PointFinitePower.ptFin_pow :
    ∀ {O S : Type} [inst : CommRing O] [inst_1 : CommRing S]
    [inst_2 : Algebra O S] [IsNoetherianRing S] (m : Ideal S),
    (∀ (x : S), ∃ (a : O), x - (Algebra.algebraMap O S : O → S) a ∈ m) →
      ∀ (n : ℕ), ∃ (N : Submodule O S), N.FG ∧ ∀ (x : S), ∃ y ∈ N, x - y ∈ m ^ n := by
  intro O S _ _ _ _ m hm n
  induction n with
  | zero =>
    refine ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := IsNoetherian.noetherian (m ^ n)
    have key : ∀ z : S, z ∈ Submodule.span S (s : Set S) →
        ∃ w ∈ Submodule.span O (s : Set S), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        exact ⟨z, Submodule.subset_span hz, by rw [sub_self]; exact Submodule.zero_mem _⟩
      | zero =>
        exact ⟨0, Submodule.zero_mem _, by rw [sub_self]; exact Submodule.zero_mem _⟩
      | add z z' _ _ h h' =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨w', hw', h'⟩ := h'
        refine ⟨w + w', Submodule.add_mem _ hw hw', ?_⟩
        have e : z + z' - (w + w') = (z - w) + (z' - w') := by ring
        rw [e]
        exact Submodule.add_mem _ h h'
      | smul c z hz h =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨a, ha⟩ := hm c
        refine ⟨a • w, Submodule.smul_mem _ a hw, ?_⟩
        have hz' : z ∈ m ^ n := by
          rw [← hs]
          exact hz
        have e : c • z - a • w
            = algebraMap O S a * (z - w) + z * (c - algebraMap O S a) := by
          rw [Algebra.smul_def a w, smul_eq_mul]
          ring
        rw [e]
        refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ h) ?_
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' ha
    refine ⟨N ⊔ Submodule.span O (s : Set S), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, h⟩ := key (x - y) hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rw [← sub_sub]
    exact h
end

section

theorem UpperTheory.Reformulated.B.ExistsEvaluation.exists_eval :
    ∀ {C Ω J : Type}
    [inst : CommRing C] [inst_1 : Field Ω] [Fintype J] (f : (J → C) →+* Ω),
    ∃ (j : J),
      ∀ (v : J → C), (f : (J → C) → Ω) v = (f : (J → C) → Ω) ((Algebra.algebraMap C (J → C) : C → J → C) (v j)) := by
  intro C Ω J _ _ _ f
  classical
  have hsum : ∑ j : J, f (Pi.single j 1) = 1 := by

    rw [← map_sum]
    have h : (∑ j : J, (Pi.single j (1 : C) : J → C)) = 1 := by
      simpa using Finset.univ_sum_single (1 : J → C)
    rw [h, map_one]
  obtain ⟨j, hj⟩ : ∃ j : J, f (Pi.single j 1) ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero (fun j _ => hne j)] at hsum
    exact zero_ne_one hsum
  have hidem : f (Pi.single j 1) * f (Pi.single j 1) = f (Pi.single j 1) := by
    rw [← map_mul]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  have hone : f (Pi.single j 1) = 1 := by
    exact mul_left_cancel₀ hj (by rw [hidem, mul_one])
  refine ⟨j, fun v => ?_⟩
  have hmul : v * Pi.single j 1 =
      (Algebra.algebraMap C (J → C) : C → J → C) (v j) * Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst hi; simp [Algebra.algebraMap_eq_smul_one]
    · simp [Pi.single_eq_of_ne hi]
  have h2 := congrArg f hmul
  simpa [map_mul, hone] using h2
end

section

theorem UpperTheory.Reformulated.B.Ydb6.main :
    ∀ {O Ω V : Type} [inst : CommRing O] [inst_1 : Field Ω] [inst_2 : Algebra O Ω] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module Ω V] (R : Subalgebra O Ω) (A B : AddSubgroup V) (c : Ω),
      (∀ (v : V), v ∈ B ↔ ∃ e ∈ A, v = c • e) →
        ∀ (v : V),
          v ∈ AddSubgroup.closure {v : V | ∃ a ∈ R, ∃ e ∈ B, v = a • e} ↔
            ∃ e ∈ AddSubgroup.closure {v : V | ∃ a ∈ R, ∃ e ∈ A, v = a • e}, v = c • e := by
  intro O Ω V _ _ _ _ _ R A B c hB v
  let f : V →+ V := DistribSMul.toAddMonoidHom V c
  have hS : {v : V | ∃ a ∈ R, ∃ e ∈ B, v = a • e} =
      f '' {v : V | ∃ a ∈ R, ∃ e ∈ A, v = a • e} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, e, he, rfl⟩
      obtain ⟨e', he', rfl⟩ := (hB e).1 he
      refine ⟨a • e', ⟨a, ha, e', he', rfl⟩, ?_⟩
      show c • a • e' = a • c • e'
      rw [smul_smul, smul_smul, mul_comm]
    · rintro ⟨x, ⟨a, ha, e, he, rfl⟩, rfl⟩
      refine ⟨a, ha, c • e, (hB _).2 ⟨e, he, rfl⟩, ?_⟩
      show c • a • e = a • c • e
      rw [smul_smul, smul_smul, mul_comm]
  rw [hS, ← AddMonoidHom.map_closure, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
end

section

noncomputable def UpperTheory.Reformulated.B.Qh70.Hs :
    {L V ι : Type} →
      [inst : Field L] →
        [inst_1 : Algebra ℂ L] →
          [inst_2 : AddCommGroup V] → [_root_.Module L V] → Subalgebra ℂ L → Finset ι → (ι → V) → V → Prop :=
    fun {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [_root_.Module L V] (B : Subalgebra ℂ L) (P : Finset ι)
        (g : ι → V) (w : V) ↦
      ∃ (c : ι → L), (∀ (S : ι), c S ∈ B) ∧ w = ∑ S ∈ P, c S • g S

theorem UpperTheory.Reformulated.B.Qh70.Hs_sum :
    ∀ {L V ι : Type} [inst : Field L] [inst_1 : Algebra ℂ L] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module L V]
      {B : Subalgebra ℂ L} {P : Finset ι} {g : ι → V} {α : Type} (s : Finset α) (f : α → V),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qh70.Hs B P g (f a)) → UpperTheory.Reformulated.B.Qh70.Hs B P g (∑ a ∈ s, f a) := by
  intro L V ι _ _ _ _ B P g α s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh70.Hs B P g) ?_ ?_ h
  · rintro a b ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨fun S => c S + d S, fun S => B.add_mem (hc S) (hd S), ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
  · exact ⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩
end

section

open Polynomial in
private lemma spectrum_nonempty_of_countable_rank {V : Type} [AddCommGroup V] [_root_.Module ℂ V]
    [Nontrivial V] (hV : Module.rank ℂ V ≤ Cardinal.aleph0) (T : Module.End ℂ V) :
    (spectrum ℂ T).Nonempty := by
  classical
  by_contra hne
  have hunit : ∀ a : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) a) := fun a => by
    have h : a ∉ spectrum ℂ T := fun h => hne ⟨a, h⟩
    rw [spectrum.notMem_iff] at h
    exact IsUnit.sub_iff.mp h
  have hR : ∀ a : ℂ, ∃ R : Module.End ℂ V, (T - algebraMap ℂ (Module.End ℂ V) a) * R = 1 :=
    fun a => (hunit a).exists_right_inv
  choose R hR using hR
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hdep : ¬ LinearIndependent ℂ (fun a : ℂ => R a v) := by
    intro hli
    have h1 := hli.cardinal_le_rank
    rw [Cardinal.mk_complex] at h1
    exact absurd (h1.trans hV) (not_le.mpr Cardinal.aleph0_lt_continuum)
  rw [linearIndependent_iff'] at hdep
  push_neg at hdep
  obtain ⟨s, m, hm, i, hi, hmi⟩ := hdep
  let q : ℂ → ℂ[X] := fun a => ∏ j ∈ s.erase a, (X - C j)
  let p : ℂ[X] := ∑ a ∈ s, C (m a) * q a
  have key : ∀ a ∈ s, aeval T (∏ j ∈ s, (X - C j)) * R a = aeval T (q a) := by
    intro a ha
    rw [← Finset.prod_erase_mul s _ ha, map_mul, mul_assoc]
    have : aeval T (X - C a) = T - algebraMap ℂ (Module.End ℂ V) a := by simp
    rw [this, hR, mul_one]
  have hp : aeval T p v = 0 := by
    have h1 := congrArg (aeval T (∏ j ∈ s, (X - C j))) hm

    rw [map_zero, map_sum] at h1
    rw [← h1]

    simp only [p, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_mul, aeval_C, ← key a ha, map_smul]
    simp [Module.End.mul_apply, Module.algebraMap_end_apply]
  have hp0 : p ≠ 0 := by
    intro h0
    have h1 : eval i p = m i * ∏ j ∈ s.erase i, (i - j) := by
      simp only [p, Polynomial.eval_finsetSum, eval_mul, eval_C]
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [q, eval_prod]
      · intro b hb hbi
        have : eval i (q b) = 0 := by
          simp only [q, eval_prod]
          refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hbi.symm, hi⟩) (by simp)
        rw [this, mul_zero]
    rw [h0, eval_zero] at h1
    have h2 : ∏ j ∈ s.erase i, (i - j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (Finset.ne_of_mem_erase hj).symm
    exact (mul_ne_zero hmi h2) h1.symm
  have hnu : ¬ IsUnit (aeval T p) := by
    intro hu
    have hinj := ((Module.End.isUnit_iff _).mp hu).injective
    exact hv (hinj (by rw [hp, map_zero]))
  have hprod := (IsAlgClosed.splits p).eq_prod_roots
  have lead_ne := leadingCoeff_ne_zero.mpr hp0
  have lead_unit : IsUnit (algebraMap ℂ (Module.End ℂ V) p.leadingCoeff) :=
    (Units.map (algebraMap ℂ (Module.End ℂ V)).toMonoidHom (Units.mk0 _ lead_ne)).isUnit
  rw [hprod, aeval_mul, ((Commute.all _ _).map (aeval T : ℂ[X] →ₐ[ℂ] _)).isUnit_mul_iff,
    aeval_C] at hnu
  obtain ⟨k, hk, -⟩ := spectrum.exists_mem_of_not_isUnit_aeval_prod (not_and.mp hnu lead_unit)
  exact hne ⟨k, hk⟩

theorem UpperTheory.Reformulated.B.DYhd6.main :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] [Nontrivial V],
      Module.rank ℂ V ≤ Cardinal.aleph0 →
        ∀ (B : Subalgebra ℂ (Module.End ℂ V)),
          (∀ (N : Submodule ℂ V), (∀ b ∈ B, ∀ x ∈ N, (b : V → V) x ∈ N) → N = ⊥ ∨ N = ⊤) →
            ∀ (f : Module.End ℂ V) (s : Finset V), ∃ b ∈ B, ∀ m ∈ s, (f : V → V) m = (b : V → V) m := by
  intro V _ _ _ hV B hB f s
  have hsc : ∀ (c : ℂ) (x : V), c • x = (algebraMap ℂ B c) • x := fun c x => by
    change c • x = ((algebraMap ℂ (Module.End ℂ V) c : Module.End ℂ V)) x
    simp [Module.algebraMap_end_apply]
  have hbc : ∀ (b : B) (c : ℂ) (x : V), b • (c • x) = c • (b • x) := fun b c x =>
    (b : Module.End ℂ V).map_smul c x
  haveI hsimple : IsSimpleModule B V :=
    { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩
      eq_bot_or_eq_top := fun N => by
        let N' : Submodule ℂ V :=
          { carrier := N
            add_mem' := fun h1 h2 => N.add_mem h1 h2
            zero_mem' := N.zero_mem
            smul_mem' := fun c x hx => by
              rw [hsc]
              exact N.smul_mem _ hx }
        rcases hB N' (fun b hb x hx => N.smul_mem (⟨b, hb⟩ : B) hx) with h | h
        · left
          rw [eq_bot_iff]
          intro x hx
          have : x ∈ N' := hx
          rw [h] at this
          simpa using this
        · right
          rw [eq_top_iff]
          intro x _
          have : x ∈ N' := by rw [h]; trivial
          exact this }
  have hscal : ∀ d : Module.End B V, ∃ a : ℂ, ∀ x, d x = a • x := by
    intro d
    let T : Module.End ℂ V :=
      { toFun := d
        map_add' := d.map_add
        map_smul' := fun c x => by
          simp only [RingHom.id_apply]
          rw [hsc, d.map_smul, ← hsc] }
    obtain ⟨a, ha⟩ := spectrum_nonempty_of_countable_rank hV T
    let e : V →ₗ[B] V :=
      { toFun := fun x => a • x - d x
        map_add' := fun x y => by
          rw [smul_add, map_add d x y]
          abel
        map_smul' := fun b x => by
          simp only [RingHom.id_apply]
          rw [d.map_smul, smul_sub, hbc] }
    rcases LinearMap.bijective_or_eq_zero e with hb | h0
    · exfalso
      apply ha
      rw [spectrum.mem_resolventSet_iff, Module.End.isUnit_iff]
      have hfe : ⇑(algebraMap ℂ (Module.End ℂ V) a - T) = ⇑e := by
        funext x
        simp [T, e, Module.algebraMap_end_apply]
      rw [hfe]
      exact hb
    · refine ⟨a, fun x => ?_⟩
      have : a • x - d x = 0 := congrArg (fun g : V →ₗ[B] V => g x) h0
      exact (sub_eq_zero.mp this).symm
  let F : Module.End (Module.End B V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun d x => by
        obtain ⟨a, ha⟩ := hscal d
        simp only [RingHom.id_apply, Module.End.smul_def]
        rw [ha, ha, f.map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, r.2, fun m hm => hr m hm⟩
end

section

theorem UpperTheory.Reformulated.B.Ra7.exists_span_mod_sq :
    ∀ {O R K : Type} [inst : CommRing O]
    [inst_1 : CommRing R] [inst_2 : Algebra O R] [IsNoetherianRing R] [inst_4 : CommRing K] [inst_5 : Algebra O K]
    (y : R →ₐ[O] K),
    Module.Finite O ↥y.range →
      ∃ (s : Finset R), ∀ (a : R), ∃ b ∈ Submodule.span O (↑s : Set R), a - b ∈ RingHom.ker y ^ (2 : ℕ) := by
  intro O R K _ _ _ _ _ _ y hfin
  classical
  obtain ⟨t', ht'⟩ := hfin.fg_top
  have hsurj : Function.Surjective y.rangeRestrict := y.rangeRestrict_surjective
  obtain ⟨σ, hσ⟩ := hsurj.hasRightInverse
  obtain ⟨g, hg⟩ : (RingHom.ker y).FG := IsNoetherian.noetherian _
  let t : Finset R := t'.image σ
  have h1 : ∀ a : R, ∃ b ∈ Submodule.span O (↑t : Set R), a - b ∈ RingHom.ker y := by
    intro a
    have hm : Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R)) = ⊤ := by
      rw [Submodule.map_span, eq_top_iff, ← ht']
      apply Submodule.span_mono
      intro z hz
      exact ⟨σ z, Finset.mem_coe.2 (Finset.mem_image_of_mem σ hz), hσ z⟩
    have hz : y.rangeRestrict a ∈
        Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R)) := by
      rw [hm]; exact Submodule.mem_top
    obtain ⟨b, hb, hab⟩ := hz
    refine ⟨b, hb, ?_⟩
    have hab' : y b = y a := congrArg Subtype.val hab
    rw [RingHom.mem_ker, map_sub, hab', sub_self]
  let s : Finset R := t ∪ Finset.image₂ (· * ·) t g
  have h2 : ∀ x ∈ g, ∀ b ∈ Submodule.span O (↑t : Set R),
      b * x ∈ Submodule.span O (↑s : Set R) := by
    intro x hx b hb
    induction hb using Submodule.span_induction with
    | mem z hz =>
      exact Submodule.subset_span (Finset.mem_coe.2
        (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hz hx)))
    | zero => rw [zero_mul]; exact zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
    | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  have h3 : ∀ x ∈ Ideal.span (↑g : Set R), ∀ r : R,
      ∃ b ∈ Submodule.span O (↑s : Set R), r * x - b ∈ RingHom.ker y ^ (2 : ℕ) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      intro r
      obtain ⟨b, hb, hrb⟩ := h1 r
      refine ⟨b * z, h2 z hz b hb, ?_⟩
      have hzI : z ∈ RingHom.ker y := by
        rw [← hg]; exact Ideal.subset_span hz
      rw [← sub_mul, pow_two]
      exact Ideal.mul_mem_mul hrb hzI
    | zero => intro r; exact ⟨0, zero_mem _, by rw [mul_zero, sub_zero]; exact zero_mem _⟩
    | add u v _ _ hu hv =>
      intro r
      obtain ⟨b, hb, hb'⟩ := hu r
      obtain ⟨c, hc, hc'⟩ := hv r
      refine ⟨b + c, add_mem hb hc, ?_⟩
      have e : r * (u + v) - (b + c) = (r * u - b) + (r * v - c) := by ring
      rw [e]; exact add_mem hb' hc'
    | smul c u _ hu =>
      intro r
      rw [smul_eq_mul, ← mul_assoc]
      exact hu (r * c)
  refine ⟨s, fun a => ?_⟩
  obtain ⟨b, hb, hab⟩ := h1 a
  obtain ⟨c, hc, hc'⟩ := h3 (a - b) (by rw [hg]; exact hab) 1
  refine ⟨b + c, add_mem (Submodule.span_mono ?_ hb) hc, ?_⟩
  · exact Finset.coe_subset.2 Finset.subset_union_left
  · have e : a - (b + c) = 1 * (a - b) - c := by ring
    rw [e]; exact hc'
end

section

theorem UpperTheory.Reformulated.B.Qf48.isLC_prod {X : Type*} {ι : Type*} [TopologicalSpace X] (T : Finset ι) (f : ι → X → ℂ)
    (h : ∀ i ∈ T, IsLocallyConstant (f i)) : IsLocallyConstant fun x ↦ ∏ i ∈ T, f i x := by
  classical
  induction T using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end
