module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.SimpleModule.Basic

@[expose] public section

section

open Polynomial

namespace GlobalTheory.CommSemisimpleChars


open Classical in
theorem card_eq_of_sum_eq {H ι κ : Type} [Monoid H] [Fintype ι] [Fintype κ]
    (a : ι → (H →* ℂ)) (c : κ → (H →* ℂ)) (h : ∀ g, ∑ j, a j g = ∑ i, c i g) (ψ : H →* ℂ) :
    (Finset.univ.filter fun j => a j = ψ).card = (Finset.univ.filter fun i => c i = ψ).card := by
  classical
  let F : Finset (H →* ℂ) := insert ψ (Finset.univ.image a ∪ Finset.univ.image c)
  have li := linearIndependent_iff'.1 (linearIndependent_monoidHom H ℂ) F
    (fun φ => ((Finset.univ.filter fun j => a j = φ).card : ℂ) - (Finset.univ.filter fun i => c i = φ).card)
  have key : ∀ {τ : Type} [Fintype τ] (e : τ → (H →* ℂ)), (∀ t, e t ∈ F) →
      ∑ φ ∈ F, ((Finset.univ.filter fun t => e t = φ).card : ℂ) • (φ : H → ℂ) = ∑ t, (e t : H → ℂ) := by
    intro τ _ e he
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := F) (g := e) (fun t _ => he t)]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
  have hz : ∑ φ ∈ F, (((Finset.univ.filter fun j => a j = φ).card : ℂ) -
      (Finset.univ.filter fun i => c i = φ).card) • (φ : H → ℂ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [key a (fun j => by simp [F]), key c (fun i => by simp [F]), sub_eq_zero]
    funext g
    simp only [Finset.sum_apply]
    exact h g
  have := li hz ψ (Finset.mem_insert_self _ _)
  exact_mod_cast sub_eq_zero.1 this

end GlobalTheory.CommSemisimpleChars
end

section

namespace GlobalTheory

private lemma exists_pos_pow_mul_pow_eq_pow_of_finite {S : Type} [Monoid S] [Finite S] (a : S) :
    ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M := by
  have key : ∀ i j : ℕ, i < j → a ^ i = a ^ j → ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M := by
    intro i j hij h
    obtain ⟨p, rfl⟩ : ∃ p, j = i + (p + 1) := ⟨j - i - 1, by omega⟩
    have step : ∀ n, a ^ (i + n + (p + 1)) = a ^ (i + n) := by
      intro n
      rw [show i + n + (p + 1) = n + (i + (p + 1)) by ring, pow_add, ← h, ← pow_add,
        show n + i = i + n by ring]
    have rep : ∀ k n, a ^ (i + n + k * (p + 1)) = a ^ (i + n) := by
      intro k
      induction k with
      | zero => intro n; simp
      | succ k ih =>
        intro n
        rw [show i + n + (k + 1) * (p + 1) = i + (n + k * (p + 1)) + (p + 1) by ring, step,
          ← add_assoc, ih]
    refine ⟨(i + 1) * (p + 1), by positivity, ?_⟩
    rw [← pow_add]
    have hr := rep (i + 1) (i * p + p + 1)
    rwa [show i + (i * p + p + 1) + (i + 1) * (p + 1) = (i + 1) * (p + 1) + (i + 1) * (p + 1) by ring,
      show i + (i * p + p + 1) = (i + 1) * (p + 1) by ring] at hr
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt h
  · exact key j i hlt h.symm

theorem finite_involution_hilbert90 {S : Type} [CommRing S] [Finite S] (c : S →+* S)
    (hc : ∀ x, c (c x) = x) (ω : S) (hω : IsUnit (ω - c ω)) (y : S) (hy : y * c y = 1) :
    ∃ x : S, IsUnit x ∧ x = y * c x := by
  have hyu : IsUnit y := ⟨⟨y, c y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  obtain ⟨M, hM0, hM⟩ := exists_pos_pow_mul_pow_eq_pow_of_finite ((1 + y) * c (1 + y))
  obtain ⟨e, he⟩ : ∃ e, e = ((1 + y) * c (1 + y)) ^ M := ⟨_, rfl⟩
  rw [← he] at hM
  have hce : c e = e := by
    rw [he, map_pow, map_mul, hc, mul_comm]
  have h1 : y * c (1 + y) = 1 + y := by
    rw [map_add (f := _), map_one]; linear_combination hy
  refine ⟨e * (1 + y) + (1 - e) * (ω + y * c ω), ?_, ?_⟩
  · by_contra hx
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
    have hp := hm.isPrime
    have hnot : y * (ω - c ω) ∉ m := fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem m h (hyu.mul hω))
    have hid : ω * (1 + y) - (ω + y * c ω) = y * (ω - c ω) := by ring
    have hex : e ∈ m → 1 + y ∈ m := by
      intro h
      rw [he] at h
      rcases hp.mem_or_mem (hp.mem_of_pow_mem M h) with h' | h'
      · exact h'
      · rw [← h1]; exact m.mul_mem_left y h'
    by_cases hem : e ∈ m
    · have hx1 : 1 + y ∈ m := hex hem
      have h2 : (1 - e) * (ω + y * c ω) ∈ m := by
        have hr : (1 - e) * (ω + y * c ω)
            = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - e * (1 + y) := by ring
        rw [hr]; exact m.sub_mem hxm (m.mul_mem_right _ hem)
      have h1e : 1 - e ∉ m := by
        intro h
        apply hm.ne_top
        rw [Ideal.eq_top_iff_one]
        have hs := m.add_mem hem h
        rwa [add_sub_cancel] at hs
      have hxω : ω + y * c ω ∈ m := (hp.mem_or_mem h2).resolve_left h1e
      apply hnot
      rw [← hid]
      exact m.sub_mem (m.mul_mem_left ω hx1) hxω
    · have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hM, sub_self]
      have h1e : 1 - e ∈ m := by
        refine (hp.mem_or_mem ?_).resolve_left hem
        rw [hee]; exact m.zero_mem
      have h2 : e * (1 + y) ∈ m := by
        have hr : e * (1 + y)
            = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - (1 - e) * (ω + y * c ω) := by ring
        rw [hr]; exact m.sub_mem hxm (m.mul_mem_right _ h1e)
      have hx1 : 1 + y ∈ m := (hp.mem_or_mem h2).resolve_left hem
      apply hem
      rw [he]
      exact Ideal.pow_mem_of_mem m (m.mul_mem_right _ hx1) M hM0
  · simp only [map_add (f := _), map_mul, map_sub, map_one, hc, hce]
    linear_combination (-(e + (1 - e) * ω)) * hy

theorem finite_involution_fixed_unit_isNorm :
    ∀ (S : Type) [CommRing S] [Finite S] (c : S →+* S), (∀ x, c (c x) = x) →
      (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  intro S _ _ c hc hω u hcu hu
  obtain ⟨ω, hω⟩ := hω
  let cu : Sˣ →* Sˣ := Units.map (c : S →* S)
  have hcuv : ∀ x : Sˣ, ((cu x : Sˣ) : S) = c x := fun x => rfl
  have hcc : ∀ x : Sˣ, cu (cu x) = x := fun x => Units.ext (by rw [hcuv, hcuv, hc])
  let N : Sˣ →* Sˣ := MonoidHom.id Sˣ * cu
  let ψ : Sˣ →* Sˣ := MonoidHom.id Sˣ / cu
  have hN : ∀ x, N x = x * cu x := fun x => rfl
  have hψ : ∀ x, ψ x = x / cu x := fun x => MonoidHom.div_apply _ _ x
  have hker : N.ker ≤ ψ.range := by
    intro y hy
    rw [MonoidHom.mem_ker, hN] at hy
    have hy' : (y : S) * c y = 1 := by
      have := congrArg Units.val hy
      rwa [Units.val_mul, hcuv, Units.val_one] at this
    obtain ⟨x, hxu, hx⟩ := finite_involution_hilbert90 c hc ω hω y hy'
    refine ⟨hxu.unit, ?_⟩
    rw [hψ, div_eq_iff_eq_mul]
    exact Units.ext (by rw [Units.val_mul, hcuv, IsUnit.unit_spec]; exact hx)
  have hrange : N.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, hψ, div_eq_one, hN, map_mul, hcc, mul_comm]
  have hcard : Nat.card ψ.ker ≤ Nat.card N.range := by
    have e1 := N.ker.card_mul_index
    have e2 := ψ.ker.card_mul_index
    rw [Subgroup.index_ker] at e1 e2
    have hle : Nat.card N.ker ≤ Nat.card ψ.range := Subgroup.card_le_of_le hker
    have hpos : 0 < Nat.card ψ.range := Nat.card_pos
    have h3 : Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card N.range * Nat.card ψ.range := by
      rw [e2, ← e1, mul_comm (Nat.card N.range)]
      exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have heq : N.range = ψ.ker := Subgroup.eq_of_le_of_card_ge hrange hcard
  have hmem : hu.unit ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hψ, div_eq_one]
    exact Units.ext (by rw [hcuv, IsUnit.unit_spec, hcu])
  rw [← heq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  have := congrArg Units.val hx
  rwa [hN, Units.val_mul, hcuv, IsUnit.unit_spec] at this

end GlobalTheory
end

section

universe u_1 u_2 u_3

namespace GlobalTheory.IntertwiningFunctional

private theorem freeAlgebra_lift_intertwine {K : Type u_1} {F : Type u_2} {V : Type u_3}
    [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V) (T : V →ₗ[ℂ] F)
    (hT : ∀ (k : K) (v : V), T (ρ k v) = r k (T v)) (a : FreeAlgebra ℂ K) :
    ∀ v : V, T (FreeAlgebra.lift ℂ ρ a v) = FreeAlgebra.lift ℂ r a (T v) := by
  induction a using FreeAlgebra.induction with
  | grade0 c => intro v; simp [AlgHom.commutes, Module.algebraMap_end_apply]
  | grade1 k => intro v; simp [FreeAlgebra.lift_ι_apply, hT]
  | mul a b ha hb => intro v; simp only [map_mul, Module.End.mul_apply]; rw [ha, hb]
  | add a b ha hb => intro v; simp only [map_add (f := _), LinearMap.add_apply]; rw [ha, hb]

theorem exists_intertwining_functional {K : Type u_1} {F : Type u_2} {V : Type u_3}
    [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V)
    (hirr : ∀ (W : Submodule ℂ V), (∀ (k : K), ∀ v ∈ W, ρ k v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : (V →ₗ[ℂ] F) → Prop)
    (hP : ∀ (T : V →ₗ[ℂ] F), P T → ∀ (k : K) (v : V), T (ρ k v) = r k (T v)) :
    ∀ f ∈ ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T, f ≠ (0 : F) →
      ∃ (φ : F →ₗ[ℂ] V), φ f ≠ (0 : V) ∧ ∀ (k : K),
        ∀ f' ∈ ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T,
          φ (r k f') = ρ k (φ f') := by
  classical
  intro f hf hf0
  set S := ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T with hSdef

  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply hf0
    have hS : S = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun T _ => ?_)
      rintro _ ⟨v, rfl⟩
      rw [Subsingleton.elim v 0, map_zero]
      exact Submodule.zero_mem _
    rw [hS, Submodule.mem_bot] at hf
    exact hf

  let A := FreeAlgebra ℂ K
  let rA : A →ₐ[ℂ] Module.End ℂ F := FreeAlgebra.lift ℂ r
  let ρA : A →ₐ[ℂ] Module.End ℂ V := FreeAlgebra.lift ℂ ρ
  let : Module A F := Module.compHom F rA.toRingHom
  let : Module A V := Module.compHom V ρA.toRingHom
  have smulF : ∀ (a : A) (x : F), a • x = rA a x := fun _ _ => rfl
  have smulV : ∀ (a : A) (x : V), a • x = ρA a x := fun _ _ => rfl
  have : IsScalarTower ℂ A F := ⟨fun c a x => by
    rw [smulF, smulF, map_smul, LinearMap.smul_apply]⟩
  have : IsScalarTower ℂ A V := ⟨fun c a x => by
    rw [smulV, smulV, map_smul, LinearMap.smul_apply]⟩
  have hιF : ∀ (k : K) (x : F), (FreeAlgebra.ι ℂ k : A) • x = r k x := fun k x => by
    show FreeAlgebra.lift ℂ r (FreeAlgebra.ι ℂ k) x = r k x
    rw [FreeAlgebra.lift_ι_apply]
  have hιV : ∀ (k : K) (v : V), (FreeAlgebra.ι ℂ k : A) • v = ρ k v := fun k v => by
    show FreeAlgebra.lift ℂ ρ (FreeAlgebra.ι ℂ k) v = ρ k v
    rw [FreeAlgebra.lift_ι_apply]

  have hVs : IsSimpleModule A V := by
    refine { toNontrivial := inferInstance, eq_bot_or_eq_top := fun W => ?_ }
    have hWinv : ∀ (k : K), ∀ v ∈ W.restrictScalars ℂ, ρ k v ∈ W.restrictScalars ℂ := by
      intro k v hv
      rw [← hιV]
      exact W.smul_mem _ hv
    rcases hirr (W.restrictScalars ℂ) hWinv with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)

  let mkA : ∀ T : V →ₗ[ℂ] F, (∀ (k : K) (v : V), T (ρ k v) = r k (T v)) → V →ₗ[A] F :=
    fun T hT =>
      { toFun := T
        map_add' := T.map_add
        map_smul' := fun a v => freeAlgebra_lift_intertwine r ρ T hT a v }
  let p : (V →ₗ[ℂ] F) → Submodule A F := fun T =>
    if h : ∀ (k : K) (v : V), T (ρ k v) = r k (T v) then LinearMap.range (mkA T h) else ⊥
  let s : Set (V →ₗ[ℂ] F) := {T | P T}
  let SA : Submodule A F := ⨆ T ∈ s, p T
  have hpT : ∀ T (hT : T ∈ s), p T = LinearMap.range (mkA T (hP T hT)) :=
    fun T hT => dif_pos (hP T hT)
  have hpSA : ∀ T (hT : T ∈ s), p T ≤ SA := fun T hT =>
    le_iSup₂ (f := fun T (_ : T ∈ s) => p T) T hT
  have memSA : ∀ x : F, x ∈ S ↔ x ∈ SA := by
    intro x
    constructor
    · intro hx
      have hle : S ≤ SA.restrictScalars ℂ := by
        refine iSup₂_le fun T hT => ?_
        rintro _ ⟨v, rfl⟩
        have h1 : T v ∈ p T := by
          rw [hpT T hT]
          exact ⟨v, rfl⟩
        exact hpSA T hT h1
      exact hle hx
    · intro hx
      refine Submodule.iSup_induction (fun T => ⨆ (_ : T ∈ s), p T) (motive := fun y => y ∈ S)
        hx ?_ (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _)
      intro T y hy
      by_cases hT : T ∈ s
      · have hy' : y ∈ p T := (iSup_le fun _ => le_rfl : (⨆ (_ : T ∈ s), p T) ≤ p T) hy
        rw [hpT T hT] at hy'
        obtain ⟨v, rfl⟩ := hy'
        exact (le_iSup₂ (f := fun T (_ : P T) => LinearMap.range T) T hT : _ ≤ S) ⟨v, rfl⟩
      · rw [iSup_neg hT, Submodule.mem_bot] at hy
        rw [hy]
        exact Submodule.zero_mem _

  have : IsSemisimpleModule A SA :=
    isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (fun T hT => by
      rw [hpT T hT]
      exact IsSemisimpleModule.range _)
  let f₀ : SA := ⟨f, (memSA f).mp hf⟩
  have hf₀ : f₀ ≠ 0 := fun h => hf0 (congrArg Subtype.val h)

  obtain ⟨m, hmN, hm⟩ : ∃ m ≤ Submodule.span A {f₀}, IsSimpleModule A m := by
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (Submodule.span A {f₀}) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hf₀
    · exact h
  have := hm
  have : Nontrivial m := IsSimpleModule.nontrivial A m
  obtain ⟨q, hq⟩ := exists_isCompl m
  let π : SA →ₗ[A] m := Submodule.projectionOnto m q hq
  have hπleft : ∀ y : m, π y = y := fun y => Submodule.projectionOnto_apply_left hq y
  have hπf : π f₀ ≠ 0 := by
    intro h0
    have hNk : Submodule.span A {f₀} ≤ LinearMap.ker π := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact h0
    obtain ⟨y, hy0⟩ := exists_ne (0 : m)
    apply hy0
    have hyk : (y : SA) ∈ LinearMap.ker π := hNk (hmN y.2)
    rw [LinearMap.mem_ker, hπleft] at hyk
    exact hyk

  have hmemT : ∀ T (hT : T ∈ s) (v : V), mkA T (hP T hT) v ∈ SA := fun T hT v =>
    hpSA T hT (by rw [hpT T hT]; exact ⟨v, rfl⟩)
  obtain ⟨T, hT, hg⟩ : ∃ T, ∃ hT : T ∈ s,
      π ∘ₗ LinearMap.codRestrict SA (mkA T (hP T hT)) (hmemT T hT) ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hπf
    have hle : SA ≤ (LinearMap.ker π).map SA.subtype := by
      refine iSup₂_le fun T hT => ?_
      rw [hpT T hT]
      rintro _ ⟨v, rfl⟩
      refine ⟨LinearMap.codRestrict SA (mkA T (hP T hT)) (hmemT T hT) v, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, ← LinearMap.comp_apply, hne T hT, LinearMap.zero_apply]
    obtain ⟨y, hy, hyf⟩ := hle f₀.2
    have hyeq : y = f₀ := Subtype.ext hyf
    rw [← hyeq]
    exact hy
  let e : V ≃ₗ[A] m := LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hg)
  let φ₀ : SA →ₗ[A] V := e.symm.toLinearMap ∘ₗ π
  have hφ₀f : φ₀ f₀ ≠ 0 := by
    intro h
    apply hπf
    have h1 : e (φ₀ f₀) = π f₀ := e.apply_symm_apply (π f₀)
    rw [← h1, h, map_zero]

  let ψ : S →ₗ[ℂ] V :=
    { toFun := fun x => φ₀ ⟨x.1, (memSA x.1).mp x.2⟩
      map_add' := fun x y => by
        rw [← map_add (f := _)]
        rfl
      map_smul' := fun c x => by
        have h1 : (⟨c • x.1, (memSA _).mp (S.smul_mem c x.2)⟩ : SA) =
            algebraMap ℂ A c • (⟨x.1, (memSA _).mp x.2⟩ : SA) :=
          Subtype.ext (algebraMap_smul (A := A) c x.1).symm
        show φ₀ ⟨c • x.1, (memSA _).mp (S.smul_mem c x.2)⟩ = c • φ₀ ⟨x.1, (memSA _).mp x.2⟩
        rw [h1, map_smul, algebraMap_smul] }
  obtain ⟨φ, hφext⟩ := LinearMap.exists_extend ψ
  have hφ : ∀ (x : F) (hx : x ∈ S), φ x = φ₀ ⟨x, (memSA x).mp hx⟩ := fun x hx =>
    LinearMap.congr_fun hφext ⟨x, hx⟩
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ f hf]
    exact hφ₀f
  · intro k x hx
    have hrk : r k x = (FreeAlgebra.ι ℂ k : A) • x := (hιF k x).symm
    have hmem : r k x ∈ S := by
      rw [memSA, hrk]
      exact SA.smul_mem _ ((memSA _).mp hx)
    rw [hφ _ hmem, hφ _ hx, ← hιV k, ← map_smul φ₀]
    congr 1
    exact Subtype.ext hrk

end GlobalTheory.IntertwiningFunctional
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

def FibrePointsLE {Z X : Scheme.{0}} (f : Z ⟶ X) (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ X) (s : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z)),
    (∀ j, s j ≫ f = y) → ¬ Function.Injective s

def diagCompl {Z X : Scheme.{0}} (f : Z ⟶ X) [IsSeparated f] : (pullback f f).Opens :=
  ⟨(Set.range (pullback.diagonal f))ᶜ, (pullback.diagonal f).isClosedEmbedding.isClosed_range.isOpen_compl⟩

def diagComplHom {Z X : Scheme.{0}} (f : Z ⟶ X) [IsSeparated f] : (diagCompl f).toScheme ⟶ Z :=
  (diagCompl f).ι ≫ pullback.snd f f

end GlobalTheory.EtC.Tr
end
end

section

open MeasureTheory

namespace GlobalTheory

section
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] {μ : Measure H} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H}


omit [μ.IsMulLeftInvariant] [Countable Γ] in
theorem isFundamentalDomain_image_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) '' 𝓕) μ := by
  refine h𝓕.image_of_equiv (Equiv.mulRight y) ?_ (Equiv.refl _) ?_
  · exact (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
  · intro γ h
    simp [Subgroup.smul_def, mul_assoc]

theorem setIntegral_fundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H)
    (u : H → ℂ) (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
  rw [h𝓕.setIntegral_eq (isFundamentalDomain_image_mul_right h𝓕 y) (f := u)
    (fun γ h => hu γ γ.2 h)]
  exact ((measurePreserving_mul_right μ y).setIntegral_image_emb
    (measurableEmbedding_mulRight y) u 𝓕).symm

theorem integrableOn_fundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H)
    (u : H → ℂ) (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (hi : IntegrableOn u 𝓕 μ) :
    IntegrableOn (fun h => u (h * y)) 𝓕 μ := by
  rw [h𝓕.integrableOn_iff (isFundamentalDomain_image_mul_right h𝓕 y) (f := u)
    (fun γ h => hu γ γ.2 h)] at hi
  exact ((measurePreserving_mul_right μ y).integrableOn_image
    (measurableEmbedding_mulRight y)).1 hi

end

end GlobalTheory
end
