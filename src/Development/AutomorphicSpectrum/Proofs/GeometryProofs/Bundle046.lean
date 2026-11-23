module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle034
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.Data.Fintype.Order
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem dual_pull : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (ω : Submodule R (Module.Dual Ω V)) (ω' : Submodule R' (Module.Dual Ω' V')) (r : ℕ) (b : Fin r → Module.Dual Ω W), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (0 < r → ω' = Submodule.span R' (jd '' (ω : Set (Module.Dual Ω V)))) → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = ⊤ → ω.map (W.dualRestrict.restrictScalars R) = Submodule.span R (Set.range b) → Submodule.span R' {e | e ∈ W' ∧ ∀ w ∈ ω', w e ∈ R'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} : Set V)) := by
  intro Ω Ω' _ _ i R R' V V' _ _ _ _ j jd W W' ω ω' r b hj hR hjd hW' hω' hli hsp hmap
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hD : ∀ f : Module.Dual Ω W, f = 0 := by
      intro f
      have hf : f ∈ Submodule.span Ω (Set.range b) := hsp ▸ Submodule.mem_top
      rw [Set.range_eq_empty, Submodule.span_empty] at hf
      exact (Submodule.mem_bot Ω).1 hf
    have hW0 : ∀ e ∈ W, e = 0 := by
      intro e he
      have : (⟨e, he⟩ : W) = 0 :=
        (Module.forall_dual_apply_eq_zero_iff Ω _).1 fun f => by rw [hD f]; rfl
      exact congrArg Subtype.val this
    have hW'0 : W' = ⊥ := by
      rw [hW', Submodule.span_eq_bot]
      rintro _ ⟨e, he, rfl⟩
      rw [hW0 e he, map_zero]
    have hS0 : Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} = ⊥ :=
      Submodule.span_eq_bot.2 fun e he => hW0 e he.1
    rw [hS0, Submodule.span_eq_bot.2, Submodule.span_eq_bot.2]
    · rintro _ ⟨e, he, rfl⟩
      have : e = 0 := by simpa using he
      rw [this, map_zero]
    · rintro e ⟨he, -⟩
      rw [hW'0] at he
      exact (Submodule.mem_bot Ω').1 he
  have hω'' := hω' hr
  let hb : Module.Basis (Fin r) Ω (Module.Dual Ω W) := Module.Basis.mk hli hsp.ge
  have hbb : ∀ k, hb k = b k := fun k => Module.Basis.mk_apply hli hsp.ge k
  haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis hb
  haveI : Module.Finite Ω W := Module.finite_dual_iff Ω |>.1 inferInstance
  let c : Module.Basis (Fin r) Ω W := hb.dualBasis.map (Module.evalEquiv Ω W).symm
  have hbc : ∀ l k, b l (c k) = if l = k then 1 else 0 := by
    intro l k
    have h1 : c k = (Module.evalEquiv Ω W).symm (hb.dualBasis k) := by
      simp [c]
    rw [h1, Module.apply_evalEquiv_symm_apply, ← hbb, Module.Basis.dualBasis_apply_self]

  have hexp : ∀ e : W, e = ∑ k, b k e • c k := by
    intro e
    conv_lhs => rw [← c.sum_repr e]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have : b k e = ∑ m, c.repr e m * b k (c m) := by
      calc b k e = b k (∑ m, c.repr e m • c m) := by rw [c.sum_repr]
        _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
    rw [this]
    simp [hbc]

  have hcS : ∀ k, (c k : V) ∈ {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} := by
    intro k
    refine ⟨(c k).2, fun w hw => ?_⟩
    have hwr : W.dualRestrict w ∈ Submodule.span R (Set.range b) := by
      rw [← hmap]
      exact ⟨w, hw, rfl⟩
    have key : ∀ f ∈ Submodule.span R (Set.range b), f (c k) ∈ R := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        rw [hbc]
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      | zero => simpa using R.zero_mem
      | add x y _ _ hx hy => simpa using R.add_mem hx hy
      | smul a x _ hx =>
        have : (a • x) (c k) = (a : Ω) * x (c k) := rfl
        rw [this]
        exact R.mul_mem a.2 hx
    exact key _ hwr

  have hpick : ∀ l, ∃ w ∈ ω, W.dualRestrict w = b l := by
    intro l
    have : b l ∈ ω.map (W.dualRestrict.restrictScalars R) := by
      rw [hmap]
      exact Submodule.subset_span ⟨l, rfl⟩
    obtain ⟨w, hw, hwb⟩ := this
    exact ⟨w, hw, hwb⟩
  choose wl hwl hwb using hpick
  have hspan : ∀ e' ∈ W', ∃ a : Fin r → Ω', e' = ∑ k, a k • j (c k : V) := by
    intro e' he'
    have hle : W' ≤ Submodule.span Ω' (Set.range fun k => j (c k : V)) := by
      rw [hW', Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      have h1 : e = ∑ k, b k ⟨e, he⟩ • (c k : V) := by
        have := congrArg (Subtype.val) (hexp ⟨e, he⟩)
        simpa using this

      rw [SetLike.mem_coe, h1, map_sum]
      refine sum_mem fun k _ => ?_
      rw [hj.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω').1 (hle he')
    exact ⟨a, ha.symm⟩
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro e' ⟨he', hint⟩
    obtain ⟨a, rfl⟩ := hspan e' he'
    have hal : ∀ l, a l ∈ R' := by
      intro l
      have h1 := hint (jd (wl l)) (by
        rw [hω'']
        exact Submodule.subset_span ⟨wl l, hwl l, rfl⟩)
      have h2 : jd (wl l) (∑ k, a k • j (c k : V)) = a l := by

        rw [map_sum]
        have : ∀ k, jd (wl l) (a k • j (c k : V)) = a k * (if l = k then 1 else 0) := by
          intro k
          have h3 : wl l (c k : V) = if l = k then 1 else 0 := by
            rw [← hbc, ← hwb]
            simp [Submodule.dualRestrict_apply]
          rw [map_smul, hjd, smul_eq_mul, h3, apply_ite i, map_one, map_zero]
        simp [this]
      rwa [h2] at h1
    rw [SetLike.mem_coe]
    refine sum_mem fun k _ => ?_
    have : a k • j (c k : V) = (⟨a k, hal k⟩ : R') • j (c k : V) := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨(c k : V), Submodule.subset_span (hcS k), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨?_, fun w hw => ?_⟩
      · rw [hW']
        exact Submodule.subset_span ⟨x, hx.1, rfl⟩
      · rw [hω''] at hw
        induction hw using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨u, hu, rfl⟩ := hf
          rw [hjd]
          exact hR _ (hx.2 u hu)
        | zero => simpa using R'.zero_mem
        | add f g _ _ hf hg => simpa using R'.add_mem hf hg
        | smul a f _ hf =>
          have : (a • f) (j x) = (a : Ω') * f (j x) := rfl
          rw [this]
          exact R'.mul_mem a.2 hf
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      have : j (a • x) = (⟨i a, hR a a.2⟩ : R') • j x := hj.1 (a : Ω) x
      rw [this]
      exact Submodule.smul_mem _ _ hx

end GlobalTheory.CompanionTheory.Ar.HcptPull
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.IntClGens

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)

theorem twist_mem {c j : κ} (hc : x c ≠ 0) {b : Ω} (hb : b ∈ chRing o x c) :
    ∃ e : ℕ, ∀ m, e ≤ m → (x c / x j) ^ m * b ∈ chRing o x j := by
  have ht : x c / x j ∈ chRing o x j := Algebra.subset_adjoin ⟨c, rfl⟩
  induction hb using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have key : x c / x j * (x l / x c) = x l / x j := by
      rw [div_mul_div_comm, mul_comm (x j), mul_div_mul_left _ _ hc]
    have : (x c / x j) ^ (1 + k) * (x l / x c) = (x c / x j) ^ k * (x l / x j) := by
      rw [← key]; ring
    rw [this]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ht _) (Algebra.subset_adjoin ⟨l, rfl⟩)
  | algebraMap r =>
    exact ⟨0, fun m _ => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ht _) (Subalgebra.algebraMap_mem _ r)⟩
  | add y z _ _ hy hz =>
    obtain ⟨e1, h1⟩ := hy
    obtain ⟨e2, h2⟩ := hz
    exact ⟨max e1 e2, fun m hm => by
      rw [mul_add]
      exact Subalgebra.add_mem _ (h1 m (le_of_max_le_left hm)) (h2 m (le_of_max_le_right hm))⟩
  | mul y z _ _ hy hz =>
    obtain ⟨e1, h1⟩ := hy
    obtain ⟨e2, h2⟩ := hz
    refine ⟨e1 + e2, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have : (x c / x j) ^ (e1 + e2 + k) * (y * z) =
        ((x c / x j) ^ (e1 + k) * y) * ((x c / x j) ^ e2 * z) := by ring
    rw [this]
    exact Subalgebra.mul_mem _ (h1 _ (by omega)) (h2 _ le_rfl)

theorem twist_integral {c j : κ} (hc : x c ≠ 0) {a : Ω} (ha : IsIntegral (chRing o x c) a) :
    ∃ e : ℕ, ∀ m, e ≤ m → IsIntegral (chRing o x j) ((x c / x j) ^ m * a) := by
  have ht : x c / x j ∈ chRing o x j := Algebra.subset_adjoin ⟨c, rfl⟩
  obtain ⟨p, hmon, hp⟩ := ha
  have hE : ∀ i, ∃ e : ℕ, ∀ m, e ≤ m → (x c / x j) ^ m * (p.coeff i : Ω) ∈ chRing o x j :=
    fun i => twist_mem x hc (p.coeff i).2
  choose E hE using hE
  obtain ⟨E0, hE0⟩ : ∃ E0, ∀ i ≤ p.natDegree, E i ≤ E0 :=
    ⟨(Finset.range (p.natDegree + 1)).sup E, fun i hi => Finset.le_sup (Finset.mem_range.2 (by omega))⟩
  have hn' : (p.map (algebraMap (chRing o x c) Ω)).natDegree = p.natDegree := hmon.natDegree_map _
  have hqm : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).Monic :=
    (Polynomial.monic_scaleRoots_iff _).2 (hmon.map _)
  have hq0 : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).eval
      ((x c / x j) ^ E0 * a) = 0 := by
    have h1 : (p.map (algebraMap (chRing o x c) Ω)).eval₂ (RingHom.id Ω) a = 0 := by
      rw [Polynomial.eval₂_map, RingHom.id_comp]; exact hp
    have := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id Ω) (s := (x c / x j) ^ E0) h1
    simpa [Polynomial.eval₂_id] using this
  have hlift : (p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0) ∈
      Polynomial.lifts (algebraMap (chRing o x j) Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    have hmem : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).coeff i ∈
        chRing o x j := by
      rw [Polynomial.coeff_scaleRoots, hn', Polynomial.coeff_map]
      rcases lt_trichotomy i p.natDegree with hi | hi | hi
      · have h1 : E i ≤ E0 := hE0 i hi.le
        have h2 : 1 ≤ p.natDegree - i := by omega
        have hle : E i ≤ E0 * (p.natDegree - i) :=
          calc E i ≤ E0 := h1
            _ = E0 * 1 := (mul_one _).symm
            _ ≤ E0 * (p.natDegree - i) := Nat.mul_le_mul_left _ h2
        rw [← pow_mul, mul_comm]
        exact hE i _ hle
      · rw [hi, Nat.sub_self, pow_zero, mul_one, hmon.coeff_natDegree, map_one]
        exact Subalgebra.one_mem _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
        exact Subalgebra.zero_mem _
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q0, hq0map, -, hq0m⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hqm
  have hint : IsIntegral (chRing o x j) ((x c / x j) ^ E0 * a) :=
    ⟨q0, hq0m, by rw [← Polynomial.eval_map, hq0map]; exact hq0⟩
  refine ⟨E0, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have : (x c / x j) ^ (E0 + k) * a = (x c / x j) ^ k * ((x c / x j) ^ E0 * a) := by ring
  rw [this]
  have htk : IsIntegral (chRing o x j) ((x c / x j) ^ k) :=
    isIntegral_algebraMap (x := (⟨_, Subalgebra.pow_mem _ ht k⟩ : chRing o x j))
  exact htk.mul hint

theorem exists_twisted_gens : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω), (∀ c, x c ≠ 0 → Module.Finite (chRing o x c) (integralClosure (chRing o x c) Ω)) →
    ∃ (d n : ℕ) (z : κ ⊕ Fin n → Ω), (∀ c, z (Sum.inl c) = x c ^ d) ∧ ∀ c, x c ≠ 0 → ∀ a : Ω,
      IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d) := by
  intro o _ Ω _ _ κ _ x hfin
  have hgen : ∀ c, ∃ (N : ℕ) (g : Fin N → Ω), (∀ k, x c ≠ 0 ∧ IsIntegral (chRing o x c) (g k)) ∧
      (x c ≠ 0 → ∀ a, IsIntegral (chRing o x c) a → a ∈ Submodule.span (chRing o x c) (Set.range g)) := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨0, Fin.elim0, fun k => k.elim0, fun h => absurd hc h⟩
    · haveI := hfin c hc
      obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin (R := chRing o x c) (M := integralClosure (chRing o x c) Ω)
      refine ⟨N, fun k => ((s k : integralClosure (chRing o x c) Ω) : Ω),
        fun k => ⟨hc, (s k).2⟩, fun _ a ha => ?_⟩
      have hle : Submodule.map (integralClosure (chRing o x c) Ω).val.toLinearMap
          (Submodule.span (chRing o x c) (Set.range s)) ≤
          Submodule.span (chRing o x c) (Set.range fun k => ((s k : integralClosure (chRing o x c) Ω) : Ω)) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨k, rfl⟩
        exact Submodule.subset_span ⟨k, rfl⟩
      rw [hs] at hle
      exact hle (Submodule.mem_map_of_mem (p := ⊤) (f := (integralClosure (chRing o x c) Ω).val.toLinearMap)
        (r := ⟨a, ha⟩) Submodule.mem_top)
  choose N g hg using hgen
  obtain ⟨M, ⟨eI⟩⟩ := Finite.exists_equiv_fin (Σ c, Fin (N c))
  have hD : ∀ (i : Σ c, Fin (N c)) (j : κ), ∃ e : ℕ, ∀ m, e ≤ m →
      IsIntegral (chRing o x j) ((x i.1 / x j) ^ m * g i.1 i.2) :=
    fun i j => twist_integral x ((hg i.1).1 i.2).1 ((hg i.1).1 i.2).2
  choose D hD using hD
  obtain ⟨d, hd⟩ := Finite.exists_le (fun q : (Σ c, Fin (N c)) × κ => D q.1 q.2)
  refine ⟨d, M, Sum.elim (fun c => x c ^ d) (fun k => x (eI.symm k).1 ^ d * g (eI.symm k).1 (eI.symm k).2),
    fun c => rfl, fun c hc a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · refine Submodule.span_mono ?_ ((hg c).2 hc a ha)
    rintro _ ⟨k, rfl⟩
    refine ⟨Sum.inr (eI ⟨c, k⟩), ?_⟩
    have he : eI.symm (eI ⟨c, k⟩) = ⟨c, k⟩ := eI.symm_apply_apply _
    simp only [Sum.elim_inr]
    rw [he]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hc)
  · have hsub : (Set.range fun k => (Sum.elim (fun c => x c ^ d)
        (fun k => x (eI.symm k).1 ^ d * g (eI.symm k).1 (eI.symm k).2) k : Ω) / x c ^ d) ⊆
        ((integralClosure (chRing o x c) Ω).toSubmodule : Set Ω) := by
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
      rcases k with j | k
      · simp only [Sum.elim_inl]
        rw [← div_pow]
        exact isIntegral_algebraMap (x := (⟨_, Subalgebra.pow_mem _
          (Algebra.subset_adjoin ⟨j, rfl⟩ : x j / x c ∈ chRing o x c) d⟩ : chRing o x c))
      · simp only [Sum.elim_inr]
        rw [mul_div_right_comm, ← div_pow]
        exact hD (eI.symm k) c d (hd (eI.symm k, c))
    have := Submodule.span_le.2 hsub ha
    rwa [Subalgebra.mem_toSubmodule, mem_integralClosure_iff] at this

end GlobalTheory.CompanionTheory.Ar.IntClGens
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem scale_pull_ext : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (W : Submodule Ω V) (W' : Submodule Ω' V') (O : Type) [CommRing O] (σ : O →+* Ω) (𝔡 : Ideal O) (d₀ : O) (D : Submodule R V) (D' : Submodule R' V'), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → W' = Submodule.span Ω' (j '' (W : Set V)) → d₀ ∈ 𝔡 → σ d₀ ≠ 0 → (∀ d ∈ 𝔡, σ d / σ d₀ ∈ R) → (∀ e ∈ D, e ∈ W) → D' = Submodule.span R' (j '' (D : Set V)) → Submodule.span R' {e | e ∈ W' ∧ ∀ d ∈ 𝔡, (i.comp σ) d • e ∈ D'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
  intro Ω Ω' _ _ i R R' V V' _ _ _ _ j W W' O _ σ 𝔡 d₀ D D' hsemi hR hW' hd₀ hσd₀ hdiv hDW hD'
  have hj : ∀ (a : Ω) (v : V), j (a • v) = i a • j v := hsemi.1
  subst hW' hD'
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro e ⟨-, he⟩
    have hu : i (σ d₀) ≠ 0 := (map_ne_zero i).mpr hσd₀
    have key : ∀ y ∈ Submodule.span R' (j '' (D : Set V)),
        (i (σ d₀))⁻¹ • y ∈ Submodule.span R'
          (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨(σ d₀)⁻¹ • x, Submodule.subset_span ⟨W.smul_mem (σ d₀)⁻¹ (hDW x hx), fun d hd => ?_⟩, ?_⟩
        · rw [smul_smul, ← div_eq_mul_inv]
          exact D.smul_mem ⟨σ d / σ d₀, hdiv d hd⟩ hx
        · rw [hj, map_inv₀]
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul a y _ hy =>
        have e1 : (i (σ d₀))⁻¹ • (a • y) = a • ((i (σ d₀))⁻¹ • y) :=
          show (i (σ d₀))⁻¹ • ((a : Ω') • y) = (a : Ω') • ((i (σ d₀))⁻¹ • y) by
            rw [smul_smul, smul_smul, mul_comm]
        rw [e1]
        exact Submodule.smul_mem _ a hy
    have h1 := key _ (he d₀ hd₀)
    rwa [RingHom.comp_apply, inv_smul_smul₀ hu] at h1
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem v hv =>
      apply Submodule.subset_span
      refine ⟨Submodule.subset_span ⟨v, hv.1, rfl⟩, fun d hd => ?_⟩
      rw [RingHom.comp_apply, ← hj]
      exact Submodule.subset_span ⟨_, hv.2 d hd, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      show j ((a : Ω) • x) ∈ _
      rw [hj]
      exact Submodule.smul_mem _ ⟨i a, hR a a.2⟩ hx

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigExt

theorem mem_eigSp_iff' {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    (ρ : O →+* Module.End R E) (σ : O →+* R) (v : E) :
    v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem eigSp_ext :
    ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → (∀ a e, ρ' a (j e) = j (ρ a e)) → eigSp ρ' (i.comp σ) = Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) := by
  intro F _ _ Ω Ω' _ _ _ i V V' _ _ _ _ j ρ ρ' σ hj hspan hcomp
  obtain ⟨n, a, c, hsum, hcas⟩ := GlobalTheory.CompanionTheory.Ar.ScaledCasimir.exists_scaledCasimir F

  let P' : V' →ₗ[Ω'] V' := ∑ m, i (σ (c m)) • ρ' (a m)
  have hP'apply : ∀ w, P' w = ∑ m, i (σ (c m)) • ρ' (a m) w := fun w => by
    simp [P', LinearMap.sum_apply]
  have hscal : ∑ m, i (σ (c m)) * i (σ (a m)) = ((NumberField.discr F : ℤ) : Ω') := by

    rw [← map_intCast (i.comp σ), ← hsum, map_sum]
    simp [map_mul]
  have hP'eig : ∀ w ∈ eigSp ρ' (i.comp σ), P' w = ((NumberField.discr F : ℤ) : Ω') • w := by
    intro w hw
    have hw' := (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ' (i.comp σ) w).mp hw
    calc P' w = ∑ m, i (σ (c m)) • ρ' (a m) w := hP'apply w
      _ = ∑ m, (i (σ (c m)) * i (σ (a m))) • w :=
          Finset.sum_congr rfl fun m _ => by rw [hw', RingHom.comp_apply, smul_smul]
      _ = _ := by rw [← Finset.sum_smul, hscal]
  have hP'j : ∀ e, P' (j e) = j (∑ m, σ (c m) • ρ (a m) e) := by
    intro e

    rw [hP'apply, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcomp, hj.1]
  have hPe : ∀ e, ∑ m, σ (c m) • ρ (a m) e ∈ eigSp ρ σ := fun e =>
    (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ σ _).mpr fun b => hcas Ω V ρ σ b e
  apply le_antisymm
  · intro w hw
    have hle : Submodule.span Ω' (Set.range j) ≤
        (Submodule.span Ω' (j '' (eigSp ρ σ : Set V))).comap P' := by
      rw [Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hP'j]
      exact Submodule.subset_span ⟨_, hPe e, rfl⟩
    have hmem : P' w ∈ Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) :=
      hle (by rw [hspan]; exact Submodule.mem_top)
    rw [hP'eig w hw] at hmem
    have hd : ((NumberField.discr F : ℤ) : Ω') ≠ 0 := by
      rw [← map_intCast i]
      exact (map_ne_zero i).mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))
    have h2 := Submodule.smul_mem _ ((NumberField.discr F : ℤ) : Ω')⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at h2
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ σ v).mp hv
    refine (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ' (i.comp σ) (j v)).mpr fun b => ?_
    rw [hcomp, hv' b, hj.1, RingHom.comp_apply]

end GlobalTheory.CompanionTheory.Ar.EigExt
end

section

open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

theorem _root_.GlobalTheory.T.global_index_frame_log_norm : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (C : Matrix (Fin n) (Fin n) L), C.det ≠ 0 → (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (frame C).toAddSubgroup ≠ 0 ∧ (frame C).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧ gIdx (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup (frame C).toAddSubgroup = ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet.gIdx_frame | exact GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet.gIdx_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet.gIdx_frame <;> assumption)
end
