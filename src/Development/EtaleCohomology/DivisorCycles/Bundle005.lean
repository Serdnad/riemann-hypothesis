module

public import Development.EtaleCohomology.DivisorCycles.Bundle002
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.FinEmbedPf

section core
variable {K V U ι : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup U] [Module K U]

def SS {W : Type} [AddCommGroup W] [Module K W] (a : ι → W →ₗ[K] W) : Prop :=
  ∀ S : Submodule K W, (∀ i, ∀ v ∈ S, a i v ∈ S) → ∃ S' : Submodule K W, IsCompl S S' ∧ ∀ i, ∀ v ∈ S', a i v ∈ S'

def gens (a : ι → V →ₗ[K] V) (b : ι → U →ₗ[K] U) : Set (V →ₗ[K] V) :=
  {F | ∃ (t' : U →ₗ[K] V) (t : V →ₗ[K] U), (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ (∀ i, t ∘ₗ a i = b i ∘ₗ t) ∧
    F = t' ∘ₗ t}

theorem proj_comm {E : Type} [AddCommGroup E] [Module K E] (p q : Submodule K E) (h : IsCompl p q)
    (φ : E →ₗ[K] E) (hp : ∀ v ∈ p, φ v ∈ p) (hq : ∀ v ∈ q, φ v ∈ q) (x : E) :
    p.projection q h (φ x) = φ (p.projection q h x) := by
  have hx := Submodule.projection_add_projection_eq_self h x
  conv_lhs => rw [← hx]
  rw [map_add (f := _), map_add (f := _), Submodule.projection_apply_of_mem_left h (hp _ (Submodule.projection_apply_mem h x)),
    Submodule.projection_apply_of_mem_right h (hq _ (Submodule.projection_apply_mem h.symm x)), add_zero]

theorem step (a : ι → V →ₗ[K] V) (b : ι → U →ₗ[K] U) (hV : SS a) (hU : SS b)
    (hspan : ∀ Z : V →ₗ[K] V, (∀ t : U →ₗ[K] V, (∀ i, a i ∘ₗ t = t ∘ₗ b i) → Z ∘ₗ t = 0) → Z = 0)
    (E : V →ₗ[K] V) (hE : E ∈ Submodule.span K (gens a b)) (hEi : ∀ x, E (E x) = E x)
    (hEc : ∀ i x, E (a i x) = a i (E x)) (hker : LinearMap.ker E ≠ ⊥) :
    ∃ E' : V →ₗ[K] V, E' ∈ Submodule.span K (gens a b) ∧ (∀ x, E' (E' x) = E' x) ∧
      (∀ i x, E' (a i x) = a i (E' x)) ∧ LinearMap.ker E' < LinearMap.ker E := by
  set P : V →ₗ[K] V := LinearMap.id - E with hPdef
  have hP : ∀ x, P x = x - E x := fun x => rfl
  have hEP : ∀ x, E (P x) = 0 := fun x => by rw [hP, map_sub, hEi, sub_self]
  have hPE : ∀ x, P (E x) = 0 := fun x => by rw [hP, hEi, sub_self]
  have hPP : ∀ x, P (P x) = P x := fun x => by rw [hP (P x), hEP, sub_zero]
  have hPc : ∀ i x, P (a i x) = a i (P x) := fun i x => by rw [hP, hP, hEc, map_sub]
  obtain ⟨t', ht', hPt'⟩ : ∃ t' : U →ₗ[K] V, (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ P ∘ₗ t' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := hspan P hcon
    apply hker
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have := congrArg (fun f => f m) h0
    simpa [hP, hm] using this
  set M : U →ₗ[K] V := P ∘ₗ t' with hMdef
  have hMc : ∀ i u, a i (M u) = M (b i u) := fun i u => by
    simp only [hMdef, LinearMap.comp_apply]
    rw [← hPc]; congr 1; exact congrArg (fun f => f u) (ht' i)
  have hEM : ∀ u, E (M u) = 0 := fun u => hEP _
  have hPM : ∀ u, P (M u) = M u := fun u => hPP _
  obtain ⟨Cc, hC, hCs⟩ := hU (LinearMap.ker M) (fun i v hv => by
    rw [LinearMap.mem_ker] at hv ⊢; rw [← hMc, hv, map_zero])
  have hinj : ∀ c ∈ Cc, M c = 0 → c = 0 := fun c hc h0 => by
    have : c ∈ LinearMap.ker M ⊓ Cc := ⟨h0, hc⟩
    rw [hC.inf_eq_bot] at this; exact this
  set R : Submodule K V := Submodule.map M Cc with hRdef
  obtain ⟨D, hD, hDs⟩ := hV R (fun i v hv => by
    obtain ⟨c, hc, rfl⟩ := hv
    exact ⟨b i c, hCs i c hc, (hMc i c).symm⟩)
  have hinj' : Function.Injective (M ∘ₗ Cc.subtype) := by
    intro x y hxy
    apply Subtype.ext
    have := hinj (x - y) (Cc.sub_mem x.2 y.2) (by simpa [sub_eq_zero] using hxy)
    exact sub_eq_zero.mp this
  have hRr : LinearMap.range (M ∘ₗ Cc.subtype) = R := by
    ext y; simp [hRdef, Submodule.mem_map]
  let e := LinearEquiv.ofInjective (M ∘ₗ Cc.subtype) hinj'
  let T : V →ₗ[K] U := Cc.subtype ∘ₗ e.symm.toLinearMap ∘ₗ
    (LinearEquiv.ofEq _ _ hRr.symm).toLinearMap ∘ₗ R.projectionOnto D hD
  have hTC : ∀ v, T v ∈ Cc := fun v => (e.symm _).2
  have hMT : ∀ v, M (T v) = R.projection D hD v := fun v => by
    have := congrArg Subtype.val (e.apply_symm_apply
      ((LinearEquiv.ofEq _ _ hRr.symm).toLinearMap (R.projectionOnto D hD v)))
    rw [LinearEquiv.ofInjective_apply] at this
    simpa [T] using this
  have hpc : ∀ i v, R.projection D hD (a i v) = a i (R.projection D hD v) := fun i v =>
    proj_comm R D hD (a i) (fun w hw => by
      obtain ⟨c, hc, rfl⟩ := hw
      exact ⟨b i c, hCs i c hc, (hMc i c).symm⟩) (hDs i) v
  have hTc : ∀ i v, T (a i v) = b i (T v) := fun i v => by
    have h1 := hinj (T (a i v) - b i (T v)) (Cc.sub_mem (hTC _) (hCs i _ (hTC v)))
      (by rw [map_sub, hMT, ← hMc, hMT, hpc, sub_self])
    exact sub_eq_zero.mp h1
  set H : V →ₗ[K] V := M ∘ₗ (T ∘ₗ P) with hHdef
  have hH : ∀ x, H x = R.projection D hD (P x) := fun x => hMT _
  have hHgen : H ∈ gens a b := ⟨M, T ∘ₗ P, fun i => LinearMap.ext fun u => by simp [hMc],
    fun i => LinearMap.ext fun v => by simp [hPc, hTc], rfl⟩
  have hprojR : ∀ x, R.projection D hD x ∈ R := fun x => Submodule.projection_apply_mem hD x
  have hER : ∀ y ∈ R, E y = 0 := fun y hy => by
    obtain ⟨c, _, rfl⟩ := hy; exact hEM c
  have hPR : ∀ y ∈ R, P y = y := fun y hy => by rw [hP, hER y hy, sub_zero]
  have hEH : ∀ x, E (H x) = 0 := fun x => by rw [hH]; exact hER _ (hprojR _)
  have hHE : ∀ x, H (E x) = 0 := fun x => by rw [hH, hPE, map_zero]
  have hHH : ∀ x, H (H x) = H x := fun x => by
    rw [hH (H x), hPR _ (by rw [hH]; exact hprojR _), hH,
      Submodule.projection_apply_of_mem_left hD (hprojR _)]
  refine ⟨E + H, Submodule.add_mem _ hE (Submodule.subset_span hHgen), fun x => ?_, fun i x => ?_, ?_⟩
  · simp only [LinearMap.add_apply, map_add (f := _), hEi, hEH, hHE, hHH, add_zero, zero_add]
  · simp only [LinearMap.add_apply, map_add (f := _), hEc, hH, hPc, hpc]
  · have hle : LinearMap.ker (E + H) ≤ LinearMap.ker E := fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.add_apply] at hx
      have := congrArg E hx
      rw [map_add (f := _), hEi, hEH, add_zero, map_zero] at this
      exact this
    refine lt_of_le_of_ne hle (fun heq => ?_)
    have hRne : ∃ c ∈ Cc, M c ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hPt'
      ext u
      have hu : u ∈ LinearMap.ker M ⊔ Cc := by rw [hC.sup_eq_top]; trivial
      obtain ⟨k, hk, c, hc', rfl⟩ := Submodule.mem_sup.mp hu
      show M (k + c) = 0
      rw [map_add (f := _), LinearMap.mem_ker.mp hk, hc c hc', add_zero]
    obtain ⟨c, hc, hne⟩ := hRne
    have hyR : M c ∈ R := ⟨c, hc, rfl⟩
    have hy : M c ∈ LinearMap.ker E := hEM c
    rw [← heq, LinearMap.mem_ker, LinearMap.add_apply, hEM, zero_add, hH, hPR _ hyR,
      Submodule.projection_apply_of_mem_left hD hyR] at hy
    exact hne hy

theorem main (a : ι → V →ₗ[K] V) (b : ι → U →ₗ[K] U) (hV : SS a) (hU : SS b)
    (hspan : ∀ Z : V →ₗ[K] V, (∀ t : U →ₗ[K] V, (∀ i, a i ∘ₗ t = t ∘ₗ b i) → Z ∘ₗ t = 0) → Z = 0) :
    (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b) := by
  have key : ∀ d : ℕ, ∀ E : V →ₗ[K] V, E ∈ Submodule.span K (gens a b) → (∀ x, E (E x) = E x) →
      (∀ i x, E (a i x) = a i (E x)) → Module.finrank K (LinearMap.ker E) ≤ d →
      (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b) := by
    have fin : ∀ E : V →ₗ[K] V, E ∈ Submodule.span K (gens a b) → (∀ x, E (E x) = E x) →
        LinearMap.ker E = ⊥ → (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b) := by
      intro E hE hi hk
      have : E = LinearMap.id := by
        ext x
        have h1 : E (E x - x) = 0 := by rw [map_sub, hi, sub_self]
        have := (LinearMap.ker_eq_bot'.mp hk) _ h1
        simpa [sub_eq_zero] using this
      rw [← this]; exact hE
    intro d
    induction d with
    | zero =>
      intro E hE hi _ hd
      exact fin E hE hi (Submodule.finrank_eq_zero.mp (by omega))
    | succ d ih =>
      intro E hE hi hc hd
      by_cases hk : LinearMap.ker E = ⊥
      · exact fin E hE hi hk
      · obtain ⟨E', hE', hi', hc', hlt⟩ := step a b hV hU hspan E hE hi hc hk
        have := Submodule.finrank_lt_finrank_of_lt hlt
        exact ih E' hE' hi' hc' (by omega)
  exact key _ 0 (Submodule.zero_mem _) (fun x => by simp) (fun i x => by simp)
    (Submodule.finrank_le _)

end core

theorem FinEmbed_of : FinEmbed := by
  intro Γ K _ _ N n ρ r A B hSub hρ hr
  let a : Γ → (Fin N → K) →ₗ[K] (Fin N → K) := fun g => Matrix.toLin' (ρ g : Mat K N)
  let b : Γ → (Fin n → K) →ₗ[K] (Fin n → K) := fun g => Matrix.toLin' (r g : Mat K n)
  have hV : SS a := fun S hS => by
    obtain ⟨S', h1, h2⟩ := hρ S (fun g v hv => by simpa [a, Matrix.toLin'_apply] using hS g v hv)
    exact ⟨S', h1, fun g v hv => by simpa [a, Matrix.toLin'_apply] using h2 g v hv⟩
  have hU : SS b := fun S hS => by
    obtain ⟨S', h1, h2⟩ := hr S (fun g v hv => by simpa [b, Matrix.toLin'_apply] using hS g v hv)
    exact ⟨S', h1, fun g v hv => by simpa [b, Matrix.toLin'_apply] using h2 g v hv⟩
  have hspan : ∀ Z : (Fin N → K) →ₗ[K] (Fin N → K),
      (∀ t : (Fin n → K) →ₗ[K] (Fin N → K), (∀ g, a g ∘ₗ t = t ∘ₗ b g) → Z ∘ₗ t = 0) → Z = 0 := by
    intro Z hZ
    have h0 := hSub.2.2 (LinearMap.toMatrix' Z) (fun T hT => by
      have := hZ (Matrix.toLin' T) (fun g => by
        simp only [a, b, ← Matrix.toLin'_mul, hT g])
      have := congrArg LinearMap.toMatrix' this
      simpa [LinearMap.toMatrix'_comp] using this)
    have := congrArg Matrix.toLin' h0
    simpa using this
  have hid := main a b hV hU hspan
  obtain ⟨k, f, g, hsum⟩ := Submodule.mem_span_set'.mp hid
  have hg : ∀ j, ∃ (t' : (Fin n → K) →ₗ[K] (Fin N → K)) (t : (Fin N → K) →ₗ[K] (Fin n → K)),
      (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ (∀ i, t ∘ₗ a i = b i ∘ₗ t) ∧ (g j : _) = t' ∘ₗ t := fun j => (g j).2
  choose t' t ht' ht hEq using hg
  refine ⟨k, fun j => LinearMap.toMatrix' (t j), fun j => f j • LinearMap.toMatrix' (t' j), ?_, ?_, ?_⟩
  · intro j g
    have := congrArg LinearMap.toMatrix' (ht j g)
    simpa [a, b, LinearMap.toMatrix'_comp] using this
  · intro j g
    have := congrArg LinearMap.toMatrix' (ht' j g)
    simp only [a, b, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at this
    rw [Matrix.mul_smul, smul_mul, this]
  · have h1 : ∑ j, f j • (t' j ∘ₗ t j) = LinearMap.id := by
      rw [← hsum]; exact Finset.sum_congr rfl fun j _ => by rw [hEq]
    have h2 := congrArg LinearMap.toMatrix' h1

    rw [map_sum, LinearMap.toMatrix'_id] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, LinearMap.toMatrix'_comp, smul_mul]

end LateralTheory.DivDb.FinEmbedPf
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.GenSpecProof
open LateralTheory.DivDb Finset

variable {C : Type} [Field C] {N n : ℕ}

theorem mem_periodic (π : Equiv.Perm (Fin n)) (k : Fin n) : k ∈ Function.periodicPts π :=
  Function.mk_mem_periodicPts (orderOf_pos π) (by
    show (π^[orderOf π]) k = k
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]; rfl)

theorem mp_pos (π : Equiv.Perm (Fin n)) (k : Fin n) : 0 < Function.minimalPeriod π k :=
  Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodic π k)

theorem orbit_eq (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (univ.filter (fun m => π.SameCycle k m)) =
      (range (Function.minimalPeriod π k)).image (fun s => (π^[s]) k) := by
  ext m
  simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
    refine ⟨i % Function.minimalPeriod π k, Nat.mod_lt _ (mp_pos π k), ?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq, Equiv.Perm.iterate_eq_pow, hi]
  · rintro ⟨s, -, rfl⟩
    rw [Equiv.Perm.iterate_eq_pow]
    exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)

theorem injOn_orbit (π : Equiv.Perm (Fin n)) (k : Fin n) :
    Set.InjOn (fun s => (π^[s]) k) ↑(range (Function.minimalPeriod π k)) := by
  intro a ha b hb h
  exact Function.iterate_injOn_Iio_minimalPeriod (by simpa using ha) (by simpa using hb) h

theorem card_orbit (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (univ.filter (fun m => π.SameCycle k m)).card = Function.minimalPeriod π k := by
  rw [orbit_eq, card_image_of_injOn (injOn_orbit π k), card_range]

theorem prod_orbit (π : Equiv.Perm (Fin n)) (k : Fin n) (τ : Fin n → C) :
    ∏ s ∈ range (Function.minimalPeriod π k), τ ((π^[s]) k) =
      ∏ m ∈ univ.filter (fun m => π.SameCycle k m), τ m := by
  rw [orbit_eq, prod_image (injOn_orbit π k)]

theorem filt_eq (π : Equiv.Perm (Fin n)) {i k : Fin n} (h : π.SameCycle i k) :
    univ.filter (fun m => π.SameCycle i m) = univ.filter (fun m => π.SameCycle k m) := by
  ext m
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem tp {p : Fin n → Mat C N} (hp : Sys p) (τ : Fin n → C) (k : Fin n) :
    (∑ j, τ j • p j) * p k = τ k • p k := by
  rw [Finset.sum_mul, Finset.sum_eq_single k]
  · rw [smul_mul_assoc, (hp.1.idem k).eq]
  · intro j _ hj; rw [smul_mul_assoc, hp.1.ortho hj, smul_zero]
  · simp

theorem xpow {p : Fin n → Mat C N} {x : Mat C N} {π : Equiv.Perm (Fin n)}
    (hx : ∀ j, x * p j = p (π j) * x) (m : ℕ) (k : Fin n) :
    x ^ m * p k = p ((π^[m]) k) * x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, hx, mul_assoc, ← pow_succ',
      Function.iterate_succ_apply']

theorem ypow {p : Fin n → Mat C N} {x : Mat C N} {π : Equiv.Perm (Fin n)} (hp : Sys p)
    (hx : ∀ j, x * p j = p (π j) * x) (τ : Fin n → C) (m : ℕ) (k : Fin n) :
    (x * ∑ j, τ j • p j) ^ m * p k = (∏ s ∈ range m, τ ((π^[s]) k)) • (x ^ m * p k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, xpow hx, prod_range_succ,
      ← smul_smul, pow_succ', mul_assoc x (x ^ m), xpow hx]
    congr 1
    rw [← mul_assoc, mul_assoc x, tp hp, mul_smul_comm, smul_mul_assoc]
    simp only [mul_assoc]

theorem split {p : Fin n → Mat C N} (hp : Sys p) (O : Finset (Fin n)) (v : Fin N → C)
    (hs : ∀ k, k ∉ O → p k *ᵥ v = 0) (M : Mat C N) : M *ᵥ v = ∑ k ∈ O, (M * p k) *ᵥ v := by
  have h1 : M *ᵥ v = ∑ k, (M * p k) *ᵥ v := by
    conv_lhs => rw [← mul_one M, ← hp.1.complete, Finset.mul_sum]
    rw [Matrix.sum_mulVec]
  rw [h1, ← Finset.sum_subset (subset_univ O)]
  intro k _ hk; rw [← mulVec_mulVec, hs k hk, mulVec_zero]

theorem powv (y : Mat C N) (l : C) (v : Fin N → C) (h : y *ᵥ v = l • v) (m : ℕ) :
    (y ^ m) *ᵥ v = l ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ']

theorem root_of (M : Mat C N) (β : C) (v : Fin N → C) (hv : v ≠ 0) (h : M *ᵥ v = β • v) :
    M.charpoly.IsRoot β := by
  rw [Polynomial.IsRoot.def, eval_charpoly, ← exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  rw [sub_mulVec, h]
  ext a
  simp [Matrix.scalar_apply]

theorem eig {p : Fin n → Mat C N} {x : Mat C N} {π : Equiv.Perm (Fin n)} (hp : Sys p)
    (hxu : IsUnit x) (hx : ∀ j, x * p j = p (π j) * x) (τ : Fin n → C) (hτ : ∀ j, τ j ≠ 0)
    (i : Fin n) (l : C) (v : Fin N → C) (hv : v ≠ 0) (hy : (x * ∑ j, τ j • p j) *ᵥ v = l • v)
    (hs : ∀ k, ¬ π.SameCycle i k → p k *ᵥ v = 0) :
    ∃ β : C, β ≠ 0 ∧ (x ^ (univ.filter (fun m => π.SameCycle i m)).card).charpoly.IsRoot β ∧
      l ^ (univ.filter (fun m => π.SameCycle i m)).card =
        (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) * β := by
  have hs' : ∀ k, k ∉ univ.filter (fun m => π.SameCycle i m) → p k *ᵥ v = 0 :=
    fun k hk => hs k (by simpa using hk)
  have hQ : (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) ≠ 0 :=
    prod_ne_zero_iff.2 fun k _ => hτ k
  have hk : ∀ k ∈ univ.filter (fun m => π.SameCycle i m),
      (x * ∑ j, τ j • p j) ^ (univ.filter (fun m => π.SameCycle i m)).card * p k =
        (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) •
          (x ^ (univ.filter (fun m => π.SameCycle i m)).card * p k) := by
    intro k hk
    have hik : π.SameCycle i k := by simpa using hk
    rw [ypow hp hx]
    congr 1
    rw [filt_eq π hik, card_orbit, prod_orbit]
  have key : (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) •
      (x ^ (univ.filter (fun m => π.SameCycle i m)).card *ᵥ v) =
        l ^ (univ.filter (fun m => π.SameCycle i m)).card • v := by
    rw [← powv _ _ _ hy, split hp _ v hs' (x ^ _),
      split hp _ v hs' ((x * ∑ j, τ j • p j) ^ _), smul_sum]
    refine sum_congr rfl fun k hk' => ?_
    rw [hk k hk', smul_mulVec]
  have hxc := hxu.pow (univ.filter (fun m => π.SameCycle i m)).card
  have hl : l ^ (univ.filter (fun m => π.SameCycle i m)).card ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at key
    have h2 := (smul_eq_zero.1 key).resolve_left hQ
    exact hv ((mulVec_injective_iff_isUnit.2 hxc) (by rw [h2, mulVec_zero]))
  refine ⟨_, div_ne_zero hl hQ, root_of _ _ v hv ?_, by field_simp⟩
  rw [div_eq_inv_mul, ← smul_smul, ← key, smul_smul, inv_mul_cancel₀ hQ, one_smul]

theorem GenSpec_of : GenSpec := by
  intro C _ N n p x π hp hxu hx
  classical
  refine ⟨⋃ a : Fin (n + 1), ⋃ b : Fin (n + 1), Set.image2 (fun β β' => β' ^ (a : ℕ) / β ^ (b : ℕ))
    (↑(x ^ (a : ℕ)).charpoly.roots.toFinset) (↑(x ^ (b : ℕ)).charpoly.roots.toFinset), ?_, ?_⟩
  · exact Set.finite_iUnion fun a => Set.finite_iUnion fun b =>
      (Finset.finite_toSet _).image2 _ (Finset.finite_toSet _)
  intro τ hτ hml i j hij l v w hv hw hyv hyw hsv hsw
  obtain ⟨β, hβ0, hβr, hβ⟩ := eig hp hxu hx τ hτ i l v hv hyv hsv
  obtain ⟨β', hβ0', hβr', hβ'⟩ := eig hp hxu hx τ hτ j l w hw hyw hsw
  have hO : (univ.filter (fun m => π.SameCycle i m)).Nonempty := ⟨i, mem_filter.2 ⟨mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩⟩
  have hO' : (univ.filter (fun m => π.SameCycle j m)).Nonempty := ⟨j, mem_filter.2 ⟨mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩⟩
  have hd : Disjoint (univ.filter (fun m => π.SameCycle i m)) (univ.filter (fun m => π.SameCycle j m)) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact hij (h1.trans h2.symm)
  have hc : ∀ O : Finset (Fin n), O.card < n + 1 := fun O =>
    Nat.lt_succ_of_le ((card_le_univ O).trans (by simp))
  refine hml _ _ hO hO' hd (β' ^ (univ.filter (fun m => π.SameCycle i m)).card /
    β ^ (univ.filter (fun m => π.SameCycle j m)).card) ?_ ?_
  · refine Set.mem_iUnion.2 ⟨⟨_, hc (univ.filter (fun m => π.SameCycle i m))⟩, Set.mem_iUnion.2
      ⟨⟨_, hc (univ.filter (fun m => π.SameCycle j m))⟩, Set.mem_image2_of_mem ?_ ?_⟩⟩
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).2 hβr
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).2 hβr'
  · rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hβ0), ← mul_pow, ← hβ, ← pow_mul,
      ← mul_pow, mul_comm β', ← hβ', ← pow_mul, mul_comm]

end LateralTheory.DivDb.GenSpecProof
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb


open Polynomial in
def DivPlus : Prop :=
  ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [Field K'] [IsAlgClosed K'] [Algebra K K']
    (N n : ℕ) (ρ : Γ →* GL (Fin N) K),
      Continuous (fun g : Γ => (ρ g : Matrix (Fin N) (Fin N) K)) → IsSSMat ρ →
    ∀ (S : Set Γ), Dense S →
    ∀ (P : Γ → K[X]), (∀ s ∈ S, (P s).Monic ∧ (P s).natDegree = n) →
      (∀ s ∈ S, aeval (ρ s : Matrix (Fin N) (Fin N) K) (P s) = 0) →
    ∀ (X : Matrix (Fin N) (Fin N) K'), InLieZar ρ X →
      (∃ e : Fin n → K', Function.Injective e ∧ IsLac e ∧ ∀ i, X.charpoly.IsRoot (e i)) →
    ∀ (ψ : Γ →* Kˣ), Continuous (fun g : Γ => ((ψ g : Kˣ) : K)) →
      (∀ s ∈ S, ((ψ s : Kˣ) : K) = (-1) ^ n * (P s).coeff 0) →
    ∃ r : Γ →* GL (Fin n) K,
      Continuous (fun g : Γ => (r g : Matrix (Fin n) (Fin n) K)) ∧ IsSSMat r ∧
      (∃ A : Matrix (Fin N) (Fin n) K, A.rank = n ∧
        ∀ g : Γ, (ρ g : Matrix (Fin N) (Fin N) K) * A = A * (r g : Matrix (Fin n) (Fin n) K)) ∧
      (∀ g : Γ, aeval (ρ g : Matrix (Fin N) (Fin N) K) (r g : Matrix (Fin n) (Fin n) K).charpoly = 0) ∧
      (∀ s ∈ S, aeval (r s : Matrix (Fin n) (Fin n) K) (P s) = 0) ∧
      (∀ g : Γ, ((r g : Matrix (Fin n) (Fin n) K).det) = ((ψ g : Kˣ) : K)) ∧
      IsOpen {g : Γ | (r g : Matrix (Fin n) (Fin n) K).charpoly.Separable} ∧
      Dense {g : Γ | (r g : Matrix (Fin n) (Fin n) K).charpoly.Separable} ∧
      (∀ s ∈ S, (r s : Matrix (Fin n) (Fin n) K).charpoly.Separable →
        (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      (∀ s ∈ S, ProdGen n (P s) → (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      ∃ (k : ℕ) (T : Fin k → Matrix (Fin n) (Fin N) K) (T' : Fin k → Matrix (Fin N) (Fin n) K),
        (∀ j g, T j * (ρ g : Mat K N) = (r g : Mat K n) * T j) ∧
        (∀ j g, (ρ g : Mat K N) * T' j = T' j * (r g : Mat K n)) ∧ ∑ j, T' j * T j = 1

theorem plus_of (hSpec : SpecLie) (hDeg : DegAll) (hStruct : Struct) (hKey : Key) (hBig : BigCorner)
    (hSemis : Semis) (hMU : MatrixUnits₂) (hRep : Rep) (hDA : DenseAlg) (hSub : FinSub) (hFD : FinDense)
    (hFP : FinPoly) (hEm : FinEmbed) : DivPlus := by
  intro Γ _ _ _ _ K K' _ _ _ _ _ _ _ _ _ N n ρ hρ hss S hS P hP hk X hX he ψ hψ hψS
  obtain ⟨e, -, hL, hr⟩ := he
  obtain ⟨X₀, e₀, hX₀, hL₀, hr₀⟩ := hSpec Γ K K' N n ρ X e hX hL hr
  have hd : ∀ g, Deg n (ρ g : Mat K N) := hDeg Γ K N n ρ hρ S hS fun s hs =>
    ⟨P s, (hP s hs).1.ne_zero, (hP s hs).2.le, hk s hs⟩
  obtain ⟨p, hG⟩ := hStruct Γ K N n ρ X₀ e₀ hss hd hX₀ hL₀ hr₀
  have key := hKey Γ K N n ρ e₀ p hd hL₀ hG
  obtain ⟨hsys, -, hC, -, hN, hK, -⟩ := hG
  obtain ⟨R, hR, hRC, hRN, hRK⟩ := hBig Γ K N n ρ (env ρ) p hC hN hK
    fun g => (key ⊤ inferInstance inferInstance g).2
  obtain ⟨E, hE⟩ := hMU K N n R p hsys hRC (hSemis Γ K N ρ R hss hRN hRK)
  obtain ⟨r, A, B, hsub⟩ := hRep Γ K N n ρ R p E hsys hE hR
  obtain ⟨h1, h2, h3, h4⟩ := hSub Γ K N n ρ r A B hsub hss
  have hc : Continuous (fun g => (r g : Mat K n)) := by
    simp only [h3]
    exact (continuous_const.matrix_mul hρ).matrix_mul continuous_const
  obtain ⟨ho, hD⟩ := hFD Γ K n r hc fun U hU hf g => by
    obtain ⟨m, hm, hE⟩ := (key U hU hf g).1
    exact hDA Γ K N n ρ r A B hsub U g m hm hE
  have hkr : ∀ s ∈ S, Polynomial.aeval (r s : Mat K n) (P s) = 0 := fun s hs => (h4 s _).1 (hk s hs)
  have hsep : ∀ s ∈ S, (r s : Mat K n).charpoly.Separable → (r s : Mat K n).charpoly = P s := fun s hs =>
    (hFP K n _ _ (hP s hs).1 (hP s hs).2 (hkr s hs)).1
  have hdet : ∀ g, (r g : Mat K n).det = ((ψ g : Kˣ) : K) := by
    have := Continuous.ext_on (hS.inter_of_isOpen_right hD ho) hc.matrix_det hψ (fun s hs => by
      show (r s : Mat K n).det = _
      rw [hψS s hs.1, Matrix.det_eq_sign_charpoly_coeff, hsep s hs.1 hs.2, Fintype.card_fin])
    exact fun g => congrFun this g
  refine ⟨r, hc, h1, ⟨A, h2, hsub.2.1⟩, fun g => (h4 g _).2 (Matrix.aeval_self_charpoly _), hkr, hdet, ho, hD,
    hsep, fun s hs hg => (hFP K n _ _ (hP s hs).1 (hP s hs).2 (hkr s hs)).2 hg ?_, hEm Γ K N n ρ r A B hsub hss h1⟩
  rw [hdet, hψS s hs]

end LateralTheory.DivDb
end
