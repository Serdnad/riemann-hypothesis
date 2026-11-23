module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.Algebra.Module.Projective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.NNReal.Defs
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle002
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Ar.Num.Reflexive

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

theorem mem_of_locally_mem (R : Subalgebra o Ω) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R)
    (hc : ∀ l, c l ∈ R) (h1 : ∑ l, c l * f l = 1) (v : E) (hv : ∀ l, ∃ n : ℕ, f l ^ n • v ∈ L) :
    v ∈ L := by
  let I : Ideal R :=
    { carrier := {a | (a : Ω) • v ∈ L}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, AddMemClass.coe_add, add_smul] at *
        exact L.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul, mul_smul] at *
        exact hL _ a.2 _ hb }
  have hrad : ∀ l, (⟨f l, hf l⟩ : R) ∈ I.radical := fun l => by
    obtain ⟨n, hn⟩ := hv l
    exact ⟨n, by simpa [I] using hn⟩
  have hone : (1 : R) ∈ I.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [h1]
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hrad l)
  obtain ⟨n, hn⟩ := hone
  simpa [I] using hn

theorem exists_uniform_pow (R : Subalgebra o Ω) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {ι : Type*} [Finite ι] (g : Ω) (hg : g ∈ R) (x : ι → E)
    (hx : ∀ i, ∃ n : ℕ, g ^ n • x i ∈ L) : ∃ n : ℕ, ∀ i, g ^ n • x i ∈ L := by
  classical
  have := Fintype.ofFinite ι
  choose n hn using hx
  refine ⟨∑ i, n i, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le'
    (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  rw [hd, pow_add, mul_smul]
  exact hL _ (R.pow_mem hg d) _ (hn i)

theorem exists_uniform_denominator (R : Subalgebra o Ω) (r : ℕ) (L : AddSubgroup E)
    (h : LocFree R r L) (g : Ω) (hg : g ∈ R) (ψ : Module.Dual Ω E)
    (hψ : ∀ e ∈ L, ∃ n : ℕ, g ^ n * ψ e ∈ R) : ∃ m : ℕ, ∀ e ∈ L, g ^ m * ψ e ∈ R := by
  classical
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h
  choose b _ _ hb using hb
  let R' : AddSubgroup Ω := R.toSubring.toAddSubgroup
  have hR' : ∀ a ∈ R, ∀ e ∈ R', a • e ∈ R' := fun a ha e he => R.mul_mem ha he
  have hbL : ∀ j q, ∃ n : ℕ, f j ^ n • b j q ∈ L := fun j q => by
    refine (hb j (b j q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]
    · simp [Pi.single_apply]
  choose N hN using hbL
  obtain ⟨m, hm⟩ := exists_uniform_pow R R' hR' g hg
    (fun p : Fin k × Fin r => ψ (f p.1 ^ N p.1 p.2 • b p.1 p.2)) (fun p => hψ _ (hN p.1 p.2))
  refine ⟨m, fun e he => ?_⟩
  refine mem_of_locally_mem R R' hR' f c hf hc h1 _ fun j => ?_
  obtain ⟨a, ha, rfl⟩ := (hb j e).1 ⟨0, by simpa using he⟩
  have key : ∀ q, ∃ n : ℕ, f j ^ n • (g ^ m * (a q * ψ (b j q))) ∈ R' := fun q => by
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n + N j q, ?_⟩
    have h2 : g ^ m * ψ (f j ^ N j q • b j q) ∈ R := hm (j, q)
    have h3 := R.mul_mem hn h2
    have h4 : f j ^ (n + N j q) • (g ^ m * (a q * ψ (b j q)))
        = f j ^ n * a q * (g ^ m * ψ (f j ^ N j q • b j q)) := by
      simp only [map_smul, smul_eq_mul]; ring
    rw [h4]; exact h3
  obtain ⟨n, hn⟩ := exists_uniform_pow R R' hR' (f j) (hf j) _ key
  refine ⟨n, ?_⟩
  have h5 : f j ^ n • (g ^ m * ψ (∑ q, a q • b j q))
      = ∑ q, f j ^ n • (g ^ m * (a q * ψ (b j q))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [h5]
  exact R'.sum_mem fun q _ => hn q

theorem locFree_reflexive : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : AddSubgroup E), LocFree R r L → ∀ v : E, (∀ ψ : Module.Dual Ω E, (∀ e ∈ L, ψ e ∈ R) → ψ v ∈ R) → v ∈ L := by
  intro o Ω _ _ _ R E _ _ r L h v hv
  have h' := h
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h'
  refine mem_of_locally_mem R L hL f c hf hc h1 v fun l => ?_
  obtain ⟨b, hli, hsp, hb⟩ := hb l
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ q, B q = b q := fun q => Module.Basis.mk_apply _ _ q
  refine (hb v).2 ⟨fun q => B.coord q v, fun q => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := exists_uniform_denominator R r L h (f l) (hf l) (B.coord q) fun e he => by
      obtain ⟨a, ha, rfl⟩ := (hb e).1 ⟨0, by simpa using he⟩
      have : B.coord q (∑ q, a q • b q) = a q := by
        simp only [← hB, Module.Basis.coord_apply]
        exact congrFun (B.repr_sum_self a) q
      rw [this]; exact ha q
    exact ⟨m, by simpa using hv (f l ^ m • B.coord q) (by simpa using hm)⟩
  · simp only [← hB, Module.Basis.coord_apply]
    exact (B.sum_repr v).symm

end GlobalTheory.CompanionTheory.Ar.Num.Reflexive
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num.SpanExact

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω]
  {E E₂ : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup E₂] [Module Ω E₂]

theorem smul_mem_spanOver (R : Subalgebra o Ω) (S : Set E) {a : Ω} (ha : a ∈ R) {v : E}
    (hv : v ∈ spanOver R S) : a • v ∈ spanOver R S := by
  unfold spanOver at hv ⊢
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * b, R.mul_mem ha hb, e, he, by rw [mul_smul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_spanOver (R : Subalgebra o Ω) (S : Set E) (q : E →ₗ[Ω] E₂) :
    (spanOver R S).map q.toAddMonoidHom = spanOver R (q '' S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, ha, e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, q e, ⟨e, he, rfl⟩, by simp⟩
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a • e, ⟨a, ha, e, he, rfl⟩, by simp⟩

theorem local_step (R R₁ : Subalgebra o Ω) (hR : R ≤ R₁) (q : E →ₗ[Ω] E₂) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (f : Ω) (hf : f ∈ R) (b : Fin r → E₂)
    (hb : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤)
    (hloc : ∀ e, (∃ n : ℕ, f ^ n • e ∈ L.map q.toAddMonoidHom) ↔
        ∃ a : Fin r → Ω, (∀ j, ∃ n : ℕ, f ^ n * a j ∈ R) ∧ e = ∑ j, a j • b j)
    {v : E} (hv : v ∈ spanOver R₁ (L : Set E)) (hq : q v = 0) :
    ∃ m : ℕ, f ^ m • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
  classical
  have h1 : ∀ j, ∃ n : ℕ, ∃ s ∈ L, q s = f ^ n • b j := by
    intro j
    obtain ⟨n, s, hs, hs'⟩ := (hloc (b j)).2 ⟨Pi.single j 1, fun k => ⟨0, by
      by_cases h : k = j
      · subst h; simpa using R.one_mem
      · simpa [h] using R.zero_mem⟩, by simp [Pi.single_apply]⟩
    exact ⟨n, s, hs, hs'⟩
  choose n s hs hqs using h1
  set N := ∑ j, n j with hN
  have hle : ∀ j, n j ≤ N := fun j =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let t : Fin r → E := fun j => f ^ (N - n j) • s j
  have ht : ∀ j, t j ∈ L := fun j => hL _ (R.pow_mem hf _) _ (hs j)
  have hqt : ∀ j, q (t j) = f ^ N • b j := fun j => by
    simp only [t, map_smul, hqs, smul_smul, ← pow_add, Nat.sub_add_cancel (hle j)]
  let B : Module.Basis (Fin r) Ω E₂ := Module.Basis.mk hb hsp.ge
  let σ : E₂ →ₗ[Ω] E := B.constr Ω t
  have hσ : ∀ j, σ (b j) = t j := fun j => by
    have : b j = B j := by simp [B]
    rw [this]; simp [σ]
  set S := spanOver R₁ {e | e ∈ L ∧ q e = 0} with hS
  have hup : ∀ (w : E) (m k : ℕ), f ^ m • w ∈ S → f ^ (k + m) • w ∈ S := fun w m k h => by
    rw [pow_add, mul_smul]
    exact smul_mem_spanOver R₁ _ (R₁.pow_mem (hR hf) _) h
  have key : ∃ m : ℕ, f ^ m • (f ^ N • v - σ (q v)) ∈ S := by
    clear hq
    unfold spanOver at hv
    induction hv using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, e, he, rfl⟩ := hx
      obtain ⟨c, hc, hce⟩ := (hloc (q e)).1 ⟨0, e, he, by simp⟩
      choose p hp using hc
      set M := ∑ j, p j with hM
      have hle' : ∀ j, p j ≤ M := fun j =>
        Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have hp' : ∀ j, f ^ M * c j ∈ R := fun j => by
        rw [← Nat.sub_add_cancel (hle' j), pow_add, mul_assoc]
        exact R.mul_mem (R.pow_mem hf _) (hp j)
      refine ⟨M, AddSubgroup.subset_closure ⟨a, ha, f ^ M • (f ^ N • e - σ (q e)), ⟨?_, ?_⟩, ?_⟩⟩
      · rw [smul_sub]
        refine sub_mem (hL _ (R.pow_mem hf _) _ (hL _ (R.pow_mem hf _) _ he)) ?_

        rw [hce, map_sum, Finset.smul_sum]
        refine sum_mem fun j _ => ?_
        rw [map_smul, smul_smul, hσ]
        exact hL _ (hp' j) _ (ht j)
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_smul, map_sub, map_smul, hce, map_sum, map_sum, Finset.smul_sum]
        simp only [map_smul, hσ, hqt]
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_zero, smul_zero]
        intro j _
        rw [smul_comm, sub_self]
      · simp only [map_smul]
        module
    | zero => exact ⟨0, by simpa using S.zero_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨k, hk⟩ := hy
      refine ⟨k + m, ?_⟩
      have h2 := hup _ _ m hk
      rw [add_comm] at h2
      convert add_mem (hup _ _ k hm) h2 using 1
      simp only [map_add (f := _)]
      module
    | neg x _ hx =>
      obtain ⟨m, hm⟩ := hx
      refine ⟨m, ?_⟩
      convert neg_mem hm using 1
      simp only [map_neg]
      module
  obtain ⟨m, hm⟩ := key
  refine ⟨m + N, ?_⟩
  simpa [hq, smul_smul, pow_add] using hm

theorem mem_spanOver_ker (R R₁ : Subalgebra o Ω) (hR : R ≤ R₁) (q : E →ₗ[Ω] E₂) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (hF : LocFree R r (L.map q.toAddMonoidHom))
    {v : E} (hv : v ∈ spanOver R₁ (L : Set E)) (hq : q v = 0) :
    v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
  obtain ⟨-, k, f, c, hf, hc, hsum, hl⟩ := hF
  let J : Ideal R :=
    { carrier := {a | (a : Ω) • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0}}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, MulMemClass.coe_mul, mul_smul] at hb ⊢
        exact smul_mem_spanOver R₁ _ (hR a.2) hb }
  have h1 : (1 : R) ∈ J.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [hsum]
    rw [this]
    refine sum_mem fun l _ => Ideal.mul_mem_left _ _ ?_
    obtain ⟨b, hb, hsp, hloc⟩ := hl l
    obtain ⟨m, hm⟩ := local_step R R₁ hR q L hL (f l) (hf l) b hb hsp hloc hv hq
    exact ⟨m, hm⟩
  obtain ⟨m, hm⟩ := h1
  have : ((1 ^ m : R) : Ω) • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := hm
  simpa using this

theorem span_comap_exact : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R R₁ : Subalgebra o Ω), R ≤ R₁ → ∀ {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₂ : ℕ), (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) → LocFree R r₂ (L.map q.toAddMonoidHom) → (spanOver R₁ (L : Set E)).comap i.toAddMonoidHom = spanOver R₁ (L.comap i.toAddMonoidHom : Set E₁) ∧ (spanOver R₁ (L : Set E)).map q.toAddMonoidHom = spanOver R₁ (L.map q.toAddMonoidHom : Set E₂) := by
  intro o Ω _ _ _ R R₁ hR E E₁ E₂ _ _ _ _ _ _ i q hi hex L r₂ hL hF
  refine ⟨?_, ?_⟩
  · have himg : i '' (L.comap i.toAddMonoidHom : Set E₁) = {e | e ∈ L ∧ q e = 0} := by
      ext e
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, by rw [← LinearMap.mem_ker, ← hex]; exact ⟨x, rfl⟩⟩
      · rintro ⟨he, hq⟩
        rw [← LinearMap.mem_ker, ← hex] at hq
        obtain ⟨x, rfl⟩ := hq
        exact ⟨x, he, rfl⟩
    have hmap := map_spanOver R₁ (L.comap i.toAddMonoidHom : Set E₁) i
    rw [himg] at hmap
    ext x
    constructor
    · intro hx
      have hq : q (i x) = 0 := by rw [← LinearMap.mem_ker, ← hex]; exact ⟨x, rfl⟩
      have := mem_spanOver_ker R R₁ hR q L hL hF (v := i x) hx hq
      rw [← hmap] at this
      obtain ⟨y, hy, hxy⟩ := this
      obtain rfl : y = x := hi hxy
      exact hy
    · intro hx
      have h1 : i x ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
        rw [← hmap]; exact ⟨x, hx, rfl⟩
      have h2 : spanOver R₁ {e | e ∈ L ∧ q e = 0} ≤ spanOver R₁ (L : Set E) :=
        AddSubgroup.closure_mono fun w ⟨a, ha, e, he, hw⟩ => ⟨a, ha, e, he.1, hw⟩
      exact h2 h1
  · rw [map_spanOver, AddSubgroup.coe_map]
    rfl

end GlobalTheory.CompanionTheory.Ar.Num.SpanExact
end

section

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

variable {O : Type} [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
  [Module O L'] {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'}

theorem ProIso.exists_section_level [Module.Projective O L'] (f : ProIso O B B') (n : ℕ) :
    ∃ h : L' →ₗ[O] L, 0 < n → ∀ y, ∃ e, f.a n (h y) = y + n • e := by
  by_cases hn : 0 < n
  · let Ψ : L × L' →ₗ[O] L' := (f.a n).coprod (n • LinearMap.id)
    have hΨ : ∀ p : L × L', Ψ p = f.a n p.1 + n • p.2 := fun p => by
      simp only [Ψ, LinearMap.coprod_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hsurj : Function.Surjective Ψ := fun y => by
      obtain ⟨x, e, hxe⟩ := f.3 n hn y
      exact ⟨(x, e), by rw [hΨ, hxe]⟩
    obtain ⟨s, hs⟩ := Module.projective_lifting_property Ψ LinearMap.id hsurj
    refine ⟨LinearMap.fst O L L' ∘ₗ s, fun _ y => ⟨-(s y).2, ?_⟩⟩
    have hy := LinearMap.congr_fun hs y
    rw [LinearMap.comp_apply, hΨ, LinearMap.id_apply] at hy
    rw [LinearMap.comp_apply, LinearMap.fst_apply, smul_neg, ← sub_eq_add_neg,
      eq_sub_iff_add_eq, hy]
  · exact ⟨0, fun h => absurd h hn⟩

theorem ProIso.congr_of_map_congr (f : ProIso O B B') {n : ℕ} (hn : 0 < n) {x x' : L} {e : L'}
    (h : f.a n x = f.a n x' + n • e) : ∃ d, x = x' + n • d := by
  obtain ⟨d, hd⟩ := (f.inj n hn (x - x')).1 ⟨e, by rw [map_sub, h]; abel⟩
  exact ⟨d, by rw [← hd]; abel⟩

theorem ProIso.exists_isInv (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L]
    [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L')
    [Module.Projective O L'] (f : ProIso O B B') : ∃ g : ProIso O B' B, f.IsInv g := by
  choose h hh using fun n => GlobalTheory.CompanionTheory.Ar.ProIso.exists_section_level f n
  have hA : ∀ n, 0 < n → ∀ x : L, ∃ d, h n (f.a n x) = x + n • d := fun n hn x => by
    obtain ⟨e, he⟩ := hh n hn (f.a n x)
    exact GlobalTheory.CompanionTheory.Ar.ProIso.congr_of_map_congr f hn he
  refine ⟨⟨h, fun n hn y => ⟨?_, ?_⟩, fun n hn x => ?_, fun n hn x y => ?_,
    fun n m hn hm y => ?_⟩, ?_⟩
  · rintro ⟨z, hz⟩
    obtain ⟨e, he⟩ := hh n hn y
    rw [hz, map_nsmul] at he
    exact ⟨f.a n z - e, by rw [smul_sub, he]; abel⟩
  · rintro ⟨z, rfl⟩
    exact ⟨h n z, map_nsmul _ _ _⟩
  · obtain ⟨d, hd⟩ := hA n hn x
    exact ⟨f.a n x, -d, by rw [hd, smul_neg]; abel⟩
  · obtain ⟨e₁, he₁⟩ := hh n hn x
    obtain ⟨e₂, he₂⟩ := hh n hn y
    have d₁ := f.4 n hn (h n x) (h n y)
    have d₂ : (n : ℤ) ∣ B' (f.a n (h n x)) (f.a n (h n y)) - B' x y := by
      rw [he₁, he₂]
      simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      exact ⟨B' x e₂ + B' e₁ y + n * B' e₁ e₂, by ring⟩
    have key : B (h n x) (h n y) - B' x y =
        (B' (f.a n (h n x)) (f.a n (h n y)) - B' x y) -
          (B' (f.a n (h n x)) (f.a n (h n y)) - B (h n x) (h n y)) := by ring
    rw [key]
    exact dvd_sub d₂ d₁
  · obtain ⟨e₁, he₁⟩ := hh (n * m) (Nat.mul_pos hn hm) y
    obtain ⟨e₂, he₂⟩ := f.5 n m hn hm (h (n * m) y)
    obtain ⟨e₃, he₃⟩ := hh n hn y
    refine GlobalTheory.CompanionTheory.Ar.ProIso.congr_of_map_congr f hn
      (e := m • e₁ - e₂ - e₃) ?_
    have h12 : f.a n (h (n * m) y) = y + (n * m) • e₁ - n • e₂ :=
      eq_sub_of_add_eq (he₂.symm.trans he₁)
    rw [h12, he₃, smul_sub, smul_sub, smul_smul]
    abel
  · show (∀ n, 0 < n → ∀ x : L, ∃ e, h n (f.a n x) = x + n • e) ∧
      ∀ n, 0 < n → ∀ y : L', ∃ e, f.a n (h n y) = y + n • e
    exact ⟨hA, hh⟩

end GlobalTheory.CompanionTheory.Ar
end

section

open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem isSplit_injective_and_exists (O k S : Type) [CommRing O] [Field k] [Fintype S]
    (χ : S → (O →+* k)) (h : IsSplit χ) :
    Function.Injective χ ∧ ∀ ψ : O →+* k, ∃ s, χ s = ψ := by
  classical
  unfold IsSplit at h
  set F := Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom)
    (fun _ _ => Commute.all _ _) with hF
  have hv : ∀ (a : k) (x : O) (s : S), F (a ⊗ₜ[ℤ] x) s = a * χ s x := by
    intro a x s
    simp [hF, Algebra.ofId_apply]
  constructor
  · intro s t hst
    by_contra hne
    obtain ⟨y, hy⟩ := h.2 (Pi.single s 1)
    have key : ∀ y : TensorProduct ℤ k O, F y s = F y t := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rw [hv, hv, hst]
      | add u v hu hv' => simp [map_add (f := _), hu, hv']
    have h1 := key y
    rw [hy] at h1
    simp [Pi.single_apply, Ne.symm hne] at h1
  · intro ψ
    let Ψ : TensorProduct ℤ k O →ₐ[k] k :=
      Algebra.TensorProduct.lift (AlgHom.id k k) ψ.toIntAlgHom (fun _ _ => Commute.all _ _)
    choose y hy using fun s => h.2 (Pi.single s (1 : k))
    have hsum : ∑ s, y s = 1 := by
      apply h.1

      rw [map_sum, map_one]
      simp only [hy]
      ext t
      simp [Finset.sum_apply, Pi.single_apply]
    have hne : ∑ s, Ψ (y s) ≠ 0 := by

      rw [← map_sum, hsum, map_one]
      exact one_ne_zero
    obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine ⟨s, ?_⟩
    have hmul : ∀ z, z * y s = (F z s) • y s := by
      intro z
      apply h.1
      rw [map_mul, map_smul, hy]
      ext t
      by_cases hts : t = s
      · subst hts
        simp
      · simp [Pi.single_apply, hts]
    ext o
    have h1 := congrArg Ψ (hmul ((1 : k) ⊗ₜ[ℤ] o))
    have h2 : Ψ ((1 : k) ⊗ₜ[ℤ] o) = ψ o := by
      simp [Ψ]
    rw [map_mul, map_smul, hv, h2, smul_eq_mul, one_mul] at h1
    exact (mul_right_cancel₀ hs h1).symm

end GlobalTheory.CompanionTheory.Ar.Crv
end

section

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem grcount : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s :=
  PositivityTheory.HtPt.Rh.grcount

end GlobalTheory.CompanionTheory.Ar.GR
end
