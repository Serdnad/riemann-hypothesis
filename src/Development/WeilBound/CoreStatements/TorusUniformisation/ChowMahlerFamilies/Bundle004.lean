module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle008
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_graph_restrict_bc

section Span

variable {o C : Type} [CommRing o] [Field C] [Algebra o C] {RC : Subalgebra o C}
  {A B : Type} [AddCommGroup A] [Module C A] [AddCommGroup B] [Module C B]

theorem mem_span {S : Set A} {e : A} (he : e ∈ S) : e ∈ spanOver RC S :=
  AddSubgroup.subset_closure ⟨1, RC.one_mem, e, he, (one_smul _ _).symm⟩

theorem smul_mem {S : Set A} {a : C} (ha : a ∈ RC) {x : A} (hx : x ∈ spanOver RC S) :
    a • x ∈ spanOver RC S := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, RC.mul_mem ha hc, e, he, (mul_smul _ _ _).symm⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem map_mem (T : A →ₗ[C] B) {S : Set A} {S' : Set B} (h : ∀ e ∈ S, T e ∈ spanOver RC S')
    {x : A} (hx : x ∈ spanOver RC S) : T x ∈ spanOver RC S' := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, e, he, rfl⟩ := hx
    rw [map_smul]
    exact smul_mem hc (h e he)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

end Span

theorem exists_section {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {V Z : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Z] [Module Ω Z]
    (Δ : AddSubgroup (V × Z)) (N : ℕ) (hΔ : ∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ)
    (hL : LocFree R N (Δ.map (AddMonoidHom.fst V Z))) :
    ∃ σ : V →ₗ[Ω] Z, ∀ v ∈ Δ.map (AddMonoidHom.fst V Z), (v, σ v) ∈ Δ := by
  let L : Submodule R V :=
    { carrier := Δ.map (AddMonoidHom.fst V Z)
      add_mem' := fun ha hb => AddSubgroup.add_mem _ ha hb
      zero_mem' := AddSubgroup.zero_mem _
      smul_mem' := fun a x hx => hL.1 a a.2 x hx }
  have hL' : LocFree R N L.toAddSubgroup := hL
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis hL'
  have hz : ∀ i, ∃ z : Z, ((v i : V), z) ∈ Δ := by
    intro i
    obtain ⟨⟨x, z⟩, hx, h⟩ := (v i).2
    have h' : x = v i := h
    exact ⟨z, h' ▸ hx⟩
  choose z hz using hz
  refine ⟨∑ i, (φ i).smulRight (z i), fun e he => ?_⟩
  have : (e, (∑ i, (φ i).smulRight (z i)) e) = ∑ i, φ i e • ((v i : V), z i) := by
    ext
    · simp [Prod.fst_sum, hv]
    · simp [Prod.snd_sum]
  rw [this]
  exact AddSubgroup.sum_mem _ fun i _ => hΔ _ (hφ i e he) _ (hz i)

end PositivityTheory.Xgn.A_graph_restrict_bc

open PositivityTheory.Xgn.A_graph_restrict_bc in
theorem PositivityTheory.Xgn.t_graph_restrict_bc : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc] [IsScalarTower Ω C Zc] (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc), IsBaseChange C b → IsBaseChange C b' → ∀ (Δ : AddSubgroup (V × Z)) (H : AddSubgroup V) (N : ℕ), (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → LocFree R N (Δ.map (AddMonoidHom.fst V Z)) → H ≤ Δ.map (AddMonoidHom.fst V Z) → (∀ a ∈ R, ∀ v ∈ H, a • v ∈ H) → spanOver RC (Prod.map b b' '' Δ) ⊓ (spanOver RC (b '' H)).prod ⊤ = spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) ∧ (spanOver RC (Prod.map b b' '' Δ)).comap (AddMonoidHom.inr Vc Zc) = spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) := by
  intro o Ω C _ _ _ _ _ _ _ R RC _ V Vc _ _ _ _ _ _ Z Zc _ _ _ _ _ _ b b' hb _ Δ H N hΔ hL hH _
  obtain ⟨σ, hσ⟩ := exists_section R Δ N hΔ hL
  obtain ⟨τ, hτ⟩ : ∃ τ : Vc →ₗ[C] Zc, ∀ v, τ (b v) = b' (σ v) :=
    ⟨hb.lift (b' ∘ₗ σ), fun v => hb.lift_eq _ v⟩
  have K1 : ∀ x ∈ spanOver RC (Prod.map b b' '' Δ),
      x.2 - τ x.1 ∈ spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) := by
    intro x hx
    refine map_mem (LinearMap.snd C Vc Zc - τ ∘ₗ LinearMap.fst C Vc Zc) ?_ hx
    rintro _ ⟨⟨v, z⟩, hvz, rfl⟩
    refine mem_span ⟨z - σ v, ?_, by simp [hτ]⟩
    have := Δ.sub_mem hvz (hσ v ⟨(v, z), hvz, rfl⟩)
    simpa using this
  have K2 : ∀ y ∈ spanOver RC (b '' H), (y, τ y) ∈
      spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) := by
    intro y hy
    refine map_mem (LinearMap.prod LinearMap.id τ) ?_ hy
    rintro _ ⟨v, hv, rfl⟩
    refine mem_span ⟨(v, σ v), ⟨hσ v (hH hv), hv, trivial⟩, ?_⟩
    simp [hτ]
  have K3 : ∀ z ∈ spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)), ((0 : Vc), z) ∈
      spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) := by
    intro z hz
    refine map_mem (LinearMap.inr C Vc Zc) ?_ hz
    rintro _ ⟨v, hv, rfl⟩
    refine mem_span ⟨(0, v), ⟨hv, H.zero_mem, trivial⟩, ?_⟩
    simp
  have K4 : ∀ x ∈ spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))),
      x ∈ spanOver RC (Prod.map b b' '' Δ) := by
    intro x hx
    refine map_mem LinearMap.id ?_ hx
    rintro _ ⟨v, hv, rfl⟩
    exact mem_span ⟨v, hv.1, rfl⟩
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · rintro ⟨y, z⟩ ⟨h1, h2, -⟩
    have := AddSubgroup.add_mem _ (K2 y h2) (K3 _ (K1 _ h1))
    simpa using this
  · intro x hx
    refine ⟨K4 x hx, ?_, trivial⟩
    refine map_mem (LinearMap.fst C Vc Zc) ?_ hx
    rintro _ ⟨v, hv, rfl⟩
    exact mem_span ⟨v.1, hv.2.1, rfl⟩
  · intro z hz
    simpa using K1 _ hz
  · intro z hz
    exact K4 _ (K3 z hz)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_powspan

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mul_mem_gen (R : Subalgebra o Ω) (S : Set Ω) {a e : Ω} (ha : a ∈ R) (he : e ∈ S) :
    a * e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨a, ha, e, he, rfl⟩

theorem span_stable (R : Subalgebra o Ω) (S : Set Ω) {a : Ω} (ha : a ∈ R) {v : Ω}
    (hv : v ∈ spanOver R S) : a * v ∈ spanOver R S := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', e, he, rfl⟩ := hx
    rw [smul_eq_mul, ← mul_assoc]
    exact mul_mem_gen R S (R.mul_mem ha ha') he
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem span_le (R : Subalgebra o Ω) (S : Set Ω) (T : AddSubgroup Ω)
    (hT : ∀ a ∈ R, ∀ v ∈ T, a * v ∈ T) (hS : ∀ e ∈ S, e ∈ T) : spanOver R S ≤ T := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact hT a ha e (hS e he)

theorem span_loc (R : Subalgebra o Ω) (S : Set Ω) {f : Ω} (hf : f ∈ R) (b : Ω)
    (hS : ∀ e ∈ S, ∃ n : ℕ, f ^ n * (e / b) ∈ R) {v : Ω} (hv : v ∈ spanOver R S) :
    ∃ n : ℕ, f ^ n * (v / b) ∈ R := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, e, he, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hS e he
    refine ⟨n, ?_⟩
    have : f ^ n * (a • e / b) = a * (f ^ n * (e / b)) := by rw [smul_eq_mul]; ring
    rw [this]; exact R.mul_mem ha hn
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * ((x + y) / b) = f ^ m * (f ^ n * (x / b)) + f ^ n * (f ^ m * (y / b)) := by
      ring
    rw [this]
    exact R.add_mem (R.mul_mem (R.pow_mem hf m) hn) (R.mul_mem (R.pow_mem hf n) hm)
  | neg x _ hx =>
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    have : f ^ n * (-x / b) = -(f ^ n * (x / b)) := by ring
    rw [this]; exact R.neg_mem hn

theorem mem_of_loc (R : Subalgebra o Ω) (T : AddSubgroup Ω) (hT : ∀ a ∈ R, ∀ v ∈ T, a * v ∈ T)
    {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hs : ∑ l, c l * f l = 1)
    {w : Ω} (hw : ∀ l, ∃ n : ℕ, f l ^ n * w ∈ T) : w ∈ T := by
  let I : Ideal R :=
    { carrier := {r | (r : Ω) * w ∈ T}
      add_mem' := fun {x y} hx hy => by
        change ((x + y : R) : Ω) * w ∈ T
        rw [Subalgebra.coe_add, add_mul]; exact add_mem hx hy
      zero_mem' := by
        change ((0 : R) : Ω) * w ∈ T
        simp
      smul_mem' := fun r x hx => by
        change ((r * x : R) : Ω) * w ∈ T
        rw [Subalgebra.coe_mul, mul_assoc]; exact hT r r.2 _ hx }
  have h1 : (1 : R) ∈ I.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [hs]
    rw [this]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_
    obtain ⟨n, hn⟩ := hw l
    exact ⟨n, by
      change (((⟨f l, hf l⟩ : R) ^ n : R) : Ω) * w ∈ T
      simpa using hn⟩
  obtain ⟨n, hn⟩ := h1
  rw [one_pow] at hn
  have : ((1 : R) : Ω) * w ∈ T := hn
  simpa using this

theorem unpack (R : Subalgebra o Ω) (X : AddSubgroup Ω) (f : Ω)
    (h : ∃ b : Fin 1 → Ω, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f ^ n • e ∈ X) ↔
        ∃ a : Fin 1 → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q) :
    ∃ b : Ω, b ≠ 0 ∧ (∃ m : ℕ, f ^ m * b ∈ X) ∧ ∀ x ∈ X, ∃ n : ℕ, f ^ n * (x / b) ∈ R := by
  obtain ⟨b, hb, -, h⟩ := h
  have hb0 : b 0 ≠ 0 := hb.ne_zero 0
  refine ⟨b 0, hb0, ?_, fun x hx => ?_⟩
  · exact (h (b 0)).2 ⟨fun _ => 1, fun _ => ⟨0, by simpa using R.one_mem⟩, by simp⟩
  · obtain ⟨a, ha, hx'⟩ := (h x).1 ⟨0, by simpa using hx⟩
    obtain ⟨n, hn⟩ := ha 0
    refine ⟨n, ?_⟩
    have : x / b 0 = a 0 := by
      rw [hx']; simp [hb0]
    rwa [this]

theorem locFree_pow (R : Subalgebra o Ω) (p : ℕ) (X : AddSubgroup Ω) (hX : LocFree R 1 X) :
    LocFree R 1 (powSpan R p X) := by
  obtain ⟨-, k, f, c, hf, hc, hs, hl⟩ := hX
  refine ⟨fun a ha e he => span_stable R _ ha he, k, f, c, hf, hc, hs, fun l => ?_⟩
  obtain ⟨b, hb, ⟨m, hm⟩, hx⟩ := unpack R X (f l) (hl l)
  have hbp : b ^ p ≠ 0 := pow_ne_zero p hb
  refine ⟨fun _ => b ^ p, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
  · exact linearIndependent_unique_iff.2 hbp
  · rw [eq_top_iff]
    intro v _
    have : v = (v / b ^ p) • b ^ p := by simp [hbp]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · rintro ⟨n, hn⟩
    obtain ⟨n', hn'⟩ := span_loc R _ (hf l) (b ^ p) (by
      rintro _ ⟨x, hx', rfl⟩
      obtain ⟨j, hj⟩ := hx x hx'
      refine ⟨j * p, ?_⟩
      have := R.pow_mem hj p
      rwa [mul_pow, ← pow_mul, div_pow] at this) hn
    refine ⟨fun _ => e / b ^ p, fun _ => ⟨n' + n, ?_⟩, by simp [hbp]⟩
    have : f l ^ (n' + n) * (e / b ^ p) = f l ^ n' * (f l ^ n • e / b ^ p) := by
      rw [smul_eq_mul]; ring
    rwa [this]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨n, hn⟩ := ha 0
    refine ⟨n + m * p, ?_⟩
    have : f l ^ (n + m * p) • (∑ q : Fin 1, a q • b ^ p) = (f l ^ n * a 0) * (f l ^ m * b) ^ p := by
      simp only [Fin.sum_univ_one, smul_eq_mul]; ring
    rw [this]
    exact mul_mem_gen R _ hn ⟨_, hm, rfl⟩

end PositivityTheory.Xgn.A_powspan

open PositivityTheory.Xgn.A_powspan in
theorem PositivityTheory.Xgn.t_powspan : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ (p : ℕ) (X : AddSubgroup Ω), LocFree R 1 X → LocFree R 1 (powSpan R p X) ∧ powSpan RC p (spanOver RC (algebraMap Ω C '' X)) = spanOver RC (algebraMap Ω C '' powSpan R p X) := by
  intro o Ω C _ _ _ _ _ _ _ R RC hR p X hX
  refine ⟨locFree_pow R p X hX, le_antisymm ?_ ?_⟩
  · obtain ⟨-, k, f, c, hf, hc, hs, hl⟩ := hX
    refine span_le RC _ _ (fun a ha v hv => span_stable RC _ ha hv) ?_
    rintro _ ⟨z, hz, rfl⟩
    refine mem_of_loc RC _ (fun a ha v hv => span_stable RC _ ha hv)
      (fun l => algebraMap Ω C (f l)) (fun l => algebraMap Ω C (c l)) (fun l => hR _ (hf l))
      (fun l => hR _ (hc l)) ?_ fun l => ?_
    · have := congrArg (algebraMap Ω C) hs

      simpa [map_sum] using this
    · obtain ⟨b, hb, ⟨m, hm⟩, hx⟩ := unpack R X (f l) (hl l)
      have hb' : algebraMap Ω C b ≠ 0 := by simpa using hb
      obtain ⟨n, hn⟩ := span_loc RC _ (hR _ (hf l)) (algebraMap Ω C b) (by
        rintro _ ⟨x, hx', rfl⟩
        obtain ⟨j, hj⟩ := hx x hx'
        exact ⟨j, by simpa using hR _ hj⟩) hz
      refine ⟨(n + m) * p, ?_⟩
      have : algebraMap Ω C (f l) ^ ((n + m) * p) * z ^ p =
          (algebraMap Ω C (f l) ^ n * (z / algebraMap Ω C b)) ^ p *
            algebraMap Ω C (1 * (f l ^ m * b) ^ p) := by
        rw [one_mul, map_pow, map_mul, map_pow, ← mul_pow, pow_mul, ← mul_pow]
        congr 1
        field_simp
        ring
      beta_reduce
      rw [this]
      exact mul_mem_gen RC _ (RC.pow_mem hn p)
        ⟨_, mul_mem_gen R _ R.one_mem ⟨_, hm, rfl⟩, rfl⟩
  · refine span_le RC _ _ (fun a ha v hv => span_stable RC _ ha hv) ?_
    rintro _ ⟨y, hy, rfl⟩
    have : powSpan R p X ≤ (powSpan RC p (spanOver RC (algebraMap Ω C '' X))).comap
        (algebraMap Ω C).toAddMonoidHom := by
      refine span_le R _ _ (fun a ha v hv => ?_) ?_
      · change algebraMap Ω C (a * v) ∈ powSpan RC p _
        rw [map_mul]
        exact span_stable RC _ (hR a ha) hv
      · rintro _ ⟨x, hx, rfl⟩
        change algebraMap Ω C (x ^ p) ∈ powSpan RC p _
        have h1 : algebraMap Ω C (x ^ p) = 1 * (1 * algebraMap Ω C x) ^ p := by simp
        rw [h1]
        exact mul_mem_gen RC _ RC.one_mem ⟨_, mul_mem_gen RC _ RC.one_mem ⟨x, hx, rfl⟩, rfl⟩
    exact this hy
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.TestFactsBaseChange

theorem span_span {o Ω C V W : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] [AddCommGroup V] [Module Ω V] [AddCommGroup W] [Module C W]
    (R₁ : Subalgebra o Ω) (RC : Subalgebra o C) (h : ∀ a ∈ R₁, algebraMap Ω C a ∈ RC)
    (f : V → W) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hs : ∀ (a : Ω) x, f (a • x) = algebraMap Ω C a • f x)
    (g : V → V) (hg : ∀ x, g x = x) (S : Set V) :
    spanOver RC (f '' (spanOver R₁ (g '' S) : Set V)) = spanOver RC (f '' S) := by
  have h0 : f 0 = 0 := by simpa using hs 0 0
  have hn : ∀ x, f (-x) = -f x := fun x => by simpa using hs (-1) x
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, _, ⟨v, hv, rfl⟩, rfl⟩
    show c • f v ∈ spanOver RC (f '' S)
    induction hv using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hx
      rw [hs, hg, smul_smul]
      exact AddSubgroup.subset_closure ⟨_, RC.mul_mem hc (h a ha), _, ⟨e, he, rfl⟩, rfl⟩
    | zero => rw [h0, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hadd, smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [hn, smul_neg]; exact neg_mem hx
  · refine AddSubgroup.closure_mono ?_
    rintro _ ⟨c, hc, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨c, hc, _, ⟨v, AddSubgroup.subset_closure
      ⟨1, R₁.one_mem, v, ⟨v, hv, hg v⟩, (one_smul _ _).symm⟩, rfl⟩, rfl⟩

theorem bcMap_smul {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C] (ι : Type) (a : Ω) (x : ι → Ω) :
    bcMap Ω C ι (a • x) = algebraMap Ω C a • bcMap Ω C ι x := by
  rw [map_smul, algebraMap_smul]

theorem span_one {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] (R₁ : Subalgebra o Ω) (RC : Subalgebra o C)
    (h : ∀ a ∈ R₁, algebraMap Ω C a ∈ RC) (ι : Type) (S : Set (ι → Ω)) :
    spanOver RC (bcMap Ω C ι '' (spanOver R₁ (bcMap Ω Ω ι '' S) : Set (ι → Ω))) =
      spanOver RC (bcMap Ω C ι '' S) :=
  span_span R₁ RC h _ (map_add _) (bcMap_smul ι) _ (fun _ => rfl) S

theorem span_two {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] (R₁ : Subalgebra o Ω) (RC : Subalgebra o C)
    (h : ∀ a ∈ R₁, algebraMap Ω C a ∈ RC) (ι κ : Type) (S : Set ((ι → Ω) × (κ → Ω))) :
    spanOver RC (Prod.map (bcMap Ω C ι) (bcMap Ω C κ) ''
        (spanOver R₁ (Prod.map (bcMap Ω Ω ι) (bcMap Ω Ω κ) '' S) : Set ((ι → Ω) × (κ → Ω)))) =
      spanOver RC (Prod.map (bcMap Ω C ι) (bcMap Ω C κ) '' S) :=
  span_span R₁ RC h _
    (fun _ _ => Prod.ext (map_add (bcMap Ω C ι) _ _) (map_add (bcMap Ω C κ) _ _))
    (fun a _ => Prod.ext (bcMap_smul ι a _) (bcMap_smul κ a _)) _ (fun _ => rfl) S

theorem bc_bc {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] {F : Type} {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s)
    (R₁ : Subalgebra o Ω) (RC : Subalgebra o C) (h : ∀ a ∈ R₁, algebraMap Ω C a ∈ RC) :
    (D.bc R₁).bc RC = D.bc RC := by
  simp only [LieLatticeData.bc, span_one R₁ RC h, span_two R₁ RC h]

end PositivityTheory.Xgn.TestFactsBaseChange

theorem PositivityTheory.Xgn.test_facts_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R R₁ : Subalgebra o Ω), R ≤ R₁ → ∀ (p : ℕ) (w : Ω) (χ : Sg → F → Ω) (φ : Equiv.Perm Sg), D.TestFacts R p w χ φ → (D.bc R₁).TestFacts R₁ p w χ φ := by
  intro o Ω _ _ _ F _ _ n Sg r s D R R₁ hR p w χ φ H C _ _ _ _ RC hT
  obtain ⟨h1, h2, h3, h4⟩ := hT
  rw [PositivityTheory.Xgn.TestFactsBaseChange.bc_bc D R₁ RC h4]
  exact H C RC ⟨h1, h2, h3, fun a ha => h4 a (hR ha)⟩
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem PositivityTheory.Xgn.t_summand_bc : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] (b : V →ₗ[Ω] Vc), IsBaseChange C b → ∀ (L : AddSubgroup V) (U : Submodule Ω V), (∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) → Summand L U → Summand (spanOver RC (b '' L)) (Submodule.span C (b '' U)) ∧ spanOver RC (b '' L) ⊓ (Submodule.span C (b '' U)).toAddSubgroup = spanOver RC (b '' (L ⊓ U.toAddSubgroup : AddSubgroup V)) := by
  intro o Ω C _ _ _ _ _ _ _ R RC hR V Vc _ _ _ _ _ _ b hb L U hL hS
  obtain ⟨ρ, hρU, hρid, hρL⟩ := hS
  let ρC : Vc →ₗ[C] Vc := hb.lift (b ∘ₗ ρ)
  have hρC : ∀ v, ρC (b v) = b (ρ v) := fun v => hb.lift_eq _ v
  have hmap : ∀ {S T : Set V}, (∀ e ∈ S, ρ e ∈ T) →
      ∀ x ∈ spanOver RC (b '' S), ρC x ∈ spanOver RC (b '' T) := by
    intro S T hST x hx
    unfold spanOver at hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hy
      rw [map_smul, hρC]
      exact AddSubgroup.subset_closure ⟨a, ha, _, ⟨ρ e, hST e he, rfl⟩, rfl⟩
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [map_neg]
      exact neg_mem hy
  have hid : ∀ u ∈ Submodule.span C (b '' U), ρC u = u := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      rw [hρC, hρid e he]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  refine ⟨⟨ρC, fun v => ?_, hid, hmap hρL⟩, ?_⟩
  · refine hb.inductionOn v ?_ ?_ ?_
    · intro m
      show ρC (b m) ∈ _
      rw [hρC]
      exact Submodule.subset_span ⟨ρ m, hρU m, rfl⟩
    · intro s n hn
      show ρC (s • n) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ s hn
    · intro n₁ n₂ h₁ h₂
      show ρC (n₁ + n₂) ∈ _
      rw [map_add (f := _)]
      exact add_mem h₁ h₂
  · apply le_antisymm
    · rintro x ⟨hx1, hx2⟩
      rw [← hid x hx2]
      exact hmap (S := (L : Set V)) (T := ((L ⊓ U.toAddSubgroup : AddSubgroup V) : Set V))
        (fun e he => ⟨hρL e he, hρU e⟩) x hx1
    · apply (AddSubgroup.closure_le _).2
      rintro _ ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
      constructor
      · exact AddSubgroup.subset_closure ⟨a, ha, _, ⟨e, he.1, rfl⟩, rfl⟩
      · exact Submodule.smul_mem _ a (Submodule.subset_span ⟨e, he.2, rfl⟩)
end
