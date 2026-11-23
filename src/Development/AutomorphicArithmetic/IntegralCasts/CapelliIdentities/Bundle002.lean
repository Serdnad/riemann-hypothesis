module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.IntegralDomain

@[expose] public section

section

namespace UpperTheory.Reformulated.B.QuantumMinorsCasimir

noncomputable def GlRel.{u_1} : {A : Type u_1} → [Ring A] → {n : ℕ} → (Fin n → Fin n → A) → Prop := fun {A} [Ring A] {n} E =>
  ∀ (a b c d : Fin n), E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - if d = a then E c b else 0

noncomputable def Tm.{u_1} : {A : Type u_1} → [inst : Ring A] → [Algebra ℂ A] → {n : ℕ} → (Fin n → Fin n → A) → ℂ → Fin n → Fin n → A := fun {A} [Ring A] [Algebra ℂ A] {n} E u a b => (if a = b then (algebraMap ℂ A) u else 0) + E a b

noncomputable def qminor.{u_1} : {A : Type u_1} →
  [inst : Ring A] → [Algebra ℂ A] → {n t : ℕ} → (Fin n → Fin n → A) → (Fin t → Fin n) → (Fin t → Fin n) → ℂ → A := fun {A} [Ring A] [Algebra ℂ A] {n t} E a b u =>
  ∑ σ,
    ↑↑(Equiv.Perm.sign σ) *
      (List.ofFn fun k => Tm E (u - ↑↑k) (a (σ k)) (b k)).prod

noncomputable def qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : A :=
  qminor E (id : Fin n → Fin n) id u

theorem casimir : ∀ {V : Type} [inst : AddCommGroup V]
  [inst_1 : Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V),
  GlRel E →
    ∀ (k : ℂ) (φ : V),
      (E 0 0) φ + (E 1 1) φ = 0 →
        (E 0 1) φ - (E 1 0) φ = (Complex.I * k) • φ →
          (E 0 0) φ - (E 1 1) φ = Complex.I • ((E 0 1) φ + (E 1 0) φ) →
            ∀ (u : ℂ),
              (qdet E (u + 1 / 2)) φ =
                ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ := by
  intro V _ _ E h k φ h1 h2 h3 u
  have hq : ∀ v : ℂ, qdet E v φ =
      (v * (v - 1)) • φ + v • E 1 1 φ + (v - 1) • E 0 0 φ + E 0 0 (E 1 1 φ) - E 1 0 (E 0 1 φ) := by
    intro v
    have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
    have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
    unfold qdet qminor Tm
    rw [hu, Finset.sum_pair hne]
    simp [List.ofFn_succ, Module.algebraMap_end_apply]
    module
  have c (a b c d : Fin 2) := congrArg (fun f : Module.End ℂ V => f φ) (h a b c d)
  have cad := c 0 0 1 1
  have cab := c 0 0 0 1
  have cac := c 0 0 1 0
  have cdb := c 1 1 0 1
  have cdc := c 1 1 1 0
  have cbc := c 0 1 1 0
  simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, Fin.zero_eq_one_iff,
    Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, LinearMap.zero_apply] at cad cab cac cdb cdc cbc
  have z (a b : Fin 2) := congrArg (E a b) h1
  have w (a b : Fin 2) := congrArg (E a b) h2
  have g (a b : Fin 2) := congrArg (E a b) h3
  simp only [map_add (f := _), map_sub, map_smul, map_zero] at z w g
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [hq]
  linear_combination (norm := skip) u • h1 + (1 / 4 : ℂ) • (z 0 0 + z 1 1 - (g 0 0 - g 1 1)
    - Complex.I • (g 0 1 + g 1 0) - (2 * Complex.I) • h2 + (w 0 1 - w 1 0) + (Complex.I * k) • h2
    + (2 : ℂ) • cad - Complex.I • (cab + cac - cdb - cdc) + (2 : ℂ) • cbc)
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

end UpperTheory.Reformulated.B.QuantumMinorsCasimir
end

section

namespace UpperTheory.Reformulated.B.Qf10

noncomputable def GlRel.{u_1} : {A : Type u_1} → [Ring A] → {n : ℕ} → (Fin n → Fin n → A) → Prop := fun {A} [Ring A] {n} E =>
  ∀ (a b c d : Fin n), E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - if d = a then E c b else 0

noncomputable def Tm.{u_1} : {A : Type u_1} → [inst : Ring A] → [Algebra ℂ A] → {n : ℕ} → (Fin n → Fin n → A) → ℂ → Fin n → Fin n → A := fun {A} [Ring A] [Algebra ℂ A] {n} E u a b => (if a = b then (algebraMap ℂ A) u else 0) + E a b

noncomputable def qminor.{u_1} : {A : Type u_1} →
  [inst : Ring A] → [Algebra ℂ A] → {n t : ℕ} → (Fin n → Fin n → A) → (Fin t → Fin n) → (Fin t → Fin n) → ℂ → A := fun {A} [Ring A] [Algebra ℂ A] {n t} E a b u =>
  ∑ σ, ↑↑(Equiv.Perm.sign σ) * (List.ofFn fun k => Tm E (u - ↑↑k) (a (σ k)) (b k)).prod

noncomputable def qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : A :=
  qminor E (id : Fin n → Fin n) id u

theorem casimir : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V]
  (E : Fin 2 → Fin 2 → Module.End ℂ V),
  GlRel E →
    ∀ (k : ℂ) (φ : V),
      (E 0 0) φ + (E 1 1) φ = 0 →
        (E 0 1) φ - (E 1 0) φ = (Complex.I * k) • φ →
          (E 0 0) φ - (E 1 1) φ = Complex.I • ((E 0 1) φ + (E 1 0) φ) →
            ∀ (u : ℂ),
              (qdet E (u + 1 / 2)) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ := by
  intro V _ _ E hE k φ h1 h2 h3 u
  have rel : ∀ a b c d : Fin 2, E a b (E c d φ) - E c d (E a b φ) =
      (if b = c then E a d φ else 0) - (if d = a then E c b φ else 0) := by
    intro a b c d
    have h := congrArg (fun f : Module.End ℂ V => f φ) (hE a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [h]
    split_ifs <;> simp
  have rab : E 0 0 (E 0 1 φ) - E 0 1 (E 0 0 φ) = E 0 1 φ := by simpa using rel 0 0 0 1
  have rac : E 0 0 (E 1 0 φ) - E 1 0 (E 0 0 φ) = -E 1 0 φ := by simpa using rel 0 0 1 0
  have rdb : E 1 1 (E 0 1 φ) - E 0 1 (E 1 1 φ) = -E 0 1 φ := by simpa using rel 1 1 0 1
  have rdc : E 1 1 (E 1 0 φ) - E 1 0 (E 1 1 φ) = E 1 0 φ := by simpa using rel 1 1 1 0
  have rbc : E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) = E 0 0 φ - E 1 1 φ := by simpa using rel 0 1 1 0
  have rad : E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) = 0 := by simpa using rel 0 0 1 1
  have t1 : ∀ X : Module.End ℂ V, X (E 0 0 φ) + X (E 1 1 φ) = 0 := fun X => by
    rw [← map_add (f := _), h1, map_zero]
  have t2 : ∀ X : Module.End ℂ V,
      X (E 0 1 φ) - X (E 1 0 φ) = (Complex.I * k) • X φ := fun X => by
    rw [← map_sub, h2, map_smul]
  have t3 : ∀ X : Module.End ℂ V, X (E 0 0 φ) - X (E 1 1 φ) =
      Complex.I • (X (E 0 1 φ) + X (E 1 0 φ)) := fun X => by
    rw [← map_sub, h3, map_smul, map_add (f := _)]
  have hc : (E 0 0 (E 0 0 φ) - E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) + E 1 1 (E 1 1 φ)) +
      (E 0 1 (E 0 1 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ)) =
      (-2 * k) • φ := by
    linear_combination (norm := module)
      (t3 (E 0 0) - t3 (E 1 1) + Complex.I • t3 (E 0 1) + Complex.I • t3 (E 1 0)) +
        Complex.I • (rab + rac - rdb - rdc) + (2 * Complex.I) • h2 +
        Complex.I_sq • (E 0 1 (E 0 1 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ) +
          (2 * k) • φ)
  have hw : E 0 1 (E 0 1 φ) - E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ) =
      (-k ^ 2) • φ := by
    linear_combination (norm := module)
      (t2 (E 0 1) - t2 (E 1 0)) + (Complex.I * k) • h2 + Complex.I_sq • (k ^ 2 • φ)
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hq : ∀ v : ℂ, qdet E v φ =
      v • ((v - 1) • φ + E 1 1 φ) + ((v - 1) • E 0 0 φ + E 0 0 (E 1 1 φ)) - E 1 0 (E 0 1 φ) := by
    intro v
    unfold qdet qminor Tm
    rw [hu, Finset.sum_pair hne]
    simp [List.ofFn_succ, Module.algebraMap_end_apply]
    module
  rw [hq]
  linear_combination (norm := module)
    u • h1 + (1 / 4 : ℂ) • (t1 (E 0 0) + t1 (E 1 1)) + (1 / 2 : ℂ) • rad - (1 / 4 : ℂ) • hc +
      (1 / 4 : ℂ) • hw + (1 / 2 : ℂ) • rbc

end UpperTheory.Reformulated.B.Qf10
end

section

theorem UpperTheory.Reformulated.B.Qe54.exists_of_li :
    ∀ {Q ι : Type} [inst : AddCommGroup Q]
    [inst_1 : _root_.Module ℂ Q] [Finite ι] (f : ι → Q →ₗ[ℂ] ℂ),
    LinearIndependent ℂ f → ∀ (v : ι → ℂ), ∃ (q : Q), ∀ (i : ι), (f i : Q → ℂ) q = v i := by
  intro Q ι _ _ _ f hf v
  classical
  have := Fintype.ofFinite ι
  have hs : Function.Surjective (LinearMap.pi f : Q →ₗ[ℂ] (ι → ℂ)) := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    have hsum : ∑ i, φ (fun j => if i = j then 1 else 0) • f i = 0 := by
      ext q
      have h1 : φ (LinearMap.pi f q) = 0 := LinearMap.congr_fun hφ q
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [LinearMap.sum_apply, mul_comm] using h1
    have h0 := Fintype.linearIndependent_iff.1 hf _ hsum
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [h0]
  obtain ⟨q, hq⟩ := hs v
  exact ⟨q, fun i => congrFun hq i⟩
end

section

noncomputable def UpperTheory.Reformulated.B.Qk18.PolyIn :
    {R : Type} → [inst : Ring R] → [Algebra ℂ R] → (ℂ → R) → ℕ → Prop :=
    fun {R : Type} [Ring R] [Algebra ℂ R] (f : ℂ → R) (d : ℕ) ↦
      ∃ (a : ℕ → R), ∀ (s : ℂ), f s = ∑ k ∈ Finset.range (d + (1 : ℕ)), s ^ k • a k

theorem UpperTheory.Reformulated.B.Qk18.polyIn_mul :
    ∀ {R : Type} [inst : Ring R] [inst_1 : Algebra ℂ R] {f g : ℂ → R} {d₁ d₂ : ℕ},
      UpperTheory.Reformulated.B.Qk18.PolyIn f d₁ →
        UpperTheory.Reformulated.B.Qk18.PolyIn g d₂ → UpperTheory.Reformulated.B.Qk18.PolyIn (fun (t : ℂ) ↦ f t * g t) (d₁ + d₂) := by
  intro R _ _ f g d₁ d₂ hf hg
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun n => ∑ i ∈ Finset.range (d₁ + 1), ∑ j ∈ Finset.range (d₂ + 1),
    if i + j = n then a i * b j else 0, fun s => ?_⟩
  show f s * g s = _
  rw [ha s, hb s, Finset.sum_mul_sum]
  simp only [Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hmem : i + j ∈ Finset.range (d₁ + d₂ + 1) := by
    rw [Finset.mem_range] at hi hj ⊢
    omega
  rw [Finset.sum_eq_single_of_mem (i + j) hmem]
  · rw [if_pos rfl, smul_mul_smul_comm, pow_add]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), smul_zero]
end

section

noncomputable def UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF :
    {A : Type} → [inst : Ring A] → [Algebra ℂ A] → (ℂ → A) → Prop :=
  fun {A} _ _ f => ∃ p : Polynomial A, ∀ Y : ℂ, f Y = Polynomial.eval (algebraMap ℂ A Y) p
end

section

noncomputable def UpperTheory.Reformulated.B.IdempotentMatrixMonoidHom.prM :
    {R A : Type} →
      [inst : CommRing R] →
        [inst_1 : CommRing A] →
          [Algebra R A] →
            (e : R) → e * e = e → (ι : Type) → [inst : Fintype ι] → [inst_3 : DecidableEq ι] → Matrix ι ι A →* Matrix ι ι A :=
  fun {R A} _ _ _ e he ι _ _ =>
    { toFun := fun M => e • M + (1 - e) • (1 : Matrix ι ι A)
      map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
      map_mul' := fun M N => by
        have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
        have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
        have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
          smul_smul, he, h1, h2, h3, zero_smul, add_zero, zero_add, Matrix.mul_one] }
end

section

theorem UpperTheory.Reformulated.B.CoproductGeometry.cop_geom :
    ∀ {R κ : Type} [inst : CommRing R] [IsNoetherianRing R]
    [inst_2 : NormedField κ] [IsUltrametricDist κ] (m : Ideal R) (y : R →+* κ),
    (∀ (x : R), ‖(y : R → κ) x‖ ≤ (1 : ℝ)) →
      (∀ x ∈ m, ‖(y : R → κ) x‖ < (1 : ℝ)) →
        ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ (n : ℕ), ∀ x ∈ m ^ n, ‖(y : R → κ) x‖ ≤ a ^ n := by
  intro R κ _ _ _ _ m y h1 hm
  classical
  have key : ∀ T : Finset R, (∀ s ∈ T, ‖y s‖ < 1) →
      ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ s ∈ T, ‖y s‖ ≤ a := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨0, by norm_num, le_rfl, by simp⟩
    | insert b T hb ih =>
      intro h
      obtain ⟨a, ha1, ha0, ha⟩ := ih (fun s hs => h s (Finset.mem_insert_of_mem hs))
      refine ⟨max a ‖y b‖, max_lt ha1 (h b (Finset.mem_insert_self _ _)),
        le_max_of_le_left ha0, ?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact le_max_right _ _
      · exact (ha s hs).trans (le_max_left _ _)
  obtain ⟨S, hS⟩ : m.FG := IsNoetherian.noetherian m
  obtain ⟨a, ha1, ha0, ha⟩ := key S (fun s hs => hm s (hS ▸ Ideal.subset_span hs))
  have hgen : ∀ z ∈ m, ‖y z‖ ≤ a := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact ha x hx
    | zero => simpa using ha0
    | add u v _ _ hu hv =>
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
    | smul r u _ hu =>
      rw [smul_eq_mul, map_mul, norm_mul]
      calc ‖y r‖ * ‖y u‖ ≤ 1 * a := mul_le_mul (h1 r) hu (norm_nonneg _) zero_le_one
        _ = a := one_mul a
  refine ⟨a, ha1, ha0, ?_⟩
  intro n
  induction n with
  | zero => intro x _; simpa using h1 x
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem u hu v hv =>
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih u hu) (hgen v hv) (norm_nonneg _) (pow_nonneg ha0 n)
    | add u _ v _ hu hv =>
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
end

section

theorem UpperTheory.Reformulated.B.Qf4.pow_sub_one_mem :
    ∀ {S : Type} [inst : CommRing S] (J : Ideal S) (p : ℕ),
    Nat.Prime p → (↑p : S) ∈ J → ∀ (x : S), x - (1 : S) ∈ J → ∀ (j : ℕ), x ^ p ^ j - (1 : S) ∈ J ^ (j + (1 : ℕ)) := by
  intro S _ J p _ hp x hx j
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have h1 : x ^ p ^ j - 1 ∈ J := Ideal.pow_le_self (Nat.succ_ne_zero j) ih
    have h2 : (∑ i ∈ Finset.range p, (x ^ p ^ j) ^ i) ∈ J := by
      have h3 : (∑ i ∈ Finset.range p, (x ^ p ^ j) ^ i)
          = (∑ i ∈ Finset.range p, ((x ^ p ^ j) ^ i - 1)) + (p : S) := by
        simp [Finset.sum_sub_distrib]
      rw [h3]
      refine J.add_mem (J.sum_mem fun i _ => ?_) hp
      exact J.mem_of_dvd (sub_one_dvd_pow_sub_one _ i) h1
    rw [pow_succ p j, pow_mul, ← mul_geom_sum, pow_succ J (j + 1)]
    exact Ideal.mul_mem_mul ih h2
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.OmegaConstruction.Om :
    (O : Type) → [inst : CommRing O] → [IsLocalRing O] → ℕ → Type :=
    fun (O : Type) [CommRing O] [IsLocalRing O] (m : ℕ) ↦ O ⧸ IsLocalRing.maximalIdeal O ^ m

noncomputable def UpperTheory.Reformulated.B.OmegaConstruction.red :
    {O : Type} →
      [inst : CommRing O] →
        [inst_1 : IsLocalRing O] →
          {n : ℕ} → (m : ℕ) → Matrix (Fin n) (Fin n) O → Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.OmegaConstruction.Om O m) :=
    fun {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (Z : Matrix (Fin n) (Fin n) O) ↦
      Z.map (⇑(Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ m)) : O → O ⧸ IsLocalRing.maximalIdeal O ^ m)

theorem UpperTheory.Reformulated.B.OmegaConstruction.red_sub :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O),
      UpperTheory.Reformulated.B.OmegaConstruction.red m (A - B) = UpperTheory.Reformulated.B.OmegaConstruction.red m A - UpperTheory.Reformulated.B.OmegaConstruction.red m B := by
  intro O _ _ n m A B
  ext i j
  exact map_sub (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ m)) (A i j) (B i j)
end

section

theorem UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero :
    ∀ (R Q : Type) [inst : CommRing R] [inst_1 : IsLocalRing R]
    [inst_2 : AddCommGroup Q] [inst_3 : _root_.Module R Q] [Finite Q],
    ∃ (c : ℕ), ∀ a ∈ IsLocalRing.maximalIdeal R ^ c, ∀ (z : Q), a • z = (0 : Q) := by
  intro R Q _ _ _ _ _
  haveI : Finite (Submodule R Q) :=
    Finite.of_injective (fun N : Submodule R Q => (N : Set Q)) SetLike.coe_injective
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧
      (IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)) =
        IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R Q))
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, j, hlt, h⟩
    · exact ⟨j, i, hlt, h.symm⟩
  have hbot : IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (Submodule.fg_def.2 ⟨_, Set.toFinite _, Submodule.span_eq _⟩) ?_
      (IsLocalRing.maximalIdeal_le_jacobson _)
    calc IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)
        = IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := h
      _ ≤ IsLocalRing.maximalIdeal R ^ (i + 1) • (⊤ : Submodule R Q) :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)
      _ = _ := by rw [pow_succ', Submodule.mul_smul]
  refine ⟨i, fun a ha z => ?_⟩
  have hz : a • z ∈ IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rwa [hbot, Submodule.mem_bot] at hz
end

section

namespace UpperTheory.Reformulated.B.FinitelyGeneratedModPow

theorem fg_mod_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n := by
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, by simp⟩⟩
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := IsNoetherian.noetherian (m ^ n)
    have key : ∀ z ∈ Ideal.span (s : Set A),
        ∃ w ∈ Submodule.span O (s : Set A), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact ⟨z, Submodule.subset_span hz, by simp⟩
      | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
      | add z₁ z₂ _ _ h₁ h₂ =>
        obtain ⟨w₁, hw₁, e₁⟩ := h₁
        obtain ⟨w₂, hw₂, e₂⟩ := h₂
        refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_⟩
        have : z₁ + z₂ - (w₁ + w₂) = (z₁ - w₁) + (z₂ - w₂) := by ring
        rw [this]
        exact Ideal.add_mem _ e₁ e₂
      | smul a z hz h =>
        obtain ⟨w, hw, e⟩ := h
        obtain ⟨c, hc⟩ := hres a
        have hz' : z ∈ m ^ n := by rw [← hs]; exact hz
        refine ⟨c • w, Submodule.smul_mem _ c hw, ?_⟩
        have : a • z - c • w = z * (a - algebraMap O A c) + algebraMap O A c * (z - w) := by
          rw [smul_eq_mul, Algebra.smul_def]; ring
        rw [this]
        refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ e)
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' hc
    refine ⟨N ⊔ Submodule.span O (s : Set A), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, e⟩ := key _ hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rwa [← sub_sub]

end UpperTheory.Reformulated.B.FinitelyGeneratedModPow
end

section

theorem UpperTheory.Reformulated.B.Qe46.sum_char :
    ∀ {G : Type} [inst : CommGroup G] [inst_1 : Fintype G] (χ : G →* ℂˣ),
    χ ≠ (1 : G →* ℂˣ) → ∑ z : G, (↑((χ : G → ℂˣ) z) : ℂ) = (0 : ℂ) := by
  intro G _ _ χ hχ
  have hne : (Units.coeHom ℂ).comp χ ≠ 1 := by
    intro h
    apply hχ
    ext z
    have hz := DFunLike.congr_fun h z
    simpa using hz
  simpa using sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) hne
end
