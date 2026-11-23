module

public import Formalism.SatakeDualWeyl.Statement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace PI.UnitaryGroupMassFormula.InHHClassFin

open DoubleCoset

theorem classSet_mono {G : Type} [Group G] (Γ K K' : Subgroup G) (h : K ≤ K') :
    Finite (Formalism.UG.ClassSet Γ K) → Finite (Formalism.UG.ClassSet Γ K') := by
  intro hfin
  let f : Formalism.UG.ClassSet Γ K → Formalism.UG.ClassSet Γ K' := Quotient.map' id (fun a b hab => by
    have hb : b ∈ DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) := by
      rw [show DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) = DoubleCoset.doubleCoset b Γ K from hab]
      exact DoubleCoset.mem_doubleCoset_self Γ K b
    obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.mem_doubleCoset.mp hb
    have hb' : b ∈ DoubleCoset.doubleCoset a (Γ : Set G) (K' : Set G) :=
      DoubleCoset.mem_doubleCoset.mpr ⟨x, hx, y, h hy, hxy⟩
    exact (DoubleCoset.doubleCoset_eq_of_mem hb').symm)
  refine Finite.of_surjective f (fun q => ?_)
  induction q using Quotient.inductionOn' with
  | h x => exact ⟨Quotient.mk'' x, rfl⟩

theorem classSet_finIdx {G : Type} [Group G] (Γ K K' : Subgroup G) (h : K' ≤ K)
    (hi : K'.relIndex K ≠ 0) :
    Finite (Formalism.UG.ClassSet Γ K) → Finite (Formalism.UG.ClassSet Γ K') := by
  intro hf
  haveI : (K'.subgroupOf K).FiniteIndex := ⟨hi⟩
  haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  let f : Formalism.UG.ClassSet Γ K × (K ⧸ K'.subgroupOf K) → Formalism.UG.ClassSet Γ K' :=
    fun p => DoubleCoset.mk Γ K' (p.1.out * ((p.2.out : K) : G))
  refine Finite.of_surjective f ?_
  intro q
  obtain ⟨g, rfl⟩ := Quotient.mk''_surjective q
  obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mk_out_eq_mul Γ K g
  let k : K := ⟨b⁻¹, K.inv_mem hb⟩
  refine ⟨(DoubleCoset.mk Γ K g, (QuotientGroup.mk k : K ⧸ K'.subgroupOf K)), ?_⟩
  have ht : ((QuotientGroup.mk k : K ⧸ K'.subgroupOf K).out)⁻¹ * k ∈ K'.subgroupOf K :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  rw [Subgroup.mem_subgroupOf] at ht
  show DoubleCoset.mk Γ K' _ = DoubleCoset.mk Γ K' g
  rw [DoubleCoset.eq]
  refine ⟨a⁻¹, Γ.inv_mem ha, _, ht, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, k]
  rw [hab]; group

theorem classSet_map {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (Γ K : Subgroup G) :
    Finite (Formalism.UG.ClassSet (Γ.map Φ.toMonoidHom) (K.map Φ.toMonoidHom)) →
      Finite (Formalism.UG.ClassSet Γ K) := by
  intro hfin
  have himg : ∀ a : G, Φ '' DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) =
      DoubleCoset.doubleCoset (Φ a) ((Γ.map Φ.toMonoidHom : Subgroup G') : Set G')
        ((K.map Φ.toMonoidHom : Subgroup G') : Set G') := by
    intro a
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hx
      exact DoubleCoset.mem_doubleCoset.2 ⟨Φ h, ⟨h, hh, rfl⟩, Φ k, ⟨k, hk, rfl⟩, by simp [map_mul]⟩
    · intro hy
      obtain ⟨h', ⟨h, hh, rfl⟩, k', ⟨k, hk, rfl⟩, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
      exact ⟨h * a * k, DoubleCoset.mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩, by simp [map_mul]⟩
  let f : Formalism.UG.ClassSet Γ K → Formalism.UG.ClassSet (Γ.map Φ.toMonoidHom) (K.map Φ.toMonoidHom) :=
    Quotient.map' Φ (fun a b hab => by
      show DoubleCoset.doubleCoset (Φ a) _ _ = DoubleCoset.doubleCoset (Φ b) _ _
      rw [← himg, ← himg]
      exact congrArg (fun s => Φ '' s) hab)
  refine Finite.of_injective f (fun x y hxy => ?_)
  induction x using Quotient.inductionOn' with
  | h a =>
    induction y using Quotient.inductionOn' with
    | h b =>
      apply Quotient.sound'
      have h1 : DoubleCoset.doubleCoset (Φ a) ((Γ.map Φ.toMonoidHom : Subgroup G') : Set G')
          ((K.map Φ.toMonoidHom : Subgroup G') : Set G') =
          DoubleCoset.doubleCoset (Φ b) ((Γ.map Φ.toMonoidHom : Subgroup G') : Set G')
          ((K.map Φ.toMonoidHom : Subgroup G') : Set G') := Quotient.exact' hxy
      rw [← himg, ← himg] at h1
      exact (Set.image_injective.2 Φ.injective) h1

end PI.UnitaryGroupMassFormula.InHHClassFin
end

section

noncomputable section

open NumberField Matrix IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

section Generic

variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}

theorem lvA_mulVec_int {ι κ : Type} [Fintype κ] (M : Matrix ι κ R) (hM : ∀ i j, M i j ∈ S)
    (v : κ → R) (hv : ∀ i, v i ∈ S) : ∀ i, (M *ᵥ v) i ∈ S := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact S.sum_mem fun j _ => S.mul_mem (hM i j) (hv j)

theorem lvA_key {ι : Type} [Fintype ι] [DecidableEq ι] (LA : Submodule S (Fin n → R))
    (c₁ c₂ c g : R)
    (h₁ : ∀ y ∈ LA, ∀ i, c₁ * y i ∈ S) (h₂ : ∀ y : Fin n → R, (∀ i, y i ∈ S) → c₂ • y ∈ LA)
    (P : Matrix (Fin n) ι R) (Q : Matrix ι (Fin n) R) (hPQ : P * Q = 1)
    (hP : ∀ i j, (c • P) i j ∈ S) (hQ : ∀ i j, (c • Q) i j ∈ S)
    (N : Matrix ι ι R) (hN : ∀ i j, N i j ∈ S) (u : Matrix ι ι R)
    (hu : u = 1 + (g * c₂ * c * c * c₁) • N) :
    ∀ y ∈ LA, ∃ z ∈ LA, (P * u * Q - 1) *ᵥ y = g • z := by
  intro y hy
  have hcy : ∀ i, (c₁ • y) i ∈ S := fun i => by
    simpa [Pi.smul_apply, smul_eq_mul] using h₁ y hy i
  have hw : ∀ i, ((c • P) *ᵥ (N *ᵥ ((c • Q) *ᵥ (c₁ • y)))) i ∈ S :=
    lvA_mulVec_int S _ hP _ (lvA_mulVec_int S _ hN _ (lvA_mulVec_int S _ hQ _ hcy))
  refine ⟨c₂ • ((c • P) *ᵥ (N *ᵥ ((c • Q) *ᵥ (c₁ • y)))), h₂ _ hw, ?_⟩
  have hexp : P * u * Q - 1 = (g * c₂ * c * c * c₁) • (P * N * Q) := by
    rw [hu, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPQ, Matrix.mul_smul, Matrix.smul_mul]
    abel
  rw [hexp]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, ← Matrix.mulVec_mulVec]
  congr 1
  ring

theorem lvA_maps {ι : Type} [Fintype ι] [DecidableEq ι] (LA : Submodule S (Fin n → R))
    (c₁ c₂ c g : R) (hg : g ∈ S)
    (h₁ : ∀ y ∈ LA, ∀ i, c₁ * y i ∈ S) (h₂ : ∀ y : Fin n → R, (∀ i, y i ∈ S) → c₂ • y ∈ LA)
    (P : Matrix (Fin n) ι R) (Q : Matrix ι (Fin n) R) (hPQ : P * Q = 1)
    (hP : ∀ i j, (c • P) i j ∈ S) (hQ : ∀ i j, (c • Q) i j ∈ S)
    (N : Matrix ι ι R) (hN : ∀ i j, N i j ∈ S) (u : Matrix ι ι R)
    (hu : u = 1 + (g * c₂ * c * c * c₁) • N) :
    ∀ y ∈ LA, (P * u * Q) *ᵥ y ∈ LA := by
  intro y hy
  obtain ⟨z, hz, hzeq⟩ := lvA_key S LA c₁ c₂ c g h₁ h₂ P Q hPQ hP hQ N hN u hu y hy
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add'] at hzeq
  rw [hzeq]
  exact LA.add_mem hy (LA.smul_mem (⟨g, hg⟩ : S) hz)

theorem lvA_princ_form {ι : Type} [Fintype ι] [DecidableEq ι] (d : S) (u : GL ι R)
    (hu : u ∈ Formalism.UG.princ (n := ι) S.subtype (Ideal.span {d})) :
    ∃ N : Matrix ι ι R, (∀ i j, N i j ∈ S) ∧ (u : Matrix ι ι R) = 1 + (d : R) • N := by
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
  have h1 : Formalism.UG.redGL (Ideal.span {d}) u' = 1 := Subgroup.mem_bot.1 (Subgroup.mem_comap.1 hu')
  have hent : ∀ i j, ∃ a : S, a * d = (u' : Matrix ι ι S) i j - (1 : Matrix ι ι S) i j := by
    intro i j
    have h2 := congrArg (fun g : GL ι (S ⧸ Ideal.span {d}) => (g : Matrix ι ι (S ⧸ Ideal.span {d})) i j) h1
    simp only [Formalism.UG.redGL, Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Units.val_one] at h2
    have h3 : (u' : Matrix ι ι S) i j - (1 : Matrix ι ι S) i j ∈ Ideal.span {d} := by
      rw [← Ideal.Quotient.eq]
      have h2' : Ideal.Quotient.mk (Ideal.span {d}) ((u' : Matrix ι ι S) i j) =
          (1 : Matrix ι ι (S ⧸ Ideal.span {d})) i j := h2
      rw [h2', Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    exact Ideal.mem_span_singleton'.1 h3
  choose a ha using hent
  refine ⟨fun i j => (a i j : R), fun i j => (a i j).2, ?_⟩
  ext i j
  have h4 := congrArg (fun s : S => (s : R)) (ha i j)
  push_cast at h4
  show S.subtype ((u' : Matrix ι ι S) i j) = (1 : Matrix ι ι R) i j + (d : R) * (a i j : R)
  rw [Subring.coe_subtype, Matrix.one_apply]
  rw [Matrix.one_apply] at h4
  split_ifs at h4 ⊢ <;> simp at h4 ⊢ <;> linear_combination -h4

end Generic

end PI.UnitaryGroupMassFormula.InHHClassFin
end
end
