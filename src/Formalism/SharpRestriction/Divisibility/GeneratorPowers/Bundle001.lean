module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

namespace CIndRelPf

theorem dim_eq_card {S : Type} [CommRing S] [Nontrivial S] {ι : Type} [Fintype ι] {d : ℕ}
    (u : ι → Fin d → S) (h : ∀ v : Fin d → S, ∃! a : ι → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) :
    d = Fintype.card ι := by
  let f : (ι → S) →ₗ[S] (Fin d → S) :=
    { toFun := fun a j => ∑ ℓ, a ℓ * u ℓ j
      map_add' := by
        intro a b
        funext j
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        funext j
        simp [Finset.mul_sum, mul_assoc] }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      obtain ⟨c, -, hc⟩ := h (f a)
      have ha : a = c := hc a (fun j => rfl)
      have hb : b = c := hc b (fun j => congrFun hab.symm j)
      rw [ha, hb]
    · intro v
      obtain ⟨a, ha, -⟩ := h v
      exact ⟨a, funext ha⟩
  have hr := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun] at hr
  exact hr.symm

end CIndRelPf

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.SatLin

theorem exists_basis_of_saturated {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {d r : ℕ}
    (u : Fin r → (Fin d → R)) (hu : LinearIndependent R u)
    (hs : ∀ (v : Fin d → R) (a : R), a ≠ 0 → a • v ∈ Submodule.span R (Set.range u) →
      v ∈ Submodule.span R (Set.range u)) :
    ∃ (w : Fin d → Fin d → R) (emb : Fin r ↪ Fin d), (∀ i, w (emb i) = u i) ∧
      ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j := by
  classical
  set S := Submodule.span R (Set.range u) with hS
  haveI : NoZeroSMulDivisors R ((Fin d → R) ⧸ S) := by
    refine ⟨fun {a q} h => ?_⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective S q
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      rw [Submodule.Quotient.mk_eq_zero]
      exact hs v a ha h
  haveI : Module.Free R ((Fin d → R) ⧸ S) := Module.free_of_finite_type_torsion_free'
  let bQ := Module.Free.chooseBasis R ((Fin d → R) ⧸ S)
  choose s' hs' using fun j => Submodule.Quotient.mk_surjective S (bQ j)
  let w' := Sum.elim u s'
  have hmk : ∀ i, Submodule.Quotient.mk (p := S) (u i) = 0 := fun i =>
    (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent R w' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    have hr : ∀ j, g (Sum.inr j) = 0 := by
      have h1 := congrArg S.mkQ hg

      simp only [w', Sum.elim_inl, Sum.elim_inr, map_add (f := _), map_sum, map_smul, map_zero, Submodule.mkQ_apply,
      hmk, hs', smul_zero, Finset.sum_const_zero, zero_add] at h1
      exact Fintype.linearIndependent_iff.1 bQ.linearIndependent _ h1
    have hl : ∀ i, g (Sum.inl i) = 0 := by
      simp only [hr, zero_smul, Finset.sum_const_zero, add_zero, w', Sum.elim_inl] at hg
      exact Fintype.linearIndependent_iff.1 hu _ hg
    rintro (i | j)
    · exact hl i
    · exact hr j
  have hsp : ⊤ ≤ Submodule.span R (Set.range w') := by
    intro v _
    have hv := bQ.sum_repr (Submodule.Quotient.mk (p := S) v)
    have ht : (∑ j, bQ.repr (Submodule.Quotient.mk (p := S) v) j • s' j) ∈ Submodule.span R (Set.range w') :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
    have hvt : v - ∑ j, bQ.repr (Submodule.Quotient.mk (p := S) v) j • s' j ∈ S := by

      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
      simp only [map_smul, Submodule.mkQ_apply, hs']
      rw [hv, sub_self]
    have hSle : S ≤ Submodule.span R (Set.range w') :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    have h := Submodule.add_mem _ (hSle hvt) ht
    rwa [sub_add_cancel] at h
  let B := Module.Basis.mk hli hsp
  have hcard : Fintype.card (Fin r ⊕ Module.Free.ChooseBasisIndex R ((Fin d → R) ⧸ S)) = d := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  let b := B.reindex e
  refine ⟨fun k => b k, ⟨fun i => e (Sum.inl i), e.injective.comp Sum.inl_injective⟩, fun i => ?_, fun v => ?_⟩
  · simp [b, B, Module.Basis.reindex_apply, Module.Basis.mk_apply, w']
  · refine ⟨fun k => b.repr v k, fun j => ?_, fun a ha => ?_⟩
    · have h := congrFun (b.sum_repr v) j
      simpa [Finset.sum_apply, smul_eq_mul] using h
    · have hv : ∑ k, a k • b k = v := funext fun j => by simpa [Finset.sum_apply, smul_eq_mul] using ha j
      funext k
      rw [← hv]

      simp [map_sum, Module.Basis.repr_self, Finsupp.single_apply]

end Formalism.L2.Pj.SatLin
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

def WhitenStatement : Prop :=
  ∀ (d : ℕ) (L : Matrix (Fin d) (Fin d) ℝ), L.PosDef →
    ∃ R : Matrix (Fin d) (Fin d) ℝ, IsUnit R.det ∧ L = Rᵀ * R

def HalfTraceStatement : Prop :=
  ∀ (d : ℕ) (L G K R : Matrix (Fin d) (Fin d) ℝ), L = Rᵀ * R → IsUnit R.det → G.PosSemidef →
    Kᵀ * G = -(G * K) → K * L = -(L * Kᵀ) → IsUnit K.det →
    ∀ x : Fin d → ℝ, x ⬝ᵥ (G *ᵥ x) ≤
      (1 / 2) * trace (L * G) * (((R⁻¹)ᵀ *ᵥ x) ⬝ᵥ ((R⁻¹)ᵀ *ᵥ x))

def ShortDualStatement : Prop :=
  ∀ (d : ℕ) (L R : Matrix (Fin d) (Fin d) ℝ) (μ : ℝ), 0 < d → L = Rᵀ * R → IsUnit R.det → 0 < μ →
    (∀ t : Fin d → ℤ, t ≠ 0 → μ ^ 2 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (L *ᵥ fun i => (t i : ℝ))) →
    ∀ δ : ℝ, 0 < δ → ∃ c : Fin d → Fin d → ℤ, LinearIndependent ℤ c ∧
      ∀ j, ((R⁻¹)ᵀ *ᵥ fun i => (c j i : ℝ)) ⬝ᵥ ((R⁻¹)ᵀ *ᵥ fun i => (c j i : ℝ)) ≤
        ((d : ℝ) / μ + δ) ^ 2

def FiniteShortStatement : Prop :=
  ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℝ), G.PosDef → ∀ B : ℝ,
    {c : Fin d → ℤ | (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) ≤ B}.Finite

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg

open NumberField Matrix

section Core

variable {E : Type} [Field E] [NumberField E] {κ : Type} [Fintype κ]

theorem hom_basis {R' : Type} [Ring R'] (f : 𝓞 E →+* R') (b : Module.Basis κ ℤ (𝓞 E)) (x : 𝓞 E) :
    f x = ∑ k, ((b.repr x k : ℤ) : R') * f (b k) := by
  conv_lhs => rw [← b.sum_repr x]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, zsmul_eq_mul]

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq κ]

theorem decomp_of_inv (ρ : 𝓞 E →+* Module.End R M) (χ : ι → (𝓞 E →+* R)) (b : Module.Basis κ ℤ (𝓞 E))
    (Cm : κ → ι → R) (hAC : ∀ σ τ, ∑ i, χ σ (b i) * Cm i τ = if σ = τ then 1 else 0)
    (hCA : ∀ i j, ∑ τ, Cm i τ * χ τ (b j) = if i = j then 1 else 0) :
    (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
    (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0) := by
  classical
  set Q : ι → M → M := fun σ m => ∑ i, Cm i σ • ρ (b i) m with hQ
  have hcoef : ∀ (a : 𝓞 E) (i : κ), ∑ τ, χ τ a * Cm i τ = ((b.repr a i : ℤ) : R) := by
    intro a i
    have h1 : ∀ τ, χ τ a = ∑ k, ((b.repr a k : ℤ) : R) * χ τ (b k) := fun τ => hom_basis (χ τ) b a
    have hCA' : ∀ k, ∑ τ, χ τ (b k) * Cm i τ = if i = k then 1 else 0 := by
      intro k
      rw [← hCA i k]
      exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
    simp_rw [h1, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hCA']
    simp
  have F3 : ∀ (a : 𝓞 E) (m : M), ρ a m = ∑ τ, χ τ a • Q τ m := by
    intro a m
    simp only [hQ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hcoef]
    conv_lhs => rw [hom_basis ρ b a]
    simp [Module.End.mul_apply, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  have eig : ∀ σ (a : 𝓞 E) (m : M), ρ a (Q σ m) = χ σ a • Q σ m := by
    intro σ a m
    have h1 : ρ a (Q σ m) = ∑ i, Cm i σ • ρ (a * b i) m := by

      simp only [hQ, map_sum, map_smul, map_mul, Module.End.mul_apply]
    rw [h1]
    simp_rw [F3 _ m, map_mul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have h2 : ∀ τ, ∑ i, Cm i σ * (χ τ a * χ τ (b i)) = χ τ a * (if τ = σ then 1 else 0) := by
      intro τ
      rw [← hAC τ σ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [h2]
    simp
  have hsum1 : ∀ m : M, ∑ σ, Q σ m = m := by
    intro m
    have := F3 1 m
    simp at this
    exact this.symm
  have hlin : ∀ σ (f : ι → M), Q σ (∑ σ', f σ') = ∑ σ', Q σ (f σ') := by
    intro σ f

    simp only [hQ, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  refine ⟨fun m => ⟨fun σ => Q σ m, fun σ a => eig σ a m, hsum1 m⟩, ?_⟩
  intro mσ hmσ hsum σ
  have hQe : ∀ τ σ', Q τ (mσ σ') = if σ' = τ then mσ σ' else 0 := by
    intro τ σ'
    simp only [hQ, hmσ, smul_smul]
    rw [← Finset.sum_smul]
    rw [show ∑ i, Cm i τ * χ σ' (b i) = if σ' = τ then 1 else 0 from by
      rw [← hAC σ' τ]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _]
    split_ifs <;> simp
  have h0 : Q σ (∑ σ', mσ σ') = 0 := by
    rw [hsum]
    simp [hQ]
  rw [hlin] at h0
  simpa [hQe] using h0

end Core

section NT

variable (E : Type) [Field E] [NumberField E]

theorem isUnit_of_not_dvd {V : Type} [CommRing V] [IsLocalRing V] (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V))
    (d : ℤ) (hd : ¬ (g : ℤ) ∣ d) : IsUnit (d : V) := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hd
  have h1 : (u : V) * (g : V) + (v : V) * (d : V) = 1 := by
    have := congrArg (Int.cast : ℤ → V) huv
    push_cast at this
    exact this
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hgV
  · exact isUnit_of_mul_isUnit_right h

end NT

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
end
end
