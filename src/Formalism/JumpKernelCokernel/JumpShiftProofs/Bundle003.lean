module

public import Formalism.JumpKernelCokernel.Bundle001
public import Mathlib.RingTheory.OrderOfVanishing.Basic
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
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

@[expose] public section

section

namespace Formalism.KernelCokernelLengths.LengthSplittingLemmas

theorem main (O : Type) [CommRing O] (R : Type) [AddCommGroup R] [Module O R]
    (π : Module.End O R) (R' R'' : Submodule O R) (h : R' ≤ R'') :
    Module.length O (R ⧸ (R' ⊔ LinearMap.range π)) ≤
      Module.length O (R ⧸ (R'' ⊔ LinearMap.range π)) +
        Module.length O (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) := by
  set A := R' ⊔ LinearMap.range π with hA
  set B := R'' ⊔ LinearMap.range π with hB
  have hAB : A ≤ B := sup_le_sup_right h _
  let f : (B ⧸ A.comap B.subtype) →ₗ[O] (R ⧸ A) := Submodule.mapQ (A.comap B.subtype) A B.subtype le_rfl
  let g : (R ⧸ A) →ₗ[O] (R ⧸ B) := Submodule.mapQ A B LinearMap.id (by simpa using hAB)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.subtype_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hx
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk r, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero] at hy
      exact ⟨Submodule.Quotient.mk ⟨r, hy⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      simp only [f, g, Submodule.mapQ_apply, Submodule.subtype_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero]
      exact b.2
  have hlen := Module.length_eq_add_of_exact f g hf hg hex
  have hRB : R'' ≤ B := le_sup_left
  let k : (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) →ₗ[O] (B ⧸ A.comap B.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hRB) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact sup_le_sup_left (LinearMap.map_le_range) R' hx)
  have hk : Function.Surjective k := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨r, hr, p, hp, rfl⟩ := Submodule.mem_sup.mp hb
    refine ⟨Submodule.Quotient.mk ⟨r, hr⟩, ?_⟩
    simp only [k, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
    have : r - (r + p) = -p := by abel
    rw [this]
    exact A.neg_mem (Submodule.mem_sup_right hp)
  have hle := Module.length_le_of_surjective k hk
  rw [hlen, add_comm]
  gcongr

end Formalism.KernelCokernelLengths.LengthSplittingLemmas

theorem Formalism.KernelCokernelLengths.length_splits_additively : Formalism.KernelCokernelLengths.LenSplit := by
  intro O _ R _ _ π R' R'' h
  exact Formalism.KernelCokernelLengths.LengthSplittingLemmas.main O R π R' R'' h
end

section

namespace Formalism.KernelCokernelLengths.DeterminantLengthLemmas

open Module

theorem ord_prod {O : Type} [CommRing O] [IsDomain O] {ι : Type} (s : Finset ι) (a : ι → O)
    (ha : ∀ i, a i ≠ 0) :
    Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]

end Formalism.KernelCokernelLengths.DeterminantLengthLemmas

open Module in
theorem Formalism.KernelCokernelLengths.determinant_length_formula : Formalism.KernelCokernelLengths.DetLen := by
  intro O _ _ _ M _ _ _ _ d hdet
  classical
  have hinj : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  let e : M ≃ₗ[O] LinearMap.range d := LinearEquiv.ofInjective d hinj
  have h : finrank O (LinearMap.range d) = finrank O M := e.finrank_eq.symm
  let b := Free.chooseBasis O M
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have hab : ∀ i, (ab i : M) = a i • b' i := Submodule.smithNormalFormBotBasis_def b h
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h

  have hL : Module.length O (M ⧸ LinearMap.range d) = ∑ i, Ring.ord O (a i) := by
    rw [((LinearMap.range d).quotientEquivPiSpan b h).length_eq,
      Module.length_pi_of_fintype]
    rfl

  let u : M ≃ₗ[O] LinearMap.range d := b'.equiv ab (Equiv.refl _)
  let D : M →ₗ[O] M := (LinearMap.range d).subtype ∘ₗ u.toLinearMap
  have hD : LinearMap.det D = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' D = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      simp only [D, u, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Basis.equiv_apply, Equiv.refl_apply, Submodule.coe_subtype, hab, map_smul,
        Basis.repr_self, Finsupp.smul_apply, smul_eq_mul, Matrix.diagonal_apply,
        Finsupp.single_apply]
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [this, Matrix.det_diagonal]
  have hd : d = D ∘ₗ (e.trans u.symm).toLinearMap := by
    ext x
    simp [D, e]
  have hdet' : LinearMap.det d = (∏ i, a i) * LinearMap.det (e.trans u.symm).toLinearMap := by
    rw [congrArg LinearMap.det hd, LinearMap.det_comp, hD]
  rw [hL]
  change _ = Ring.ord O (LinearMap.det d)
  rw [hdet', Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' _),
    Formalism.KernelCokernelLengths.DeterminantLengthLemmas.ord_prod _ _ ha]
end
