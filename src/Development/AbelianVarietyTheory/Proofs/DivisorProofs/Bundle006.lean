module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

section Corner

variable {A : Type} [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]

noncomputable def leftIdealMulAlgHom (A : Type) [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]
    (e : Λ) : Λ →ₐ[A] Module.End A (LinearMap.range (LinearMap.mulRight A e)) where
  toFun l := (LinearMap.mulLeft A l).restrict (by
    rintro _ ⟨y, rfl⟩
    exact ⟨l * y, by simp [mul_assoc]⟩)
  map_one' := by ext p; simp [LinearMap.restrict_apply]
  map_mul' x y := by ext p; simp [LinearMap.restrict_apply, mul_assoc]
  map_zero' := by ext p; simp [LinearMap.restrict_apply]
  map_add' x y := by ext p; simp [LinearMap.restrict_apply, add_mul]
  commutes' c := by ext p; simp [LinearMap.restrict_apply, Algebra.smul_def]

theorem leftIdealMulAlgHom_apply_coe (e l : Λ) (p : LinearMap.range (LinearMap.mulRight A e)) :
    ((leftIdealMulAlgHom A e l p : LinearMap.range (LinearMap.mulRight A e)) : Λ) = l * p := rfl

theorem leftIdealMulAlgHom_injective (e : Λ)
    (h : ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) :
    Function.Injective (leftIdealMulAlgHom A e) := by
  obtain ⟨N, a, b, hab⟩ := h
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro l hl
  have h0 : ∀ y : Λ, l * (y * e) = 0 := by
    intro y
    have := leftIdealMulAlgHom_apply_coe (A := A) e l ⟨y * e, y, rfl⟩
    rw [hl] at this
    simpa using this.symm
  calc l = l * ∑ i, a i * e * b i := by rw [hab, mul_one]
    _ = ∑ i, l * (a i * e) * b i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [mul_assoc]
    _ = 0 := by simp [h0]

theorem exists_mul_eq_mulLeftRight_of_corner (e : Λ)
    (hc : ∀ y : Λ, ∃ c : A, e * y * e = c • e) (t : Λ ⊗[A] Λᵐᵒᵖ) :
    ∃ l : Λ, ∀ y : Λ, AlgHom.mulLeftRight A Λ t (y * e) * e = l * (y * e) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, fun y => by simp⟩
  | tmul a b =>
    obtain ⟨c, hc⟩ := hc b.unop
    refine ⟨c • a, fun y => ?_⟩
    rw [AlgHom.mulLeftRight_apply]
    calc a * (y * e) * b.unop * e = a * y * (e * b.unop * e) := by simp only [mul_assoc]
      _ = c • a * (y * e) := by rw [hc]; simp [mul_assoc]
  | add s t hs ht =>
    obtain ⟨l, hl⟩ := hs
    obtain ⟨m, hm⟩ := ht
    exact ⟨l + m, fun y => by rw [map_add (f := _), LinearMap.add_apply, add_mul, hl, hm, add_mul]⟩

theorem leftIdealMulAlgHom_surjective [IsAzumaya A Λ] (e : Λ) (he : IsIdempotentElem e)
    (hc : ∀ y : Λ, ∃ c : A, e * y * e = c • e) :
    Function.Surjective (leftIdealMulAlgHom A e) := by
  intro f
  obtain ⟨t, ht⟩ := (IsAzumaya.bij (R := A) (A := Λ)).2
    ((LinearMap.range (LinearMap.mulRight A e)).subtype ∘ₗ f ∘ₗ
      (LinearMap.mulRight A e).rangeRestrict)
  obtain ⟨l, hl⟩ := exists_mul_eq_mulLeftRight_of_corner e hc t
  refine ⟨l, ?_⟩
  ext ⟨_, y, rfl⟩
  rw [leftIdealMulAlgHom_apply_coe]
  change l * (y * e) = _
  rw [← hl y, ht]
  have h1 : (LinearMap.mulRight A e).rangeRestrict (y * e)
      = ⟨LinearMap.mulRight A e y, y, rfl⟩ := by
    ext; simp [mul_assoc, he.eq]
  simp only [LinearMap.comp_apply, h1, Submodule.subtype_apply]
  obtain ⟨z, hz⟩ := (f ⟨LinearMap.mulRight A e y, y, rfl⟩).2
  rw [← hz]
  simp [mul_assoc, he.eq]

end Corner

theorem azumaya_algEquiv_matrix_of_idempotent :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ]
      [Module.Free A Λ] (n : ℕ), Module.finrank A Λ = n ^ 2 → ∀ e : Λ, IsIdempotentElem e →
      (∀ y : Λ, ∃ c : A, e * y * e = c • e) →
      (∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) →
      Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro A _ _ Λ _ _ _ _ n hn e he hc hs
  let P := LinearMap.range (LinearMap.mulRight A e)
  let φ : Λ ≃ₐ[A] Module.End A P := AlgEquiv.ofBijective (leftIdealMulAlgHom A e)
    ⟨leftIdealMulAlgHom_injective e hs, leftIdealMulAlgHom_surjective e he hc⟩
  haveI : Module.Projective A P :=
    Module.Projective.of_split P.subtype (LinearMap.mulRight A e).rangeRestrict (by
      ext ⟨_, y, rfl⟩
      simp [mul_assoc, he.eq])
  haveI : Module.Finite A P := Module.Finite.range _
  haveI : Module.Free A P := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank A P = n := by
    have h1 := φ.toLinearEquiv.finrank_eq
    rw [hn, Module.finrank_linearMap, ← sq] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  exact ⟨φ.trans (LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq A P hr))⟩

end GlobalTheory
end

section

namespace GlobalTheory.ClassPart

private lemma summand_conj {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (η : Γ) (y : Y) (γ : Γ) :
    ((Nat.card (MulAction.stabilizer Γ (η • y) ⊓ Subgroup.centralizer {η * γ * η⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
        F (η • y) (η * γ * η⁻¹) =
      ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y γ := by
  rw [hF]
  congr 3
  symm
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (MulAut.conj η).toEquiv ?_
  intro s
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff, mul_smul, inv_smul_smul, smul_left_cancel_iff]
  refine and_congr_right (fun _ => ?_)
  change s * γ = γ * s ↔ (η * s * η⁻¹) * (η * γ * η⁻¹) = (η * γ * η⁻¹) * (η * s * η⁻¹)
  rw [show η * s * η⁻¹ * (η * γ * η⁻¹) = η * (s * γ) * η⁻¹ by group,
    show η * γ * η⁻¹ * (η * s * η⁻¹) = η * (γ * s) * η⁻¹ by group, mul_left_inj, mul_right_inj]

theorem orbitSum_conj : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → ∀ (γ g : Γ), ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) γ = ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {g * γ * g⁻¹}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {g * γ * g⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (g * γ * g⁻¹) := by
  intro Γ Y _ _ F hF γ g
  set S : Γ → Y → ℂ := fun c y =>
    ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y c with hSdef
  have hS : ∀ (η : Γ) (y : Y) (c : Γ), S (η * c * η⁻¹) (η • y) = S c y := fun η y c => summand_conj F hF η y c
  have hZ : ∀ (c : Γ) (ζ : Γ), ζ ∈ Subgroup.centralizer {c} → ∀ y, S c (ζ • y) = S c y := by
    intro c ζ hζ y
    have hcj : ζ * c * ζ⁻¹ = c := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hζ
      rw [hζ]; group
    have := hS ζ y c
    rwa [hcj] at this
  set γ' := g * γ * g⁻¹ with hγ'
  have hrel : ∀ a b : Y, (MulAction.orbitRel (Subgroup.centralizer {γ}) Y) a b ↔
      (MulAction.orbitRel (Subgroup.centralizer {γ'}) Y) (g • a) (g • b) := by
    intro a b
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subtype.exists, Subgroup.mk_smul]
    constructor
    · rintro ⟨ζ, hζ, h⟩
      refine ⟨g * ζ * g⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hζ ⊢
        rw [hγ']
        change (g * ζ * g⁻¹) * (g * γ * g⁻¹) = (g * γ * g⁻¹) * (g * ζ * g⁻¹)
        rw [show g * ζ * g⁻¹ * (g * γ * g⁻¹) = g * (ζ * γ) * g⁻¹ by group,
          show g * γ * g⁻¹ * (g * ζ * g⁻¹) = g * (γ * ζ) * g⁻¹ by group, hζ]
      · rw [← h]; simp [mul_smul]
    · rintro ⟨ζ, hζ, h⟩
      refine ⟨g⁻¹ * ζ * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hζ ⊢
        rw [hγ'] at hζ
        have h2 : g⁻¹ * (g * γ * g⁻¹ * ζ) * g = g⁻¹ * (ζ * (g * γ * g⁻¹)) * g := by rw [hζ]
        rw [show g⁻¹ * (g * γ * g⁻¹ * ζ) * g = γ * (g⁻¹ * ζ * g) by group,
          show g⁻¹ * (ζ * (g * γ * g⁻¹)) * g = g⁻¹ * ζ * g * γ by group] at h2
        exact h2.symm
      · have := congrArg (g⁻¹ • ·) h
        simpa [mul_smul] using this
  let e : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y ≃
      MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y :=
    Quotient.congr (MulAction.toPerm g) hrel
  change ∑ᶠ o, S γ (Quotient.out o) = ∑ᶠ o, S γ' (Quotient.out o)
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro o
  have hmk : (Quotient.mk _ (Quotient.out (e o)) : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y) =
      Quotient.mk _ (g • Quotient.out o) := by
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have hr := Quotient.exact hmk
  have hr' : Quotient.out (e o) ∈ MulAction.orbit (Subgroup.centralizer {γ'}) (g • Quotient.out o) := hr
  rw [MulAction.mem_orbit_iff] at hr'
  obtain ⟨ζ, hζ⟩ := hr'
  rw [← hζ, Subgroup.smul_def, hZ γ' ζ ζ.2, hγ', hS]

end GlobalTheory.ClassPart
end

section

namespace GlobalTheory.OrbitAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)

def stab (x : V) : Subgroup L where
  carrier := {l | π (l : G) x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_stab {x : V} {l : L} : l ∈ stab π L x ↔ π (l : G) x = x := Iff.rfl

noncomputable def cv (H : Subgroup L) (x : V) (q : L ⧸ H) : V := π ((q.out : L) : G) x

theorem cv_mk {H : Subgroup L} {x : V} (hH : H ≤ stab π L x) (a : L) :
    cv π L H x (QuotientGroup.mk a) = π (a : G) x := by
  unfold cv
  set b : L := (QuotientGroup.mk a : L ⧸ H).out with hb
  have h1 : (QuotientGroup.mk b : L ⧸ H) = QuotientGroup.mk a := QuotientGroup.out_eq' _
  have h2 : b⁻¹ * a ∈ H := QuotientGroup.eq.mp h1
  have h3 := (mem_stab π L).mp (hH h2)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply] at h3
  calc π (b : G) x = π (b : G) (π (b : G)⁻¹ (π (a : G) x)) := by rw [h3]
    _ = π (a : G) x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

noncomputable def avgH (H : Subgroup L) (x : V) : V :=
  ((H.index : ℂ))⁻¹ • ∑ᶠ q : L ⧸ H, cv π L H x q

theorem avgH_refine {H H' : Subgroup L} {x : V} (hle : H' ≤ H) (hH : H ≤ stab π L x)
    [H'.FiniteIndex] : avgH π L H' x = avgH π L H x := by
  classical
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hrel := Subgroup.relIndex_mul_index hle
  haveI : (H'.subgroupOf H).FiniteIndex := by
    refine ⟨?_⟩
    intro h0
    have h4 : H'.index = 0 := by rw [← hrel]; simp [Subgroup.relIndex, h0]
    exact Subgroup.FiniteIndex.index_ne_zero h4
  haveI := Fintype.ofFinite (L ⧸ H)
  haveI := Fintype.ofFinite (L ⧸ H')
  haveI := Fintype.ofFinite (H ⧸ H'.subgroupOf H)
  unfold avgH
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let e := Subgroup.quotientEquivProdOfLE hle
  have hcv : ∀ q : L ⧸ H', cv π L H' x q = cv π L H x (e q).1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cv_mk π L (le_trans hle hH), show (e (QuotientGroup.mk a)).1 = QuotientGroup.mk a from rfl,
        cv_mk π L hH]
  have hsum : ∑ q : L ⧸ H', cv π L H' x q =
      (Fintype.card (H ⧸ H'.subgroupOf H) : ℂ) • ∑ q : L ⧸ H, cv π L H x q := by
    simp_rw [hcv]
    rw [Equiv.sum_comp e (fun p => cv π L H x p.1), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [Finset.smul_sum]
    simp [Nat.cast_smul_eq_nsmul]
  have hc : Fintype.card (H ⧸ H'.subgroupOf H) = H'.relIndex H := by
    rw [Fintype.card_eq_nat_card]; rfl
  rw [hsum, hc, ← hrel, smul_smul]
  congr 1
  have h5 : (H'.relIndex H : ℂ) ≠ 0 := by
    have := Subgroup.FiniteIndex.index_ne_zero (H := H'.subgroupOf H)
    exact_mod_cast this
  push_cast
  field_simp

theorem stab_le_add (x y : V) : stab π L x ⊓ stab π L y ≤ stab π L (x + y) := by
  intro l hl
  rw [mem_stab, map_add (f := _), (mem_stab π L).mp hl.1, (mem_stab π L).mp hl.2]

theorem stab_le_smul (c : ℂ) (x : V) : stab π L x ≤ stab π L (c • x) := by
  intro l hl
  rw [mem_stab, map_smul, (mem_stab π L).mp hl]

theorem avgH_add (H : Subgroup L) [H.FiniteIndex] (x y : V) :
    avgH π L H (x + y) = avgH π L H x + avgH π L H y := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH cv
  simp only [finsum_eq_sum_of_fintype, map_add (f := _), Finset.sum_add_distrib, smul_add]

theorem avgH_smul (H : Subgroup L) [H.FiniteIndex] (c : ℂ) (x : V) :
    avgH π L H (c • x) = c • avgH π L H x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH cv
  simp only [finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum, smul_comm c]

noncomputable def avg (x : V) : V := avgH π L (stab π L x) x

theorem avg_eq {H : Subgroup L} {x : V} [H.FiniteIndex] (hH : H ≤ stab π L x) :
    avg π L x = avgH π L H x := (avgH_refine π L hH le_rfl).symm

theorem avg_fixed {x : V} (hx : (stab π L x).FiniteIndex) (hfix : ∀ l ∈ L, π l x = x) :
    avg π L x = x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ stab π L x)
  unfold avg avgH
  have : ∀ q : L ⧸ stab π L x, cv π L (stab π L x) x q = x := fun q => hfix _ (q.out).2
  simp only [finsum_eq_sum_of_fintype, this, Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h0 : ((stab π L x).index : ℂ) ≠ 0 := by exact_mod_cast hx.index_ne_zero
  rw [show Nat.card (L ⧸ stab π L x) = (stab π L x).index from rfl, inv_mul_cancel₀ h0, one_smul]

theorem avg_invariant {x : V} (hx : (stab π L x).FiniteIndex) (l : L) :
    π (l : G) (avg π L x) = avg π L x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ stab π L x)
  unfold avg avgH

  rw [finsum_eq_sum_of_fintype, map_smul, map_sum]
  congr 1
  have h : ∀ q : L ⧸ stab π L x, π (l : G) (cv π L (stab π L x) x q) =
      cv π L (stab π L x) x (l • q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cv_mk π L le_rfl, MulAction.Quotient.smul_mk, cv_mk π L le_rfl, smul_eq_mul, Subgroup.coe_mul, map_mul,
        Module.End.mul_apply]
  simp_rw [h]
  exact Equiv.sum_comp (MulAction.toPerm l) (cv π L (stab π L x) x)

theorem avg_add {x y : V} (hx : (stab π L x).FiniteIndex) (hy : (stab π L y).FiniteIndex) :
    avg π L (x + y) = avg π L x + avg π L y := by
  haveI : (stab π L x ⊓ stab π L y).FiniteIndex := inferInstance
  rw [avg_eq π L (stab_le_add π L x y), avg_eq π L (inf_le_left : stab π L x ⊓ stab π L y ≤ stab π L x),
    avg_eq π L (inf_le_right : stab π L x ⊓ stab π L y ≤ stab π L y), avgH_add]

theorem avg_smul {x : V} (hx : (stab π L x).FiniteIndex) (c : ℂ) :
    avg π L (c • x) = c • avg π L x := by
  rw [avg_eq π L (stab_le_smul π L c x), avgH_smul]
  rfl

end GlobalTheory.OrbitAvg

end

section

namespace GlobalTheory

theorem finsum_fiberwise_of_finite_support {A B : Type} (ρ : A → B) (f : A → ℂ)
    (hf : (Function.support f).Finite) :
    ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // ρ a = b}, f a.1 := by
  classical
  set S := hf.toFinset with hS
  have hsupp : Function.support f ⊆ (S : Set A) := by simp [hS]
  have hinner : ∀ b, (∑ᶠ a : {a // ρ a = b}, f a.1) = ∑ a ∈ S with ρ a = b, f a := by
    intro b
    rw [finsum_subtype_eq_finsum_cond (fun a => ρ a = b)]
    have : (fun a => ∑ᶠ (_ : ρ a = b), f a) = fun a => if ρ a = b then f a else 0 := by
      funext a; exact finsum_eq_if
    rw [this, finsum_eq_sum_of_support_subset _ (s := S), Finset.sum_filter]
    intro a ha
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at ha
    obtain ⟨_, h⟩ := ha
    exact hsupp h
  simp_rw [hinner]
  rw [finsum_eq_sum_of_support_subset f hsupp,
    finsum_eq_sum_of_support_subset _ (s := S.image ρ)]
  · exact (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem ρ ha) f).symm
  · intro b hb
    rw [Function.mem_support] at hb
    obtain ⟨a, ha, hab⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    rw [Finset.mem_filter] at ha
    rw [Finset.coe_image]
    exact ⟨a, ha.1, ha.2⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem finsum_regroup_fibre_bij {α ι : Type} {κ : ι → Type} (U : α → ℂ)
    (W : (i : ι) → κ i → ℂ) (π : α → ι) (Φ : (i : ι) → α → κ i)
    (hU : (Function.support U).Finite)
    (hval : ∀ a, U a ≠ 0 → W (π a) (Φ (π a) a) = U a)
    (hinj : ∀ a a', U a ≠ 0 → U a' ≠ 0 → π a' = π a → Φ (π a) a = Φ (π a) a' → a = a')
    (hsurj : ∀ i c, W i c ≠ 0 → ∃ a, π a = i ∧ U a ≠ 0 ∧ Φ i a = c) :
    ∑ᶠ a, U a = ∑ᶠ i, ∑ᶠ c, W i c := by
  classical
  set S : Finset α := hU.toFinset with hS
  have hmem : ∀ a, a ∈ S ↔ U a ≠ 0 := fun a => by simp [hS]
  have hin : ∀ i, ∑ᶠ c, W i c = ∑ a ∈ S.filter (fun a => π a = i), U a := by
    intro i
    have h1 : Function.support (W i) ⊆
        ((S.filter (fun a => π a = i)).image (Φ i) : Finset (κ i)) := by
      intro c hc
      obtain ⟨a, ha, hUa, hac⟩ := hsurj i c hc
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
      exact ⟨a, ⟨(hmem a).2 hUa, ha⟩, hac⟩
    rw [finsum_eq_sum_of_support_subset _ h1, Finset.sum_image]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      subst ha2
      exact hval a ((hmem a).1 ha1)
    · intro a ha a' ha' h
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      obtain ⟨ha1', ha2'⟩ := Finset.mem_filter.1 ha'
      subst ha2
      exact hinj a a' ((hmem a).1 ha1) ((hmem a').1 ha1') ha2' h
  simp only [hin]
  have h2 : Function.support (fun i => ∑ a ∈ S.filter (fun a => π a = i), U a) ⊆
      (S.image π : Finset ι) := by
    intro i hi
    obtain ⟨a, ha, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨a, ha1, ha2⟩
  rw [finsum_eq_sum_of_support_subset _ h2, finsum_eq_sum U hU,
    Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem π ha)]

end GlobalTheory
end

section

namespace GlobalTheory.AbelianSumIdentityFirst

theorem main : ∀ {ι : Type} {z : ℂ}, z ≠ (0 : ℂ) → ∀ (s : Finset ι) (a : ι → ℤ),
    z ^ ∑ i ∈ s, a i = ∏ i ∈ s, z ^ a i := by
  intro ι z hz s a
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ hz, ih]

end GlobalTheory.AbelianSumIdentityFirst
end
