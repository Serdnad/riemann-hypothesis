module

public import Formalism.SatakeDualWeyl.Statement
public import Lemmata.MiscLemmasI.Imports
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.Extension
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

@[expose] public section

section

open Matrix
open scoped ComplexOrder

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.WbDefC

theorem cT_eq_conjTranspose {m k : Type} (P : Matrix m k ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) P = Pᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

theorem jpq_mulVec_of_inr {p q : ℕ} (w : Fin p ⊕ Fin q → ℂ) (hw : ∀ j, w (Sum.inr j) = 0) :
    Formalism.UG.Jpq p q *ᵥ w = w := by
  have hr : w ∘ Sum.inr = 0 := funext hw
  ext x
  rcases x with i | j
  · simp [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, hr]
  · simp [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, hr, hw]

theorem sigNeg_card_le {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]
    (J : Matrix n n ℂ) (p q : ℕ) (hJ : Formalism.UG.HasSignature J p q) (u : ι → n → ℂ)
    (hu : LinearIndependent ℂ u)
    (hneg : ∀ d : ι → ℂ, (star (∑ a, d a • u a) ⬝ᵥ (J *ᵥ ∑ a, d a • u a)).re ≤ 0) :
    Fintype.card ι ≤ q := by
  classical
  obtain ⟨e, P, hP⟩ := hJ
  rw [cT_eq_conjTranspose] at hP
  set Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQ
  set Qi : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQi
  have hQQi : Q * Qi = 1 := by
    rw [hQ, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]

  have key : ∀ v : n → ℂ, star v ⬝ᵥ (J *ᵥ v) =
      star (Qi *ᵥ (v ∘ e.symm)) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ (Qi *ᵥ (v ∘ e.symm))) := by
    intro v
    have hv : Q *ᵥ (Qi *ᵥ (v ∘ e.symm)) = v ∘ e.symm := by
      rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    conv_rhs =>
      rw [← hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, dotProduct_mulVec,
        ← Matrix.star_mulVec, hv, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    simp only [dotProduct]
    exact Fintype.sum_equiv e _ _ (fun i => by simp [Function.comp_def])
  by_contra hlt
  push_neg at hlt
  let L : (ι → ℂ) →ₗ[ℂ] (Fin q → ℂ) :=
    (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ (Matrix.mulVecLin Qi) ∘ₗ
      (LinearMap.funLeft ℂ ℂ e.symm) ∘ₗ (Fintype.linearCombination ℂ u)
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨d, hdk, hd0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hLd : L d = 0 := hdk
  have hyr : ∀ j, (Qi *ᵥ ((∑ a, d a • u a) ∘ e.symm)) (Sum.inr j) = 0 := by
    intro j
    have := congrFun hLd j
    simp only [L, LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply] at this
    exact this
  have hform := hneg d
  rw [key, jpq_mulVec_of_inr _ hyr] at hform
  set y := Qi *ᵥ ((∑ a, d a • u a) ∘ e.symm) with hy
  have hnn : 0 ≤ star y ⬝ᵥ y := dotProduct_star_self_nonneg y
  have hz : star y ⬝ᵥ y = 0 := by
    rw [Complex.nonneg_iff] at hnn
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith [hnn.1]
    · simpa using hnn.2.symm
  have hy0 : y = 0 := dotProduct_star_self_eq_zero.1 hz
  have hv0 : (∑ a, d a • u a) ∘ e.symm = 0 := by
    rw [← Matrix.one_mulVec ((∑ a, d a • u a) ∘ e.symm), ← hQQi, ← Matrix.mulVec_mulVec, ← hy, hy0,
      Matrix.mulVec_zero]
  have hsum : ∑ a, d a • u a = 0 := by
    funext x
    have := congrFun hv0 (e x)
    simpa using this
  exact hd0 (funext (Fintype.linearIndependent_iff.1 hu d hsum))

theorem linIndep_map {K L ι n : Type} [Field K] [Field L] [Fintype ι] [Fintype n] [DecidableEq ι]
    [DecidableEq n] (τ : K →+* L) (c : ι → n → K) (hc : LinearIndependent K c) :
    LinearIndependent L (fun a => fun i => τ (c a i)) := by
  first | exact Bl.SecondBlockLemmaJ.goal1 .. | (apply Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaJ.goal1 <;> first | assumption | infer_instance)

end PI.UnitaryGroupMassFormula.CntFormula.WbDefC
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S

theorem locE_isUnit_or_exists_algEquiv_prod_swap {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) :
    (∀ x : E, x ≠ 0 → IsUnit x) ∨ ∃ e : E ≃ₐ[F] F × F, ∀ x, e (L.cj x) = (e x).swap := by
  classical
  have hrank := L.rank
  have : Module.Free F E := L.free
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [hrank]; norm_num)
  have : IsReduced E := L.reduced
  by_cases hfield : ∀ x : E, x ≠ 0 → IsUnit x
  · exact Or.inl hfield
  right
  obtain ⟨x, hx⟩ := not_forall.1 hfield
  have hx0 : x ≠ 0 := fun heq => hx (fun hne => (hne heq).elim)
  have hxu : ¬ IsUnit x := fun hu => hx (fun _ => hu)
  have hfix : ∀ y : E, L.cj y = y → ∃ a : F, algebraMap F E a = y := fun y hy => (L.cj_fix y).1 hy
  obtain ⟨a, ha⟩ := hfix (x * L.cj x) (by rw [map_mul, L.cj_cj, mul_comm])
  have hN : x * L.cj x = 0 := by
    by_contra hne
    apply hxu
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact hne ha.symm
    refine IsUnit.of_mul_eq_one (L.cj x * algebraMap F E a⁻¹) ?_
    rw [← mul_assoc, ← ha, ← map_mul, mul_inv_cancel₀ ha0, map_one]
  obtain ⟨t, ht⟩ := hfix (x + L.cj x) (by rw [map_add (f := _), L.cj_cj, add_comm])
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    have hc : L.cj x = -x := by linear_combination -ht
    have hsq : x ^ 2 = 0 := by
      rw [hc] at hN
      linear_combination -hN
    exact hx0 (IsReduced.eq_zero x ⟨2, hsq⟩)
  have hcu : L.cj (algebraMap F E t⁻¹) = algebraMap F E t⁻¹ := L.cj.commutes _
  have hpq : x * algebraMap F E t⁻¹ + L.cj x * algebraMap F E t⁻¹ = 1 := by
    rw [← add_mul, ← ht, ← map_mul, mul_inv_cancel₀ ht0, map_one]
  set p := x * algebraMap F E t⁻¹ with hp
  set q := L.cj x * algebraMap F E t⁻¹ with hq
  have hpq0 : p * q = 0 := by
    rw [hp, hq]
    linear_combination (algebraMap F E t⁻¹ * algebraMap F E t⁻¹) * hN
  have hqp : q * p = 0 := by rw [mul_comm]; exact hpq0
  have hcp : L.cj p = q := by rw [hp, hq, map_mul, hcu]
  have hcq : L.cj q = p := by rw [hp, hq, map_mul, hcu, L.cj_cj]
  have hpp : p * p = p := by
    have h : p * (p + q) = p := by rw [hpq, mul_one]
    linear_combination h - hpq0
  have hqq : q * q = q := by
    have h : (p + q) * q = q := by rw [hpq, one_mul]
    linear_combination h - hpq0
  have hp0 : p ≠ 0 := by
    intro h
    have h1 : q = 1 := by rw [← hpq, h, zero_add]
    apply one_ne_zero (α := E)
    rw [← h1, ← hcp, h, map_zero]
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : p = 1 := by rw [← hpq, h, add_zero]
    apply one_ne_zero (α := E)
    rw [← h1, ← hcq, h, map_zero]
  let g : (F × F) →ₐ[F] E :=
    { toFun := fun z => z.1 • p + z.2 • q
      map_one' := by simp [hpq]
      map_mul' := fun z w => by
        simp only [Prod.fst_mul, Prod.snd_mul, Algebra.smul_def, map_mul]
        linear_combination (-(algebraMap F E z.1 * algebraMap F E w.1)) * hpp -
          (algebraMap F E z.2 * algebraMap F E w.2) * hqq -
          (algebraMap F E z.1 * algebraMap F E w.2 + algebraMap F E z.2 * algebraMap F E w.1) * hpq0
      map_zero' := by simp
      map_add' := fun z w => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      commutes' := fun r => by
        simp only [Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [← smul_add, hpq, Algebra.algebraMap_eq_smul_one] }
  have ginj : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have hz' : z.1 • p + z.2 • q = 0 := hz
    have h1 : z.1 • p = 0 := by
      have h := congrArg (· * p) hz'
      simp only [add_mul, smul_mul_assoc, hpp, hqp, smul_zero, add_zero, zero_mul] at h
      exact h
    have h2 : z.2 • q = 0 := by
      have h := congrArg (· * q) hz'
      simp only [add_mul, smul_mul_assoc, hqq, hpq0, smul_zero, zero_add, zero_mul] at h
      exact h
    rw [smul_eq_zero] at h1 h2
    exact Prod.ext (h1.resolve_right hp0) (h2.resolve_right hq0)
  have gsurj : Function.Surjective g := by
    have hdim : Module.finrank F (F × F) = Module.finrank F E := by
      rw [Module.finrank_prod, Module.finrank_self, hrank]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := g.toLinearMap)).1 ginj
  let e0 := AlgEquiv.ofBijective g ⟨ginj, gsurj⟩
  refine ⟨e0.symm, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := gsurj y
  have hez : e0.symm (g z) = z := e0.symm_apply_apply z
  have hcz : L.cj (g z) = g z.swap := by
    show L.cj (z.1 • p + z.2 • q) = z.2 • p + z.1 • q
    rw [map_add (f := _), map_smul, map_smul, hcp, hcq, add_comm]
  rw [hcz, hez]
  exact e0.symm_apply_apply z.swap

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Polynomial
open ValuativeRel

theorem fl_cj_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.9] at hx ⊢
  exact hx.map ((L.1 : E →ₐ[F] E).restrictScalars 𝒪[F])

theorem fl_mem_int {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {a : F} (ha : algebraMap F E a ∈ L.O) : a ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (algebraMap F E a) := (L.9 _).1 ha
  letI : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).2 hinj
  have h2 : IsIntegral 𝒪[F] a := isIntegral_algebraMap_iff.1 h1
  exact (Valuation.integer.integers _).mem_of_integral h2

theorem fl_int_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  rw [L.9]
  have h : IsIntegral 𝒪[F] (algebraMap 𝒪[F] E a) := isIntegral_algebraMap
  rwa [IsScalarTower.algebraMap_apply 𝒪[F] F E] at h

theorem fl_fix_int {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {y : E} (hy : y ∈ L.O) (hc : L.cj y = y) : ∃ a : 𝒪[F], algebraMap F E a = y := by
  obtain ⟨a, ha⟩ := (L.3 y).1 hc
  have haO : a ∈ 𝒪[F] := fl_mem_int L hinj (ha ▸ hy)
  exact ⟨⟨a, haO⟩, ha⟩

theorem fl_norm {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {x : E} (hx : x ∈ L.O) : ∃ n : 𝒪[F], algebraMap F E n = x * L.cj x := by
  refine fl_fix_int L hinj (L.O.mul_mem hx (fl_cj_mem L hx)) ?_
  rw [map_mul, L.2, mul_comm]

theorem fl_trace {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {x : E} (hx : x ∈ L.O) : ∃ t : 𝒪[F], algebraMap F E t = x + L.cj x := by
  refine fl_fix_int L hinj (L.O.add_mem hx (fl_cj_mem L hx)) ?_
  rw [map_add (f := _), L.2, add_comm]

theorem fl_den_F {F : Type} [Field F] [ValuativeRel F] (a : F) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ (c : F) * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨1, one_ne_zero, by simpa using ha⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (zero_mem _)
    have hv : 1 < ValuativeRel.valuation F a := by
      rw [Valuation.mem_integer_iff, not_le] at ha
      exact ha
    have hmem : a⁻¹ ∈ 𝒪[F] := by
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hv.le
    refine ⟨⟨a⁻¹, hmem⟩, ?_, ?_⟩
    · intro h
      have h' := congrArg Subtype.val h
      simp [ha0] at h'
    · simp [ha0]

theorem fl_den {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (x : E) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O := by
  obtain ⟨t, ht⟩ := (L.3 (x + L.cj x)).1 (by rw [map_add (f := _), L.2, add_comm])
  obtain ⟨m, hm⟩ := (L.3 (x * L.cj x)).1 (by rw [map_mul, L.2, mul_comm])
  obtain ⟨c1, hc1, ht1⟩ := fl_den_F t
  obtain ⟨c2, hc2, hm2⟩ := fl_den_F m
  refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
  rw [L.9]
  have key : ∀ z : 𝒪[F], algebraMap 𝒪[F] E z = algebraMap F E (z : F) :=
    fun z => IsScalarTower.algebraMap_apply 𝒪[F] F E z
  have hx2 : x * x = algebraMap F E t * x - algebraMap F E m := by rw [ht, hm]; ring
  refine ⟨X ^ 2 - C (c2 * ⟨(c1 : F) * t, ht1⟩) * X + C (c1 ^ 2 * c2 * ⟨(c2 : F) * m, hm2⟩), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, key]
  push_cast
  try simp only [map_mul, map_pow]
  linear_combination (algebraMap F E c1 * algebraMap F E c2) ^ 2 * hx2

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel

theorem latBasis_exists (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (S : Submodule 𝒪[F] (Fin n → F))
    (hfg : S.FG) (hsp : Submodule.span F (S : Set (Fin n → F)) = ⊤) :
    ∃ b : Module.Basis (Fin n) F (Fin n → F), (∀ k, b k ∈ S) ∧
      ∀ v, v ∈ S ↔ ∀ k, b.repr v k ∈ 𝒪[F] := by
  have : Module.Finite 𝒪[F] S := Module.Finite.of_fg hfg
  have : S.IsLattice F := Submodule.IsLattice.of_fg F hfg
  have : S.IsFullLattice F := ⟨hsp⟩
  have hr : Module.finrank 𝒪[F] S = n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq F S).trans (Module.finrank_fintype_fun_eq_card F))
  have : Module.Free 𝒪[F] S := Submodule.IsLattice.free F S
  let b0 : Module.Basis (Fin n) 𝒪[F] S := Module.finBasisOfFinrankEq 𝒪[F] S hr
  let b := b0.extendOfIsFullLattice F
  have hb : ∀ k, b k = (b0 k : Fin n → F) := fun k => by simp [b]
  refine ⟨b, fun k => by rw [hb]; exact (b0 k).2, fun v => ⟨fun hv k => ?_, fun h => ?_⟩⟩
  · have key : v = b.equivFun.symm (fun k => ((b0.repr ⟨v, hv⟩ k : 𝒪[F]) : F)) := by
      rw [Module.Basis.equivFun_symm_apply]
      have h1 : ∑ i, ((b0.repr ⟨v, hv⟩ i • b0 i : S) : Fin n → F) = v := by
        rw [← Submodule.coe_sum, b0.sum_repr]
      conv_lhs => rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, Submodule.coe_smul]
      rfl
    have h2 := congrArg b.equivFun key
    rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at h2
    rw [h2]
    exact (b0.repr ⟨v, hv⟩ k).2
  · rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun k _ => ?_
    have := S.smul_mem (⟨b.repr v k, h k⟩ : 𝒪[F]) (show b k ∈ S by rw [hb]; exact (b0 k).2)
    exact this

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

end Herm

section Coord

variable {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V]

def sig (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x : V) : (Fin n → F) × (Fin n → F) :=
  (fun k => (e (β.repr x k)).1, fun k => (e (β.repr x k)).2)

def tau (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p : (Fin n → F) × (Fin n → F)) : V :=
  ∑ k, e.symm (p.1 k, p.2 k) • β k

theorem sig_tau (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p : (Fin n → F) × (Fin n → F)) :
    sig e β (tau e β p) = p := by
  unfold sig tau
  first
  | simp only [Basis.repr_sum_self, AlgEquiv.apply_symm_apply]
  | simp [map_sum, Finsupp.single_apply]

theorem tau_sig (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x : V) :
    tau e β (sig e β x) = x := by
  unfold sig tau
  simp only [Prod.mk.eta, AlgEquiv.symm_apply_apply]
  exact β.sum_repr x

theorem sig_add (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x y : V) :
    sig e β (x + y) = sig e β x + sig e β y := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig, map_add (f := _)]

theorem sig_smul (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (a : E) (x : V) :
    sig e β (a • x) = ((e a).1 • (sig e β x).1, (e a).2 • (sig e β x).2) := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig, map_mul]

theorem tau_add (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p q : (Fin n → F) × (Fin n → F)) :
    tau e β (p + q) = tau e β p + tau e β q := by
  unfold tau
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← add_smul, ← map_add (f := _)]
  rfl

theorem tau_smul (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (a : E)
    (p : (Fin n → F) × (Fin n → F)) :
    tau e β ((e a).1 • p.1, (e a).2 • p.2) = a • tau e β p := by
  unfold tau
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  have h1 : (((e a).1 • p.1) k, ((e a).2 • p.2) k) = e a * (p.1 k, p.2 k) :=
    Prod.ext (by simp) (by simp)
  rw [h1, map_mul, AlgEquiv.symm_apply_apply]

theorem sig_zero (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) : sig e β 0 = 0 := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig]

end Coord

end PI.UnitaryGroupMassFormula.CntFormula
end
end
