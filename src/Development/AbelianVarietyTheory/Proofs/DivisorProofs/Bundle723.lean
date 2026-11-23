module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle683
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle684
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
open scoped TensorProduct

namespace GlobalTheory.BadCount

theorem tmul_one_mem_nonZeroDivisors_of_field {K L R : Type} [Field K] [Field L] [Algebra K L]
    [CommRing R] [Algebra K R] (d : R) (hd : d ∈ nonZeroDivisors R) :
    ((1 : L) ⊗ₜ[K] d) ∈ nonZeroDivisors (L ⊗[K] R) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have hinj : Function.Injective ((LinearMap.mulRight K d).lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b hab => by
      have : (a - b) * d = 0 := by simpa [sub_mul, sub_eq_zero] using hab
      exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hd) _ this))
  have heq : ∀ y : L ⊗[K] R, (LinearMap.mulRight K d).lTensor L y = y * ((1 : L) ⊗ₜ[K] d) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add a b ha hb => simp [map_add (f := _), add_mul, ha, hb]
  apply hinj
  rw [heq, hx, map_zero]

theorem finrank_le_card_mul_finrank_eig_baseChange : ∀ (K L Γ R W : Type) [Field K] [Field L] [Algebra K L] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (Vm V : Submodule K R) [FiniteDimensional K V] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ Vm, x * act h u ∈ V) → ∀ [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (ρ' : Representation L Γ W), (∀ g v, ρ' g (f v) = f (ρ g v)) → ∀ lam : H →* Lˣ, finrank K Vm ≤ Nat.card H * finrank L (eig ρ' H lam) := by
  intro K L Γ R W _ _ _ _ _ _ _ act H _ _ u hdet Vm V _ ρ hρ hVm _ _ _ _ f hf ρ' hρ' lam
  classical
  let actL : Γ → (L ⊗[K] R →ₐ[L] L ⊗[K] R) := fun g => Algebra.TensorProduct.map (AlgHom.id L L) (act g)
  have actL_tmul : ∀ g (l : L) (r : R), actL g (l ⊗ₜ r) = l ⊗ₜ act g r := fun g l r => by
    simp [actL, Algebra.TensorProduct.map_tmul]
  have actL_mul : ∀ g g' x, actL (g * g') x = actL g (actL g' x) := by
    intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp only [actL_tmul, map_mul, AlgHom.mul_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have actL_one : ∀ x, actL 1 x = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp only [actL_tmul, map_one, AlgHom.one_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have inj_of : ∀ {M : Type} [AddCommGroup M] [Module K M] (g : M →ₗ[K] R), Function.Injective g →
      Function.Injective (g.baseChange L) := by
    intro M _ _ g hg
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap g hg
  let ιV : L ⊗[K] V →ₗ[L] L ⊗[K] R := V.subtype.baseChange L
  let ιm : L ⊗[K] Vm →ₗ[L] L ⊗[K] R := Vm.subtype.baseChange L
  let A : H → (Vm →ₗ[K] V) := fun h =>
    { toFun := fun x => ⟨(x : R) * act h u, hVm h x x.2⟩
      map_add' := by intro x y; ext; simp [add_mul]
      map_smul' := by intro c x; ext; simp [smul_mul_assoc] }
  have hA : ∀ h y, ιV ((A h).baseChange L y) = ιm y * ((1 : L) ⊗ₜ act h u) := by
    intro h y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l x => simp [ιV, ιm, A, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add (f := _), add_mul, hx, hy]
  let e := hf.equiv
  let j : W →ₗ[L] L ⊗[K] R := ιV ∘ₗ e.symm.toLinearMap
  have hj : ∀ (g : Γ) w, j (ρ' g w) = actL g (j w) := by
    intro g w
    obtain ⟨z, rfl⟩ := e.surjective w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul l v =>
      have h1 : e (l ⊗ₜ v) = l • f v := hf.equiv_tmul l v
      have h2 : e (l ⊗ₜ ρ g v) = l • f (ρ g v) := hf.equiv_tmul l _
      simp only [j, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [h1, map_smul, hρ', ← h2, ← h1, e.symm_apply_apply, e.symm_apply_apply]
      simp [ιV, actL_tmul, hρ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hje : ∀ z, j (e z) = ιV z := fun z => by simp [j]
  let T : W →ₗ[L] W := ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • ρ' g
  have hT : ∀ w, T w ∈ eig ρ' H lam := by
    intro w
    rw [mem_eig]
    intro k

    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ (fun g => ?_)
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul ρ', Module.End.mul_apply, smul_smul, map_mul lam]
    congr 1
    rw [← Units.val_mul, mul_inv, mul_inv_cancel_left]
  have hjT : ∀ w, j (T w) = ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • actL g (j w) := by
    intro w

    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hj]
  let Ψ : L ⊗[K] Vm →ₗ[L] (H → eig ρ' H lam) :=
    LinearMap.pi fun h => LinearMap.codRestrict (eig ρ' H lam) (T ∘ₗ e.toLinearMap ∘ₗ (A h).baseChange L)
      (fun y => hT _)
  have hΨ : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have P : ∀ h : H, ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • actL g (ιm y * ((1 : L) ⊗ₜ act h u)) = 0 := by
      intro h
      have h0 := congrArg Subtype.val (congrFun hy h)
      simp only [Ψ, LinearMap.pi_apply, LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Pi.zero_apply, ZeroMemClass.coe_zero] at h0
      have h1 := congrArg j h0
      rw [hjT, hje, hA, map_zero] at h1
      exact h1
    have key := GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H L (L ⊗[K] R)
      (fun h => actL ((h : Γ)⁻¹)) (fun x => by simp [actL_one])
      (fun h h' x => by simp [mul_inv_rev, actL_mul]) lam⁻¹ ((1 : L) ⊗ₜ u) ?_
    · have hy0 : ιm y = 0 := by
        refine key.2.1 (ιm y) (fun h' => ?_)
        rw [← P h'⁻¹]
        refine Fintype.sum_equiv (Equiv.inv H) _ _ (fun g => ?_)
        simp [actL_tmul]
      exact inj_of _ Vm.injective_subtype (by rw [hy0, map_zero])
    · have hM : (Matrix.of fun h g : H => actL (((h * g : H) : Γ)⁻¹) ((1 : L) ⊗ₜ[K] u)) =
          (Algebra.TensorProduct.includeRight : R →ₐ[K] L ⊗[K] R).mapMatrix
            ((Matrix.transpose (Matrix.of fun h g : H => act ((h : Γ) * g) u)).submatrix (Equiv.inv H) (Equiv.inv H)) := by
        ext h g
        simp [actL_tmul, mul_inv_rev, Function.swap]
      show (Matrix.of fun h g : H => actL (((h * g : H) : Γ)⁻¹) ((1 : L) ⊗ₜ[K] u)).det ∈ _
      rw [hM, ← AlgHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_transpose,
        Algebra.TensorProduct.includeRight_apply]
      exact tmul_one_mem_nonZeroDivisors_of_field _ hdet
  have hfinW : Module.Finite L W := Module.Finite.equiv e
  have h1 : finrank K Vm = finrank L (L ⊗[K] Vm) := (Module.finrank_baseChange).symm
  rw [h1]
  refine (LinearMap.finrank_le_finrank_of_injective hΨ).trans (le_of_eq ?_)
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

end GlobalTheory.BadCount
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.RegEmbed

variable {K Γ R : Type} [Field K] [Group Γ] [CommRing R] [Algebra K R]
  (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H]

theorem act_mul_apply (a b : Γ) (x : R) : act (a * b) x = act a (act b x) := by
  rw [map_mul]; rfl

theorem act_one_apply (x : R) : act 1 x = x := by
  rw [map_one]; rfl

theorem sum_act_act (x : R) (g : H) : ∑ k : H, act k (act g x) = ∑ k : H, act k x := by
  rw [← Equiv.sum_comp (Equiv.mulRight g⁻¹)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [← act_mul_apply]

theorem act_sum_act (x : R) (g : H) : act g (∑ k : H, act k x) = ∑ k : H, act k x := by

  rw [map_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft g⁻¹)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Equiv.coe_mulLeft, ← act_mul_apply, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

def invIn (V₁ : Submodule K R) : Submodule K R where
  carrier := {x | x ∈ V₁ ∧ ∀ h : H, act h x = x}
  add_mem' := fun ha hb => ⟨V₁.add_mem ha.1 hb.1, fun h => by rw [map_add (f := _), ha.2, hb.2]⟩
  zero_mem' := ⟨V₁.zero_mem, fun h => map_zero _⟩
  smul_mem' := fun c x hx => ⟨V₁.smul_mem c hx.1, fun h => by rw [map_smul, hx.2]⟩

def trL : R →ₗ[K] R := ∑ g : H, (act g).toLinearMap

theorem trL_apply (x : R) : trL act H x = ∑ g : H, act g x := by
  simp [trL]

theorem trL_mem (V₁ : Submodule K R) (hV₁ : ∀ h : H, ∀ x ∈ V₁, act h x ∈ V₁) (x : R) (hx : x ∈ V₁) :
    trL act H x ∈ invIn act H V₁ := by
  rw [trL_apply]
  exact ⟨V₁.sum_mem fun g _ => hV₁ g x hx, fun g => act_sum_act act H x g⟩

theorem eq_zero_of_traces [DecidableEq H] (u : R)
    (hdet : (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R) (v : R)
    (hv : ∀ h : H, ∑ g : H, act g (v * act h u) = 0) : v = 0 := by
  have h0 := GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.transpose (Matrix.of fun h g : H => act ((h : Γ) * g) u))
    (by rwa [Matrix.det_transpose]) (fun g : H => act g v) (by
      funext h
      rw [Pi.zero_apply, ← hv h]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul (act (g : Γ)), act_mul_apply, mul_comm])
  simpa [act_one_apply] using congrFun h0 1

theorem eq_zero_of_sum [DecidableEq H] (u : R)
    (hdet : (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R) (F : H → R)
    (hF : ∀ g h : H, act g (F h) = F h) (h0 : ∑ h : H, F h * act h u = 0) : F = 0 := by
  refine GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor _ hdet F ?_
  funext g
  have h2 := congrArg (fun x => act (g : Γ) x) h0

  simp only [map_sum, map_zero] at h2
  rw [Pi.zero_apply, ← h2]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul (act (g : Γ)), hF, act_mul_apply, mul_comm]

end GlobalTheory.RegEmbed

namespace GlobalTheory.BadCount


open GlobalTheory.RegEmbed in
theorem embReg_of_groupDet : ∀ (K Γ R : Type) [Field K] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (V V₁ V₂ : Submodule K R) [FiniteDimensional K V₂] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V₁) → (∀ h : H, ∀ x ∈ V₁, act h x ∈ V₁) → (∀ h : H, ∀ x ∈ V₁, x * act h u ∈ V₂) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H ≤ finrank K V₂ := by
  intro K Γ R _ _ _ _ _ act H _ _ u hdet V V₁ V₂ _ ρ hρ hV hV₁ hV₁₂
  let I := invIn act H V₁
  let T : H → (V →ₗ[K] I) := fun h =>
    ((trL act H).comp ((LinearMap.mulRight K (act h u)).comp V.subtype)).codRestrict I
      (fun v => trL_mem act H V₁ hV₁ _ (hV h v v.2))
  have hT : ∀ h v, ((T h v : I) : R) = ∑ g : H, act g (v * act h u) := fun h v => by
    simp [T, trL_apply]
  let Ψ : (H → I) →ₗ[K] V₂ :=
    (∑ h : H, (LinearMap.mulRight K (act h u)).comp (I.subtype.comp (LinearMap.proj h))).codRestrict V₂
      (fun F => by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        exact V₂.sum_mem fun h _ => hV₁₂ h _ (F h).2.1)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro F hF
    have h0 := eq_zero_of_sum act H u hdet (fun h => (F h : R)) (fun g h => (F h).2.2 g) (by
      have := congrArg Subtype.val hF
      simpa [Ψ] using this)
    funext h
    exact Subtype.ext (congrFun h0 h)
  haveI : Module.Finite K (H → I) := Module.Finite.of_injective Ψ hΨ
  haveI : Module.Finite K I :=
    Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : H => I) 1) (fun x => ⟨fun _ => x, rfl⟩)
  have hle := LinearMap.finrank_le_finrank_of_injective hΨ
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  let b := Module.finBasis K I
  let j : V →ₗ[K] (Fin (finrank K I) → MonoidAlgebra K H) := LinearMap.pi fun i =>
    (MonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ (Finsupp.linearEquivFunOnFinite K K H).symm.toLinearMap ∘ₗ
      LinearMap.pi (fun h => (LinearMap.proj i ∘ₗ b.equivFun.toLinearMap) ∘ₗ T h)
  have hj : ∀ v i h, (j v i).coeff h = b.equivFun (T h v) i := fun v i h => by
    simp [j]
  refine ⟨finrank K I, ⟨j, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hTv : ∀ h, T h v = 0 := fun h => by
      apply b.equivFun.injective
      funext i
      rw [← hj, hv]
      simp
    apply Subtype.ext
    refine eq_zero_of_traces act H u hdet (v : R) fun h => ?_
    rw [← hT, hTv]
    rfl
  · intro h v i
    apply MonoidAlgebra.ext
    ext k
    rw [MonoidAlgebra.single_mul_apply, one_mul, hj, hj]
    have : T k (ρ h v) = T (h⁻¹ * k) v := by
      apply Subtype.ext
      rw [hT, hT, hρ]
      conv_rhs => rw [← sum_act_act act H _ h]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      rw [map_mul (act (h : Γ)), Subgroup.coe_mul, Subgroup.coe_inv, ← act_mul_apply act (h : Γ) ((h : Γ)⁻¹ * k),
        mul_inv_cancel_left]
    rw [this]
  · rw [Nat.card_eq_fintype_card, mul_comm]
    exact hle

end GlobalTheory.BadCount
end
end

section

open Module NumberField

namespace GlobalTheory.BadCount

theorem semilin_eq_sum {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ} {σ : K →+* ℂ}
    (f : (Fin N → K) →ₛₗ[σ] V) (x : Fin N → K) : f x = ∑ k, σ (x k) • f (Pi.single k 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ]

theorem top_le_span_single {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ} {σ : K →+* ℂ}
    (f : (Fin N → K) →ₛₗ[σ] V) (h : Submodule.span ℂ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
  rw [← h, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [semilin_eq_sum f x]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem embReg_of_semilinear {V V' G : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [Group G] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (τ : ℂ ≃+* ℂ) (T : V' →+ V)
    (hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v) (hi : Function.Injective T)
    (he : ∀ g v, T (ρ' g v) = ρ g (T v)) (H : Subgroup G) (n : ℕ) (h : EmbReg ρ H n) : EmbReg ρ' H n := by
  obtain ⟨j, hj, hje⟩ := h
  let m : MonoidAlgebra ℂ H →+* MonoidAlgebra ℂ H := MonoidAlgebra.mapRingHom H (τ : ℂ →+* ℂ)
  have hm : ∀ x a, (m x).coeff a = τ (x.coeff a) := fun x a => MonoidAlgebra.coeff_mapRingHom _ _ _
  have hmi : Function.Injective m := by
    intro x y hxy
    ext a
    apply τ.injective
    rw [← hm, ← hm, hxy]
  refine ⟨{ toFun := fun v i => m (j (T v) i)
            map_add' := fun v w => ?_
            map_smul' := fun c v => ?_ }, fun v w hvw => ?_, fun g v i => ?_⟩
  · funext i
    simp
  · funext i
    ext a
    simp [hs, hm]
  · exact hi (hj (funext fun i => hmi (congrFun hvw i)))
  · show m (j (T (ρ' g v)) i) = _ * m (j (T v) i)
    rw [he, hje, map_mul]
    congr 1
    exact (MonoidAlgebra.mapRingHom_single _ _ _).trans (by rw [map_one])

theorem embReg_of_baseChange : ∀ (K V V' G : Type) [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Group G] [Finite G] (N : ℕ) (ρK : Representation K G (Fin N → K))
    (σ σ' : K →+* ℂ) (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (f : (Fin N → K) →ₛₗ[σ] V)
    (f' : (Fin N → K) →ₛₗ[σ'] V'), (LinearIndependent ℂ fun k => f (Pi.single k 1)) →
    Submodule.span ℂ (Set.range f) = ⊤ → (LinearIndependent ℂ fun k => f' (Pi.single k 1)) →
    Submodule.span ℂ (Set.range f') = ⊤ → (∀ g v, ρ g (f v) = f (ρK g v)) →
    (∀ g v, ρ' g (f' v) = f' (ρK g v)) → ∀ (H : Subgroup G) (n : ℕ),
    GlobalTheory.BadCount.EmbReg ρ H n → GlobalTheory.BadCount.EmbReg ρ' H n := by
  intro K V V' G _ _ _ _ _ _ _ _ N ρK σ σ' ρ ρ' f f' hl _ hl' hsp' he he' H n h
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq K σ σ'
  let b' : Basis (Fin N) ℂ V' := Basis.mk hl' (top_le_span_single f' hsp')
  have hb' : ∀ k, b' k = f' (Pi.single k 1) := fun k => Basis.mk_apply _ _ k
  let T : V' →+ V :=
    { toFun := fun v => ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1)
      map_zero' := by simp
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib] }
  have hT : ∀ v, T v = ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1) := fun _ => rfl
  have hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v := fun c v => by
    simp [hT, Finset.smul_sum, mul_smul]
  have hTf : ∀ x, T (f' x) = f x := fun x => by
    have hr : ∀ k, b'.repr (f' x) k = σ' (x k) := fun k => by
      rw [semilin_eq_sum f' x]
      simp only [← hb']
      exact congrFun (b'.repr_sum_self _) k
    rw [hT, semilin_eq_sum f x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hr, ← hτ, RingEquiv.symm_apply_apply]
  refine embReg_of_semilinear ρ ρ' τ T hs ?_ (fun g v => ?_) H n h
  · rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hT] at hv
    have h0 := Fintype.linearIndependent_iff.1 hl _ hv
    apply b'.repr.injective
    ext k
    simpa using h0 k
  · have hv : v ∈ Submodule.span ℂ (Set.range f') := hsp' ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [he', hTf, hTf, he]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hs, hs, map_smul, hx]

end GlobalTheory.BadCount
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem jT_eq_latDisc (Λ : PeriodPair) (c : ℂ) (τ : ℍ) (h : IsTauOf Λ c τ) :
    jT τ = 1728 * Λ.g₂ ^ 3 / latDisc Λ :=
  (ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT h).symm

theorem pow_twelve_eq_DD (Λ : PeriodPair) (c : ℂ) (τ : ℍ) (h : IsTauOf Λ c τ) (Ω : ℂ)
    (hΩ : Ω ^ 12 = latDisc Λ) : (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ := by
  have hc : c ≠ 0 := h.1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ^ 12 = 1 := by
    rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, Complex.I_pow_four, one_pow]
  have hd : latDisc Λ = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ :=
    ReciprocityTheory.ChartRestriction.L1.disc_eq h
  rw [div_pow, mul_pow, mul_pow, mul_pow, hI, hΩ, hd]
  field_simp
  ring

theorem jT_eq_and_pow_twelve_eq_DD : ∀ (Λ : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf Λ c τ → jT τ = 1728 * Λ.g₂ ^ 3 / latDisc Λ ∧ ∀ Ω : ℂ, Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ :=
  fun Λ c τ h => ⟨jT_eq_latDisc Λ c τ h, pow_twelve_eq_DD Λ c τ h⟩

end GlobalTheory.QFam
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I → ∃ c' : Katz.Chart (G.baseChange (O ⧸ I)) d, c'.IsLawOf (fun i => map (Ideal.Quotient.mk I) (c.μ i)) ∧ (∀ n f, c'.ev n (map (Ideal.Quotient.mk I) f) = (G.toBase (O ⧸ I)).app n (c.ev n f)) ∧ ∀ n s, c'.ev₂ n (map (Ideal.Quotient.mk I) s) = ((G.toBase (O ⧸ I)).app n).two (c.ev₂ n s) := by
  first | exact @GlobalTheory.QLog.ChartRed.exists_chart | exact GlobalTheory.QLog.ChartRed.exists_chart | (intros; apply GlobalTheory.QLog.ChartRed.exists_chart <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.cob1_formalLog_mem_ker_of_map_grouplike : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ' i) = 0) → ∀ g : MvPowerSeries (Fin d) B, constantCoeff g = 1 → subst (fun i => map θ (μ' i)) (map θ g) = inL (map θ g) * inR (map θ g) → In (RingHom.ker θ) (cob1 (up Q μ') (formalLog (map (algebraMap B Q) g))) := by
  first | exact @GlobalTheory.CobLog.cob1_formalLog_mem_ker | exact GlobalTheory.CobLog.cob1_formalLog_mem_ker | (intros; apply GlobalTheory.CobLog.cob1_formalLog_mem_ker <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.frobenius_formalLog_sub_smul_integral : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σB : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σB b)) → (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B), constantCoeff g = 1 → In (⊤ : Ideal B) (frob p s (formalLog (map (algebraMap B Q) g)) - (p : Q) • formalLog (map (algebraMap B Q) g)) := by
  first | exact @GlobalTheory.QLog.in_frob_formalLog_sub_smul | exact GlobalTheory.QLog.in_frob_formalLog_sub_smul | (intros; apply GlobalTheory.QLog.in_frob_formalLog_sub_smul <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.convPow_ofConv_sub_constantCoeff_invariantDerivation : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (k : ℕ) (F : MvPowerSeries (Fin d) O), (φ ^ k) (c.ev n F) - constantCoeff ((invDer c.μ u)^[k] F) ∈ m := by
  first | exact @GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem | exact GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem | (intros; apply GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem <;> assumption)
end
