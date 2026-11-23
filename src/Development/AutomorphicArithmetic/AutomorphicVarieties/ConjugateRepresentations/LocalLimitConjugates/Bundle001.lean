module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle001
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Algebra.Star.Unitary
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Algebra.Group.Matrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private def stab (ψ : Sm E a) : Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) where
  carrier := {k | rt E a (finGL E a k) ψ = ψ}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_mul, map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

private theorem lev_lie (X : Lie E a) (ψ : Sm E a) (h : HasLev ψ) : HasLev (lie E a X ψ) := by
  have hle : stab ψ ≤ stab (lie E a X ψ) := fun k hk =>
    (LinearMap.congr_fun (lie_rt_fin X k) ψ).symm.trans (congrArg (lie E a X) hk)
  exact Subgroup.isOpen_mono hle h

private theorem lev_rt (g : GA E a) (ψ : Sm E a) (h : HasLev ψ) : HasLev (rt E a g ψ) := by
  obtain ⟨y, l, rfl⟩ : ∃ y l, infGL E a y * finGL E a l = g := ⟨_, _, infGL_mul_finGL g⟩
  have hc : Continuous fun k : GL (Fin a) (GlobalTheory.CuspRep.Af E) => l⁻¹ * k * l := by fun_prop
  have ho : IsOpen ((fun k : GL (Fin a) (GlobalTheory.CuspRep.Af E) => l⁻¹ * k * l) ⁻¹' (stab ψ : Set _)) :=
    IsOpen.preimage hc h
  refine Subgroup.isOpen_of_mem_nhds (stab (rt E a (infGL E a y * finGL E a l) ψ)) (g := 1)
    (mem_of_superset (ho.mem_nhds ?_) fun k hk => ?_)
  · simpa using (stab ψ).one_mem
  · have hk' : rt E a (finGL E a (l⁻¹ * k * l)) ψ = ψ := hk
    change rt E a (finGL E a k) (rt E a (infGL E a y * finGL E a l) ψ) = rt E a (infGL E a y * finGL E a l) ψ
    have e : finGL E a k * (infGL E a y * finGL E a l) = infGL E a y * finGL E a l * finGL E a (l⁻¹ * k * l) := by
      rw [← mul_assoc, ← infGL_comm, mul_assoc, mul_assoc (infGL E a y), ← map_mul, ← map_mul]
      congr 2
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']

private theorem supp_lie (X : Lie E a) (ψ : Sm E a) (h : HasCompactSupport ψ.1) :
    HasCompactSupport (lie E a X ψ).1 := by
  obtain ⟨c, c0, -, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  set_option synthInstance.maxHeartbeats 200000 in
    refine HasCompactSupport.intro h fun g hg => ?_
  have hd := GlobalTheory.CuspRep.hasDerivAt_curve ψ g c X c0 cder
  have hc : Continuous fun t : ℝ => g * infGL E a (c t) := continuous_const.mul ccont
  have ht : Tendsto (fun t : ℝ => g * infGL E a (c t)) (𝓝 0) (𝓝 g) := by
    set_option synthInstance.maxHeartbeats 200000 in
      simpa [c0] using hc.tendsto 0
  have hz : (fun t : ℝ => ψ.1 (g * infGL E a (c t))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) :=
    ht.eventually (notMem_tsupport_iff_eventuallyEq.1 hg)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)

private theorem supp_rt (g : GA E a) (ψ : Sm E a) (h : HasCompactSupport ψ.1) :
    HasCompactSupport (rt E a g ψ).1 :=
  h.comp_homeomorph (Homeomorph.mulRight g)

end

theorem UpperTheory.V.Cj.H.testOps :
    UpperTheory.V.Cj.H.TestOps := by
  intro E _ _ _ a ψ
  exact ⟨fun h => ⟨ContAut.continuous_of_isOpen_stab E a ψ h, fun X => lev_lie X ψ h, fun g => lev_rt g ψ h⟩,
    fun h => ⟨fun X => ⟨supp_lie X ψ h.1, lev_lie X ψ h.2⟩, fun g => ⟨supp_rt g ψ h.1, lev_rt g ψ h.2⟩⟩⟩
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

noncomputable section

namespace UpperTheory.V.Cj.H

private theorem multi_cont {H : Type} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [T2Space H] [FiniteDimensional ℝ H] {q : ℕ} (f : (Fin q → H) →ₘₗ[ℝ] ℂ) :
    Continuous f := by
  classical
  let b := Module.finBasis ℝ H
  have h : (f : (Fin q → H) → ℂ) = fun x => ∑ r : Fin q → Fin (Module.finrank ℝ H),
      (∏ i, b.coord (r i) (x i)) • f fun i => b (r i) := by
    funext x
    have e : x = fun i => ∑ j, b.coord j (x i) • b j := funext fun i => (b.sum_repr (x i)).symm
    conv_lhs => rw [e]

    rw [f.map_sum]
    exact Finset.sum_congr rfl fun r _ => f.map_smul_univ _ _
  rw [h]
  refine continuous_finsetSum _ fun r _ => Continuous.fun_smul (continuous_finsetProd _ fun i _ => ?_) continuous_const
  exact (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)

private def contr {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} :
    (Fin d → ℂ) →ₗ[ℂ] S ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] S :=
  ∑ i, (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ).smulRight (Bor.cmp i)

private theorem contr_tmul {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} (v u : Fin d → ℂ) (φ : S) :
    contr v (φ ⊗ₜ[ℂ] u) = (v ⬝ᵥ u) • φ := by
  simp [contr, LinearMap.sum_apply, dotProduct, Finset.sum_smul, smul_smul]

private theorem contr_single {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} (i : Fin d) (m : S ⊗[ℂ] (Fin d → ℂ)) :
    contr (Pi.single i 1) m = Bor.cmp i m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ u => simp [contr_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem abs_type {K H S : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [T2Space H] [FiniteDimensional ℝ H] [AddCommGroup S] [Module ℂ S] [Module ℝ S] [IsScalarTower ℝ ℂ S]
    {d : ℕ} (q : ℕ) (ad : K →* (H →ₗ[ℝ] H)) (had : ∀ X, Continuous fun k => ad k X)
    (M : K →* Matrix (Fin d) (Fin d) ℂ) (hM : Continuous M) (π : Representation ℂ K S) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (ρ : Representation ℂ K W), GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ ω : (Fin q → H) →ₘₗ[ℝ] S ⊗[ℂ] (Fin d → ℂ),
        (∀ k X, ω (fun i => ad k (X i)) = TensorProduct.map (π k) (Matrix.toLin' (M k)) (ω X)) → ∀ X i,
      ∃ (T : W →ₗ[ℂ] S) (w : W), (∀ k v, T (ρ k v) = π k (T v)) ∧ T w = Bor.cmp i (ω X) := by
  classical
  let P := PiTensorProduct ℝ fun _ : Fin q => H
  let A : K → P →ₗ[ℝ] P := fun k => PiTensorProduct.map fun _ => ad k
  let B : K → (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := fun k => Matrix.toLin' (M k⁻¹)ᵀ
  let ρ : Representation ℂ K ((Fin d → ℂ) ⊗[ℝ] P) :=
    { toFun := fun k => TensorProduct.AlgebraTensorModule.map (B k) (A k)
      map_one' := by
        have h1 : A 1 = LinearMap.id := by
          simp only [A, map_one]; exact PiTensorProduct.map_one
        have h2 : B 1 = LinearMap.id := by simp [B]
        rw [h1, h2, TensorProduct.AlgebraTensorModule.map_id]; rfl
      map_mul' := fun k l => by
        have h1 : A (k * l) = A k ∘ₗ A l := by
          simp only [A, map_mul]; exact PiTensorProduct.map_mul _ _
        have h2 : B (k * l) = B k ∘ₗ B l := by simp [B, Matrix.toLin'_mul]
        rw [h1, h2, TensorProduct.AlgebraTensorModule.map_comp]; rfl }
  have hρ : ∀ k v (X : Fin q → H), ρ k (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X) =
      ((M k⁻¹)ᵀ *ᵥ v) ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ fun i => ad k (X i) := fun k v X => by
    change TensorProduct.AlgebraTensorModule.map (B k) (A k) _ = _
    rw [TensorProduct.AlgebraTensorModule.map_tmul]
    exact congrArg₂ _ rfl (PiTensorProduct.map_tprod _ _)
  have ind : ∀ (p : (Fin d → ℂ) ⊗[ℝ] P → Prop) (h0 : p 0) (ha : ∀ x y, p x → p y → p (x + y))
      (ht : ∀ v (X : Fin q → H), p (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X)) (w : (Fin d → ℂ) ⊗[ℝ] P), p w := by
    intro p h0 ha ht w
    induction w using TensorProduct.induction_on with
    | zero => exact h0
    | add x y hx hy => exact ha x y hx hy
    | tmul v t =>
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r X => rw [← TensorProduct.smul_tmul]; exact ht _ _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact ha _ _ hx hy
  refine ⟨(Fin d → ℂ) ⊗[ℝ] P, inferInstance, inferInstance, Module.Finite.of_restrictScalars_finite ℝ ℂ _, ρ,
    fun ℓ w => ?_, fun ω hω X i => ?_⟩
  · induction w using ind with
    | h0 => simpa using continuous_const
    | ha x y hx hy => simpa only [map_add (f := _)] using hx.fun_add hy
    | ht v X =>
      have e : (fun k => ℓ (ρ k (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X))) = fun k => ∑ j, ((M k⁻¹)ᵀ *ᵥ v) j *
          ((ℓ.restrictScalars ℝ ∘ₗ TensorProduct.mk ℝ (Fin d → ℂ) P (Pi.single j 1)).compMultilinearMap
            (PiTensorProduct.tprod ℝ)) fun i => ad k (X i) := by
        funext k
        rw [hρ]
        generalize (M k⁻¹)ᵀ *ᵥ v = u
        conv_lhs => rw [pi_eq_sum_univ' u]

        rw [TensorProduct.sum_tmul, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← TensorProduct.smul_tmul', map_smul]
        rfl
      rw [e]
      refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ ?_
      · exact (continuous_apply j).comp ((hM.comp continuous_inv).matrix_transpose.matrix_mulVec continuous_const)
      · exact (multi_cont _).comp (continuous_pi fun i => had _)
  · let T : (Fin d → ℂ) ⊗[ℝ] P →ₗ[ℂ] S := TensorProduct.AlgebraTensorModule.lift
      { toFun := fun v => (contr v).restrictScalars ℝ ∘ₗ PiTensorProduct.lift ω
        map_add' := fun u v => by ext; simp
        map_smul' := fun c v => by ext; simp }
    have hT : ∀ v (Y : Fin q → H), T (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ Y) = contr v (ω Y) := fun v Y => by
      exact congrArg (contr v) (PiTensorProduct.lift.tprod (φ := ω) Y)
    refine ⟨T, Pi.single i 1 ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X, fun k w => ?_, by rw [hT, contr_single]⟩
    induction w using ind with
    | h0 => simp
    | ha x y hx hy => simp only [map_add (f := _), hx, hy]
    | ht v Y =>
      rw [hρ, hT, hT, hω]
      induction ω Y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul φ u =>
        rw [TensorProduct.map_tmul, contr_tmul, contr_tmul, map_smul, Matrix.toLin'_apply, Matrix.mulVec_transpose,
          ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

end UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.kType :
    UpperTheory.V.Cj.H.KType := by
  intro E _ _ _ a Ξ q
  let ad : Kinf E a →* (Herm E a →ₗ[ℝ] Herm E a) :=
    { toFun := fun k =>
        { toFun := adHerm k
          map_add' := fun X Y => Subtype.ext (by simp [adHerm, mul_add, add_mul])
          map_smul' := fun c X => Subtype.ext (by simp [adHerm]) }
      map_one' := LinearMap.ext fun X => Subtype.ext (by simp [adHerm])
      map_mul' := fun k l => LinearMap.ext fun X => Subtype.ext (by simp [adHerm, mul_assoc]) }
  have had : ∀ X, Continuous fun k => ad k X := fun X =>
    Continuous.subtype_mk ((continuous_subtype_val.mul continuous_const).mul continuous_subtype_val.star) _
  have hM : Continuous (Ξ.mat.comp (Unitary.toUnits : Kinf E a →* _)) := by
    refine continuous_matrix fun i j => continuous_iff_continuousAt.2 fun k => ?_
    have h := (differentiableAt_extGL (Ξ.reg i j) (x := toL (Unitary.toUnits k).val) (Unitary.toUnits k).isUnit).continuousAt
    have h2 : Continuous fun l : Kinf E a => (toL (Unitary.toUnits l).val : Lie E a) := continuous_subtype_val
    have h3 := ContinuousAt.comp (f := fun l : Kinf E a => (toL (Unitary.toUnits l).val : Lie E a)) h h2.continuousAt
    simp only [Function.comp_def, extGL_val] at h3
    exact h3
  obtain ⟨W, i1, i2, i3, ρ, h1, h2⟩ := abs_type q ad had _ hM (cptRep E a)
  exact ⟨W, i1, i2, i3, ρ, h1, fun ω hω => h2 ω.toMultilinearMap hω⟩
end
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.absDense :
    UpperTheory.V.Cj.H.AbsDense := by
  intro G H _ _ _ _ R D A hD hR hA hsym hirr s hs w hw
  set u : D → H := fun v => (A v : H) + (Complex.I * s) • (v : H) with hu
  have hinner : ∀ (g : G) (x y : H), inner ℂ (R g x) (R g y) = inner ℂ x y := fun g x y =>
    (LinearIsometry.mk (R g).toLinearMap (hR g)).inner_map_map x y
  have hinv : ∀ (g : G) (y : H), R g (R g⁻¹ y) = y := by
    intro g y
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let W : Submodule ℂ H :=
    { carrier := {x | ∀ v : D, inner ℂ x (u v) = 0}
      add_mem' := by
        intro a b ha hb v
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [inner_add_left, ha v, hb v, add_zero]
      zero_mem' := by
        intro v
        simp only [Set.mem_setOf_eq, inner_zero_left]
      smul_mem' := by
        intro c a ha v
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [inner_smul_left, ha v, mul_zero] }
  have hW : GlobalTheory.AutomorphicL2Unitary.IsSubrep R W := by
    refine ⟨?_, ?_⟩
    · have hset : (W : Set H) = ⋂ v : D, {x | inner ℂ x (u v) = 0} := by
        ext x
        simp [W]
      rw [hset]
      exact isClosed_iInter fun v => isClosed_eq (continuous_id.inner continuous_const) continuous_const
    · intro g x hx v
      show inner ℂ (R g x) (u v) = 0
      have key : R g⁻¹ (u v) = u ⟨R g⁻¹ v, hD g⁻¹ v v.2⟩ := by
        simp only [hu, map_add (f := _), map_smul]
        rw [hA g⁻¹ v]
      rw [← hinv g (u v), hinner, key]
      exact hx _
  have hWD : W ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxD⟩ := Submodule.mem_inf.mp hx
    have h0 : inner ℂ x (u ⟨x, hxD⟩) = 0 := hxW ⟨x, hxD⟩
    have hre : (inner ℂ x (A ⟨x, hxD⟩ : H)).im = 0 := by
      have hs' := hsym ⟨x, hxD⟩ ⟨x, hxD⟩
      rw [← inner_conj_symm] at hs'
      exact Complex.conj_eq_iff_im.mp hs'
    simp only [hu] at h0
    rw [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
    have him := congrArg Complex.im h0
    simp [hre, hs] at him
    rw [← Complex.ofReal_pow, Complex.ofReal_re] at him
    rw [Submodule.mem_bot]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp him)
  have hwW : w ∈ W := hw
  rw [hirr W hW hWD] at hwW
  exact (Submodule.mem_bot ℂ).mp hwW
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private noncomputable def cj (χ : HChar E) (T : Module.End ℂ (Sm E a)) : Module.End ℂ (Sm E a) :=
  (mulChi a χ).symm.toLinearMap ∘ₗ T ∘ₗ (mulChi a χ).toLinearMap

private theorem mul_cj (χ : HChar E) (T : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    mulChi a χ (cj χ T φ) = T (mulChi a χ φ) := (mulChi a χ).apply_symm_apply _

private theorem isOp_cj {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) {N : Submodule ℂ (Sm E a)}
    {T : Module.End ℂ (Sm E a)} (hT : IsOp N T) : IsOp (N.comap (mulChi a χ).toLinearMap) (cj χ T) := by
  refine { maps := ?_, lie := ?_, rt := ?_ }
  · intro φ hφ
    change mulChi a χ (cj χ T φ) ∈ N
    rw [mul_cj]
    exact hT.maps _ hφ
  · intro X φ hφ
    apply (mulChi a χ).injective
    have h1 := hT.lie X _ hφ
    have h2 := hχ.2 X (cj χ T φ)
    change lie E a X (T (mulChi a χ φ)) = T (lie E a X (mulChi a χ φ)) at h1
    rw [mul_cj, h1, hχ.2, map_add (f := _), map_add (f := _), map_add (f := _), map_smul, map_smul, map_smul, mul_cj] at h2
    rw [mul_cj]
    exact (add_right_cancel h2).symm
  · intro g φ hφ
    apply (mulChi a χ).injective
    have h1 := hT.rt g _ hφ
    have h2 := rt_mulChi χ g (cj χ T φ)
    change rt E a g (T (mulChi a χ φ)) = T (rt E a g (mulChi a χ φ)) at h1
    rw [mul_cj, h1, rt_mulChi, map_smul, map_smul, map_smul] at h2
    rw [mul_cj]
    exact (smul_right_injective _ (chiDet a χ g).ne_zero h2).symm

private theorem shift_mul {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) (X : Lie E a) (φ : Sm E a) :
    shift (lie E a) 0 X (mulChi a χ φ) = mulChi a χ (shift (lie E a) r X φ) := by
  rw [shift_apply, shift_apply, zero_mul, zero_smul, add_zero, hχ.2, LinearMap.add_apply, LinearMap.smul_apply,
    one_apply_eq_self, Complex.coe_smul]

private theorem casA_mul {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) (c : ℝ) {n : ℕ} (e : Fin n → Herm E a)
    (φ : Sm E a) : casA 0 c e (mulChi a χ φ) = mulChi a χ (casA r c e φ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, mul_apply_eq_comp, LinearMap.smul_apply,
    one_apply_eq_self, map_sub, map_sum, map_smul, shift_mul hχ]

private theorem locLim_mul (χ : HChar E) {f : ℕ → Sm E a} {φ : Sm E a}
    (h : LocLim (fun k => mulChi a χ (f k)) (mulChi a χ φ)) : LocLim f φ := by
  intro C hC
  have hc : Continuous fun g : GA E a => (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (χ.2.1.comp Matrix.GeneralLinearGroup.continuous_det).inv
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  have h1 := h C hC
  rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
  intro ε hε
  have hp : 0 < |B| + 1 := by positivity
  filter_upwards [h1 (ε / (|B| + 1)) (by positivity)] with k hk g hg
  have h2 := hk g hg
  rw [dist_eq_norm, mulChi_apply, mulChi_apply, ← sub_mul, lt_div_iff₀ hp] at h2
  have e : φ.1 g - (f k).1 g = (φ.1 g - (f k).1 g) * (chiDet a χ g : ℂˣ) * (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) :=
    (Units.mul_inv_cancel_right _ _).symm
  rw [dist_eq_norm, e, norm_mul]
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) h2
  exact (hB g hg).trans ((le_abs_self B).trans (le_add_of_nonneg_right zero_le_one))

end

theorem UpperTheory.V.Cj.H.twRes :
    UpperTheory.V.Cj.H.TwRes := by
  intro E _ _ _ a r χ hχ N n e c P Q S h
  refine ⟨cj χ P, fun k => cj χ (Q k), fun k => cj χ (S k), isOp_cj hχ h.opP, fun k => isOp_cj hχ (h.opQ k),
    fun k => isOp_cj hχ (h.opS k), fun k φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · apply (mulChi a χ).injective
    rw [map_sub, ← casA_mul hχ, mul_cj, mul_cj]
    exact h.res k _ hφ
  · apply (mulChi a χ).injective
    rw [map_zero, ← casA_mul hχ, mul_cj]
    exact h.ker _ hφ
  · apply locLim_mul χ
    simp only [mul_cj]
    exact h.lim _ hφ
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.chiGrow :
    UpperTheory.V.Cj.H.ChiGrow := by
  intro E _ _ _ a χ s _ φ hφ g
  obtain ⟨A, p, hA⟩ := hφ g
  obtain ⟨B, q, hB⟩ := chiDet_growth (a := a) χ⁻¹
  have hback : mulChi a χ⁻¹ (mulChi a χ φ) = φ := by
    rw [← mulChi_mul, mul_inv_cancel, mulChi_one]
  refine ⟨‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (A * B), p + q, fun y => ?_⟩
  have e : φ.1 (g * infGL E a y) = ((chiDet a χ⁻¹ g : ℂˣ) : ℂ) *
      ((mulChi a χ φ).1 (g * infGL E a y) * ((chiDet a χ⁻¹ (infGL E a y) : ℂˣ) : ℂ)) := by
    conv_lhs => rw [← hback, mulChi_apply, map_mul, Units.val_mul]
    ring
  have hprod := mul_le_mul (hA y) (hB y) (norm_nonneg _) ((norm_nonneg _).trans (hA y))
  calc ‖φ.1 (g * infGL E a y)‖
      = ‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (‖(mulChi a χ φ).1 (g * infGL E a y)‖ *
          ‖((chiDet a χ⁻¹ (infGL E a y) : ℂˣ) : ℂ)‖) := by rw [e, norm_mul, norm_mul]
    _ ≤ ‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (A * GlobalTheory.CuspRep.height y ^ p * (B * GlobalTheory.CuspRep.height y ^ q)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := by rw [pow_add]; ring
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private def levFnSub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsLevelFn U Ξ φ}
  zero_mem' := ⟨fun _ _ => rfl, fun u _ => map_zero _, fun m _ => by simp⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ g => congrArg₂ (· + ·) (h.1 γ g) (h'.1 γ g),
    fun u hu => by rw [map_add (f := _), h.2.1 u hu, h'.2.1 u hu],
    fun m hm => by rw [map_add (f := _), h.2.2 m hm, h'.2.2 m hm, smul_add]⟩
  smul_mem' := fun c φ h => ⟨fun γ g => congrArg (c • ·) (h.1 γ g),
    fun u hu => by rw [map_smul, h.2.1 u hu],
    fun m hm => by rw [map_smul, h.2.2 m hm, smul_comm]⟩

private theorem cmp_rTensor {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : Module.End ℂ W) (i : Fin d)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor (Fin d → ℂ) m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

theorem UpperTheory.V.Cj.H.levLin :
    UpperTheory.V.Cj.H.LevLin := by
  intro E _ _ _ a U Ξ q
  have ap : ∀ (α β : Co Ξ q) (s t : ℂ) X, (s • α + t • β) X = s • α X + t • β X := fun _ _ _ _ _ => rfl
  refine ⟨fun α β s t hα hβ => ⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, fun α β s t => ?_,
    fun α hα X i => ?_, fun T α X i => ?_⟩
  · rw [ap, ap, hα.equiv k X, hβ.equiv k X, map_add (f := _), map_smul, map_smul]
  · rw [ap, hα.basic X i hi, hβ.basic X i hi, smul_zero, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hα.val X)) (Submodule.smul_mem _ _ (hβ.val X))
  · refine AlternatingMap.ext fun X => ?_
    have e : (s • dCo (smLie Ξ) α + t • dCo (smLie Ξ) β) X = s • dCo (smLie Ξ) α X + t • dCo (smLie Ξ) β X := rfl
    rw [e, dCo_apply, dCo_apply, dCo_apply]
    simp only [ap, map_add (f := _), map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · exact mem_tens.1 (span_le_tens (N := levFnSub U Ξ) (fun φ h => h) (hα.val X)) i
  · rw [app_apply, cmp_rTensor]
end
