module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private def outL {n : ℕ} (w : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun u := vecMulVec u w
  map_add' u u' := by ext; simp [vecMulVec_apply, add_mul]
  map_smul' c u := by ext; simp [vecMulVec_apply, mul_assoc]

private theorem eps_left_mul_eq_det_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : (Π _ : Fin n, Matrix (Fin n) (Fin n) ℂ) →ₘₗ[ℂ] M) (g : Matrix (Fin n) (Fin n) ℂ) :
    eps (fun x => μ fun i => g * x i) = g.det • eps μ := by
  have hs : ∀ a b : Fin n, g * single a b (1 : ℂ) = ∑ c, g c a • single c b (1 : ℂ) := by
    intro a b
    ext i j
    by_cases hbj : b = j <;> simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, hbj]
  have hdet : ∀ c : Fin n → Fin n, ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, g (c k) (σ k) = (g.submatrix c id).det := by
    intro c
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  have hsum : ∀ w : (Fin n → Fin n) → M, ∑ c, (g.submatrix c id).det • w c =
      ∑ α : Equiv.Perm (Fin n), (((Equiv.Perm.sign α : ℤ) : ℂ) * g.det) • w α := by
    intro w
    rw [← Finset.sum_subset (Finset.subset_univ
      (Finset.univ.image (fun α : Equiv.Perm (Fin n) => (⇑α : Fin n → Fin n))))]
    · rw [Finset.sum_image (fun α _ β _ h => Equiv.coe_fn_injective h)]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Matrix.det_permute]
    · intro c _ hc
      have hni : ¬ Function.Injective c := by
        intro hinj
        apply hc
        exact Finset.mem_image.mpr
          ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
      simp only [Function.Injective, not_forall] at hni
      obtain ⟨i, j, hij, hne⟩ := hni
      rw [Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]), zero_smul]
  simp only [eps, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hμ : ∀ σ : Equiv.Perm (Fin n), μ (fun i => g * units σ τ i) =
      ∑ c : Fin n → Fin n, (∏ k, g (c k) (σ k)) • μ (fun k => single (c k) (τ k) (1 : ℂ)) := by
    intro σ
    simp only [units, hs]

    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply]
  have hc : ∀ c : Fin n → Fin n, ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) • (∏ k, g (c k) (σ k)) •
        μ (fun k => single (c k) (τ k) (1 : ℂ)) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) • ((g.submatrix c id).det • μ (fun k => single (c k) (τ k) (1 : ℂ))) := by
    intro c
    simp only [← Int.cast_smul_eq_zsmul ℂ, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [← hdet c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    push_cast
    ring
  simp only [hμ, Finset.smul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun c _ => hc c, ← Finset.smul_sum, hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 1
  push_cast
  ring

theorem UpperTheory.V.AlgRepEndIrreducible.epsGrp :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (μ : (Π _ : Fin n, Matrix (Fin n) (Fin n) ℂ) →ₘₗ[ℂ] M) (g g' : Matrix (Fin n) (Fin n) ℂ), g' * g = 1 →
      eps (fun x => μ fun i => g * x i * g') = eps μ := by
  intro M _ _ n μ g g' h
  have hT : ∀ ν : (Fin n → Matrix (Fin n) (Fin n) ℂ) → M, eps (fun x => ν fun i => (x i)ᵀ) = eps ν := by
    intro ν
    simp only [eps, units, Matrix.transpose_single]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_comm]
    rfl
  have e1 : eps (fun x => μ fun i => g * x i * g') = g.det • eps (fun x => μ fun i => x i * g') :=
    eps_left_mul_eq_det_smul (μ.compLinearMap (fun _ => LinearMap.mulRight ℂ g')) g
  have e2 : eps (fun x => μ fun i => (g'ᵀ * x i)ᵀ) = g'ᵀ.det • eps (fun x => μ fun i => (x i)ᵀ) :=
    eps_left_mul_eq_det_smul (μ.compLinearMap
      (fun _ => (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap)) g'ᵀ
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.det_transpose, hT] at e2
  have e3 : eps (fun x => μ fun i => x i * g') = g'.det • eps μ := by
    rw [← hT (fun x => μ fun i => x i * g')]
    exact e2
  rw [e1, e3, smul_smul, mul_comm, ← Matrix.det_mul, h, Matrix.det_one, one_smul]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

namespace UpperTheory.V.AlgRepEndIrreducible

open GlobalTheory.WignerGL

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {A : Type} [Ring A] [Algebra ℂ A] [Module ℝ A]


omit [Algebra ℂ A] in
private noncomputable def sL (L : Lie E a →ₗ[ℝ] A) (i j : Fin a) : Cinf E →ₗ[ℝ] A where
  toFun x := L (toL (Matrix.single i j x))
  map_add' x y := by
    have h : toL (Matrix.single i j (x + y)) = toL (Matrix.single i j x) + toL (Matrix.single i j y) :=
      congrArg toL (Matrix.single_add i j x y)
    exact (congrArg L h).trans (L.map_add _ _)
  map_smul' c x := by
    have h : toL (Matrix.single i j (c • x)) = c • toL (Matrix.single i j x) :=
      congrArg toL (Matrix.smul_single c i j x).symm
    exact (congrArg L h).trans (L.map_smul _ _)

omit [Algebra ℂ A] in
private theorem sL_apply (L : Lie E a →ₗ[ℝ] A) (i j : Fin a) (x : Cinf E) :
    sL L i j x = L (toL (Matrix.single i j x)) := rfl

omit [Algebra ℂ A] in
private theorem sL_comm (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L) (i j k l : Fin a) (x y : Cinf E) :
    sL L i j x * sL L k l y - sL L k l y * sL L i j x =
      (if j = k then sL L i l (x * y) else 0) - (if l = i then sL L k j (x * y) else 0) := by
  have h := hL (Matrix.single i j x) (Matrix.single k l y)
  have e : ∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), toL (X - Y) = toL X - toL Y := fun _ _ => rfl
  rw [e, map_sub] at h
  simp only [sL_apply]
  rw [h]
  have z : L (toL 0) = 0 := map_zero _
  congr 1
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, mul_comm y]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]

private theorem eL_comm_aux (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L) (τ τ' : E →+* ℂ) (i j k l : Fin a) :
    eL L τ i j * eL L τ' k l - eL L τ' k l * eL L τ i j =
      (if j = k then (1 / 4 : ℂ) • (sL L i l (atEmb τ 1 * atEmb τ' 1) - sL L i l (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (sL L i l (atEmb τ 1 * atEmb τ' .I) + sL L i l (atEmb τ .I * atEmb τ' 1))) else 0) -
      (if l = i then (1 / 4 : ℂ) • (sL L k j (atEmb τ 1 * atEmb τ' 1) - sL L k j (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (sL L k j (atEmb τ 1 * atEmb τ' .I) + sL L k j (atEmb τ .I * atEmb τ' 1))) else 0) := by
  have h1 := sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' 1)
  have h2 := sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' .I)
  have h3 := sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' 1)
  have h4 := sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' .I)
  simp only [eL, ← sL_apply, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  split_ifs at h1 h2 h3 h4 ⊢ <;>
    linear_combination (norm := skip) (exp := 1) (1 / 4 : ℂ) • h1 - (Complex.I / 4 : ℂ) • h2 - (Complex.I / 4 : ℂ) • h3 - (1 / 4 : ℂ) • h4 <;>
    match_scalars <;> ring_nf <;> simp

end

end UpperTheory.V.AlgRepEndIrreducible

open GlobalTheory.WignerGL in
theorem UpperTheory.V.AlgRepEndIrreducible.eLRel :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Module ℝ A] [IsScalarTower ℝ ℂ A] (L : Lie E a →ₗ[ℝ] A),
      IsLieHom L → IsMultiGl (eL L) := by
  intro E _ _ _ a A _ _ _ _ L hL
  refine ⟨fun τ i j k l => ?_, fun τ τ' h i j k l => ?_⟩
  · have e : atEmb τ (Complex.I * Complex.I) = -atEmb τ 1 := by
      rw [atEmb_eq]; simp
    rw [eL_comm_aux L hL]
    simp only [atEmb_mul, one_mul, mul_one, e, map_neg, eL, ← sL_apply]
    congr 1 <;> split_ifs <;> first | rfl | (match_scalars <;> ring)
  · rw [← sub_eq_zero, eL_comm_aux L hL]
    by_cases hw : InfinitePlace.mk τ = InfinitePlace.mk τ'
    · obtain rfl : ComplexEmbedding.conjugate τ = τ' := (InfinitePlace.mk_eq_iff.1 hw).resolve_left h
      have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
        rw [atEmb_eq]; simp
      have e' : atEmb τ (-1) = -atEmb τ 1 := by
        rw [atEmb_eq]; simp
      simp [atEmb_conj, atEmb_mul, e, e']
    · simp [atEmb_mul_of_ne hw]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.homId :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M),
      dCo L ω = 0 → InfEq L ω → ∀ (X : Matrix (Fin a) (Fin a) (Cinf E)) (Y : Fin (q + 1) → Herm E a),
        ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • (L (toL (Y i).1) (ω (Matrix.vecCons (hp (toL X)) (i.removeNth Y))) -
          ω (Matrix.vecCons (hp (toL ((Y i).1 * X - X * (Y i).1))) (i.removeNth Y))) = L (toL X) (ω Y) := by
  intro E _ _ _ a M _ _ _ _ L q ω hd hinf X Y
  let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
  have hZ : star Z = -Z := by
    simp only [Z]
    rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
  have hX : toL X = toL (hp (toL X)).1 + toL Z := by
    have h : X = (hp (toL X)).1 + Z := by
      rw [hp_val]; simp only [Z]; module
    exact congrArg toL h
  have hb : ∀ U : Herm E a, hp (toL (U.1 * X - X * U.1)) = -brH Z hZ U := by
    intro U
    apply Subtype.ext
    have h : star U.1 = U.1 := U.2
    rw [hp_val]
    change _ = -(Z * U.1 - U.1 * Z)
    simp only [Z, star_sub, star_mul, h, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub]
    module
  have h1 := dCo_cons (L := L) ω (hp (toL X)) Y
  rw [hd, AlternatingMap.zero_apply, eq_comm, sub_eq_zero, dCo_apply] at h1
  rw [congrArg L hX, map_add (f := _), LinearMap.add_apply, h1, hinf Z hZ Y, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ω (Matrix.vecCons (-brH Z hZ (Y i)) (i.removeNth Y)) =
      -ω (Matrix.vecCons (brH Z hZ (Y i)) (i.removeNth Y)) := by
    rw [← AlternatingMap.curryLeft_apply_apply, ← AlternatingMap.curryLeft_apply_apply, map_neg,
      AlternatingMap.neg_apply]
  rw [hb, h2, sub_neg_eq_add, smul_add, ← Fin.insertNth_removeNth, AlternatingMap.map_insertNth,
    AlternatingMap.curryLeft_apply_apply]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rpML {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ)
    (b : Fin n → X →ₗ[ℂ] Module.End ℂ M) :
    ∃ R : (Fin n → X) →ₘₗ[ℂ] Module.End ℂ M, ∀ x, R x = rp n b x := by
  induction n with
  | zero => exact ⟨MultilinearMap.constOfIsEmpty (RingHom.id ℂ) _ 1, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih (Fin.tail b)
    let g : X →ₗ[ℂ] (Fin n → X) →ₘₗ[ℂ] Module.End ℂ M :=
      { toFun := fun x0 => (LinearMap.mulRight ℂ (b 0 x0)).compMultilinearMap R
        map_add' := fun u v => MultilinearMap.ext fun y => by simp [mul_add]
        map_smul' := fun c u => MultilinearMap.ext fun y => by simp }
    refine ⟨LinearMap.uncurryLeft (M := fun _ : Fin (n + 1) => X) g, fun x => ?_⟩
    rw [rp_succ, ← hR]
    rfl

theorem UpperTheory.V.AlgRepEndIrreducible.telML :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M),
      ∃ T : (X →ₗ[ℂ] M) →ₗ[ℂ] (Fin n → X) →ₘₗ[ℂ] M, ∀ f x, T f x = tel n a b f x := by
  intro X M _ _ _ _ n a b
  induction n with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih (Fin.tail a) (Fin.tail b)
    obtain ⟨R, hR⟩ := rpML n (Fin.tail b)
    let g : (X →ₗ[ℂ] M) → X →ₗ[ℂ] (Fin n → X) →ₘₗ[ℂ] M := fun f =>
      { toFun := fun x0 => (a 0 x0).compMultilinearMap (T f) +
          (LinearMap.applyₗ (f x0) : Module.End ℂ M →ₗ[ℂ] M).compMultilinearMap R
        map_add' := fun u v => MultilinearMap.ext fun y => by simp; abel
        map_smul' := fun c u => MultilinearMap.ext fun y => by simp }
    have hg : ∀ (f : X →ₗ[ℂ] M) (x : Fin (n + 1) → X),
        LinearMap.uncurryLeft (σ := RingHom.id ℂ) (M := fun _ : Fin (n + 1) => X) (g f) x =
        a 0 (x 0) (T f (Fin.tail x)) + R (Fin.tail x) (f (x 0)) := by
      intro f x
      rfl
    refine ⟨{ toFun := fun f => LinearMap.uncurryLeft (M := fun _ : Fin (n + 1) => X) (g f)
              map_add' := fun u v => MultilinearMap.ext fun y => ?_
              map_smul' := fun c u => MultilinearMap.ext fun y => ?_ }, fun f x => ?_⟩
    · simp only [add_apply, hg, map_add (f := _), LinearMap.add_apply]
      abel
    · simp only [smul_apply, hg, map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_add]
    · rw [tel_succ, ← hT, ← hR]
      exact hg f x
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem update_swap_mul_eq_update {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : Fin n} (hab : a ≠ b) :
    Function.update (⇑(Equiv.swap a b * σ)) ((Equiv.swap a b * σ).symm b) a
      = Function.update (⇑σ) (σ.symm b) a := by
  have e : (Equiv.swap a b * σ).symm b = σ.symm a := by
    simp [Equiv.Perm.mul_def, Equiv.swap_apply_right]
  rw [e]
  funext j
  simp only [Function.update_apply, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.eq_symm_apply]
  by_cases h1 : σ j = a
  · have h2 : σ j ≠ b := h1 ▸ hab
    simp [h1, hab]
  · by_cases h2 : σ j = b
    · simp [h1, h2, Equiv.swap_apply_right]
    · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

private theorem sum_sign_smul_update_eq_ite {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (h : (Fin n → Fin n) → M) (a b : Fin n) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a)
      = if a = b then ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h ⇑σ else 0 := by
  split_ifs with hab
  · subst hab
    refine Finset.sum_congr rfl fun σ _ => ?_
    have := Function.update_eq_self (σ.symm a) (⇑σ)
    simp only [Equiv.apply_symm_apply] at this
    rw [this]
  · have key : ∀ σ : Equiv.Perm (Fin n),
        (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a)
          = -((Equiv.Perm.sign (Equiv.mulLeft (Equiv.swap a b) σ) : ℤ) •
              h (Function.update (⇑(Equiv.mulLeft (Equiv.swap a b) σ))
                ((Equiv.mulLeft (Equiv.swap a b) σ).symm b) a)) := by
      intro σ
      simp only [Equiv.coe_mulLeft]
      rw [update_swap_mul_eq_update σ hab, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      simp
    set S := ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a) with hSdef
    have hS : S = -S := by
      conv_lhs => rw [hSdef, Finset.sum_congr rfl fun σ _ => key σ, Finset.sum_neg_distrib,
        Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))
          (fun τ => (Equiv.Perm.sign τ : ℤ) • h (Function.update (⇑τ) (τ.symm b) a))]
    have h2 : (2:ℂ) • S = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hS]
      exact add_neg_cancel S
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
private theorem update_single_first_index_eq {n : ℕ} (r c : Fin n → Fin n) (k a : Fin n) :
    Function.update (fun j => Matrix.single (r j) (c j) (1:ℂ)) k (Matrix.single a (c k) 1)
      = fun j => Matrix.single (Function.update r k a j) (c j) (1:ℂ) := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp
  · simp [hj]

private theorem update_single_col_eq {n : ℕ} (r c : Fin n → Fin n) (k a : Fin n) :
    Function.update (fun j => Matrix.single (r j) (c j) (1:ℂ)) k (Matrix.single (r k) a 1)
      = fun j => Matrix.single (r j) (Function.update c k a j) (1:ℂ) := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp
  · simp [hj]

private theorem mul_single_eq_sum_smul_single {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    y * Matrix.single p q (1:ℂ) = ∑ a, y a p • Matrix.single a q (1:ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

private theorem single_mul_eq_sum_smul_single {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    Matrix.single p q (1:ℂ) * y = ∑ c, y q c • Matrix.single p c (1:ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

private theorem sum_sign_left_mul_update_eq_trace_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) →ₘₗ[ℂ] M)
    (y : Matrix (Fin n) (Fin n) ℂ) (τ : Equiv.Perm (Fin n)) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k))
      = Matrix.trace y • ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • μ (units σ τ) := by
  set h : (Fin n → Fin n) → M := fun r => μ (fun j => Matrix.single (r j) (τ j) (1:ℂ)) with hh
  have inner : ∀ σ : Equiv.Perm (Fin n),
      ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k))
        = ∑ b, ∑ a, y a b • h (Function.update (⇑σ) (σ.symm b) a) := by
    intro σ
    have hu : units σ τ = fun j => Matrix.single (σ j) (τ j) (1:ℂ) := rfl
    rw [hu]
    simp_rw [mul_single_eq_sum_smul_single, MultilinearMap.map_update_sum, MultilinearMap.map_update_smul,
      update_single_first_index_eq]
    rw [← Equiv.sum_comp σ.symm]
    simp [hh]
  simp_rw [inner, Finset.smul_sum]
  rw [Finset.sum_comm]
  have step : ∀ b : Fin n, ∑ σ : Equiv.Perm (Fin n), ∑ a, (Equiv.Perm.sign σ : ℤ) •
      y a b • h (Function.update (⇑σ) (σ.symm b) a)
        = y b b • ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h ⇑σ := by
    intro b
    rw [Finset.sum_comm]
    simp_rw [smul_comm ((Equiv.Perm.sign _ : ℤ)) (y _ b), ← Finset.smul_sum, sum_sign_smul_update_eq_ite]
    simp
  rw [Finset.sum_congr rfl fun b _ => step b, ← Finset.sum_smul, ← Finset.smul_sum]
  rfl

private theorem sum_sign_right_mul_update_eq_trace_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) →ₘₗ[ℂ] M)
    (y : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) :
    ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) •
        ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y))
      = Matrix.trace y • ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • μ (units σ τ) := by
  set h : (Fin n → Fin n) → M := fun c => μ (fun j => Matrix.single (σ j) (c j) (1:ℂ)) with hh
  have inner : ∀ τ : Equiv.Perm (Fin n),
      ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y))
        = ∑ b, ∑ c, y b c • h (Function.update (⇑τ) (τ.symm b) c) := by
    intro τ
    have hu : units σ τ = fun j => Matrix.single (σ j) (τ j) (1:ℂ) := rfl
    rw [hu]
    simp_rw [single_mul_eq_sum_smul_single, MultilinearMap.map_update_sum, MultilinearMap.map_update_smul,
      update_single_col_eq]
    rw [← Equiv.sum_comp τ.symm]
    simp [hh]
  simp_rw [inner, Finset.smul_sum]
  rw [Finset.sum_comm]
  have step : ∀ b : Fin n, ∑ τ : Equiv.Perm (Fin n), ∑ c, (Equiv.Perm.sign τ : ℤ) •
      y b c • h (Function.update (⇑τ) (τ.symm b) c)
        = y b b • ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • h ⇑τ := by
    intro b
    rw [Finset.sum_comm]
    simp_rw [smul_comm ((Equiv.Perm.sign _ : ℤ)) (y b _), ← Finset.smul_sum, sum_sign_smul_update_eq_ite]
    simp
  rw [Finset.sum_congr rfl fun b _ => step b, ← Finset.sum_smul, ← Finset.smul_sum]
  rfl

theorem UpperTheory.V.AlgRepEndIrreducible.epsDer :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ)
      (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) →ₘₗ[ℂ] M) (y : Matrix (Fin n) (Fin n) ℂ),
      eps (fun x => ∑ k, μ (Function.update x k (y * x k - x k * y))) = 0 := by
  intro M _ _ n μ y
  show ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k - units σ τ k * y)) = 0
  simp_rw [MultilinearMap.map_update_sub, Finset.sum_sub_distrib, smul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have L : ∀ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k))
      = (Equiv.Perm.sign τ : ℤ) • (Matrix.trace y •
          ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • μ (units σ τ)) := by
    intro τ
    rw [← sum_sign_left_mul_update_eq_trace_smul, Finset.smul_sum]
    simp_rw [mul_smul]
  have R : ∀ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y))
      = (Equiv.Perm.sign σ : ℤ) • (Matrix.trace y •
          ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • μ (units σ τ)) := by
    intro σ
    rw [← sum_sign_right_mul_update_eq_trace_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_comm, mul_smul]
  rw [Finset.sum_congr rfl fun τ _ => L τ, Finset.sum_comm,
    Finset.sum_congr rfl fun σ _ => R σ]
  simp_rw [smul_comm _ (Matrix.trace y), ← Finset.smul_sum]
  congr 1
  simp_rw [Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [mul_comm]
end
