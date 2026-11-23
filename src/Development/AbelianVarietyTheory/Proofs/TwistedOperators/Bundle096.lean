module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Matrix

variable {p q : ℕ}

def vecM (V : Mat p q) : Ix p q × Ix p q → ℂ := fun ab => V ab.1 ab.2

def sAd (Y V : Mat p q) : Mat p q := Matrix.of fun a b => (sinhcAd Y *ᵥ vecM V) (a, b)

def pY (B : Fin p → Fin q → ℂ) : Mat p q := pOf (Matrix.of B)

theorem pY_add (B C : Fin p → Fin q → ℂ) : pY (B + C) = pY B + pY C := by
  ext (i | i) (j | j) <;> simp [pY, pOf]

theorem pY_smul (t : ℝ) (B : Fin p → Fin q → ℂ) : pY (t • B) = t • pY B := by
  ext (i | i) (j | j) <;> simp [pY, pOf, Complex.real_smul, mul_comm]

theorem continuous_pY : Continuous (pY : (Fin p → Fin q → ℂ) → Mat p q) := by
  show Continuous fun B : Fin p → Fin q → ℂ => Matrix.fromBlocks 0 (Matrix.of B) (Matrix.of B)ᴴ 0
  refine continuous_pi fun a => continuous_pi fun b => ?_
  rcases a with a | a <;> rcases b with b | b <;> simp <;> fun_prop

theorem sAd_add (Y V W : Mat p q) : sAd Y (V + W) = sAd Y V + sAd Y W := by
  have h : vecM (V + W) = vecM V + vecM W := rfl
  ext a b
  simp [sAd, h, Matrix.mulVec_add]

theorem sAd_smul_real (Y V : Mat p q) (t : ℝ) : sAd Y (t • V) = t • sAd Y V := by
  have h : vecM (t • V) = (t : ℂ) • vecM V := by
    funext ab
    simp [vecM, Complex.real_smul]
  ext a b
  simp [sAd, h, Matrix.mulVec_smul, Complex.real_smul]

def sP (Y : Mat p q) : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ) where
  toFun B := fun i j => sAd Y (pY B) (Sum.inl i) (Sum.inr j)
  map_add' B C := by funext i j; simp [pY_add, sAd_add]
  map_smul' t B := by funext i j; simp [pY_smul, sAd_smul_real]

theorem adMat_mulVec (Y V : Mat p q) : adMat Y *ᵥ vecM V = vecM (Y * V - V * Y) := by
  funext ⟨a, b⟩
  have h1 : (Matrix.kroneckerMap (· * ·) Y (1 : Mat p q) *ᵥ vecM V) (a, b) = (Y * V) a b := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply,
      vecM, mul_ite, ite_mul]
  have h2 : (Matrix.kroneckerMap (· * ·) (1 : Mat p q) Yᵀ *ᵥ vecM V) (a, b) = (V * Y) a b := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type_right, Matrix.one_apply, Matrix.mul_apply,
      vecM, mul_ite, mul_comm]
  simp only [adMat, Matrix.sub_mulVec, Pi.sub_apply, h1, h2, vecM, Matrix.sub_apply]

theorem pY_conjTranspose (B : Fin p → Fin q → ℂ) : (pY B)ᴴ = pY B := by
  simp [pY, pOf, Matrix.fromBlocks_conjTranspose]

theorem pY_mem (B : Fin p → Fin q → ℂ) : pY B ∈ pR p q := by
  show pY B ∈ upq p q ∧ IsPC (pY B)
  refine ⟨?_, ?_⟩
  · show (pY B)ᴴ * Jm p q + Jm p q * pY B = 0
    rw [pY_conjTranspose]
    simp [pY, pOf, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · intro a b h
    rcases a with a | a <;> rcases b with b | b <;> simp_all [pY, pOf, sameBlock]

theorem exists_pY {Y : Mat p q} (hY : Y ∈ pR p q) : ∃ B, Y = pY B := by
  have hY' : Y ∈ upq p q ∧ IsPC Y := hY
  obtain ⟨hu, hP⟩ := hY'
  have hu' : Yᴴ * Jm p q + Jm p q * Y = 0 := hu
  refine ⟨Y.toBlocks₁₂, ?_⟩
  ext (i | i) (j | j)
  · simpa [pY, pOf] using hP (Sum.inl i) (Sum.inl j) (by simp [sameBlock])
  · rfl
  · have h := congrFun (congrFun hu' (Sum.inr i)) (Sum.inl j)
    simp [Matrix.mul_apply, Jm, Formalism.UG.Jpq, Fintype.sum_sum_type, Matrix.one_apply, mul_ite,
      ite_mul] at h
    rw [starRingEnd_apply] at h
    show Y (Sum.inr i) (Sum.inl j) = star (Y (Sum.inl j) (Sum.inr i))
    linear_combination -h
  · simpa [pY, pOf] using hP (Sum.inr i) (Sum.inr j) (by simp [sameBlock])

def posIx : Ix p q → ℕ := Sum.elim (fun i => i.val) (fun j => j.val)

def cutH (p q : ℕ) (h : ℕ → ℝ) (n : ℕ) : ℝ := if n < min p q then h n else 0

def rootP (h : ℕ → ℝ) (ab : Ix p q × Ix p q) : ℝ :=
  if ab.1.isLeft then cutH p q h (posIx ab.1) - cutH p q h (posIx ab.2)
  else cutH p q h (posIx ab.1) + cutH p q h (posIx ab.2)

def eigP (ab cd : Ix p q × Ix p q) : ℂ :=
  if cd = ab then 1
  else if ¬ sameBlock cd.1 cd.2 ∧ posIx cd.1 = posIx ab.1 ∧ posIx cd.2 = posIx ab.2 then
    (if ab.1.isLeft then 1 else -1)
  else 0

theorem eigenvectorMatrix_eq_zero_of_sameBlock (ab : PIx p q) (cd : Ix p q × Ix p q) (h : sameBlock cd.1 cd.2) :
    eigP ab.1 cd = 0 := by
  have hne : cd ≠ ab.1 := by
    rintro rfl
    exact ab.2 h
  simp [eigP, hne, h]

def matG (T : GrpData p q) (x : T.G) : Mat p q := ((T.cov x : GL (Ix p q) ℂ) : Mat p q)

theorem matG_mul (T : GrpData p q) (x y : T.G) : matG T (x * y) = matG T x * matG T y := by
  simp only [matG, map_mul, Units.val_mul]

theorem matG_expt (T : GrpData p q) (B : Fin p → Fin q → ℂ) :
    matG T (T.expt (pY B)) = NormedSpace.exp (pY B) := by
  exact T.expt_cov (pY B) (show pY B ∈ upq p q ∧ IsPC (pY B) from pY_mem B).1

theorem continuous_expt_pY (T : GrpData p q) :
    Continuous fun B : Fin p → Fin q → ℂ => T.expt (pY B) := by
  exact T.expt_cont.comp_continuous continuous_pY
    (fun B => (show pY B ∈ upq p q ∧ IsPC (pY B) from pY_mem B).1)

theorem continuous_matG (T : GrpData p q) : Continuous (matG T) := by
  show Continuous fun x => ((T.cov x : GL (Ix p q) ℂ) : Mat p q)
  exact Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)

theorem matG_J (T : GrpData p q) (x : T.G) : (matG T x)ᴴ * Jm p q * matG T x = Jm p q := by
  have h : Formalism.UG.cT (starRingEnd ℂ) (matG T x) * Formalism.UG.Jpq p q * matG T x = Formalism.UG.Jpq p q :=
    T.cov_mem x
  have hc : Formalism.UG.cT (starRingEnd ℂ) (matG T x) = (matG T x)ᴴ := by
    ext i j
    simp [Formalism.UG.cT]
  rw [hc] at h
  exact h

theorem matG_one (T : GrpData p q) : matG T 1 = 1 := by
  simp [matG]

theorem matG_inv (T : GrpData p q) (x : T.G) :
    matG T x⁻¹ = (((T.cov x)⁻¹ : GL (Ix p q) ℂ) : Mat p q) := by
  simp only [matG, map_inv]

theorem exists_blocks (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      matG T k = Matrix.fromBlocks U 0 0 V := by
  have hK : IsKC (matG T k) := hk
  have h12 : (matG T k).toBlocks₁₂ = 0 := by
    ext i j
    exact hK (Sum.inl i) (Sum.inr j) (by simp [sameBlock])
  have h21 : (matG T k).toBlocks₂₁ = 0 := by
    ext i j
    exact hK (Sum.inr i) (Sum.inl j) (by simp [sameBlock])
  have hMe : matG T k = Matrix.fromBlocks (matG T k).toBlocks₁₁ 0 0 (matG T k).toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (matG T k)]
    rw [h12, h21]
  have hJ := matG_J T k
  rw [hMe] at hJ
  generalize (matG T k).toBlocks₁₁ = A at hJ hMe
  generalize (matG T k).toBlocks₂₂ = D at hJ hMe
  simp only [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hJ
  simp [Matrix.fromBlocks_inj] at hJ
  obtain ⟨hA, hD⟩ := hJ
  refine ⟨A, ?_, D, ?_, hMe⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hA
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hD

theorem matG_star_mul (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    (matG T k)ᴴ * matG T k = 1 := by
  obtain ⟨U, hU, V, hV, h⟩ := exists_blocks T hk
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU hV
  rw [h, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hU, hV]

theorem matG_inv_of_mem (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    matG T k⁻¹ = (matG T k)ᴴ := by
  rw [matG_inv]
  exact Units.inv_eq_of_mul_eq_one_left (matG_star_mul T hk)

def Ksub (T : GrpData p q) : Subgroup T.G where
  carrier := T.Kset
  one_mem' := by
    show IsKC (matG T 1)
    rw [matG_one]; intro a b h
    have : a ≠ b := by rintro rfl; cases a <;> simp [sameBlock] at h
    simp [Matrix.one_apply, this]
  mul_mem' := by
    intro x y hx hy
    obtain ⟨U, -, V, -, h⟩ := exists_blocks T hx
    obtain ⟨U', -, V', -, h'⟩ := exists_blocks T hy
    show IsKC (matG T (x * y))
    rw [matG_mul, h, h', Matrix.fromBlocks_multiply]
    intro a b hab
    cases a <;> cases b <;> simp_all [sameBlock]
  inv_mem' := by
    intro x hx
    show IsKC (matG T x⁻¹)
    rw [matG_inv_of_mem T hx]
    have hx' : IsKC (matG T x) := hx
    intro a b hab
    have : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [hx' b a this]

end GlobalTheory.PolarU
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.InvFormUnique

theorem inner_eq_of_common_kernel_line {V H₁ H₂ ι : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : V →ₗ[ℂ] H₁) (j₂ : V →ₗ[ℂ] H₂) (A A' : ι → Module.End ℂ V) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (hA : ∀ i, ∀ w ∈ W, A i w ∈ W) (hA' : ∀ i, ∀ w ∈ W, A' i w ∈ W)
    (h₁ : ∀ i x y, inner ℂ (j₁ (A i x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (A' i y)))
    (h₂ : ∀ i x y, inner ℂ (j₂ (A i x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (A' i y)))
    (hinj : Function.Injective j₂) (v : V) (hv : ∀ i, A i v = 0)
    (hline : ∀ h, (∀ i, A i h = 0) → ∃ c : ℂ, c • v = h)
    (hn : inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v)) (y : V) (hy : y ∈ W) :
    inner ℂ (j₁ v) (j₁ y) = inner ℂ (j₂ v) (j₂ y) := by
  classical

  let f : W →ₗ[ℂ] H₂ := j₂ ∘ₗ W.subtype
  have hfi : Function.Injective f := hinj.comp Subtype.val_injective
  let e : W ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hfi
  let ψ : V →ₗ[ℂ] ℂ := (innerₛₗ ℂ (j₁ v)) ∘ₗ j₁ - (innerₛₗ ℂ (j₂ v)) ∘ₗ j₂
  have hψ : ∀ x, ψ x = inner ℂ (j₁ v) (j₁ x) - inner ℂ (j₂ v) (j₂ x) := fun x => by
    simp [ψ]
  let g : LinearMap.range f →ₗ[ℂ] ℂ := ψ ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap

  obtain ⟨u, huW, hrep⟩ : ∃ u ∈ W, ∀ z ∈ W, inner ℂ (j₂ u) (j₂ z) = ψ z := by
    let u' := (InnerProductSpace.toDual ℂ (LinearMap.range f)).symm (LinearMap.toContinuousLinearMap g)
    have key : ∀ s : LinearMap.range f, inner ℂ (u' : H₂) (s : H₂) = g s := by
      intro s
      rw [← Submodule.coe_inner]
      exact InnerProductSpace.toDual_symm_apply
    refine ⟨(e.symm u' : V), (e.symm u').2, fun z hz => ?_⟩
    have h1 := key (e ⟨z, hz⟩)
    have h2 : ((e ⟨z, hz⟩ : LinearMap.range f) : H₂) = j₂ z := LinearEquiv.ofInjective_apply _ _
    have h3 : ((u' : LinearMap.range f) : H₂) = j₂ (e.symm u' : V) := by
      conv_lhs => rw [← e.apply_symm_apply u']
      exact LinearEquiv.ofInjective_apply _ _
    rw [h2, h3] at h1
    rw [h1]
    simp [g]

  have hker : ∀ i, A i u = 0 := by
    intro i
    have horth : ∀ z ∈ W, inner ℂ (j₂ (A i u)) (j₂ z) = 0 := by
      intro z hz
      rw [h₂, hrep _ (hA' i z hz), hψ, ← h₁, ← h₂, hv]
      simp
    have h0 := horth _ (hA i u huW)
    rw [inner_self_eq_zero] at h0
    exact hinj (by rw [h0, map_zero])

  obtain ⟨c, hc⟩ := hline u hker
  have hψv : ψ v = 0 := by rw [hψ, hn, sub_self]
  have hψu : ψ u = 0 := by rw [← hc, map_smul, hψv, smul_zero]
  have hj : j₂ u = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), hrep u huW, hψu]
  have hy' := hrep y hy
  rw [hj, inner_zero_left, hψ] at hy'
  exact sub_eq_zero.mp hy'.symm

theorem adjZ_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : adjZ (Eab a b) = Eab b a := by
  unfold adjZ Eab Jm Formalism.UG.Jpq

  have hJ : (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1) : Mat p q) =
      Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, apply_ite]
  rw [hJ]
  rcases a with a | a <;> rcases b with b | b
  all_goals try exact (h : False).elim
  all_goals
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.single_apply]
    split_ifs with h1 h2 <;> (try obtain ⟨rfl, rfl⟩ := h1) <;> simp_all

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  unfold IsKC Eab
  intro c d hcd
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd h

theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b ∧ sameBlock b a := by
  rcases a with i | i <;> rcases b with j | j
  all_goals first
    | exact ⟨True.intro, True.intro⟩
    | exact (h : False).elim

theorem sameBlock_refl {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> exact True.intro

private theorem mem_hwSub_iff' {p q : ℕ} {V0 : Type} [AddCommGroup V0] [Module ℂ V0]
    (f : Mat p q →ₗ[ℂ] Module.End ℂ V0) (μ : Ix p q → ℚ) (z : V0) :
    z ∈ hwSub f μ ↔ (∀ a, f (Eab a a) z = (μ a : ℂ) • z) ∧ ∀ a b, posC a b → f (Eab a b) z = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem inner_eq_of_irreducible (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : M.V →ₗ[ℂ] H₁) (j₂ : M.V →ₗ[ℂ] H₂)
    (h₁ : ∀ Z x y, inner ℂ (j₁ (M.act Z x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (M.act (adjZ Z) y)))
    (h₂ : ∀ Z x y, inner ℂ (j₂ (M.act Z x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (M.act (adjZ Z) y)))
    (hinj : Function.Injective j₂) (hirr : IrrGK M) (μ : Ix p q → ℚ) (v : M.V) (hv : IsHW M.act μ v)
    (hdim : Module.finrank ℂ ↥(hwSub M.act μ) = 1)
    (hn : inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v)) (x y : M.V) :
    inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y) := by
  classical

  let N : Submodule ℂ M.V :=
    { carrier := {z | ∀ w, inner ℂ (j₁ z) (j₁ w) = inner ℂ (j₂ z) (j₂ w)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        intro w
        rw [map_add (f := _), map_add (f := _), inner_add_left, inner_add_left, ha, hb]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, inner_zero_left, implies_true]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        intro w
        rw [map_smul, map_smul, inner_smul_left, inner_smul_left, ha] }
  have hmemN : ∀ z, z ∈ N ↔ ∀ w, inner ℂ (j₁ z) (j₁ w) = inner ℂ (j₂ z) (j₂ w) := fun z => Iff.rfl

  have hNinv : ∀ Z, ∀ z ∈ N, M.act Z z ∈ N := by
    intro Z z hz
    rw [hmemN] at hz ⊢
    intro w
    rw [h₁, h₂, hz]
  obtain ⟨hv0, hvmem⟩ : v ≠ 0 ∧ v ∈ hwSub M.act μ := hv
  have hmem := (mem_hwSub_iff' M.act μ v).mp hvmem

  let A : ({ab : Ix p q × Ix p q // posC ab.1 ab.2} ⊕ Ix p q) → Module.End ℂ M.V :=
    Sum.elim (fun ab => M.act (Eab ab.1.1 ab.1.2)) (fun c => M.act (Eab c c) - (μ c : ℂ) • LinearMap.id)
  let A' : ({ab : Ix p q × Ix p q // posC ab.1 ab.2} ⊕ Ix p q) → Module.End ℂ M.V :=
    Sum.elim (fun ab => M.act (Eab ab.1.2 ab.1.1)) (fun c => M.act (Eab c c) - (μ c : ℂ) • LinearMap.id)
  have hh : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M.V →ₗ[ℂ] H),
      (∀ Z z w, inner ℂ (j (M.act Z z)) (j w) = inner ℂ (j z) (j (M.act (adjZ Z) w))) →
      ∀ i z w, inner ℂ (j (A i z)) (j w) = inner ℂ (j z) (j (A' i w)) := by
    intro H _ _ j hj
    rintro (⟨⟨a, b⟩, hab⟩ | c) z w
    · simp only [A, A', Sum.elim_inl]
      rw [hj, adjZ_Eab (sameBlock_of_posC hab).1]
    · simp only [A, A', Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
      rw [hj, adjZ_Eab (sameBlock_refl c)]
      all_goals simp
  have hAv : ∀ i, A i v = 0 := by
    rintro (⟨⟨a, b⟩, hab⟩ | c)
    · exact hmem.2 a b hab
    · simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hmem.1 c, sub_self]
  have hline : ∀ z, (∀ i, A i z = 0) → ∃ c : ℂ, c • v = z := by
    intro z hz0
    have hzmem : z ∈ hwSub M.act μ := by
      rw [mem_hwSub_iff']
      refine ⟨fun c => ?_, fun a b hab => hz0 (Sum.inl ⟨(a, b), hab⟩)⟩
      have hc0 := hz0 (Sum.inr c)
      simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hc0
      exact hc0
    have hne : (⟨v, hvmem⟩ : hwSub M.act μ) ≠ 0 := by
      rwa [Ne, Submodule.mk_eq_zero]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨z, hzmem⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩

  have hvN : v ∈ N := by
    rw [hmemN]
    intro w
    obtain ⟨W, hWfin, hwW, hWst⟩ := M.kfin w
    have := hWfin
    have hWst' : ∀ Z, IsKC Z → ∀ u ∈ W, M.act Z u ∈ W := hWst
    have hAW : ∀ i, ∀ u ∈ W, A i u ∈ W := by
      rintro (⟨⟨a, b⟩, hab⟩ | c) u hu
      · exact hWst' _ (isKC_Eab (sameBlock_of_posC hab).1) u hu
      · simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        exact W.sub_mem (hWst' _ (isKC_Eab (sameBlock_refl c)) u hu) (W.smul_mem _ hu)
    have hA'W : ∀ i, ∀ u ∈ W, A' i u ∈ W := by
      rintro (⟨⟨a, b⟩, hab⟩ | c) u hu
      · exact hWst' _ (isKC_Eab (sameBlock_of_posC hab).2) u hu
      · simp only [A', Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        exact W.sub_mem (hWst' _ (isKC_Eab (sameBlock_refl c)) u hu) (W.smul_mem _ hu)
    exact inner_eq_of_common_kernel_line j₁ j₂ A A' W hAW hA'W (hh H₁ j₁ h₁) (hh H₂ j₂ h₂) hinj v hAv
      hline hn w hwW

  obtain ⟨-, hirr2⟩ := hirr
  rcases hirr2 N hNinv with hN | hN
  · exact absurd ((Submodule.mem_bot ℂ).mp (hN ▸ hvN)) hv0
  · have hx : x ∈ N := by rw [hN]; exact Submodule.mem_top
    exact (hmemN x).mp hx y

end GlobalTheory.InvFormUnique
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.InducedPBW

def SymbolCongr {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Prop :=
  ∀ (l : List (Mat p q)) (v : V),
    (indRel act).mkQ (TensorProduct.tmul ℂ (l.map (ugι p q)).prod v) -
      (indRel act).mkQ (TensorProduct.tmul ℂ (symU p q (l.map pLin).prod) v) ∈ indFlt act l.length

end GlobalTheory.InducedPBW
end
end

end

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.inner_eq_of_irrGK_of_inner_hw_eq : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j₁ : M.V →ₗ[ℂ] H₁) (j₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j₁ (M.act Z x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (j₂ (M.act Z x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (M.act (adjZ Z) y))) → Function.Injective j₂ → IrrGK M → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → Module.finrank ℂ ↥(hwSub M.act μ) = 1 → inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v) → ∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y) := by
  first | exact @GlobalTheory.InvFormUnique.inner_eq_of_irreducible | exact GlobalTheory.InvFormUnique.inner_eq_of_irreducible | (intros; apply GlobalTheory.InvFormUnique.inner_eq_of_irreducible <;> assumption)

end
end
