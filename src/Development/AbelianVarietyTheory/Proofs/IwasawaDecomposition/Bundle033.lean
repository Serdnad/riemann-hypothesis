module

import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle025
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
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
import ReciprocityTheory.DualLattices.Bundle001

@[expose] public section

section

namespace GlobalTheory.NonzeroSmulMem

open NumberField

theorem exists_ne_zero_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  apply Formalism.L2.SG.Pf.LatEx.exists_smul_mem_of_mem_span <;> assumption

end GlobalTheory.NonzeroSmulMem
end

section

open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HermFrame

open Filter

theorem del_del_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {u : E → ℂ} {z : E} (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    GlobalTheory.del (fun x => GlobalTheory.del u x w) z v = GlobalTheory.del (fun x => GlobalTheory.del u x v) z w := by
  have h := GlobalTheory.differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e : ∀ w, (fun x => GlobalTheory.del u x w) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ u x w - Complex.I • fderiv ℝ u x (Complex.I • w)) :=
    fun w => funext fun x => GlobalTheory.del_apply u x w
  have d : ∀ w, GlobalTheory.del (fun x => (1 / 2 : ℂ) • (fderiv ℝ u x w - Complex.I • fderiv ℝ u x (Complex.I • w))) z
      = (1 / 2 : ℂ) • (GlobalTheory.del (fun x => fderiv ℝ u x w) z
          - Complex.I • GlobalTheory.del (fun x => fderiv ℝ u x (Complex.I • w)) z) := fun w => by
    rw [GlobalTheory.del_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul Complex.I)),
      GlobalTheory.del_sub (h1 _) ((h1 _).fun_const_smul Complex.I), GlobalTheory.del_const_smul _ (h1 _)]
  rw [e w, e v, d w, d v]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, GlobalTheory.del_apply,
    GlobalTheory.fderiv_fderiv_apply hu]
  rw [hs.eq v w, hs.eq (Complex.I • v) w, hs.eq v (Complex.I • w),
    hs.eq (Complex.I • v) (Complex.I • w)]
  match_scalars <;> ring

theorem mdel_mdel_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {m n : Type*} {A : E → Matrix m n ℂ} {z : E} (h : MContDiffAt 2 A z)
    (ξ η : E) : mdel (fun x => mdel A x η) z ξ = mdel (fun x => mdel A x ξ) z η := by
  ext a b
  exact del_del_comm (h a b) ξ η

theorem mdel_conn_inv_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E)
    (h2 : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (hs : ∀ᶠ x in 𝓝 z, (H x).IsSymm) (ξ η : E) :
    mdel (fun x => conn (fun y => (H y)⁻¹) x η) z ξ
      - mdel (fun x => conn (fun y => (H y)⁻¹) x ξ) z η
      = -(conn H z η * conn H z ξ - conn H z ξ * conn H z η)ᵀ := by
  have h1 : MContDiffAt 1 H z := h2.of_le one_le_two
  have hloc : ∀ ζ, (fun x => conn (fun y => (H y)⁻¹) x ζ) =ᶠ[𝓝 z]
      fun x => -((H x)⁻¹ * mdel H x ζ)ᵀ := fun ζ => by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit hu, hs.eventually_nhds]
      with x hx2 hxu hxs
    have e : (fun y => (H y)⁻¹) =ᶠ[𝓝 x] fun y => GlobalTheory.HermFrame.dualGram (H y) :=
      hxs.mono fun y hy => by
        change (H y)⁻¹ = (H y)⁻¹ᵀ
        rw [transpose_nonsing_inv, hy.eq]
    rw [conn_congr e, conn_dual (hx2.of_le one_le_two) hxu, conn_eq_of_isSymm hxs]
  have hP : ∀ ζ, MContDiffAt 1 (fun x => mdel H x ζ) z := fun ζ => h2.mdel (by norm_num) ζ
  rw [mdel_congr (hloc η), mdel_congr (hloc ξ), mdel_neg, mdel_neg,
    mdel_transpose (fun x => (H x)⁻¹ * mdel H x η), mdel_transpose (fun x => (H x)⁻¹ * mdel H x ξ),
    mdel_mul (h1.inv hu) (hP η), mdel_mul (h1.inv hu) (hP ξ), mdel_inv h1 hu, mdel_inv h1 hu,
    mdel_mdel_comm h2 ξ η, conn_eq_of_isSymm hs, conn_eq_of_isSymm hs]
  have key : (H z)⁻¹ * mdel (fun x => mdel H x ξ) z η + -((H z)⁻¹ * mdel H z ξ * (H z)⁻¹) * mdel H z η
      - ((H z)⁻¹ * mdel (fun x => mdel H x ξ) z η + -((H z)⁻¹ * mdel H z η * (H z)⁻¹) * mdel H z ξ)
      = (H z)⁻¹ * mdel H z η * ((H z)⁻¹ * mdel H z ξ) - (H z)⁻¹ * mdel H z ξ * ((H z)⁻¹ * mdel H z η) := by
    noncomm_ring
  rw [← key, transpose_sub]
  abel

end GlobalTheory.HermFrame
end

section

open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.RealGram

open GlobalTheory.HermFrame Filter

theorem curv_inv_of_real : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, GlobalTheory.HermFrame.mddbar H z ξ η = 0) → ∀ ξ η, GlobalTheory.HermFrame.curv (fun x => (H x)⁻¹) z ξ η = -((GlobalTheory.HermFrame.conn H z η)ᵀᴴ * GlobalTheory.HermFrame.conn H z ξ)ᵀ := by
  intro E _ _ _ _ g H z h2 hu hs hh hdd ξ η
  have hsz : (H z)ᵀ = H z := hs.self_of_nhds.eq
  have hhz : (H z)ᴴ = H z := hh.self_of_nhds.eq
  have he : (fun x => (H x)⁻¹) =ᶠ[𝓝 z] fun x => dualGram (H x) :=
    hs.mono fun x hx => by
      show (H x)⁻¹ = (H x)⁻¹ᵀ
      rw [transpose_nonsing_inv, hx.eq]
  have hbar : (mdbar H z η)ᵀ = mdbar H z η := by
    rw [← mdbar_transpose]; exact mdbar_congr (hs.mono fun x hx => hx.eq) η
  have hdel : (mdel H z η)ᴴ = mdbar H z η := conjTranspose_mdel hh η
  have key : (conn H z η)ᵀᴴ = (H z)ᵀ⁻¹ * (mdbar H z η)ᵀ := by
    rw [conn, transpose_mul, transpose_transpose, conjTranspose_mul, hdel, transpose_nonsing_inv,
      transpose_transpose, hsz, hbar, conjTranspose_nonsing_inv, hhz]
  rw [curv_congr he, curv_dual h2 hu, curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero,
    sub_zero, key, conn, Matrix.mul_assoc, Matrix.mul_assoc]

end GlobalTheory.RealGram
end

section

open scoped Matrix

namespace GlobalTheory.HermFrame

open Matrix Filter Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [DecidableEq m] [Fintype l]

theorem curv_inv_one_sub_mul {P : E → Matrix m l ℂ} {Q : E → Matrix l m ℂ} {z ξ η : E}
    {C : Matrix l m ℂ} (hP : ∀ x, MContDiffAt 2 P x) (hQ : ∀ x, MContDiffAt 2 Q x)
    (hP0 : P z = 0) (hdP : ∀ x, mdel P x ξ = 0) (hdQ : ∀ x, mdel Q x ξ = C) :
    curv (fun x => (1 - P x * Q x)⁻¹) z ξ η = -(mdbar P z η * C)ᵀ := by
  have hK : ∀ x, MContDiffAt 2 (fun x => 1 - P x * Q x) x :=
    fun x => (mContDiffAt_const 1).sub ((hP x).mul (hQ x))
  have hK0 : (1 - P z * Q z) = 1 := by rw [hP0]; simp
  have hd : ∀ x, mdel (fun x => 1 - P x * Q x) x ξ = -(P x * C) := fun x => by
    have h1 := (hP x).of_le one_le_two
    have h2 := (hQ x).of_le one_le_two
    simp only [sub_eq_add_neg]
    rw [mdel_add (mContDiffAt_const 1) (h1.mul h2).neg, mdel_neg, mdel_mul h1 h2, hdP, hdQ]
    simp
  have hdd : mddbar (fun x => 1 - P x * Q x) z ξ η = -(mdbar P z η * C) := by
    rw [← mdbar_mdel (hK z)]
    simp only [hd]
    rw [mdbar_neg, mdbar_mul ((hP z).of_le one_le_two) (mContDiffAt_const C)]
    simp
  have hu : IsUnit (1 - P z * Q z)ᵀ.det := by rw [hK0]; simp
  have e : (fun x => (1 - P x * Q x)⁻¹) = fun x => dualGram (1 - P x * Q x)ᵀ := by
    funext x; rw [dualGram, transpose_nonsing_inv, transpose_transpose]
  rw [e, curv_dual (hK z).transpose hu, curv_eq (hK z).transpose hu,
    mdel_transpose (fun x => 1 - P x * Q x), hd,
    show mddbar (fun x => (1 - P x * Q x)ᵀ) z ξ η = (mddbar (fun x => 1 - P x * Q x) z ξ η)ᵀ from rfl,
    hdd, hK0, hP0]
  simp

end

section

variable {n : ℕ} {a b : Type*}

theorem mContDiffAt_coordMatrix (f : a → b → Fin n) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w := fun i j =>
  ((EuclideanSpace.proj (𝕜 := ℂ) (f i j)).restrictScalars ℝ).contDiff.contDiffAt

theorem mdel_coordMatrix (f : a → b → Fin n) (w ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ =
      Matrix.of fun i j => ξ (f i j) := by
  ext i j
  let L : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ := EuclideanSpace.proj (𝕜 := ℂ) (f i j)
  change del L w ξ = L ξ
  rw [del_eq_fderiv L.differentiableAt, L.fderiv]

theorem mdbar_coordMatrix (f : a → b → Fin n) (w ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ = 0 := by
  have h := mdel_add_mdbar (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ
  rw [mdel_coordMatrix] at h
  rw [← add_right_inj (Matrix.of fun i j => ξ (f i j)), h, add_zero]
  ext i j
  let L : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) (f i j)).restrictScalars ℝ
  change fderiv ℝ L w ξ = L ξ
  rw [L.fderiv]

end

theorem curv_inv_one_sub_conj_mul_transpose_zero : ∀ {n r s : ℕ} (f g : Fin r → Fin s → Fin n) (ξ η : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.HermFrame.curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 ξ η = -((Matrix.of fun i j => ξ (g i j)) * (Matrix.of fun i j => η (f i j))ᴴ) := by
  intro n r s f g ξ η
  let Z : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin s) ℂ := fun u => Matrix.of fun i j => u (f i j)
  let W : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin s) ℂ := fun u => Matrix.of fun i j => u (g i j)
  have h := curv_inv_one_sub_mul (P := fun u => (Z u)ᴴᵀ) (Q := fun u => (W u)ᵀ) (z := 0) (ξ := ξ)
    (η := η) (C := (W ξ)ᵀ) (fun x => (mContDiffAt_coordMatrix f x).conjTranspose.transpose)
    (fun x => (mContDiffAt_coordMatrix g x).transpose) (by ext i j; simp [Z])
    (fun x => by
      rw [mdel_transpose (fun u => (Z u)ᴴ), mdel_conjTranspose, mdbar_coordMatrix]; simp)
    (fun x => by rw [mdel_transpose W, mdel_coordMatrix])
  rw [mdbar_transpose (fun u => (Z u)ᴴ), mdbar_conjTranspose, mdel_coordMatrix, ← transpose_mul,
    transpose_transpose] at h
  exact h

end GlobalTheory.HermFrame
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem exists_section_of_isIntegralElem_of_isOpenImmersion {T Z : Scheme.{0}}
    [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j] :
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  intro hd U s hs u hu
  let C : irreducibleComponents Z := ⟨_, irreducibleComponent_mem_irreducibleComponents u⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, huW, hWle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show u ∈ ((U ⊓ IsNormalScheme.component C : Z.Opens) : Set Z) from
      ⟨hu, mem_irreducibleComponent⟩)
    (U ⊓ IsNormalScheme.component C).isOpen
  have hWU : W ≤ U := fun x hx ↦ (hWle hx).1
  refine ⟨W, hWU, huW, ?_⟩
  have hWirr : IsIrreducible (W : Set Z) :=
    ⟨⟨u, huW⟩, C.2.1.2.open_subset W.isOpen fun x hx ↦ (hWle hx).2⟩
  obtain ⟨_, _⟩ := IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hWirr
  obtain ⟨x, hxW, hfr, hgen⟩ : ∃ (x : Z) (hxW : x ∈ W),
      (letI := Z.presheaf.algebra_section_stalk (U := W) ⟨x, hxW⟩;
        IsFractionRing Γ(Z, W) (Z.presheaf.stalk x)) ∧ ∀ w ∈ W, x ⤳ w := by
    let P : Spec Γ(Z, W) := ⟨⊥, Ideal.isPrime_bot⟩
    have hxW : hW.fromSpec P ∈ W := hW.range_fromSpec.le ⟨P, rfl⟩
    refine ⟨_, hxW, ?_, ?_⟩
    · let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
      have h := hW.isLocalization_stalk' P hxW
      have e : P.asIdeal.primeCompl = nonZeroDivisors Γ(Z, W) := by
        ext a
        simp [P, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
      unfold IsLocalization.AtPrime at h
      rw [e] at h
      exact h
    · intro w hw
      obtain ⟨q, rfl⟩ : w ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hw
      exact ((PrimeSpectrum.le_iff_specializes P q).mp bot_le).map hW.fromSpec.continuous
  obtain ⟨y, rfl⟩ : x ∈ Set.range j := by
    obtain ⟨w, hw, hwr⟩ := hd.inter_open_nonempty _ W.isOpen ⟨u, huW⟩
    exact (hgen w hw).mem_open j.isOpenEmbedding.isOpen_range hwr
  let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
  let _ : Algebra Γ(Z, W) Γ(T, j ⁻¹ᵁ W) := (j.app W).hom.toAlgebra
  have hyW : y ∈ j ⁻¹ᵁ W := hxW
  have hnat : (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op).hom.comp (j.app U).hom =
      (algebraMap Γ(Z, W) Γ(T, j ⁻¹ᵁ W)).comp (Z.presheaf.map (homOfLE hWU).op).hom := by
    change _ = (j.app W).hom.comp _
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, j.naturality]
    rfl
  have hs₁ : IsIntegral Γ(Z, W) (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) := by
    obtain ⟨p, hp, hps⟩ := hs
    refine ⟨p.map (Z.presheaf.map (homOfLE hWU).op).hom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hnat, ← Polynomial.hom_eval₂, hps, map_zero]
  have hgerm (a : Γ(Z, W)) : j.stalkMap y (Z.presheaf.germ W (j y) hxW a) =
      T.presheaf.germ (j ⁻¹ᵁ W) y hyW (j.app W a) :=
    j.germ_stalkMap_apply W y hxW a
  have hbij : Function.Bijective (j.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  let φ : Γ(T, j ⁻¹ᵁ W) ⟶ Z.presheaf.stalk (j y) :=
    T.presheaf.germ (j ⁻¹ᵁ W) y hyW ≫ inv (j.stalkMap y)
  have hφ (c : Γ(T, j ⁻¹ᵁ W)) : j.stalkMap y (φ c) = T.presheaf.germ (j ⁻¹ᵁ W) y hyW c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(T, j ⁻¹ᵁ W) →ₐ[Γ(Z, W)] Z.presheaf.stalk (j y) :=
    { φ.hom with commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.map ψ hs₁)
  refine ⟨a, ?_⟩
  have hg : T.presheaf.germ (j ⁻¹ᵁ W) y hyW
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) = 0 := by
    rw [map_sub, ← hgerm, ← hφ, sub_eq_zero]
    exact congr(j.stalkMap y $ha)
  have : IsReduced T := isReduced_of_isOpenImmersion j
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro t ht
  have hyt : y ⤳ t :=
    j.isOpenEmbedding.isInducing.specializes_iff.mp (hgen _ (T.basicOpen_le _ ht))
  have hy : y ∈ T.basicOpen
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) :=
    hyt.mem_open (T.basicOpen _).isOpen ht
  rw [Scheme.mem_basicOpen _ _ _ hyW, hg] at hy
  exact (not_isUnit_zero hy).elim

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem bijective_of_existsUnique_field_point {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) :
    Function.Bijective f := by
  constructor
  · intro x x' hx
    obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) x x' hx
    let p : Sp ((pullback f f).residueField z) ⟶ pullback f f :=
      (pullback f f).fromSpecResidueField z
    have e : p ≫ pullback.fst f f = p ≫ pullback.snd f f :=
      (h _ (p ≫ pullback.fst f f ≫ f)).unique (by simp) (by simp [pullback.condition])
    let a : Sp ((pullback f f).residueField z) := IsLocalRing.closedPoint _
    have ha : p a = z := Scheme.fromSpecResidueField_apply z a
    have e' : (p ≫ pullback.fst f f) a = (p ≫ pullback.snd f f) a := by rw [e]
    rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ha, hz, hz'] at e'
  · intro t
    obtain ⟨z, hz, -⟩ := h (T.residueField t) (T.fromSpecResidueField t)
    let a : Sp (T.residueField t) := IsLocalRing.closedPoint _
    refine ⟨z a, ?_⟩
    rw [← Scheme.Hom.comp_apply, hz]
    exact Scheme.fromSpecResidueField_apply t a

theorem existsUnique_field_point_morphismRestrict {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) (V : T.Opens)
    (k : Type) [Field k] (w : Sp k ⟶ V) : ∃! z : Sp k ⟶ (f ⁻¹ᵁ V), z ≫ (f ∣_ V) = w := by
  obtain ⟨z, hz, hu⟩ := h k (w ≫ V.ι)
  have P := (isPullback_morphismRestrict f V).flip
  refine ⟨P.lift z w hz, P.lift_snd _ _ _, fun y hy ↦ ?_⟩
  apply P.hom_ext
  · rw [P.lift_fst]
    apply hu
    show (y ≫ _) ≫ f = _
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]
  · rw [P.lift_snd]; exact hy

theorem isIso_stalkMap_genericPoint_of_lift {S T : Scheme.{0}} (f : S ⟶ T) [IsIntegral S]
    [IsIntegral T] [IsDominant f] (hf : Function.Injective f)
    (z : Spec T.functionField ⟶ S) (hz : z ≫ f = T.fromSpecStalk (genericPoint T)) :
    IsIso (f.stalkMap (genericPoint S)) := by
  have hs : z (IsLocalRing.closedPoint _) = genericPoint S := by
    apply hf
    rw [apply_genericPoint_of_isDominant f]
    refine (Scheme.Hom.comp_apply z f _).symm.trans ?_
    rw [hz]
    exact Scheme.fromSpecStalk_closedPoint
  have hF : IsField (S.presheaf.stalk (z (IsLocalRing.closedPoint _))) := by
    rw [hs]; exact Field.toIsField S.functionField
  rw [← hs]
  have h1 : IsIso (Scheme.stalkClosedPointTo (z ≫ f)) := by
    rw [hz, Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  rw [Scheme.stalkClosedPointTo_comp] at h1
  have h2 : IsIso (Scheme.stalkClosedPointTo z) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · letI := hF.toField
      exact (Scheme.stalkClosedPointTo z).hom.injective
    · intro y
      obtain ⟨x, hx⟩ := (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ h1).2 y
      exact ⟨_, hx⟩
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (Scheme.stalkClosedPointTo z) h2 h1

theorem isIso_of_isProper_of_existsUnique_field_point_of_isIntegral {S T : Scheme.{0}} (f : S ⟶ T)
    [IsProper f] [IsReduced S] [IsIntegral T] [GlobalTheory.IsNormalScheme T]
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by
  have hb := bijective_of_existsUnique_field_point f h
  have hh : IsHomeomorph f :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨f.continuous, f.isClosedMap, hb⟩
  have : IrreducibleSpace S := hh.homeomorph.symm.irreducibleSpace_iff.mp inferInstance
  have : IsIntegral S := isIntegral_of_irreducibleSpace_of_isReduced S
  have : IsDominant f := ⟨hb.2.denseRange⟩
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    fun t ↦ (Set.finite_singleton t).preimage hb.1.injOn
  obtain ⟨z, hz, -⟩ := h T.functionField (T.fromSpecStalk (genericPoint T))
  have := isIso_stalkMap_genericPoint_of_lift f hb.1 z hz
  exact isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap f fun _ ↦ inferInstance

theorem isIso_of_isProper_of_existsUnique_field_point (S T : Scheme.{0}) (f : S ⟶ T)
    (hf : IsProper f) (hS : IsReduced S) (hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T)
    (hN : IsLocallyNoetherian T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by
  have := GlobalTheory.IsNormalScheme.of_pred hT
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _)
    GlobalTheory.IsNormalScheme.component (@GlobalTheory.IsNormalScheme.iSup_component T _ _)).mpr fun Z ↦ ?_
  exact isIso_of_isProper_of_existsUnique_field_point_of_isIntegral
    (f ∣_ GlobalTheory.IsNormalScheme.component Z) (existsUnique_field_point_morphismRestrict f h _)

end GlobalTheory
end

section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

theorem _root_.GlobalTheory.T.coeff_composedPartialDerivList_of_nodup : ∀ {σ : Type} [DecidableEq σ] (l : List σ), l.Nodup → ∀ (m : σ →₀ ℕ), (∀ v ∈ l, m v = 0) → ∀ (G : MvPolynomial σ ℂ), AddMonoidAlgebra.coeff (dList l G) m = AddMonoidAlgebra.coeff G (m + (l.map fun v => Finsupp.single v 1).sum) := by
  first | exact @GlobalTheory.CayleyBlock.coeff_dList_of_nodup | exact GlobalTheory.CayleyBlock.coeff_dList_of_nodup | (intros; apply GlobalTheory.CayleyBlock.coeff_dList_of_nodup <;> assumption)
end

section


theorem _root_.GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero : ∀ {n p q : ℕ} (e : Fin p × Fin q → Fin n) (k : ℕ), 1 ≤ k → ((GlobalTheory.GrassModel.blockPoly e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace + ((-GlobalTheory.GrassModel.blockPolyBar e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace = 0 := by
  first | exact @GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | exact GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | (intros; apply GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar <;> assumption)
end

section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

theorem _root_.GlobalTheory.T.charpolyMulBaseChangeFinite_map_of_isPushout : ∀ {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field K']
    [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K'), (∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) →
    ∀ b : B, charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by
  first | exact @GlobalTheory.NormalDescent.charK_map_of_isPushout | exact GlobalTheory.NormalDescent.charK_map_of_isPushout | (intros; apply GlobalTheory.NormalDescent.charK_map_of_isPushout <;> assumption)
end

section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

theorem _root_.GlobalTheory.T.reversedCharpolyCoeffInDomain_mul : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  first | exact @GlobalTheory.NormalDescent.normCoeff_mul | exact GlobalTheory.NormalDescent.normCoeff_mul | (intros; apply GlobalTheory.NormalDescent.normCoeff_mul <;> assumption)
end
