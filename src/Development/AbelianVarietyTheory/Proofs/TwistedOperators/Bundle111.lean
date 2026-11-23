module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle105
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle106
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle026
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem jac_exp_herm {p q : ℕ} (B : Fin p → Fin q → ℂ) :
    (NormedSpace.exp (pY B))ᴴ = NormedSpace.exp (pY B) := by
  rw [← Matrix.exp_conjTranspose, pY_conjTranspose]

theorem jac_exp_two {p q : ℕ} (B : Fin p → Fin q → ℂ) :
    NormedSpace.exp (pY B + pY B) = NormedSpace.exp (pY B) * NormedSpace.exp (pY B) := Matrix.exp_add_of_commute _ _ (Commute.refl _)

theorem jac_cancel {p q : ℕ} (B : Fin p → Fin q → ℂ) (X Z : Mat p q)
    (h : NormedSpace.exp (pY B) * X * NormedSpace.exp (pY B)
      = NormedSpace.exp (pY B) * Z * NormedSpace.exp (pY B)) : X = Z := by
  have hu := Matrix.isUnit_exp (pY B)
  exact hu.mul_left_cancel (hu.mul_right_cancel h)

theorem jac_block {p q : ℕ} (X Z : Fin p → Fin q → ℂ) (U : Matrix (Fin p) (Fin p) ℂ)
    (V : Matrix (Fin q) (Fin q) ℂ)
    (h : pY X = (Matrix.fromBlocks U 0 0 V : Mat p q)ᴴ * pY Z * Matrix.fromBlocks U 0 0 V) :
    Matrix.of X = Uᴴ * Matrix.of Z * V := by
  have h1 := congrArg Matrix.toBlocks₁₂ h
  simpa [pY, pOf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_assoc] using h1

noncomputable def jacMul {m n : Type} [Fintype m] [Fintype n] (U : Matrix m m ℂ) (V : Matrix n n ℂ) :
    (m → n → ℂ) →ₗ[ℝ] (m → n → ℂ) where
  toFun Z := fun i j => (U * Matrix.of Z * V) i j
  map_add' Z W := by
    have : Matrix.of (Z + W) = Matrix.of Z + Matrix.of W := rfl
    rw [this, Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' t Z := by
    have : Matrix.of (t • Z) = t • Matrix.of Z := rfl
    rw [this, Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem of_jacMul {m n : Type} [Fintype m] [Fintype n] (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (Z : m → n → ℂ) : Matrix.of (jacMul U V Z) = U * Matrix.of Z * V := rfl

private theorem pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ {E : Type*} [AddCommGroup E] [Module ℝ E] (X Z : E)
    (h : X + X = Z + Z) : X = Z := by
  have h2 : (2 : ℝ) • X = (2 : ℝ) • Z := by rw [two_smul, two_smul]; exact h
  have h3 := congrArg (fun W => (1 / 2 : ℝ) • W) h2
  simpa [smul_smul] using h3

private theorem pY_injective {p q : ℕ} (X Z : Fin p → Fin q → ℂ) (h : pY X = pY Z) : X = Z := by
  funext i j
  have h1 := congrFun (congrFun (congrArg Matrix.toBlocks₁₂ h) i) j
  simpa [pY, pOf] using h1

private theorem conjTranspose_mul_mul_mul_eq_of_mul_eq {n : Type*} [Fintype n] [DecidableEq n] (g E F k X : Matrix n n ℂ)
    (hE : Eᴴ = E) (hF : Fᴴ = F) (h : E * g = k * F) :
    gᴴ * (E * X * E) * g = F * (kᴴ * X * k) * F := by
  have h1 : gᴴ * E = (E * g)ᴴ := by rw [Matrix.conjTranspose_mul, hE]
  calc gᴴ * (E * X * E) * g = (gᴴ * E) * X * (E * g) := by simp only [Matrix.mul_assoc]
    _ = (k * F)ᴴ * X * (k * F) := by rw [h1, h]
    _ = F * (kᴴ * X * k) * F := by rw [Matrix.conjTranspose_mul, hF]; simp only [Matrix.mul_assoc]

private theorem fromBlocks_unitary_conjTranspose_mul_self {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (V : Matrix (Fin q) (Fin q) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin p) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin q) ℂ) :
    (Matrix.fromBlocks U 0 0 V)ᴴ * Matrix.fromBlocks U 0 0 V = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU hV
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hU, hV]

private theorem injective_of_det_ne_zero {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (h : LinearMap.det f ≠ 0) : Function.Injective f :=
  (LinearMap.equivOfDetNeZero f h).injective

private theorem conjTranspose_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hU
  exact hU

theorem jacobian_action_p : ∀ (p q : ℕ) (g : Mat p q) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous ψ → (∀ B, ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, NormedSpace.exp (pY B) * g = Matrix.fromBlocks U 0 0 V * NormedSpace.exp (pY (ψ B))) → (∀ B : Fin p → Fin q → ℂ, 0 < LinearMap.det (sP (pY B))) → (∀ B C : Fin p → Fin q → ℂ, sAd (pY B) (pY C) = pY (sP (pY B) C)) → (∀ B : Fin p → Fin q → ℂ, ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B)) → ∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * LinearMap.det (sP (pY (ψ B))) = LinearMap.det (sP (pY B)) := by
  intro p q g ψ hψ hK hdet hsAd hdiff B
  obtain ⟨A, hA, hAeq⟩ := hdiff (ψ B)
  obtain ⟨A0, hA0, hA0eq⟩ := hdiff B
  obtain ⟨U, hU, V, hV, hUV⟩ := hK B
  set L := LinearMap.toContinuousLinearMap (jacMul gᴴ g) with hL
  have hLapp : ∀ M, Matrix.of (L M) = gᴴ * Matrix.of M * g := fun M => of_jacMul gᴴ g M

  have hcomp : (fun y => (fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) (ψ y)) =
      fun y => L ((fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) y) := by
    funext y
    obtain ⟨U', hU', V', hV', hy⟩ := hK y
    have hmat : NormedSpace.exp (pY (ψ y) + pY (ψ y)) = gᴴ * NormedSpace.exp (pY y + pY y) * g := by
      have hs := conjTranspose_mul_mul_mul_eq_of_mul_eq g _ _ _ 1 (jac_exp_herm y) (jac_exp_herm (ψ y)) hy
      rw [Matrix.mul_one, Matrix.mul_one, fromBlocks_unitary_conjTranspose_mul_self U' V' hU' hV', Matrix.mul_one] at hs
      rw [jac_exp_two, jac_exp_two, hs]
    apply Matrix.of.injective
    rw [hLapp]
    exact hmat
  have hLd : HasFDerivAt (fun y => (fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) (ψ y))
      (L.comp A0) B := by
    rw [hcomp]
    exact L.hasFDerivAt.comp B hA0.hasFDerivAt
  have hinj : Function.Injective A := by
    intro C1 C2 h
    have h1 : Matrix.of (A C1) = Matrix.of (A C2) := by rw [h]
    rw [hAeq, hAeq] at h1
    have h2 := jac_cancel (ψ B) _ _ h1
    rw [← pY_add, ← pY_add, hsAd, hsAd] at h2
    exact pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ _ _ (injective_of_det_ne_zero _ (hdet (ψ B)).ne' (pY_injective _ _ h2))
  obtain ⟨P, hP, hPA⟩ := GlobalTheory.hasFDerivAt_of_comp_immersion (Fin p → Fin q → ℂ) (Ix p q → Ix p q → ℂ)
    (fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) ψ B A (L.comp A0) hA hinj
    hψ.continuousAt hLd
  refine ⟨P, hP, ?_⟩

  have hkey : ∀ C, sP (pY (ψ B)) (P C) = jacMul Uᴴ V (sP (pY B) C) := by
    intro C
    have h1 := congrArg (fun T : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ) => Matrix.of (T C)) hPA
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [hLapp, hAeq, hA0eq, conjTranspose_mul_mul_mul_eq_of_mul_eq g _ _ _ _ (jac_exp_herm B) (jac_exp_herm (ψ B)) hUV] at h1
    have h3 := jac_cancel (ψ B) _ _ h1
    rw [← pY_add, ← pY_add, hsAd, hsAd] at h3
    have h4 := jac_block _ _ U V h3
    rw [← of_jacMul] at h4
    have h5 := Matrix.of.injective h4
    simp only [map_add (f := _)] at h5
    exact pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ _ _ h5
  have hlin : (sP (pY (ψ B))).comp (P : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ)) =
      (jacMul Uᴴ V).comp (sP (pY B)) := LinearMap.ext hkey
  have hd := congrArg (fun T => |LinearMap.det T|) hlin
  simp only [LinearMap.det_comp, abs_mul] at hd
  rw [abs_det_unitary_mul_mul p q Uᴴ (conjTranspose_mem_unitaryGroup hU) V hV _ (of_jacMul Uᴴ V), one_mul,
    abs_of_pos (hdet (ψ B)), abs_of_pos (hdet B)] at hd
  show |LinearMap.det (P : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ))| * _ = _
  rw [mul_comm]
  exact hd

end GlobalTheory.PolarU
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.RealPar

theorem flow_pair_mem_range {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : E →ₗ[ℂ] H₁) (j₂ : E →ₗ[ℂ] H₂) (a : E →ₗ[ℂ] E)
    (U₁ : ℝ → H₁ →L[ℂ] H₁) (U₂ : ℝ → H₂ →L[ℂ] H₂) (h₁ : U₁ 0 = 1) (h₂ : U₂ 0 = 1)
    (a₁ : ∀ s t, U₁ (s + t) = U₁ s * U₁ t) (a₂ : ∀ s t, U₂ (s + t) = U₂ s * U₂ t)
    (d₁ : ∀ v, HasDerivAt (fun t : ℝ => U₁ t (j₁ v)) (j₁ (a v)) 0)
    (d₂ : ∀ v, HasDerivAt (fun t : ℝ => U₂ t (j₂ v)) (j₂ (a v)) 0) (t : ℝ) (w : E) :
    ∃ w' : E, U₁ t (j₁ w) = j₁ w' ∧ U₂ t (j₂ w) = j₂ w' := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂
  let ι : E →ₗ[ℂ] WithLp 2 (H₁ × H₂) := e.symm.toLinearEquiv.toLinearMap ∘ₗ j₁.prod j₂
  let U : ℝ → WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) := fun s =>
    (e.symm : H₁ × H₂ →L[ℂ] WithLp 2 (H₁ × H₂)) ∘L ((U₁ s).prodMap (U₂ s)) ∘L
      (e : WithLp 2 (H₁ × H₂) →L[ℂ] H₁ × H₂)
  have hU : ∀ s x, U s x = e.symm (U₁ s (e x).1, U₂ s (e x).2) := fun s x => rfl
  have hι : ∀ v, ι v = e.symm (j₁ v, j₂ v) := fun v => rfl
  have key := flow_mem_map ι a ⊤ (fun _ _ => trivial) U
    (by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [hU, h₁, h₂]
      exact e.symm_apply_apply x)
    (fun s r => by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [ContinuousLinearMap.mul_apply, hU, hU, hU, a₁, a₂, e.apply_symm_apply]
      rfl)
    (fun v => by
      have h := ((e.symm : H₁ × H₂ →L[ℂ] WithLp 2 (H₁ × H₂)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) ((d₁ v).prodMk (d₂ v))
      exact h) t (ι w) ⟨w, trivial, rfl⟩
  obtain ⟨w', -, hw'⟩ := key
  rw [hU, hι, hι, e.apply_symm_apply] at hw'
  have h := e.symm.injective hw'
  exact ⟨w', (congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

theorem pair_kEquivariant_of_lie : ∀ (p q : ℕ) (T : GrpData p q), (∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y})) → ∀ (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (a : Mat p q → E →ₗ[ℂ] E) (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, IsKC Y → ∀ w, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ w)) (j₁ (a Y w)) 0 ∧ HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ w)) (j₂ (a Y w)) 0) → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') := by
  intro p q T hgen π₁ π₂ E _ _ _ a j₁ j₂ hder k hk
  have hflow : ∀ Y ∈ upq p q, IsKC Y → ∀ (t : ℝ) (w : E), ∃ w' : E,
      π₁.π (T.expt (t • Y)) (j₁ w) = j₁ w' ∧ π₂.π (T.expt (t • Y)) (j₂ w) = j₂ w' := by
    intro Y hY hK t w
    exact flow_pair_mem_range j₁ j₂ (a Y) (fun t => π₁.π (T.expt (t • Y))) (fun t => π₂.π (T.expt (t • Y)))
      (by simp [T.expt_zero]) (by simp [T.expt_zero])
      (fun s t => by simp only [T.expt_add Y hY, map_mul])
      (fun s t => by simp only [T.expt_add Y hY, map_mul])
      (fun v => (hder Y hY hK v).1) (fun v => (hder Y hY hK v).2) t w
  refine Subgroup.closure_induction'' (p := fun k _ => ∀ w : E, ∃ w' : E,
    π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') ?_ ?_ ?_ ?_ (hgen k hk)
  · rintro _ ⟨Y, ⟨hY, hK⟩, rfl⟩ w
    simpa using hflow Y hY hK 1 w
  · rintro _ ⟨Y, ⟨hY, hK⟩, rfl⟩ w
    have h : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have := T.expt_add Y hY (-1) 1
      rw [neg_add_cancel, zero_smul, one_smul, T.expt_zero] at this
      exact (eq_inv_of_mul_eq_one_left this.symm).symm
    rw [h]
    exact hflow Y hY hK (-1) w
  · intro w
    exact ⟨w, by simp, by simp⟩
  · intro x y _ _ hx hy w
    obtain ⟨w', h1, h2⟩ := hy w
    obtain ⟨w'', h3, h4⟩ := hx w'
    exact ⟨w'', by rw [map_mul, ContinuousLinearMap.mul_apply, h1, h3],
      by rw [map_mul, ContinuousLinearMap.mul_apply, h2, h4]⟩

end GlobalTheory.RealPar
end

section

noncomputable section

open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowRat

theorem exists_proj (K' : Subfield ℂ) : ∃ φ : ℂ →ₗ[K'] ℂ, (∀ x : K', φ x = x) ∧ ∀ x, φ x ∈ K' := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K' ℂ)
    (LinearMap.ker_eq_bot.2 (FaithfulSMul.algebraMap_injective K' ℂ))
  refine ⟨(Algebra.linearMap K' ℂ).comp g, fun x => ?_, fun x => (g x).2⟩
  have h := congrArg (fun f => f x) hg
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  show algebraMap K' ℂ (g (Algebra.linearMap K' ℂ x)) = algebraMap K' ℂ x
  rw [h]

theorem val_eq_sum_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (v : VV ℂ lam) :
    v.1 = ∑ a, (bVV ℂ lam).repr v a • bVVfun ℂ lam a := by
  conv_lhs => rw [← (bVV ℂ lam).sum_repr v]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, bVV_coe]

theorem coeff_mem_of_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ a, (bVV ℂ lam).repr v a ∈ Set.range κ) (m : ι × Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ := by
  rw [val_eq_sum_repr, coeff_sum, ← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun a _ => ?_
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
  rw [MvPolynomial.coeff_smul, hP, coeff_map, smul_eq_mul]
  obtain ⟨x, hx⟩ := h a
  exact ⟨x * P.coeff m, by simp [hx]⟩

end GlobalTheory.RowRat

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem repr_mem_of_coeff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) (a : VVIdx lam) :
    (bVV ℂ lam).repr v a ∈ Set.range κ := by
  set K' := κ.fieldRange
  obtain ⟨φ, hφ1, hφ2⟩ := exists_proj K'
  set c := fun a => (bVV ℂ lam).repr v a
  have hK : ∀ a m, AddMonoidAlgebra.coeff (bVVfun ℂ lam a) m ∈ K' := fun a m => by
    obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
    rw [hP, coeff_map]
    exact ⟨((AddMonoidAlgebra.coeff P m : ℤ) : L), by simp⟩
  have key : ∑ b, (c b - φ (c b)) • bVVfun ℂ lam b = 0 := by
    ext m
    have e1 : AddMonoidAlgebra.coeff v.1 m = ∑ b, c b * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m := by
      rw [val_eq_sum_repr, coeff_sum]; simp [c]
    have e2 : φ (AddMonoidAlgebra.coeff v.1 m) = AddMonoidAlgebra.coeff v.1 m := hφ1 ⟨_, RingHom.mem_fieldRange.2 (h m)⟩
    have e3 : φ (AddMonoidAlgebra.coeff v.1 m) = ∑ b, φ (c b) * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m := by

      rw [e1, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : c b * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m = (⟨_, hK b m⟩ : K') • c b := by
        rw [Subfield.smul_def, smul_eq_mul, mul_comm]
      rw [this, map_smul, Subfield.smul_def, smul_eq_mul, mul_comm]
    rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e3, e2, sub_self]
  have hz := Fintype.linearIndependent_iff.1 (bVVfun_spec ℂ lam).1 _ key a
  rw [sub_eq_zero] at hz
  have hc : c a ∈ K' := by rw [hz]; exact hφ2 _
  exact RingHom.mem_fieldRange.1 hc

end GlobalTheory.RowRat

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem coeff_map_mem {ι : Type} [Fintype ι] {n n' : ℕ} {σ : ι → Formalism.BasicNotions.DomWeight n} {σ' : ι → Formalism.BasicNotions.DomWeight n'} {L : Type} [Field L] (κ : L →+* ℂ)
    (f : VV ℂ σ →ₗ[ℂ] VV ℂ σ') (hf : ∀ a b, (bVV ℂ σ').repr (f (bVV ℂ σ b)) a ∈ Set.range κ) (v : VV ℂ σ)
    (hv : ∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) (m : ι × Fin n' × Fin n' →₀ ℕ) :
    AddMonoidAlgebra.coeff (f v).1 m ∈ Set.range κ := by
  refine coeff_mem_of_repr σ' κ _ (fun a => ?_) m
  have e : f v = ∑ b, (bVV ℂ σ).repr v b • f (bVV ℂ σ b) := by
    conv_lhs => rw [← (bVV ℂ σ).sum_repr v]

    simp only [map_sum, map_smul]
  rw [e]

  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun b _ => ?_
  exact Subfield.mul_mem _ (RingHom.mem_fieldRange.2 (repr_mem_of_coeff σ κ v hv b)) (RingHom.mem_fieldRange.2 (hf a b))

end GlobalTheory.RowRat

end
end
