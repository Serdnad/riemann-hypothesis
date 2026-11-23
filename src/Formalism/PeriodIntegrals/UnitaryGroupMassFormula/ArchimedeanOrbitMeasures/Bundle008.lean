module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExHua
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix

section MatDet

variable {n : Type} [Fintype n] [DecidableEq n]

theorem det_mulRight_mat (B : Matrix n n ℂ) :
    LinearMap.det (LinearMap.mulRight ℂ B : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      B.det ^ Fintype.card n := by
  classical
  let e : Matrix n n ℂ ≃ₗ[ℂ] (n → n → ℂ) :=
    { toFun := fun X i j => X i j
      invFun := fun v => Matrix.of v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let g : (n → n → ℂ) →ₗ[ℂ] (n → n → ℂ) :=
    LinearMap.pi fun i => (Matrix.toLin' Bᵀ).comp (LinearMap.proj i)
  have key : (LinearMap.mulRight ℂ B : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      (e.symm : (n → n → ℂ) →ₗ[ℂ] Matrix n n ℂ).comp
        (g.comp (e.symm.symm : Matrix n n ℂ →ₗ[ℂ] (n → n → ℂ))) := by
    refine LinearMap.ext fun X => ?_
    refine Matrix.ext fun i j => ?_
    rw [LinearMap.mulRight_apply, Matrix.mul_apply]
    change ∑ k, X i k * B k j = ∑ k, B k j * X i k
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [key, LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Matrix.det_transpose]

theorem det_mulLeft_mat (A : Matrix n n ℂ) :
    LinearMap.det (LinearMap.mulLeft ℂ A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      A.det ^ Fintype.card n := by
  classical
  let e : Matrix n n ℂ ≃ₗ[ℂ] Matrix n n ℂ := Matrix.transposeLinearEquiv n n ℂ ℂ
  have key : (LinearMap.mulLeft ℂ A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      (e : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ).comp
        ((LinearMap.mulRight ℂ Aᵀ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ).comp
          (e.symm : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)) := by
    refine LinearMap.ext fun X => ?_
    simp [e, Matrix.transpose_mul]
  rw [key, LinearMap.det_conj, det_mulRight_mat, Matrix.det_transpose]

end MatDet

section Real

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

def sigJ (W : Mat) : Mat := HcS.UG.Jpq P Q * Wᴴ * HcS.UG.Jpq P Q

theorem Jpq_mul_mul (X : Mat) : HcS.UG.Jpq P Q * (HcS.UG.Jpq P Q * X) = X := by
  rw [← Matrix.mul_assoc]
  simp [HcS.UG.Jpq, Matrix.fromBlocks_multiply]

theorem sigJ_add (V W : Mat) : sigJ (V + W) = sigJ V + sigJ W := by
  simp only [sigJ, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem sigJ_smul (c : ℂ) (W : Mat) : sigJ (c • W) = star c • sigJ W := by
  simp only [sigJ, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem sigJ_sigJ (W : Mat) : sigJ (sigJ W) = W := by
  have hJ : (HcS.UG.Jpq P Q)ᴴ = HcS.UG.Jpq P Q := by
    simp [HcS.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have hJJ : HcS.UG.Jpq P Q * HcS.UG.Jpq P Q = 1 := by
    simpa using Jpq_mul_mul (P := P) (Q := Q) 1
  simp only [sigJ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ,
    Matrix.mul_assoc, Jpq_mul_mul, hJJ, Matrix.mul_one]

theorem mem_lieU_iff_sigJ (X : Mat) : X ∈ lieU P Q ↔ sigJ X = -X := by
  show Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X = 0 ↔ HcS.UG.Jpq P Q * Xᴴ * HcS.UG.Jpq P Q = -X
  constructor
  · intro h
    have h' : Xᴴ * HcS.UG.Jpq P Q = -(HcS.UG.Jpq P Q * X) := eq_neg_of_add_eq_zero_left h
    rw [Matrix.mul_assoc, h', Matrix.mul_neg, Jpq_mul_mul]
  · intro h
    have e1 : HcS.UG.Jpq P Q * (Xᴴ * HcS.UG.Jpq P Q) = -X := by
      rw [← Matrix.mul_assoc]
      exact h
    calc Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X
        = HcS.UG.Jpq P Q * (HcS.UG.Jpq P Q * (Xᴴ * HcS.UG.Jpq P Q)) + HcS.UG.Jpq P Q * X := by
          rw [Jpq_mul_mul]
      _ = 0 := by rw [e1, Matrix.mul_neg, neg_add_cancel]

def cplx : (lieU P Q × lieU P Q) →ₗ[ℝ] Mat where
  toFun p := ((p.1 : lieU P Q) : Mat) + Complex.I • ((p.2 : lieU P Q) : Mat)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
    rw [smul_comm c Complex.I]

theorem cplx_apply (p : lieU P Q × lieU P Q) :
    cplx p = ((p.1 : lieU P Q) : Mat) + Complex.I • ((p.2 : lieU P Q) : Mat) := rfl

theorem cplx_injective : Function.Injective (cplx (P := P) (Q := Q)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  rintro ⟨⟨Y, hY⟩, ⟨Z, hZ⟩⟩ h
  have h1 : Y + Complex.I • Z = 0 := h
  have hY' : sigJ Y = -Y := (mem_lieU_iff_sigJ Y).1 hY
  have hZ' : sigJ Z = -Z := (mem_lieU_iff_sigJ Z).1 hZ
  have hs : star Complex.I = -Complex.I := by simp [Complex.star_def]
  have h2 : -Y + Complex.I • Z = 0 := by
    have h3 : sigJ (Y + Complex.I • Z) = 0 := by
      rw [h1]; simp [sigJ]
    rw [sigJ_add, sigJ_smul, hY', hZ', hs, neg_smul_neg] at h3
    exact h3
  have hY0 : Y = 0 := by
    have h4 : (2 : ℂ) • Y = 0 := by
      rw [two_smul]
      calc Y + Y = (Y + Complex.I • Z) - (-Y + Complex.I • Z) := by abel
        _ = 0 := by rw [h1, h2, sub_zero]
    exact (smul_eq_zero.1 h4).resolve_left two_ne_zero
  have hZ0 : Z = 0 := by
    rw [hY0, zero_add] at h1
    exact (smul_eq_zero.1 h1).resolve_left Complex.I_ne_zero
  subst hY0
  subst hZ0
  rfl

theorem cplx_surjective : Function.Surjective (cplx (P := P) (Q := Q)) := by
  intro W
  have hsub : ∀ V U : Mat, sigJ (V - U) = sigJ V - sigJ U := by
    intro V U
    simp only [sigJ, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hh : star ((1 : ℂ) / 2) = 1 / 2 := by simp
  have hi : star (-Complex.I / 2) = Complex.I / 2 := by simp [Complex.star_def]
  have hI2 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]
  have hY : ((1 : ℂ) / 2) • (W - sigJ W) ∈ lieU P Q := by
    rw [mem_lieU_iff_sigJ, sigJ_smul, hsub, sigJ_sigJ, hh, ← smul_neg, neg_sub]
  have hZ : (-Complex.I / 2) • (W + sigJ W) ∈ lieU P Q := by
    rw [mem_lieU_iff_sigJ, sigJ_smul, sigJ_add, sigJ_sigJ, hi, ← neg_smul, add_comm (sigJ W)]
    congr 1
    ring
  refine ⟨(⟨_, hY⟩, ⟨_, hZ⟩), ?_⟩
  rw [cplx_apply]
  show ((1 : ℂ) / 2) • (W - sigJ W) + Complex.I • ((-Complex.I / 2) • (W + sigJ W)) = W
  rw [smul_smul, hI2, ← smul_add,
    show W - sigJ W + (W + sigJ W) = (2 : ℂ) • W by rw [two_smul]; abel, smul_smul]
  norm_num

def cplxE : (lieU P Q × lieU P Q) ≃ₗ[ℝ] Mat :=
  LinearEquiv.ofBijective cplx ⟨cplx_injective, cplx_surjective⟩

theorem cplxE_apply (p : lieU P Q × lieU P Q) : cplxE p = cplx p := rfl

end Real

theorem det_ayb : DetAYB := by
  intro P Q A B L hL
  classical
  let M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →ₗ[ℂ] Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
    (LinearMap.mulLeft ℂ A).comp (LinearMap.mulRight ℂ B)
  have hM : LinearMap.det M = (A.det * B.det) ^ (P + Q) := by
    rw [LinearMap.det_comp, det_mulLeft_mat, det_mulRight_mat, mul_pow, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have key : ((cplxE (P := P) (Q := Q) : (lieU P Q × lieU P Q) →ₗ[ℝ] _).comp
      ((L.prodMap L).comp ((cplxE (P := P) (Q := Q)).symm :
        Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →ₗ[ℝ] (lieU P Q × lieU P Q)))) =
      M.restrictScalars ℝ := by
    refine LinearMap.ext fun W => ?_
    obtain ⟨p, rfl⟩ := (cplxE (P := P) (Q := Q)).surjective W
    show cplxE ((L.prodMap L) ((cplxE (P := P) (Q := Q)).symm (cplxE p))) = A * (cplxE p * B)
    rw [LinearEquiv.symm_apply_apply, cplxE_apply, cplxE_apply, cplx_apply, cplx_apply]
    show ((L p.1 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • ((L p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      A * ((((p.1 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • ((p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) * B)
    rw [hL, hL, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Matrix.mul_assoc]
  have h2 : LinearMap.det (L.prodMap L) = Algebra.norm ℝ (LinearMap.det M) := by
    rw [← LinearMap.det_conj (L.prodMap L) (cplxE (P := P) (Q := Q)), key,
      LinearMap.det_restrictScalars]
  rw [LinearMap.det_prodMap, hM, Algebra.norm_complex_apply] at h2
  have h3 : |LinearMap.det L| ^ 2 = (‖A.det‖ ^ (P + Q) * ‖B.det‖ ^ (P + Q)) ^ 2 := by
    rw [sq_abs, sq, h2, Complex.normSq_eq_norm_sq, norm_pow, norm_mul]
    ring
  exact (pow_left_inj₀ (abs_nonneg _) (by positivity) two_ne_zero).1 h3

theorem huaInv_of_tauDeriv (h2 : TauDeriv) : HuaInv := huaInv_of det_ayb h2

end HcInf
end
end

section

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section Deriv

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

def tauR (H X : Mat) : Mat :=
  (1 + 1) - (4 : ℂ) • (((1 + 1) - X) * Ring.inverse (H * ((1 + 1) + X) + ((1 + 1) - X)))

theorem smul_four (Z : Mat) : (4 : ℂ) • Z = (1 + 1 + 1 + 1) * Z := by
  rw [show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul, add_mul, add_mul,
    add_mul, one_mul]

theorem key_alg (H X Y Ni K : Mat)
    (hNi : Ni * (H * ((1 + 1) + X) + ((1 + 1) - X)) = 1) (hK : ((1 + 1) - X) * K = 1) :
    Y + ((1 + 1) - X) * Ni * (H * Y - Y) =
      (1 + 1 + 1 + 1) * (((1 + 1) - X) * Ni * H * K * Y) := by
  set S := (1 + 1 : Mat) - X with hS
  have hX : (1 + 1 : Mat) + X = (1 + 1 + 1 + 1) - S := by
    rw [hS]
    noncomm_ring
  have e1 : S * Ni * (H * ((1 + 1) + X) + S) * K = 1 := by
    rw [mul_assoc S Ni, hNi, mul_one, hK]
  rw [hX] at e1
  have e2 : S * Ni * (H * ((1 + 1 + 1 + 1) - S) + S) * K =
      (1 + 1 + 1 + 1) * (S * Ni * H * K) - S * Ni * H * (S * K) + S * Ni * (S * K) := by
    noncomm_ring
  rw [e2, hK, mul_one, mul_one] at e1
  have e3 : (1 + 1 + 1 + 1) * (S * Ni * H * K) = 1 + S * Ni * H - S * Ni := by
    calc (1 + 1 + 1 + 1) * (S * Ni * H * K)
        = ((1 + 1 + 1 + 1) * (S * Ni * H * K) - S * Ni * H + S * Ni) + S * Ni * H - S * Ni := by abel
      _ = 1 + S * Ni * H - S * Ni := by rw [e1]
  calc Y + S * Ni * (H * Y - Y) = (1 + S * Ni * H - S * Ni) * Y := by noncomm_ring
    _ = (1 + 1 + 1 + 1) * (S * Ni * H * K) * Y := by rw [e3]
    _ = (1 + 1 + 1 + 1) * (S * Ni * H * K * Y) := by noncomm_ring

theorem hasFDerivAt_tauR (H X : Mat) (hN : IsUnit (H * ((1 + 1) + X) + ((1 + 1) - X)).det)
    (hS : IsUnit ((1 + 1) - X).det) :
    HasFDerivAt (tauR H) (ContinuousLinearMap.mulLeftRight ℝ Mat
      ((4 : ℂ) • (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * H * ((1 + 1) - X)⁻¹))
      ((4 : ℂ) • (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹)) X := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hN
  have hA : HasFDerivAt (fun Z : Mat => (1 + 1) - Z) (-ContinuousLinearMap.id ℝ Mat) X :=
    (hasFDerivAt_id X).const_sub _
  have hB := (((hasFDerivAt_const (1 + 1 : Mat) X).add (hasFDerivAt_id X)).const_mul H).add hA
  have hI : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ Mat ↑u⁻¹ ↑u⁻¹)
      (H * ((1 + 1) + X) + ((1 + 1) - X)) := by
    rw [← hu]; exact hasFDerivAt_ringInverse u
  have hC := hI.comp X hB
  have hD := ((hA.mul' hC).const_smul (4 : ℂ)).const_sub (1 + 1 : Mat)
  have hE : HasFDerivAt (tauR H) _ X := hD
  have hinv : (↑u⁻¹ : Mat) = (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  refine hE.congr_fderiv (ContinuousLinearMap.ext fun Y => ?_)
  have hNi := Matrix.nonsing_inv_mul _ hN
  have hK := Matrix.mul_nonsing_inv _ hS
  have k := key_alg H X Y _ _ hNi hK
  change -((4 : ℂ) • (((1 + 1) - X) * (-(Units.val u⁻¹ * (H * (0 + Y) + -Y) * Units.val u⁻¹)) +
      (-Y) * Ring.inverse (H * ((1 + 1) + X) + ((1 + 1) - X)))) =
    (4 : ℂ) • (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * H * ((1 + 1) - X)⁻¹) * Y *
      ((4 : ℂ) • (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹)
  rw [hinv, ← Matrix.nonsing_inv_eq_ringInverse, smul_four, smul_four, smul_four, zero_add]
  calc _ = (1 + 1 + 1 + 1) * ((Y + ((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * (H * Y - Y)) *
          (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹) := by noncomm_ring
    _ = (1 + 1 + 1 + 1) * (((1 + 1 + 1 + 1) * (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ *
          H * ((1 + 1) - X)⁻¹ * Y)) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹) := by rw [k]
    _ = _ := by noncomm_ring

end Deriv

section Sub

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem tauDeriv_at (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q)
    (hn : IsUnit (nH h (x : Mat)).det) :
    ∃ f' : lieU P Q →L[ℝ] lieU P Q,
      (∀ Y : lieU P Q, ((f' Y : lieU P Q) : Mat) = chA h (x : Mat) * (Y : Mat) * chB h (x : Mat)) ∧
      HasFDerivAt (tauL h) f' x := by
  set ι : lieU P Q →L[ℝ] Mat := (lieU P Q).subtypeL with hι
  set L : Mat →L[ℝ] Mat :=
    ContinuousLinearMap.mulLeftRight ℝ Mat (chA h (x : Mat)) (chB h (x : Mat)) with hL
  have hM : HasFDerivAt (tauR (UpqT.mat h)) L (ι x) := hasFDerivAt_tauR (UpqT.mat h) (x : Mat) hn hx
  have c1 : Continuous fun y : lieU P Q => (1 + 1) - ι y := continuous_const.sub ι.continuous
  have c2 : Continuous fun y : lieU P Q => UpqT.mat h * ((1 + 1) + ι y) + ((1 + 1) - ι y) :=
    (continuous_const.mul (continuous_const.add ι.continuous)).add (continuous_const.sub ι.continuous)
  have hev : ∀ᶠ y in 𝓝 x, IsUnit ((1 + 1) - ι y) ∧
      IsUnit (UpqT.mat h * ((1 + 1) + ι y) + ((1 + 1) - ι y)) := by
    filter_upwards [c1.continuousAt.preimage_mem_nhds
        (Units.isOpen.mem_nhds ((Matrix.isUnit_iff_isUnit_det _).2 hx)),
      c2.continuousAt.preimage_mem_nhds
        (Units.isOpen.mem_nhds ((Matrix.isUnit_iff_isUnit_det _).2 hn))] with y h1 h2
    exact ⟨h1, h2⟩
  have heq : (fun y : lieU P Q => ((tauL h y : lieU P Q) : Mat)) =ᶠ[𝓝 x]
      (tauR (UpqT.mat h) ∘ ι) := by
    filter_upwards [hev] with y hy
    have hyD : y ∈ D0 P Q := (Matrix.isUnit_iff_isUnit_det _).1 hy.1
    have hyN : IsUnit (nH h (y : Mat)).det := (Matrix.isUnit_iff_isUnit_det _).1 hy.2
    have hu : IsUnit (UpqT.mat (h * cayF P Q y) + 1).det := by
      have e := hyN
      rw [nH_eq h y hyD, det_mul] at e
      exact isUnit_of_mul_isUnit_left e
    rw [tauL_val h y hyD hu, Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hF : HasFDerivAt (fun y : lieU P Q => ((tauL h y : lieU P Q) : Mat)) (L.comp ι) x :=
    (HasFDerivAt.comp x hM ι.hasFDerivAt).congr_of_eventuallyEq heq
  have hclosed : IsClosed ((lieU P Q : Set Mat)) := (lieU P Q).isClosed_of_finiteDimensional
  have hmem : ∀ Y, (L.comp ι) Y ∈ lieU P Q := by
    intro Y
    exact hclosed.mem_of_tendsto (hF.lim_real Y) (Eventually.of_forall fun c =>
      (lieU P Q).smul_mem c ((lieU P Q).sub_mem (tauL h _).2 (tauL h x).2))
  refine ⟨(L.comp ι).codRestrict (lieU P Q) hmem, fun Y => ?_, ?_⟩
  · have hLY : L (ι Y) = chA h (x : Mat) * ι Y * chB h (x : Mat) :=
      ContinuousLinearMap.mulLeftRight_apply _ _ _ _ _
    exact hLY
  · have hF' := hasFDerivAt_iff_isLittleO_nhds_zero.1 hF
    refine hasFDerivAt_iff_isLittleO_nhds_zero.2 ?_
    rw [← Asymptotics.isLittleO_norm_left] at hF' ⊢
    refine hF'.congr_left fun k => ?_
    rfl

end Sub

theorem tau_derivative : TauDeriv := fun _ _ h x hx hn => tauDeriv_at h x hx hn

end HcInf
end
end
