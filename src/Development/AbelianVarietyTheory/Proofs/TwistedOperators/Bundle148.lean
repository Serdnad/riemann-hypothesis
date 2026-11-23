module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FrameStab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem incA_injective (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem mt_mul (W : HSp D) (g h : GA D W) : Formalism.L2.Theta.mt W (g * h) = Formalism.L2.Theta.mt W g * Formalism.L2.Theta.mt W h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_inv_mul (W : HSp D) (g : GA D W) : Formalism.L2.Theta.mt W g⁻¹ * Formalism.L2.Theta.mt W g = 1 := by
  rw [← mt_mul]; simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (W : HSp D) (g : GA D W) : Formalism.L2.Theta.mt W g * Formalism.L2.Theta.mt W g⁻¹ = 1 := by
  rw [← mt_mul]; simp [Formalism.L2.Theta.mt]

theorem mt_mul_frame (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (n : GA D W) (hn : n ∈ NI W L) :
    Formalism.L2.Theta.mt W n * L.map (incA D) = L.map (incA D) := by
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    have h1 : (Formalism.L2.Theta.mt W g - 1) * L.map (incA D) = 0 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  | one => simp [Formalism.L2.Theta.mt]
  | mul x y _ _ hx hy => rw [mt_mul, Matrix.mul_assoc, hy, hx]
  | inv x _ hx =>
    calc Formalism.L2.Theta.mt W x⁻¹ * L.map (incA D)
        = Formalism.L2.Theta.mt W x⁻¹ * (Formalism.L2.Theta.mt W x * L.map (incA D)) := by rw [hx]
      _ = L.map (incA D) := by rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]

theorem mt_conj_sub_one (W : HSp D) (γ m : GA D W) : Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1 =
    Formalism.L2.Theta.mt W γ * (Formalism.L2.Theta.mt W m - 1) * Formalism.L2.Theta.mt W γ⁻¹ := by
  rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]

theorem conj_sub_one_kills_frame_of_fixed (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (γ m : GA D W)
    (hΓiL : Formalism.L2.Theta.mt W γ⁻¹ * L.map (incA D) = L.map (incA D))
    (h1 : (Formalism.L2.Theta.mt W m - 1) * L.map (incA D) = 0) :
    (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) * L.map (incA D) = 0 := by
  rw [mt_conj_sub_one, Matrix.mul_assoc, hΓiL, Matrix.mul_assoc, h1, Matrix.mul_zero]

theorem rowFrame_mul_conj_sub_one_eq_zero_of_fixed (W : HSp D) {s : ℕ} (P : Matrix (Fin s) (Fin W.rank) D.host.E) (γ m : GA D W)
    (hPΓ : P.map (incA D) * Formalism.L2.Theta.mt W γ = P.map (incA D))
    (h2 : P.map (incA D) * (Formalism.L2.Theta.mt W m - 1) = 0) :
    P.map (incA D) * (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) = 0 := by
  rw [mt_conj_sub_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPΓ, h2, Matrix.zero_mul]

theorem conj_unipotentRadical_kernelCondition_of_rationalFixed (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (P : Matrix (Fin s) (Fin W.rank) D.host.E)
    (γ m : GA D W) (γ₀ γi : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (hγ₀ : Formalism.L2.Theta.mt W γ = γ₀.map (incA D)) (hγγi : γ₀ * γi = 1) (hPγi : P * γi = P)
    (hΓL : Formalism.L2.Theta.mt W γ * L.map (incA D) = L.map (incA D))
    (h3 : ∀ x : Fin W.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W m - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a)
    (x : Fin W.rank → D.host.E) (hx : P *ᵥ x = 0) : ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a := by
  have hy : P *ᵥ (γi *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, hPγi]; exact hx
  obtain ⟨a, ha⟩ := h3 _ hy
  refine ⟨a, ?_⟩
  have hyb : (fun i => incA D ((γi *ᵥ x) i)) = γi.map (incA D) *ᵥ (fun i => incA D (x i)) := by
    funext i; exact RingHom.map_mulVec (incA D) γi x i
  have hxb : Formalism.L2.Theta.mt W γ *ᵥ (fun i => incA D ((γi *ᵥ x) i)) = fun i => incA D (x i) := by
    rw [hyb, Matrix.mulVec_mulVec, hγ₀, ← Matrix.map_mul, hγγi, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hxi : Formalism.L2.Theta.mt W γ⁻¹ *ᵥ (fun i => incA D (x i)) = fun i => incA D ((γi *ᵥ x) i) := by
    rw [← hxb, Matrix.mulVec_mulVec, mt_inv_mul, Matrix.one_mulVec]
  rw [mt_conj_sub_one, ← Matrix.mulVec_mulVec, hxi, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, hΓL]

theorem stab : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L →
    (∀ γ ∈ GQ W, ∀ γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = γ₀.map (incA D) →
      γ₀ * L = L → ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) ∧
    (∀ n ∈ NI W L, ∀ n₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W n = n₀.map (incA D) →
      n₀ * L = L) := by
  intro D W s L _
  refine ⟨?_, fun n hn n₀ hn₀ => ?_⟩
  swap
  · apply Matrix.map_injective (incA_injective D)
    show (n₀ * L).map (incA D) = L.map (incA D)
    rw [Matrix.map_mul, ← hn₀]
    exact mt_mul_frame W L n hn
  intro γ hγ γ₀ hγ₀ hL
  obtain ⟨g, hg, e⟩ := hγ
  have hg0 : (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = γ₀ := by
    apply Matrix.map_injective (incA_injective D)
    show (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) = γ₀.map (incA D)
    rw [← hγ₀]
    exact congrArg Units.val e

  obtain ⟨σ, hσ⟩ : ∃ σ : D.host.E →+* D.host.E, σ = (D.sp.cm.sig : D.host.E →+* D.host.E) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = W.gram := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin s) (Fin W.rank) D.host.E, P = Formalism.UG.cT σ L * G := ⟨_, rfl⟩
  obtain ⟨γi, hγi⟩ : ∃ γi : Matrix (Fin W.rank) (Fin W.rank) D.host.E, γi = (g⁻¹ : GL (Fin W.rank) D.host.E).1 :=
    ⟨_, rfl⟩
  have hγγi : γ₀ * γi = 1 := by rw [← hg0, hγi]; exact Units.mul_inv g
  have hU : Formalism.UG.cT σ γ₀ * G * γ₀ = G := by rw [← hg0, hσ, hG]; exact hg
  have hPγ : P * γ₀ = P := by
    calc P * γ₀ = Formalism.UG.cT σ (γ₀ * L) * G * γ₀ := by rw [hL, hP]
      _ = Formalism.UG.cT σ L * (Formalism.UG.cT σ γ₀ * G * γ₀) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hU, hP]
  have hPγi : P * γi = P := by
    calc P * γi = P * γ₀ * γi := by rw [hPγ]
      _ = P := by rw [Matrix.mul_assoc, hγγi, Matrix.mul_one]

  have hΓL : Formalism.L2.Theta.mt W γ * L.map (incA D) = L.map (incA D) := by
    rw [hγ₀, ← Matrix.map_mul, hL]
  have hΓiL : Formalism.L2.Theta.mt W γ⁻¹ * L.map (incA D) = L.map (incA D) := by
    calc Formalism.L2.Theta.mt W γ⁻¹ * L.map (incA D)
        = Formalism.L2.Theta.mt W γ⁻¹ * (Formalism.L2.Theta.mt W γ * L.map (incA D)) := by rw [hΓL]
      _ = L.map (incA D) := by rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have hPΓ : P.map (incA D) * Formalism.L2.Theta.mt W γ = P.map (incA D) := by
    rw [hγ₀, ← Matrix.map_mul, hPγ]
  have hPΓi : P.map (incA D) * Formalism.L2.Theta.mt W γ⁻¹ = P.map (incA D) := by
    calc P.map (incA D) * Formalism.L2.Theta.mt W γ⁻¹
        = P.map (incA D) * Formalism.L2.Theta.mt W γ * Formalism.L2.Theta.mt W γ⁻¹ := by rw [hPΓ]
      _ = P.map (incA D) := by rw [Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

  have key : NI W L ≤ (NI W L).comap (MulAut.conj γ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun m hm => ?_
    have h1 : (Formalism.L2.Theta.mt W m - 1) * L.map (incA D) = 0 := hm.1
    have h2 : P.map (incA D) * (Formalism.L2.Theta.mt W m - 1) = 0 := by
      have := hm.2.1
      rw [hP, hσ, hG]; exact this
    have h3 : ∀ x : Fin W.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W m - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a := by
      rw [hP, hσ, hG]; exact hm.2.2
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨conj_sub_one_kills_frame_of_fixed W L γ m hΓiL h1, ?_, ?_⟩
    · have := rowFrame_mul_conj_sub_one_eq_zero_of_fixed W P γ m hPΓ h2
      rw [hP, hσ, hG] at this; exact this
    · intro x hx
      rw [← hG, ← hσ, ← hP] at hx
      exact conj_unipotentRadical_kernelCondition_of_rationalFixed W L P γ m γ₀ γi hγ₀ hγγi hPγi hΓL h3 x hx
  intro n hn
  exact key hn

end GlobalTheory.FrameStab
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InvTransposeIso

def ctr {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) : GL n A →* GL m A where
  toFun g := ⟨((g⁻¹).1ᵀ).submatrix e.symm e.symm, (g.1ᵀ).submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.submatrix_one_equiv],
    by rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.submatrix_one_equiv]⟩
  map_one' := Units.ext (by ext i j; simp [Matrix.one_apply])
  map_mul' g h := Units.ext (by
    show (((g * h)⁻¹).1ᵀ).submatrix e.symm e.symm =
      ((g⁻¹).1ᵀ).submatrix e.symm e.symm * ((h⁻¹).1ᵀ).submatrix e.symm e.symm
    rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, ← Units.val_mul, _root_.mul_inv_rev])

theorem ctr_val {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : (ctr e g).1 = ((g⁻¹).1ᵀ).submatrix e.symm e.symm := rfl

theorem ctr_inv_val {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : ((ctr e g)⁻¹).1 = (g.1ᵀ).submatrix e.symm e.symm := rfl

theorem ctr_ctr {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : ctr e.symm (ctr e g) = g :=
  Units.ext (by rw [ctr_val, ctr_inv_val]; ext i j; simp)

theorem key_rel {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (c : A →+* A)
    {H Hi K : Matrix n n A} (hHi : H * Hi = 1) (hK : Hi = -Kᵀ) (g : GL n A)
    (hg : (g.1.map c)ᵀ * H * g.1 = H) :
    (((g⁻¹).1ᵀ).map c)ᵀ * K * (g⁻¹).1ᵀ = K := by
  have hHiH : Hi * H = 1 := mul_eq_one_comm.1 hHi
  have h1 : g.1.map c * (g⁻¹).1.map c = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hY : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H = 1 := by
    calc (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H
        = (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * ((g.1.map c)ᵀ * H * g.1) := by rw [hg]
      _ = (g⁻¹).1 * Hi * (g.1.map c * (g⁻¹).1.map c)ᵀ * H * g.1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [h1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc _ Hi H, hHiH, Matrix.mul_one,
            Units.inv_mul]
  have hY' : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ = Hi := by
    calc _ = (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * (H * Hi) := by rw [hHi, Matrix.mul_one]
      _ = Hi := by rw [← Matrix.mul_assoc, hY, Matrix.one_mul]
  have hKt : Kᵀ = -Hi := by rw [hK, neg_neg]
  apply Matrix.transpose_injective
  rw [Matrix.transpose_map]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hKt, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hY']

theorem reindex_rel {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : A →+* A) (e : n ≃ m) {J : Matrix m m A} {M : Matrix n n A}
    (h : (M.map c)ᵀ * J.submatrix e e * M = J.submatrix e e) :
    ((M.submatrix e.symm e.symm).map c)ᵀ * J * M.submatrix e.symm e.symm = J := by
  have hJ : J = (J.submatrix e e).submatrix e.symm e.symm := by ext i j; simp
  have hM : ((M.submatrix e.symm e.symm).map c)ᵀ = ((M.map c)ᵀ).submatrix e.symm e.symm := rfl
  rw [hM]
  conv_lhs => rw [hJ]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h, ← hJ]

theorem ctr_rel {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : A →+* A) (e : n ≃ m) {H Hi : Matrix n n A} {J : Matrix m m A} (hHi : H * Hi = 1)
    (hK : Hi = -(Jᵀ.submatrix e e)) (g : GL n A) (hg : Formalism.UG.cT c g.1 * H * g.1 = H) :
    Formalism.UG.cT c (ctr e g).1 * J * (ctr e g).1 = J :=
  reindex_rel c e (key_rel c hHi hK g hg)

theorem inv_rel {K : Type} [Field K] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n K) (B : Matrix m m K) (e : n ≃ m) (h : A⁻¹ = -(Bᵀ.submatrix e e)) (hA : IsUnit A.det) :
    B⁻¹ = -(Aᵀ.submatrix e.symm e.symm) := by
  have h1 : A * -(Bᵀ.submatrix e e) = 1 := by rw [← h]; exact Matrix.mul_nonsing_inv A hA
  have h2 : -(B.submatrix e e) * Aᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.transpose_submatrix, Matrix.transpose_transpose,
      Matrix.transpose_one] at this
    exact this
  have h3 : Aᵀ * -(B.submatrix e e) = 1 := mul_eq_one_comm.1 h2
  have h4 : Aᵀ.submatrix e.symm e.symm * -B = 1 := by
    calc Aᵀ.submatrix e.symm e.symm * -B
        = Aᵀ.submatrix e.symm e.symm * (-(B.submatrix e e)).submatrix e.symm e.symm := by
          congr 1; ext i j; simp
      _ = (Aᵀ * -(B.submatrix e e)).submatrix e.symm e.symm := Matrix.submatrix_mul_equiv _ _ _ _ _
      _ = 1 := by rw [h3, Matrix.submatrix_one_equiv]
  exact Matrix.inv_eq_left_inv (by rw [Matrix.neg_mul, ← Matrix.mul_neg]; exact h4)

end GlobalTheory.InvTransposeIso

namespace GlobalTheory.InvTransposeIso

variable {D : D7}

theorem gram_inv_rel {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    W.gram⁻¹ = -(V.gramᵀ.submatrix e.symm e.symm) :=
  inv_rel V.gram W.gram e h (Formalism.L2.Theta.gram_det_ne V).isUnit

theorem mem_HR {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : ctr e (matHom V g) ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
  have hdet : IsUnit V.gram.det := (Formalism.L2.Theta.gram_det_ne V).isUnit
  have hHi : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK : (V.gram⁻¹).map (incA D) = -(((W.gram.map (incA D))ᵀ).submatrix e e) := by
    rw [h]; ext i j; simp
  exact ctr_rel (cA D) e hHi hK (matHom V g) g.2

theorem mem_UJ {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (r : GL (Fin V.rank) D.host.E) (hr : r ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    ctr e r ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := by
  have hdet : IsUnit V.gram.det := (Formalism.L2.Theta.gram_det_ne V).isUnit
  exact ctr_rel _ e (Matrix.mul_nonsing_inv _ hdet) h r hr

def fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    GA D V →* GA D W where
  toFun g := (⟨ctr e (matHom V g), mem_HR e h g⟩ : HR (AF D.host.F) D.sp.cm.sig W.gram)
  map_one' := Subtype.ext (by simp only [map_one]; rfl)
  map_mul' g g' := Subtype.ext (by simp only [map_mul]; rfl)

theorem mt_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : Formalism.L2.Theta.mt W (fwd e h g) = ((Formalism.L2.Theta.mt V g⁻¹)ᵀ).submatrix e.symm e.symm := by
  show (ctr e (matHom V g)).1 = _
  rw [ctr_val, ← map_inv]; rfl

end GlobalTheory.InvTransposeIso

namespace GlobalTheory.InvTransposeIso

variable {D : D7}

def iso {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    GA D V ≃* GA D W :=
  { fwd e h with
    invFun := fwd e.symm (gram_inv_rel e h)
    left_inv := fun g => Subtype.ext (ctr_ctr e g.1)
    right_inv := fun g => Subtype.ext (ctr_ctr e.symm g.1) }

theorem continuous_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    Continuous (fwd e h) := by
  have hv : Continuous fun g : GA D V => (matHom V g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun g : GA D V => ((matHom V g)⁻¹).1 :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun g : GA D V => (((matHom V g)⁻¹).1ᵀ).submatrix e.symm e.symm
    exact hi.matrix_transpose.matrix_submatrix _ _
  · show Continuous fun g : GA D V => ((matHom V g).1ᵀ).submatrix e.symm e.symm
    exact hv.matrix_transpose.matrix_submatrix _ _

theorem fwd_GQ {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (γ : GA D V) (hγ : γ ∈ GQ V) : fwd e h γ ∈ GQ W := by
  obtain ⟨r, hr, hrγ⟩ := (Subgroup.mem_subgroupOf.1 hγ : γ.1 ∈
    HFin (AF D.host.F) D.sp.cm.sig V.gram)
  refine Subgroup.mem_subgroupOf.2 ⟨ctr e r, mem_UJ e h r hr, ?_⟩
  show Formalism.UG.bc (inclR (AF D.host.F)) (ctr e r) = ctr e γ.1
  rw [← hrγ]
  exact Units.ext (by ext i j; rfl)

theorem suppAt_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (a : AE D) (g : GA D V) (hg : SuppAt a V g) : SuppAt a W (fwd e h g) := by
  have hYG : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    simp only [Formalism.L2.Theta.mt]
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hsub : Formalism.L2.Theta.mt V g⁻¹ - 1 = -(Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g - 1)) := by
    rw [Matrix.mul_sub, hYG, Matrix.mul_one, neg_sub]
  intro i j
  have hij : (Formalism.L2.Theta.mt W (fwd e h g) - 1) i j = (Formalism.L2.Theta.mt V g⁻¹ - 1) (e.symm j) (e.symm i) := by
    rw [mt_fwd]
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.one_apply,
      e.symm.injective.eq_iff, eq_comm]
  rw [hij, hsub, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k (e.symm i)]

theorem det_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : (Formalism.L2.Theta.mt W (fwd e h g)).det = (Formalism.L2.Theta.mt V g⁻¹).det := by
  rw [mt_fwd, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

theorem sub_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : (Formalism.L2.Theta.mt W (fwd e h g)).submatrix e e = (Formalism.L2.Theta.mt V g⁻¹)ᵀ := by
  rw [mt_fwd]; ext i j; simp

theorem grp_contra : ∀ (D : D7) (T S' : HSp D) (e₂ : Fin S'.rank ≃ Fin T.rank), S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) →
    ∃ φ : GA D S' ≃* GA D T, Continuous φ ∧ (∀ γ ∈ GQ S', φ γ ∈ GQ T) ∧
      (∀ g, (Formalism.L2.Theta.mt T (φ g)).submatrix e₂ e₂ = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ) ∧
      (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) ∧ ∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det := by
  intro D T S' e₂ h
  exact ⟨iso e₂ h, continuous_fwd e₂ h, fun γ hγ => fwd_GQ e₂ h γ hγ, sub_fwd e₂ h,
    fun a g hg => suppAt_fwd e₂ h a g hg, det_fwd e₂ h⟩

end GlobalTheory.InvTransposeIso
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompStab

theorem idem_mul {R : Type} [CommRing R] {n : ℕ} (φ : R) (hφ : φ * φ = φ) (A B : Matrix (Fin n) (Fin n) R)
    (h : A * B = 1) : (φ • A + (1 - φ) • (1 : Matrix (Fin n) (Fin n) R)) * (φ • B + (1 - φ) • 1) = 1 := by
  have h1 : φ * (1 - φ) = 0 := by rw [mul_sub, mul_one, hφ, sub_self]
  have h2 : (1 - φ) * φ = 0 := by rw [mul_comm, h1]
  have h3 : (1 - φ) * (1 - φ) = 1 - φ := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, hφ, zero_smul, mul_one, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem map_idem {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (f : R)
    (M : Matrix (Fin n) (Fin n) R) :
    (f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)).map ψ = ψ f • M.map ψ + (1 - ψ f) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add (f := _),
    map_mul, map_sub, map_one]
  split_ifs <;> simp

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem comp_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (φ : Formalism.L2.Herm.intAf F E) (hφ : φ * φ = φ)
    (x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hS : x ∈ St β)
    (h : x'.1 = (φ : E ⊗[F] Formalism.L2.Herm.Af F) • x.1 + (1 - (φ : E ⊗[F] Formalism.L2.Herm.Af F)) • 1) : x' ∈ St β := by
  obtain ⟨y, rfl⟩ := hS
  refine ⟨⟨φ • y.1 + (1 - φ) • 1, φ • (y⁻¹).1 + (1 - φ) • 1, idem_mul φ hφ _ _ y.mul_inv,
    idem_mul φ hφ _ _ y.inv_mul⟩, Units.ext ?_⟩
  rw [h]
  show β.1 * (φ • y.1 + (1 - φ) • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))).map
      (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 =
    (φ : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * y.1.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) + _
  rw [map_idem, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Units.mul_inv]
  rfl

theorem comm_int {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E}
    (hz : z ∈ AddSubgroup.closure {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) :
    (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E z : E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.intAf F E := by
  refine AddSubgroup.closure_induction (p := fun z _ =>
    (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E z : E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨a, ha, x, rfl⟩
    have : (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E (a ⊗ₜ[F] (x : E)) : E ⊗[F] Formalism.L2.Herm.Af F) =
        ((oToS F E x : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * ((1 : E) ⊗ₜ[F] a) := by
      rw [oToS_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]; rfl
    rw [this]
    exact Subring.mul_mem _ (oToS F E x).2 (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
  · rw [map_zero]; exact Subring.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add (f := _)]; exact Subring.add_mem _ ha hb
  · intro a _ ha
    rw [map_neg]; exact Subring.neg_mem _ ha

end General

theorem component_mem_St : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g g' : GA D V) (f : AE D), f * f = f → finE V g ∈ St β → Formalism.L2.Theta.mt V g' = f • Formalism.L2.Theta.mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → finE V g' ∈ St β := by
  intro D V β g g' f hf hg h
  let ψ : AE D →+* Lev.EAf D := (swapAE D).comp (finPart D)
  have hi : ψ f ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    comm_int (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D f) (by rw [← RingHom.map_mul, hf]))
  refine comp_mem_St β ⟨ψ f, hi⟩ (Subtype.ext ?_) (finE V g) _ hg ?_
  · show ψ f * ψ f = ψ f
    rw [← RingHom.map_mul, hf]
  · show (Formalism.L2.Theta.mt V g').map ψ = ψ f • (Formalism.L2.Theta.mt V g).map ψ + (1 - ψ f) • 1
    rw [h, map_idem]

end GlobalTheory.CompStab

end
end
