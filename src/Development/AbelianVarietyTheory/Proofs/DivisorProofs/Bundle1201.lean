module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle034
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle809
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SkewLagr

open Matrix

theorem det_hyp {L : Type*} [CommRing L] (m : ℕ) :
    (fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0).det = (-1) ^ m := by
  have h : fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0 =
      (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks (-1) 0 0 1 :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    simp [fromBlocks_multiply]
  rw [h, det_mul, det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]
  simp [det_neg]

theorem exists_isLagr_of_local (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {L : Type} [Field L] [Algebra (v.adicCompletion F) L]
    [Algebra.IsQuadraticExtension (v.adicCompletion F) L]
    (c : L →ₐ[v.adicCompletion F] L) (hc : ∀ x, c (c x) = x) {δ : L} (hδ : δ ≠ 0) (hcδ : c δ = -δ)
    (m : ℕ) (J : Matrix (Fin (m + m)) (Fin (m + m)) L) (hJ : ∀ i j, c (J j i) = -J i j)
    (hd : J.det ≠ 0) (hx : ∃ x, J.det = x * c x) :
    ∃ Cy : Matrix (Fin (m + m)) (Fin m) L, GlobalTheory.WeilM.IsLagr c J Cy := by
  classical
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨x, hx⟩ := hx
  let σ : L ≃ₐ[v.adicCompletion F] L := AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)
  have hσc : ∀ y, σ y = c y := fun _ => rfl
  have h2 : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap (v.adicCompletion F) L) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hσ : σ ≠ 1 := by
    intro h
    have h1 : c δ = δ := by rw [← hσc, h]; rfl
    apply hδ
    have : (2 : L) * δ = 0 := by linear_combination hcδ - h1
    exact (mul_eq_zero.1 this).resolve_left h2
  let e : Fin m ⊕ Fin m ≃ Fin (m + m) := finSumFinEquiv
  let Hyp : Matrix (Fin (m + m)) (Fin (m + m)) L :=
    (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).submatrix e.symm e.symm
  let H : Matrix (Fin (m + m)) (Fin (m + m)) L := δ • J
  have hH : ∀ a b, σ (H a b) = H b a := by
    intro a b
    simp only [H, Matrix.smul_apply, smul_eq_mul, hσc, map_mul, hcδ, hJ]
    ring
  have hHyp : ∀ a b, σ (Hyp a b) = Hyp b a := by
    intro a b
    simp only [Hyp, submatrix_apply]
    rcases e.symm a with i | i <;> rcases e.symm b with j | j <;>
      by_cases hij : i = j <;> simp [fromBlocks, one_apply, hij, eq_comm]
  have hdH : H.det = δ ^ (m + m) * J.det := by simp [H, det_smul]
  have hdHyp : Hyp.det = (-1) ^ m := by simp [Hyp, det_submatrix_equiv_self, det_hyp]
  have hs : ((-1 : L) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  obtain ⟨P, hP, hPeq⟩ := (GlobalTheory.HermLocal.congr_iff_adicCompletion F v L σ hσ hH hHyp
    (by rw [hdH]; exact mul_ne_zero (pow_ne_zero _ hδ) hd) (by rw [hdHyp]; simp)).2 ⟨δ ^ m * x, by
      rw [hdH, hdHyp, div_eq_iff (by simp), hx, hσc, map_mul, map_pow, hcδ, neg_pow]
      linear_combination (-(δ ^ (m + m) * x * c x)) * hs⟩
  have hQ : ∀ a b, δ * (Pᵀ * J * P.map c) a b = Hyp a b := by
    intro a b
    rw [hPeq]
    simp only [H, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    rfl
  have hiso : ∀ (f : Fin m → Fin m ⊕ Fin m), (∀ a b, Hyp (e (f a)) (e (f b)) = 0) →
      (P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c = 0 := by
    intro f hf
    ext a b
    have h1 : ((P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c) a b =
        (Pᵀ * J * P.map c) (e (f a)) (e (f b)) := rfl
    rw [h1, Matrix.zero_apply]
    have h3 := hQ (e (f a)) (e (f b))
    rw [hf] at h3
    exact (mul_eq_zero.1 h3).resolve_left hδ
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hcols : fromCols (P.submatrix id (fun j => e (Sum.inl j))) (P.submatrix id (fun j => e (Sum.inr j))) =
      P.submatrix id e := by
    ext i (j | j) <;> rfl
  refine ⟨P.submatrix id (fun j => e (Sum.inl j)), hiso Sum.inl (fun a b => by simp [Hyp]),
    P.submatrix id (fun j => e (Sum.inr j)), P⁻¹.submatrix e id, hiso Sum.inr (fun a b => by simp [Hyp]), ?_, ?_⟩
  · rw [hcols, submatrix_mul_equiv, mul_nonsing_inv P hPu, submatrix_id_id]
  · rw [hcols, show (P⁻¹.submatrix e id) = P⁻¹.submatrix e (Equiv.refl _) from rfl,
      show P.submatrix id e = P.submatrix (Equiv.refl _) e from rfl, submatrix_mul_equiv,
      nonsing_inv_mul P hPu, submatrix_one_equiv]

end GlobalTheory.SkewLagr

namespace GlobalTheory.SkewLagr

open Matrix

theorem exists_isLagr_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)), IsField (Fv F v ⊗[F] E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Even n → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 →
    (∃ x : Fv F v ⊗[F] E, (1 : Fv F v) ⊗ₜ[F] J.det = x * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ x) →
    ∃ Cy : Matrix (Fin n) (Fin (n / 2)) (Fv F v ⊗[F] E),
      IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) J) Cy := by
  intro F E _ _ _ _ _ σ hcm v hF n J hn hJ hd hx
  obtain ⟨m, rfl⟩ := hn
  rw [show (m + m) / 2 = m by omega]
  letI : Field (Fv F v ⊗[F] E) := hF.toField
  haveI : Algebra.IsQuadraticExtension (Fv F v) (Fv F v ⊗[F] E) :=
    { finrank_eq_two' := by rw [Module.finrank_baseChange]; exact hcm.2.2.1 }
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ y, σ (σ y) = y := fun y => τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  obtain ⟨t, ht⟩ : ∃ t, σ t ≠ t := by
    by_contra h
    push_neg at h
    have hw := hcm.2.1.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hw
    apply hw
    ext y
    have hy := hcm.2.2.2 τ y
    rw [h] at hy
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [starRingEnd_apply]
    exact hy.symm
  set c := Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ with hcdef
  have hct : ∀ y : E, c ((1 : Fv F v) ⊗ₜ[F] y) = (1 : Fv F v) ⊗ₜ[F] σ y := fun y => by
    simp [c, Algebra.TensorProduct.map_tmul]
  have hc : ∀ z, c (c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [c, Algebra.TensorProduct.map_tmul, hσσ]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hinj : Function.Injective (inclR (Fv F v) : E →+* Fv F v ⊗[F] E) := RingHom.injective _
  have hincl : ∀ y : E, inclR (Fv F v) y = (1 : Fv F v) ⊗ₜ[F] y := fun _ => rfl
  have hδ : (1 : Fv F v) ⊗ₜ[F] (t - σ t) ≠ 0 := by
    rw [← hincl]
    exact (map_ne_zero_iff _ hinj).2 (sub_ne_zero.2 (Ne.symm ht))
  have hcδ : c ((1 : Fv F v) ⊗ₜ[F] (t - σ t)) = -((1 : Fv F v) ⊗ₜ[F] (t - σ t)) := by
    rw [hct, map_sub, hσσ, ← TensorProduct.tmul_neg, neg_sub]
  have hdet : (JR (Fv F v) J).det = (1 : Fv F v) ⊗ₜ[F] J.det := by
    rw [← hincl, RingHom.map_det]
    rfl
  refine exists_isLagr_of_local F v c hc hδ hcδ m (JR (Fv F v) J) (fun i j => ?_) ?_ ?_
  · change c (inclR (Fv F v) (J j i)) = -inclR (Fv F v) (J i j)
    rw [hincl, hincl, hct, hJ, TensorProduct.tmul_neg]
  · rw [hdet, ← hincl]
    exact (map_ne_zero_iff _ hinj).2 hd
  · rw [hdet]
    exact hx

end GlobalTheory.SkewLagr
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisLineF

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cAF_incAF (σ : E →ₐ[F] E) (x : E) : cAF σ (incAF F E x) = incAF F E (σ x) := by
  simp [cAF, incAF, sigR, inclR]

theorem cAF_cAF (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : AEF F E) : cAF σ (cAF σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cAF, sigR, hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem trace_cAF (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : AEF F E) :
    Algebra.trace (AF F) (AEF F E) (cAF σ a) = Algebra.trace (AF F) (AEF F E) a := by
  let f : AEF F E →ₐ[AF F] AEF F E := Algebra.TensorProduct.map (AlgHom.id _ _) σ
  have hf : ∀ a, f a = cAF σ a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [f, cAF, sigR]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hff : f.comp f = AlgHom.id _ _ := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hf, hf, cAF_cAF σ hσ]; rfl
  let g : AEF F E ≃ₐ[AF F] AEF F E := AlgEquiv.ofAlgHom f f hff hff
  rw [← hf]
  exact Algebra.trace_eq_of_algEquiv g a

theorem herm_sum {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P : Fin m → Fin m → A)
    (Q : Fin n → Fin n → A) (hP : ∀ i k, σ (P i k) = P k i) (hQ : ∀ i k, σ (Q i k) = Q k i)
    (x y : Matrix (Fin n) (Fin m) A) :
    σ (∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a) =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (x c b) * Q c d * y d a := by

  simp only [map_sum, map_mul, hσ, hP, hQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem inv_herm (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (i k : Fin n) :
    σ (J⁻¹ i k) = J⁻¹ k i := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have hT : Jᵀ = J.map σ := by
    ext i j
    simp [Matrix.transpose_apply, hJ.1 j i]
  have h1 : J⁻¹.map σ * Jᵀ = 1 := by
    rw [hT, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]
    simp
  have h2 : (Jᵀ)⁻¹ = J⁻¹.map σ := Matrix.inv_eq_left_inv h1
  rw [← Matrix.transpose_nonsing_inv] at h2
  have := congrFun (congrFun h2 i) k
  simpa [Matrix.transpose_apply] using this.symm

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

theorem hOF_herm (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (x y : WOF F E nS nT) :
    cAF σ (hOF σ JS JT x y) = hOF σ JS JT y x :=
  herm_sum (cAF σ) (cAF_cAF σ hσ) (fun i k => incAF F E (JS⁻¹ i k)) (fun i k => incAF F E (JT i k))
    (fun i k => by rw [cAF_incAF, inv_herm σ hS]) (fun i k => by rw [cAF_incAF, hT.1 k i]) x y

theorem symplOF_skew (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (hξ : σ ξ₀ = -ξ₀)
    (x y : WOF F E nS nT) : symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [← trace_cAF σ hσ (incAF F E ξ₀ * hOF σ JS JT x y), map_mul (cAF σ), cAF_incAF, hξ, hOF_herm σ JS JT hσ hS hT,
    map_neg, neg_mul, map_neg, neg_neg]

theorem symplOF_add_left (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (x + x') y = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x' y := by
  unfold symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOF_add_right (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ x (y + y') = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x y' := by
  unfold symplOF hOF
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_add_left (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (x + x') y = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x' y := by
  unfold symplOHF; rw [symplOF_add_left, mul_add]

theorem symplOHF_add_right (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x (y + y') = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y' := by
  unfold symplOHF; rw [symplOF_add_right, mul_add]

theorem symplOF_zero_right (ξ₀ : E) (x : WOF F E nS nT) : symplOF σ JS JT ξ₀ x 0 = 0 := by
  have := symplOF_add_right σ JS JT ξ₀ x 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem symplOF_self (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (hξ : σ ξ₀ = -ξ₀)
    (x : WOF F E nS nT) : symplOF σ JS JT ξ₀ x x = 0 := by
  have h := symplOF_skew σ JS JT hσ hS hT ξ₀ hξ x x
  have h2 : (2 : AF F) * symplOF σ JS JT ξ₀ x x = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  have hu : IsUnit (2 : AF F) := by
    have : (2 : AF F) = algebraMap F (AF F) 2 := (map_ofNat _ 2).symm
    rw [this]
    exact (isUnit_iff_ne_zero.mpr two_ne_zero).map _
  exact hu.mul_right_eq_zero.mp h2

theorem continuous_symplOF_left (ξ₀ : E) (y : WOF F E nS nT) :
    Continuous fun x : WOF F E nS nT => symplOF σ JS JT ξ₀ x y := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  refine ht.comp (continuous_const.mul ?_)
  unfold hOF
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ =>
    continuous_finsetSum _ fun d _ => continuous_const.mul (continuous_id.matrix_elem d a)

omit [Algebra F E] [Field E] [NumberField E] in
theorem line_zero (g : ℝ →+ AF F) (hg : Continuous g) (t : ℝ) (ht : g t = 0) (u : ℝ) : g (u * t) = 0 := by
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have hq : ∀ r : ℚ, g ((r : ℝ) * t) = 0 := by
    intro r
    have hden : (r.den : ℝ) * ((r : ℝ) * t) = (r.num : ℝ) * t := by
      rw [← mul_assoc]
      congr 1
      have := congrArg (Rat.cast : ℚ → ℝ) (Rat.den_mul_eq_num r)
      push_cast at this
      exact this
    have h1 : r.den • g ((r : ℝ) * t) = 0 := by
      rw [← map_nsmul, nsmul_eq_mul, hden, ← zsmul_eq_mul, map_zsmul, ht, smul_zero]
    have hu : IsUnit ((r.den : ℕ) : AF F) := by
      have : ((r.den : ℕ) : AF F) = algebraMap F (AF F) (r.den : F) := (map_natCast _ _).symm
      rw [this]
      exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast r.den_nz)).map _
    rw [nsmul_eq_mul] at h1
    exact hu.mul_right_eq_zero.mp h1
  have : (fun u : ℝ => g (u * t)) = fun _ => 0 :=
    Rat.denseRange_cast.equalizer (hg.comp (continuous_id.mul continuous_const)) continuous_const (funext hq)
  exact congrFun this u

end GlobalTheory.HeisLineF

open GlobalTheory.HeisLineF in
theorem GlobalTheory.heisOF_line_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ) (w : Formalism.IndefR.DatumF.WOF F E nS nT) (s t : ℝ),
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L (s + t)) f w = B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L s)) * Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L s) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ _ L hL _ f w s t
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have key : Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ (L s) (L t) = 0 := by
    by_cases ht : t = 0
    · rw [ht, map_zero L, symplOF_zero_right]
    · let g : ℝ →+ AF F := AddMonoidHom.mk' (fun u => Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ (L u) (L t))
        (fun a b => by simp only [map_add L, symplOF_add_left])
      have hg : Continuous g := (continuous_symplOF_left σ JS JT ξ₀ (L t)).comp hL
      have h0 : g t = 0 := symplOF_self σ JS JT hσ hS hT ξ₀ hξ (L t)
      have := line_zero g hg t h0 (s / t)
      rwa [div_mul_cancel₀ s ht] at this
  have k2 : Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (L s) (L t) = 0 := by
    unfold Formalism.IndefR.DatumF.symplOHF; rw [key, mul_zero]
  unfold Formalism.IndefR.DatumF.heisOF
  rw [map_add L, symplOHF_add_right, symplOHF_add_left, k2, add_zero, AddChar.map_add_eq_mul, add_assoc, mul_assoc]
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisDerivCM

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symplOHF_add_left (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (x + x') y = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x' y := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem map_symplOHF_eq_zero {B : Type} [CommRing B] [Algebra F B] (p : AF F →ₐ[F] B)
    (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y : WOF F E nS nT)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0) :
    p (symplOHF σ JS JT ξ₀ x y) = 0 := by
  have h1 : p (symplOF σ JS JT ξ₀ x y) = 0 := by
    unfold symplOF hOF
    rw [GlobalTheory.WeilVacMove.sum_reorder (cAF σ) (fun k i => incAF F E (JS⁻¹ k i)) (fun j l => incAF F E (JT j l)) x y]
    refine GlobalTheory.FockCompare.map_trace_sesq_eq_zero p σ _ (fun k i => incAF F E (JS⁻¹ k i))
      (fun j l => incAF F E (JT j l)) xᵀ yᵀ (h.imp (fun h => ?_) fun h => ?_) <;>
    · ext i j
      exact congrFun (congrFun h j) i
  unfold symplOHF
  rw [map_mul, h1, mul_zero]

theorem symplOHF_fin_real (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u v : WOF F E nS nT)
    (hu : u.map (infPartF F E) = 0) (hv : v.map (finPartF F E) = 0) :
    symplOHF σ JS JT ξ₀ u v = 0 ∧ symplOHF σ JS JT ξ₀ v u = 0 :=
  ⟨Prod.ext (map_symplOHF_eq_zero (fstA F) σ JS JT ξ₀ u v (Or.inl hu))
      (map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ u v (Or.inr hv)),
    Prod.ext (map_symplOHF_eq_zero (fstA F) σ JS JT ξ₀ v u (Or.inr hu))
      (map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ v u (Or.inl hv))⟩

theorem heisOF_deriv_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ u : Formalism.IndefR.DatumF.WOF F E nS nT, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) f = f →
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) (fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0) = fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f L _ hL u hu hf
  funext w
  have key : ∀ t : ℝ, B.ψ (symplOHF σ JS JT ξ₀ w u) * heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u) =
      heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    obtain ⟨h1, h2⟩ := symplOHF_fin_real σ JS JT ξ₀ u (L t) hu (hL t)
    have hfx := congrFun hf (w + L t)
    simp only [heisOF] at hfx ⊢
    conv_rhs => rw [← hfx]
    rw [symplOHF_add_left, symplOHF_add_left, h1, h2, add_zero, add_zero,
      show w + u + L t = w + L t + u by abel]
    ring
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u)) 0 = _
  rw [← deriv_const_mul_field]
  exact congrArg (fun g : ℝ → ℂ => deriv g 0) (funext key)

end GlobalTheory.HeisDerivCM
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColLie

theorem fockS_eq_colDer_of_same_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i = ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = (GlobalTheory.ColLie.colDer τ Y : Module.End ℂ (PolF D b a)) + (((b : ℂ) / 2) * Y.trace) • 1 := by
  intro D a b τ ε ε' Y h
  have hs : ∀ (i : Fin b) (j k : Fin a), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ ε ε' i j * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ ε ε' i k =
      (LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j) : PolF D b a) ∘ₗ
        (MvPolynomial.pderiv (τ, i, k)).toLinearMap : Module.End ℂ (PolF D b a)) := by
    intro i j k
    have hjk : ε j = ε k := (h i j).symm.trans (h i k)
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε j) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε k) = 1 := by
      rw [hjk]; unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn; split_ifs <;> simp
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO
    rw [if_pos (h i j), if_pos (h i k), smul_mul_smul_comm, h1, one_smul]
    rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS GlobalTheory.ColLie.colDer
  simp only [hs, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  congr 1
  · rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin b)))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
  · simp only [smul_ite, smul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory.ColLie
end
