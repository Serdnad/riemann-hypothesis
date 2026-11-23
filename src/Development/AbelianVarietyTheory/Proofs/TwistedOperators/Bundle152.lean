module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentLeviMatrixActionIdentity
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle009
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_leftInverse_isotropicFrame_killing_embedding : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 ∧ K * B = 0 := by
  first | exact @GlobalTheory.HalfAverage.exists_leftInv_frame_kill_emb | exact GlobalTheory.HalfAverage.exists_leftInv_frame_kill_emb | (intros; apply GlobalTheory.HalfAverage.exists_leftInv_frame_kill_emb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x' := by
  first | exact @GlobalTheory.TowerForm.symplOH_isoPart_add_midPart | exact GlobalTheory.TowerForm.symplOH_isoPart_add_midPart | (intros; apply GlobalTheory.TowerForm.symplOH_isoPart_add_midPart <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 ∧ adj D C' * V.gram * C' = 0 ∧ adj D C' * V.gram * B = 0 := by
  first | exact @GlobalTheory.TwistDual.exists_isotropic_dual | exact GlobalTheory.TwistDual.exists_isotropic_dual | (intros; apply GlobalTheory.TwistDual.exists_isotropic_dual <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rationalLevi_scaling_isotropicFrame : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ a : GA D V, a ∈ GQ V ∧ HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) ∧ HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) ∧ (2 : AE D) • HMul.hMul (matHom V a).1 (C'.map (incA D)) = C'.map (incA D) := by
  first | exact @GlobalTheory.LeviScale.exists_levi_scale | exact GlobalTheory.LeviScale.exists_levi_scale | (intros; apply GlobalTheory.LeviScale.exists_levi_scale <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_levi_matrix_action_identity : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ a : GA D V, HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) → HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) → (2 : AE D) • HMul.hMul (matHom V a).1 (C'.map (incA D)) = C'.map (incA D) → ∀ g : GA D V, HMul.hMul ((matHom V g).1 - 1) (C.map (incA D)) = 0 → HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D)) ((matHom V g).1 - 1) = 0 → (∀ x : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec x = 0 → ∃ y : Fin r → AE D, ((matHom V g).1 - 1).mulVec (fun i => incA D (x i)) = (C.map (incA D)).mulVec y) → ∃ m : GA D V, m ∈ NI V C ∧ g = a * m * a⁻¹ * m⁻¹ := by
  first | exact @GlobalTheory.UnipLevi.commutator_levi | exact GlobalTheory.UnipLevi.commutator_levi | (intros; apply GlobalTheory.UnipLevi.commutator_levi <;> assumption)
end

section

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ContrObj

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]

theorem norm_of_isIsoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem exists_riesz [CompleteSpace H₁] {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (φ : FF) (y : H₂) :
    ∃ w : H₁, ∀ x, ⟪x, w⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := by
  let ℓ : H₁ →L[ℂ] ℂ := ((innerₛₗ ℂ φ) ∘ₗ Tm.flip y).mkContinuous (‖φ‖ * ‖y‖) fun x => by
    have := norm_inner_le_norm (𝕜 := ℂ) φ (Tm x y)
    rw [norm_of_isIsoBilin hI] at this
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℂ H₁).surjective ℓ
  refine ⟨w, fun x => ?_⟩
  have h : ⟪w, x⟫_ℂ = ⟪φ, Tm x y⟫_ℂ := by
    have := congrArg (fun f : H₁ →L[ℂ] ℂ => f x) hw
    simpa [ℓ] using this
  rw [← inner_conj_symm, h, inner_conj_symm]

theorem existsUnique_isContr [CompleteSpace H₁] {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃! It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  choose w hw using exists_riesz hI
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) w ?_ ?_ ?_ ?_, fun φ y x => hw φ y x, ?_⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_add_right]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_smul_right]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp [hw, inner_add_right, inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_smul_right, inner_smul_left, mul_comm]
  · intro It hIt
    ext φ y
    exact ext_inner_left ℂ fun x => (hIt φ y x).trans (hw φ y x).symm

end Hilbert

theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  exact ⟨existsUnique_isContr hI, fun It hC => contrProps_of hI hE hC⟩

section Tensor

open MvPolynomial

variable {ι : Type} [Fintype ι] {σ : ι → Type} {Var : Type} (e : (Σ τ, σ τ) ≃ Var)

omit [Fintype ι] in
theorem emb_injective (i : ι) : Function.Injective fun s : σ i => e ⟨i, s⟩ :=
  e.injective.comp sigma_mk_injective

def res (α : Var →₀ ℕ) (i : ι) : σ i →₀ ℕ :=
  Finsupp.comapDomain (fun s : σ i => e ⟨i, s⟩) α (emb_injective e i).injOn

theorem res_sum (a : ∀ i, σ i →₀ ℕ) :
    res e (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) = a := by
  classical
  funext j
  ext s
  change (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) (e ⟨j, s⟩) = a j s
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · exact Finsupp.mapDomain_apply_of_injective (emb_injective e j) _ _
  · intro i _ hi
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨t, ht⟩
    exact hi (congrArg Sigma.fst (e.injective ht))
  · simp

variable {A B : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]

def tens (I : ∀ i, MvPolynomial (σ i) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) :
    MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i :=
  (basisMonomials Var ℂ).constr ℂ fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1)

theorem tens_prod (I : ∀ i, MvPolynomial (σ i) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) (P : ∀ i, MvPolynomial (σ i) ℂ) :
    tens e I (∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i)) = PiTensorProduct.map fun i => I i (P i) := by
  classical
  let pr : MultilinearMap (RingHom.id ℂ) (fun i : ι => MvPolynomial (σ i) ℂ) (MvPolynomial Var ℂ) :=
    (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun i => (rename (fun s : σ i => e ⟨i, s⟩) : MvPolynomial (σ i) ℂ →ₐ[ℂ] _).toLinearMap
  have hpr : ∀ P, pr P = ∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i) := fun P => by simp [pr]
  have key : (tens e I).compMultilinearMap pr
      = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap I := by
    refine Module.Basis.ext_multilinear (fun i => basisMonomials (σ i) ℂ) fun a => ?_
    simp only [LinearMap.compMultilinearMap_apply, hpr, coe_basisMonomials,
      MultilinearMap.compLinearMap_apply, PiTensorProduct.mapMultilinear_apply, rename_monomial]
    rw [← monomial_sum_one]
    have := (basisMonomials Var ℂ).constr_basis ℂ
      (fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1))
      (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i))
    rw [res_sum, coe_basisMonomials] at this
    exact this
  have := congrArg (fun f => f P) key
  simpa [hpr] using this

theorem tprod_ne_zero (v : ∀ i, B i) (hv : ∀ i, v i ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0
  simp [hl] at this

end Tensor

theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ I
  have h : IsTensorIt e I (tens e I) := fun P v => by
    rw [tens_prod, PiTensorProduct.map_tprod]
  refine ⟨tens e I, h, fun hI h0 => ?_⟩
  have hex : ∀ i, ∃ P v, I i P v ≠ 0 := by
    intro i
    by_contra hc
    push Not at hc
    exact hI i (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using hex
  have h1 := h P v
  rw [h0] at h1
  exact tprod_ne_zero _ hPv h1.symm

theorem contraction : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction := ⟨contrHilbert, contrTensor⟩

end GlobalTheory.ContrObj

end
end

section

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.Contr

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]


omit [CompleteSpace H₁] [CompleteSpace FF] in
theorem norm_isoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem exists_isContr {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃ It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  let L : H₂ → (H₁ →L[ℂ] FF) := fun y =>
    (Tm.flip y).mkContinuous ‖y‖ fun x => by simp [norm_isoBilin hI, mul_comm]
  let f : FF → H₂ → H₁ := fun φ y => ContinuousLinearMap.adjoint (L y) φ
  have hf : ∀ φ y x, ⟪x, f φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := fun φ y x => by
    simp only [f, ContinuousLinearMap.adjoint_inner_right]
    rfl
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) f ?_ ?_ ?_ ?_, hf⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, RingHom.id_apply]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf, map_add (f := _), inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, map_smul, inner_smul_left]


omit [CompleteSpace H₁] [CompleteSpace FF] in
theorem isContr_unique {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} {It It' : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁}
    (h : IsContr Tm It) (h' : IsContr Tm It') : It = It' := by
  ext φ y
  exact ext_inner_left ℂ fun x => by rw [h, h']

end Hilbert

theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  obtain ⟨It, hIt⟩ := exists_isContr hI
  exact ⟨⟨It, hIt, fun It' h' => isContr_unique h' hIt⟩, fun It' h' => contrProps_of hI hE h'⟩

theorem tprod_ne_zero_of_ne {ι : Type} [Fintype ι] {B : ι → Type} [∀ τ, AddCommGroup (B τ)]
    [∀ τ, Module ℂ (B τ)] (w : ∀ τ, B τ) (hw : ∀ τ, w τ ≠ 0) : PiTensorProduct.tprod ℂ w ≠ 0 := by
  classical
  have : ∀ τ, ∃ f : Module.Dual ℂ (B τ), f (w τ) ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hw τ ((Module.forall_dual_apply_eq_zero_iff ℂ (w τ)).1 hc)
  choose f hf using this
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f)) h
  simp [Finset.prod_eq_zero_iff, hf] at this

theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ Itl
  classical
  have hinj : ∀ τ, Function.Injective fun s : σ τ => e ⟨τ, s⟩ := fun τ =>
    e.injective.comp sigma_mk_injective
  let r : (Var →₀ ℕ) → ∀ τ, σ τ →₀ ℕ := fun m τ => m.comapDomain (fun s => e ⟨τ, s⟩) (hinj τ).injOn
  let It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ :=
    (MvPolynomial.basisMonomials Var ℂ).constr ℂ fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1)
  have hr : ∀ m : ∀ τ, σ τ →₀ ℕ, r (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩) = m := by
    intro m
    funext τ
    ext s
    simp only [r, Finsupp.comapDomain_apply, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single τ]
    · exact Finsupp.mapDomain_apply_of_injective (hinj τ) _ _
    · intro τ' _ hne
      apply Finsupp.mapDomain_notin_range
      rintro ⟨s', hs'⟩
      exact hne (congrArg Sigma.fst (e.injective hs'))
    · simp
  have key : It.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun τ => (MvPolynomial.rename (fun s : σ τ => e ⟨τ, s⟩)).toLinearMap) =
      (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap Itl := by
    apply Module.Basis.ext_multilinear fun τ => MvPolynomial.basisMonomials (σ τ) ℂ
    intro m
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials,
      MvPolynomial.rename_monomial, PiTensorProduct.mapMultilinear_apply]
    rw [← MvPolynomial.monomial_sum_one]
    have := (MvPolynomial.basisMonomials Var ℂ).constr_basis ℂ (fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1))
      (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩)
    rw [hr] at this
    simpa [It] using this
  have hT : IsTensorIt e Itl It := by
    intro P v
    have := congrArg (fun F => F P (PiTensorProduct.tprod ℂ v)) key
    simpa using this
  refine ⟨It, hT, fun hne h0 => ?_⟩
  have : ∀ τ, ∃ P v, Itl τ P v ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hne τ (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using this
  apply tprod_ne_zero_of_ne _ hPv
  rw [← hT P v, h0]
  rfl

theorem contraction : Contraction := ⟨contrHilbert, contrTensor⟩

end GlobalTheory.Contr

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  have := D.host.der.cm
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  have hc : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  apply ψ.injective
  rw [hc]
  exact NumberField.IsCMField.complexEmbedding_complexConj _ ψ x

theorem hT_zero_symm {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {x y : S.V}
    (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← S.herm.eq x y, h, map_zero]

theorem isDec_smul (D : D7) (t : D.host.E) :
    IsDec (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (fun _ : Fin 1 => t • D.sp.zm)
      (-(t * star t * ((D.mem D.u₀).A.T : D.host.E))) D.sp.hypE D.sp.hypF := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hsym : ∀ a b : (D.sp.Y 0).V, (D.sp.Y 0).hT a b = 0 → (D.sp.Y 0).hT b a = 0 :=
    fun a b h => hT_zero_symm (D.sp.Y 0) h
  refine
    { isom := D.sp.iXY_isom 0 hm
      a_le := le_rfl
      rank := ?_
      z_norm := ?_
      z_X := ?_
      ee := ?_
      ff := ?_
      ef := ?_
      hyp_X := ?_
      hyperbolicDecomp_hyp_orthogonal_line := ?_ }
  · rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.X_rank 0 (Nat.zero_le _)]
    obtain ⟨j, hj⟩ := D.R.m_even
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
    omega
  · intro i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, map_smul, D.sp.zm_norm, starRingEnd_apply, smul_eq_mul,
      D.sp_T]
    ring
  · intro i x
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, hsym _ _ (D.sp.zm_orth x), smul_zero]
  · intro i j
    exact D.sp.hyp_ee j i
  · intro i j
    exact D.sp.hyp_ff j i
  · intro i j
    simp only [HSpace.hD]
    rw [← (D.sp.Y 0).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
    split_ifs <;> simp
  · intro i x
    exact ⟨hsym _ _ (D.sp.hyp_orthX i x).1, hsym _ _ (D.sp.hyp_orthX i x).2⟩
  · intro i j
    simp only [HSpace.hD, map_smul, hsym _ _ (D.sp.hyp_orthz i).1, hsym _ _ (D.sp.hyp_orthz i).2, smul_zero,
      and_self]

theorem recordDec (D : D7) : RecordDecSt D := by
  refine ⟨fun u => ?_, ?_⟩
  · have hc0 := D.cOf_ne u
    have hc1 : D.host.conj (D.cOf u) ≠ 0 := (map_ne_zero _).2 hc0
    have h := isDec_smul D (D.cOf u)⁻¹
    have hs : -((D.cOf u)⁻¹ * star (D.cOf u)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -Tu D u := by
      rw [star_inv₀, star_eq_conj, ← D.cOf_eq u]
      field_simp
    rw [hs] at h
    exact h
  · obtain ⟨π, -, hπ, -⟩ := D.T_norm D.u₀
    have hT : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
      rw [← D.sp_T]
      exact_mod_cast D.sp.T_prime.ne_zero
    have hπ0 : (π : D.host.E) ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hπ
      exact hT hπ.symm
    have hπ1 : D.host.conj (π : D.host.E) ≠ 0 := (map_ne_zero _).2 hπ0
    refine ⟨(π : D.host.E)⁻¹ • D.sp.zm, ?_⟩
    have h := isDec_smul D (π : D.host.E)⁻¹
    have hs : -((π : D.host.E)⁻¹ * star (π : D.host.E)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -1 := by
      rw [star_inv₀, star_eq_conj, ← hπ]
      field_simp
    rw [hs] at h
    exact h

end GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : FinPl D → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT P → ∀ p : Place D, wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v = p) ∧ u - wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v ≠ p) ∧ ((∀ v, P v → Sum.inl v ≠ p) → wAt p u = 0) := by
  first | exact @GlobalTheory.LatticeLocal.wAt_mem_latO | exact GlobalTheory.LatticeLocal.wAt_mem_latO | (intros; apply GlobalTheory.LatticeLocal.wAt_mem_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.degree_one_prime_reduction_split_place_dictionary : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → (∃ r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP, Function.Surjective r ∧ (∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) ∧ (∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP), RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b) ∧ ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F, r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩) ∧ ∀ ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ, ∃ mu : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP mu ξ := by
  first | exact @GlobalTheory.PlaceRed.red_dict | exact GlobalTheory.PlaceRed.red_dict | (intros; apply GlobalTheory.PlaceRed.red_dict <;> assumption)
end
