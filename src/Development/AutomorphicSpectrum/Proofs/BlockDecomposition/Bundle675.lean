module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle658
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle667
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
public import GroundTheory.AutomorphicForms.AnisotropicUnitaryRes
public import GroundTheory.AutomorphicForms.Bundle006
public import GroundTheory.AutomorphicForms.Bundle015
public import GroundTheory.AutomorphicForms.ReductionMahler
public import GroundTheory.AutomorphicForms.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle825
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle290
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle666
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology


theorem _root_.GlobalTheory.T.torus_archimedean_frame_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → (∀ i, 0 < t i) → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (β : FrameIx r), archMat σ J τ (projArch σ J w a) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = ((frameWt t β : ℝ) : ℂ) • (frameIdem (σ : E →+* E) J X Y β).map τ.1 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.torus_mul_frameIdem | exact GlobalTheory.CompanionTheory.RapidDecay.torus_mul_frameIdem | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.torus_mul_frameIdem <;> assumption)
end

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

theorem hE_mulVec_self {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J M : Matrix (Fin n) (Fin n) E) (hM : cT (σ : E →+* E) M * J * M = J) (w : Fin n → E) :
    hE σ J (M *ᵥ w) (M *ᵥ w) = hE σ J w w := by
  have key : ∀ x y : Fin n → E, hE σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_assoc]
  have hs : (fun i => σ ((M *ᵥ w) i)) = (M.map (σ : E →+* E)) *ᵥ (fun i => σ (w i)) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) M w i
  rw [key, key, hs, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  have : (M.map (σ : E →+* E))ᵀ *ᵥ ((J * M) *ᵥ w) = J *ᵥ w := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
    have h := hM
    unfold cT at h
    rw [h]
  rw [this]

theorem exists_sends_hE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w := by
  intro F E _ _ _ _ _ σ _ n J _ γ hγ w
  obtain ⟨M, hM, e⟩ := hγ
  refine ⟨(M : Matrix (Fin n) (Fin n) E) *ᵥ w, ?_, hE_mulVec_self σ J _ hM w⟩
  have e' : (matHom _ σ J γ).1 = (M : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    have := congrArg (fun g : GL (Fin n) (AF F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) e
    exact this.symm
  unfold Sends
  rw [e']
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) (M : Matrix (Fin n) (Fin n) E) w i).symm

end GlobalTheory.CompanionTheory.RedCov

end
end

section

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)


variable (F E n) in
abbrev dimN : ℕ := Fintype.card (Fin n × Fin (Module.finrank F E))

def trG : GAd σ J →* GL (Fin (dimN F E n)) (AF F) :=
  (trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (matHom (AF F) σ J)


variable (F) in
def cvec (v : Fin n → E) : Fin (dimN F E n) → F := fun p =>
  (Module.finBasis F E).repr (v ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
    ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2

theorem cvec_injective : Function.Injective (cvec F : (Fin n → E) → Fin (dimN F E n) → F) := by
  intro u v h
  funext i
  apply (Module.finBasis F E).repr.injective
  ext k
  simpa [cvec] using congrFun h (Fintype.equivFin (Fin n × Fin (Module.finrank F E)) (i, k))

theorem cvec_surjective : Function.Surjective (cvec F : (Fin n → E) → Fin (dimN F E n) → F) := by
  intro x
  refine ⟨fun i => (Module.finBasis F E).equivFun.symm fun k => x (Fintype.equivFin _ (i, k)), ?_⟩
  funext p
  simp [cvec, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]

theorem cvec_ne_zero {v : Fin n → E} (hv : v ≠ 0) : cvec F v ≠ 0 := by
  intro h
  apply hv
  apply cvec_injective (F := F)
  rw [h]
  funext p
  simp [cvec]

theorem ratVec_cvec (v : Fin n → E) :
    Reduction.ratVec (cvec F v) = resVec (ι := Fin n) (Module.finBasis F E) (AF F) (ratV F v) := by
  funext p
  simp only [Reduction.ratVec, cvec, resVec, Function.comp_apply, coordsVec, coords, ratV, inclR]
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem hv_eq (ξ : Fin n → AF F ⊗[F] E) :
    hv ξ = Reduction.adelicNorm (resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ) := rfl

theorem hgt_eq (g : GAd σ J) (v : Fin n → E) : hgt σ J g v = Reduction.height (trG σ J g) (cvec F v) := by
  rw [Reduction.height, ratVec_cvec, trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hgt, hv_eq, map_inv]

section Top

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

theorem continuous_trG : Continuous (trG σ J) :=
  (continuous_trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (isEmbedding_matHom (AF F) σ J).continuous

end Top

theorem exists_hgt_le {C : Set (GAd σ J)} (hC : IsCompact C) {v : Fin n → E} (hv : v ≠ 0) :
    ∃ B : ℝ, ∀ c ∈ C, hgt σ J c v ≤ B := by
  obtain ⟨P, -, hP⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hC.image (continuous_trG σ J))
  refine ⟨P * Reduction.adelicNorm (Reduction.ratVec (cvec F v)), fun c hc => ?_⟩
  rw [hgt_eq]
  exact hP _ ⟨c, hc, rfl⟩ _ (Reduction.hasFiniteContent_ratVec (cvec_ne_zero hv))

end GlobalTheory.CompanionTheory.RedCov.Bridge
end
end

section

noncomputable section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic GroundTheory.Automorphic.Reduction

section NearMin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ}

def ratCoords [Algebra.IsQuadraticExtension F E] (u : Fin n → E) :
    Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F :=
  resVec (Module.finBasis F E) F (fun i => inclR (F := F) F (u i))

theorem hv_eq_adelicNorm_resVec [Algebra.IsQuadraticExtension F E] (ξ : Fin n → AF F ⊗[F] E) :
    hv (F := F) (E := E) ξ = adelicNorm (resVec (Module.finBasis F E) (AF F) ξ) := rfl

theorem ratCoords_ne_zero [Algebra.IsQuadraticExtension F E] {u : Fin n → E} (hu : u ≠ 0) :
    ratCoords (F := F) u ≠ 0 := by
  intro h0
  apply hu
  have h1 : (fun i => inclR (F := F) F (u i)) = fun _ : Fin n => (0 : F ⊗[F] E) := by
    apply resVec_injective (Module.finBasis F E) F
    rw [show resVec (Module.finBasis F E) F (fun i => inclR (F := F) F (u i)) = 0 from h0]
    funext p
    simp [resVec, coordsVec]
  funext i
  have h2 := congrFun h1 i
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective
    (h2.trans (map_zero _).symm)

theorem resVec_ratV [Algebra.IsQuadraticExtension F E] (u : Fin n → E) :
    resVec (Module.finBasis F E) (AF F) (ratV F u) = ratVec (ratCoords (F := F) u) := by
  have h := resVec_baseMap (Module.finBasis F E) (Algebra.ofId F (AF F))
    (fun i => inclR (F := F) F (u i))
  have e : (fun i => baseMap (Algebra.ofId F (AF F)) (inclR (F := F) F (u i))) = ratV F u := by
    funext i
    simp [ratV, inclR, baseMap]
  rw [e] at h
  rw [h]
  rfl

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem exists_pos_le_hgt [Algebra.IsQuadraticExtension F E] (g : GAd σ J) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Fin n → E, u ≠ 0 → c ≤ hgt σ J g u := by
  set T := trHom (Module.finBasis F E) (AF F) (matHom _ σ J g) with hT
  obtain ⟨P, hP, h⟩ := exists_adelicNorm_vecMul_le_mul (K := F) (C := {T⁻¹}) isCompact_singleton
  refine ⟨1 / P, one_div_pos.2 hP, fun u hu => ?_⟩
  have hx := ratCoords_ne_zero (F := F) hu
  have e2 : hgt σ J g u = adelicNorm (ratVec (ratCoords (F := F) u) ᵥ* (T : Matrix (Fin (Fintype.card (Fin n × Fin (Module.finrank F E))))
      (Fin (Fintype.card (Fin n × Fin (Module.finrank F E)))) (AF F))) := by
    rw [hT, ← resVec_ratV, resVec_vecMul_trHom, ← hv_eq_adelicNorm_resVec, hgt, map_inv]
  have h3 := h T⁻¹ rfl _ ((hasFiniteContent_ratVec hx).vecMul T)
  rw [← e2, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one] at h3
  rw [div_le_iff₀ hP, mul_comm]
  exact (one_le_adelicNorm_ratVec hx).trans h3

end NearMin

theorem exists_isotropic_of_isWittFrame {F E : Type} [Field F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin (r + 1)) E} (h : IsWittFrame σ J X Y) :
    ∃ v : Fin n → E, v ≠ 0 ∧ hE σ J v v = 0 := by
  refine ⟨Xᵀ 0, fun h0 => ?_, ?_⟩
  · have h1 := congrFun (congrFun h.xy 0) 0
    have hc : ∀ i, X i 0 = 0 := fun i => congrFun h0 i
    simp [cT, Matrix.mul_apply, hc] at h1
  · have h1 := congrFun (congrFun h.xx 0) 0
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Matrix.zero_apply] at h1
    rw [Finset.sum_comm] at h1
    simpa [hE, Formalism.UG.hform] using h1

theorem exists_nearMin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ g : GAd σ J, ∃ v, NearMin σ J g v := by
  intro F E _ _ _ _ _ σ hCM n J _ r X Y hW g
  haveI : Algebra.IsQuadraticExtension F E := ⟨hCM.2.2.1⟩
  obtain ⟨c, hc, hlow⟩ := exists_pos_le_hgt σ J g
  obtain ⟨v₀, hv₀, hi₀⟩ := exists_isotropic_of_isWittFrame hW
  let S : Set ℝ := {t | ∃ u : Fin n → E, u ≠ 0 ∧ hE σ J u u = 0 ∧ t = hgt σ J g u}
  have hne : S.Nonempty := ⟨_, v₀, hv₀, hi₀, rfl⟩
  have hbdd : BddBelow S := ⟨c, by rintro _ ⟨u, hu, -, rfl⟩; exact hlow u hu⟩
  have hm : c ≤ sInf S := le_csInf hne (by rintro _ ⟨u, hu, -, rfl⟩; exact hlow u hu)
  have hm0 : 0 < sInf S := hc.trans_le hm
  obtain ⟨_, ⟨v, hv, hi, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (show sInf S < 2 * sInf S by linarith)
  refine ⟨v, hv, hi, fun u hu hiu => ?_⟩
  have : sInf S ≤ hgt σ J g u := csInf_le hbdd ⟨u, hu, hiu, rfl⟩
  linarith

end GlobalTheory.CompanionTheory.RedCov

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov


open GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume Module in
theorem exists_ratPts_sends_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ v : Fin n → E, v ≠ 0 → hE σ J v v = 0 → ∃ γ ∈ ratPts σ J, Sends σ J γ (Xᵀ 0) v := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW v hv hvv
  obtain ⟨hF, hEc, h2, hc⟩ := hσ
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  have hH : IsHermitianFor (conjHom F E) J := Matrix.ext fun i j => hJ.1 i j
  obtain ⟨h, hg, hform⟩ : ∃ h : HermitianForm F E (Fin n → E), gram h.toSesq (Pi.basisFun E (Fin n)) = J ∧
      ∀ x y, h.toSesq x y = hE (conj F E).toAlgHom J x y :=
    ⟨HermitianForm.ofGram J hH hu, gram_ofGram J hH hu, fun x y => rfl⟩
  have key : ∀ A B : Matrix (Fin n) (Fin (r + 1)) E, h.toSesq (Aᵀ 0) (Bᵀ 0) =
      (cT (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) A * J * B) 0 0 := by
    intro A B
    rw [hform]
    simp only [hE, Formalism.UG.hform, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hxx : h.toSesq (Xᵀ 0) (Xᵀ 0) = 0 := by rw [key, hW.xx]; rfl
  have hyy : h.toSesq (Yᵀ 0) (Yᵀ 0) = 0 := by rw [key, hW.yy]; rfl
  have hxy : h.toSesq (Xᵀ 0) (Yᵀ 0) = 1 := by rw [key, hW.xy]; simp
  obtain ⟨w, hvw, hww⟩ := WittPartner.full h v hv (by rw [hform]; exact hvv)
  obtain ⟨g, hgv, -⟩ := HyperbolicPairTransitive.full h (Xᵀ 0) (Yᵀ 0) v w ⟨hxx, hyy, hxy⟩
    ⟨by rw [hform]; exact hvv, hww, hvw⟩
  obtain ⟨M, hM, hact⟩ : ∃ M : GL (Fin n) E, M ∈ Formalism.UG.UJ (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) J ∧
      (M : Matrix (Fin n) (Fin n) E) *ᵥ (Xᵀ 0) = v := by
    have h3 : ∀ N : GL (Fin n) E, N ∈ unitaryGroupMatrix (conjHom F E) (gram h.toSesq (Pi.basisFun E (Fin n))) →
        N ∈ Formalism.UG.UJ (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) J := by
      rw [hg]
      exact fun N hN => hN
    refine ⟨_, h3 _ (unitaryGroupEquivMatrix h (Pi.basisFun E (Fin n)) g).2, ?_⟩
    rw [unitaryGroupEquivMatrix_apply, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_mulVec]
    exact hgv
  refine ⟨ratEmb _ J ⟨M, hM⟩, by rw [← range_ratEmb]; exact ⟨_, rfl⟩, ?_⟩
  unfold Sends
  funext i
  rw [← hact]
  have e : (matHom _ _ J (ratEmb _ J ⟨M, hM⟩)).1 = (M : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := rfl
  rw [e]
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ _ i).symm

end GlobalTheory.CompanionTheory.RedCov

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc.Cos GlobalTheory.CompanionTheory.ThetaProd

namespace GlobalTheory.CompanionTheory.JacTheta

theorem nonempty_jac_comp_thetaW : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    Nonempty ((_root_.GlobalTheory.SmGL.jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((_root_.GlobalTheory.SmGL.jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d))) := by
  intro k _ _ _ _ h N d hd hd' V _ _ π
  exact ⟨GlobalTheory.CompanionTheory.JmThetaInv.jacCompThetaW d hd hd' π⟩

end GlobalTheory.CompanionTheory.JacTheta
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

noncomputable section

namespace GlobalTheory.CompanionTheory.SubEmb

theorem exists_injective_of_subsingleton {G V Y : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y] [Nontrivial Y] (π : Representation ℂ G V) (τ : Representation ℂ G Y)
    (hi : π.IsIrreducible) : ∃ φ : π.IntertwiningMap τ, Function.Injective φ := by
  classical
  haveI := hi
  haveI : Nontrivial V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : Y)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  let φ : π.IntertwiningMap τ :=
    { toFun := fun u => f u • w
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun c a => by simp [mul_smul]
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]
        exact LinearMap.ext fun _ => rfl }
  refine ⟨φ, (Representation.IsIrreducible.injective_or_eq_zero φ).resolve_right fun h => ?_⟩
  have h1 : f v • w = 0 := congrArg (fun ψ : π.IntertwiningMap τ => ψ v) h
  exact (smul_ne_zero hf hw) h1

theorem zero_case {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin 0) k) V) (hi : π.IsIrreducible)
    (x : Fin 0 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = 0) :
    ∃ φ : π.IntertwiningMap (prodIrr x hd), Function.Injective φ := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  have hirr : (prodIrr x hd).IsIrreducible := GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr
  exact exists_injective_of_subsingleton π _ hi

theorem succ_case
    (hstage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t), Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b c : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W')
    (hb : 0 < b) (hρs : IsSmooth ρ) (hρi : ρ.IsIrreducible) (hρc : IsCuspidal ρ)
    (x' : Fin c → IrrGL (k := k)) (hd' : ∑ i, (x' i).1 = a) (hcusp : ∀ i, (x' i).IsCusp)
    (f : σ.IntertwiningMap (prodIrr x' hd')) (hf : Function.Injective f) :
    ∃ (c' : ℕ) (x : Fin c' → IrrGL (k := k)) (hd : ∑ i, (x i).1 = a + b), (∀ i, (x i).IsCusp) ∧
      ∃ Φ : (prod₂ σ ρ).IntertwiningMap (prodIrr x hd), Function.Injective Φ := by
  have hF0 := GlobalTheory.CompanionTheory.ProdInj.prod₂_map_injective k a b _ _ W' σ _ ρ f hf
  obtain ⟨F, hF⟩ := hF0
  let y : Fin 1 → IrrGL (k := k) := fun _ => IrrGL.of ρ hρs hρi
  have hy : ∑ i, (y i).1 = b := by simp [y, IrrGL.of]
  have hy' : ∑ i : Fin 1, (IrrGL.of ρ hρs hρi).1 = (IrrGL.of ρ hρs hρi).1 := by simp
  have e₁0 := nonempty_equiv_prodIrr_one (IrrGL.of ρ hρs hρi) hy'
  obtain ⟨e₁⟩ := e₁0
  have e₂ : ρ.Equiv (prodIrr y hy) := (IrrGL.equivOf ρ hρs hρi).trans e₁
  have hd : ∑ i, (Fin.append x' y i).1 = a + b := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hd', hy]
  have e₃0 := hstage k c 1 a b x' y hd' hy hd
  obtain ⟨e₃⟩ := e₃0
  refine ⟨c + 1, Fin.append x' y, hd, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hcusp i
    · rw [Fin.append_right]; exact IrrGL.isCusp_of.2 ⟨hb, hρc⟩
  · let E := (prod₂Equiv (Representation.Equiv.refl _) e₂).trans e₃
    refine ⟨E.toIntertwiningMap.comp F, ?_⟩
    exact E.toLinearEquiv.injective.comp hF

theorem subEmbedding_of_stage
    (hstage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t), Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h))) :
    Ysupp.SubEmbedding := by
  intro k _ _ _ _ N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ π hs hi
    by_cases hN0 : N = 0
    · subst hN0
      exact ⟨0, Fin.elim0, by simp, fun a => a.elim0, zero_case π hi _ _⟩
    · have hN : 0 < N := Nat.pos_of_ne_zero hN0
      have h0 := GlobalTheory.JacFactor.exists_map_jac₂ k N V π hs hi hN
      obtain ⟨a, b, h, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩ := h0
      subst h
      have h1 := GlobalTheory.CompanionTheory.Frob.exists_injective_of_jac₂ k a b V W W' π σ ρ hs hi φ hφ
      obtain ⟨ψ, hψ⟩ := h1
      have h2 := ih a (by omega) W σ hσs hσi
      obtain ⟨c, x', hd', hcusp, f, hf⟩ := h2
      have h3 := succ_case hstage σ ρ hb hρs hρi hρc x' hd' hcusp f hf
      obtain ⟨c', x, hd, hx, Φ, hΦ⟩ := h3
      exact ⟨c', x, hd, hx, Φ.comp ψ, hΦ.comp hψ⟩

end GlobalTheory.CompanionTheory.SubEmb
end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.contragredient_segment_product_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (Δ.term a).1 = N), ∃ hd' : ∑ a, (dec (segDual Δ) a).1 = N, Nonempty ((contra (prodIrr Δ.term hd)).Equiv (prodIrr (dec (segDual Δ)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.SegIncDual.contra_prodIrr_term | exact GlobalTheory.CompanionTheory.SegIncDual.contra_prodIrr_term | (intros; apply GlobalTheory.CompanionTheory.SegIncDual.contra_prodIrr_term <;> assumption)
end
