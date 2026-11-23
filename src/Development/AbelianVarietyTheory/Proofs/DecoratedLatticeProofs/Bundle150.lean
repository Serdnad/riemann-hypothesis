module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle129
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}

def conjJAt (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) : X.Vpi u →ₗ[ℂ] ℂ where
  toFun η := star (tr.J η z)
  map_add' η η' := by simp [map_add (f := _)]
  map_smul' c η := by simp [map_smulₛₗ]

def rieszJ (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) : X.Vpi u :=
  (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap (conjJAt tr z))

theorem inner_rieszJ (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) (η : X.Vpi u) :
    ⟪η, rieszJ tr z⟫_ℂ = tr.J η z := by
  rw [← inner_conj_symm]
  simp [rieszJ, conjJAt]


variable (X) in
def RepM (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h : X.B.I.Gf) (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) : Prop :=
  ∀ j, X.B.I.fmat h *ᵥ Formalism.L2.SG.ColDict.qA X wt j = ∑ i, ιA.symm (M i j) • Formalism.L2.SG.ColDict.qA X wt i

end GlobalTheory.Core.Mi

end

namespace GlobalTheory.Core.Mi

section Helpers

variable {D : D7}

theorem unitaryAdelicPointFiniteMatrix_base_space_mul (a b : GA D (D.sp.X 0)) :
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a * b) =
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) b := by
  unfold GlobalTheory.AdForm.finM Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul, Matrix.map_mul]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem unitaryAdelicPointFiniteMatrix_base_space_one : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (1 : GA D (D.sp.X 0)) = 1 := by
  unfold GlobalTheory.AdForm.finM Formalism.L2.Theta.mt
  simp [Matrix.reindex_apply]

theorem unitaryAdelicPointInfiniteMatrices_base_space_mul (θ : InfFam D) (a b : GA D (D.sp.X 0)) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a * b) τ =
      GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) b τ := by
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = M.map ((θ τ).comp (infPart D)) := fun M => rfl
  rw [e, e, e, map_mul, Units.val_mul, Matrix.map_mul]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem unitaryAdelicPointInfiniteMatrices_base_space_one (θ : InfFam D) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (1 : GA D (D.sp.X 0)) τ = 1 := by
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = M.map ((θ τ).comp (infPart D)) := fun M => rfl
  rw [e, map_one, Units.val_one]
  simp [Matrix.reindex_apply]

theorem unitaryAdelicPointInfiniteMatrices_eq_one_of_finite (θ : InfFam D) (a : GA D (D.sp.X 0)) (ha : a ∈ GfC (D.sp.X 0)) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = 1 := by
  have h1 : Formalism.L2.Theta.infHom (D.sp.X 0) a = 1 := ha
  unfold Formalism.L2.Theta.infHom at h1
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have h2 := congrArg (fun x : GL (Fin (D.sp.X 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => ((x.1).map (θ τ))) h1
  simp only [MonoidHom.comp_apply, Units.val_one] at h2
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = (M.map (infPart D)).map (θ τ) := fun M => by ext; rfl
  rw [e]
  have h3 : ((Formalism.L2.Theta.matHom (D.sp.X 0)) a).1.map (infPart D) =
      ((Formalism.UG.bc (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom)
        ((Formalism.L2.Theta.matHom (D.sp.X 0)) a) : GL _ _).1 := rfl
  rw [h3, h2]
  simp [Matrix.reindex_apply]

end Helpers

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

theorem toH_mul {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D}
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) (a b : GA D A) :
    B.toH (a * b) = B.toH a * B.toH b := by
  unfold SBes.toH
  ext <;> simp [map_mul]

theorem RepM_cancel {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {wt : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {ιA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F}
    {h k : X.B.I.Gf} {A M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)}
    (hA : RepM X wt ιA h A) (hAM : RepM X wt ιA (h * k) (A * M)) : RepM X wt ιA k M := by
  intro j
  have hmul : X.B.I.fmat (h * k) = X.B.I.fmat h * X.B.I.fmat k := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have hinv : X.B.I.fmat h⁻¹ * X.B.I.fmat h = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : X.B.I.fmat h *ᵥ (X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j) =
      X.B.I.fmat h *ᵥ (∑ l, ιA.symm (M l j) • Formalism.L2.SG.ColDict.qA X wt l) := by
    rw [Matrix.mulVec_mulVec, ← hmul, hAM j, Matrix.mulVec_sum]

    simp only [Matrix.mulVec_smul, hA, Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hA l, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]
  calc X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j
      = X.B.I.fmat h⁻¹ *ᵥ (X.B.I.fmat h *ᵥ (X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j)) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = X.B.I.fmat h⁻¹ *ᵥ (X.B.I.fmat h *ᵥ (∑ l, ιA.symm (M l j) • Formalism.L2.SG.ColDict.qA X wt l)) := by rw [key]
    _ = _ := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

theorem span_rieszJ {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (tr : Formalism.L2.SG.ColDict.Transport X u F) :
    Submodule.span ℂ (Set.range fun y => rieszJ tr (F.val0.eY y)) = ⊤ := by
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro η hη
  apply tr.J_injective c
  rw [map_zero]
  funext z
  obtain ⟨y, rfl⟩ := F.val0.eY.surjective z
  rw [← inner_rieszJ]
  exact (Submodule.mem_orthogonal' _ _).1 hη _ (Submodule.subset_span ⟨y, rfl⟩)

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

theorem colDictL_eY_symm {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (c : (D.mem u).C.cls 0)
    (w : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) :
    Formalism.L2.SG.ColDict.colDictL X tr hK T c (F.val0.eY.symm w) = tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) w := by
  have : Formalism.L2.SG.ColDict.colDictL X tr hK T c (F.val0.eY.symm w) =
      tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) (F.val0.eY (F.val0.eY.symm w)) := rfl
  rw [this, Equiv.apply_symm_apply]

end GlobalTheory.Core.Mi
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → IsClosed {x | InBox K x} ∧ Continuous (realSize θ : Mx D m n → ℝ) ∧ (∀ N, Measurable (maj θ K N)) ∧ ∀ R : ℝ, IsCompact {x | InBox K x ∧ realSize θ x ≤ R}) ∧ ∀ (m n k : ℕ) (x : Matrix (Fin m) (Fin n) D.host.E), LinearIndependent D.host.E x.transpose → ∀ K : Set (Mx D m k), IsCompact K → ∃ K' : Set (Mx D n k), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ u : Mx D n k, maj θ K N ((rat x : Mx D m n) ⬝ u) ≤ C * maj θ K' N u := by
  first | exact @GlobalTheory.Unf.maj_measurable_rat | exact GlobalTheory.Unf.maj_measurable_rat | (intros; apply GlobalTheory.Unf.maj_measurable_rat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open GlobalTheory.PlaceModel

namespace GlobalTheory.ProdForm

def iterForm {D : D7} {S A B T : HSp D} (o : OrthDec S A B) (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ)
    (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ) : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
  ℓA ∘ₗ LinearMap.pi fun a => ℓB ∘ₗ LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b))

theorem iterForm_boxS {D : D7} {S A B T : HSp D} (o : OrthDec S A B) (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ)
    (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ) (fA : WO A T → ℂ) (fB : WO B T → ℂ) :
    iterForm o ℓA ℓB (o.boxS T fA fB) = ℓA fA * ℓB fB := by
  have h : (LinearMap.pi fun a => ℓB ∘ₗ LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b)))
      (o.boxS T fA fB) = ℓB fB • fA := by
    funext a
    have : (LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b))) (o.boxS T fA fB) = fA a • fB := by
      funext b
      simp [LinearMap.funLeft_apply, OrthDec.boxS]
    simp [this, mul_comm]
  rw [iterForm, LinearMap.comp_apply, h, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.ProdForm

namespace GlobalTheory.ProdForm

theorem exists_product_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), ∀ e, IsSplitIdem D e → ∀ (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ) (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ), (∀ u : WO A T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ A T f → ℓA (heisO ψ A T u f) = ℓA f) → (∀ u : WO B T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ B T f → ℓB (heisO ψ B T u f) = ℓB f) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → ℓ (o.boxS T fA fB) = ℓA fA * ℓB fB := by
  intro D ψ hψ S A B T o e hs ℓA ℓB hA hB
  classical
  obtain ⟨he, hec, v, ε, hε, heq⟩ := id hs
  have hs' := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  have he' : cA D e * cA D e = cA D e := hs'.1
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have c2 : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.LatVac.cA_cA, hec]

  have hresA : ∀ u : WO S T, u ∈ half S T (cA D e) → ∀ i j, cA D e * (o.resS T u).1 i j = (o.resS T u).1 i j := by
    intro u hu i j
    have hu' : ∀ i j, cA D e * u i j = u i j := (isHalf_iff S T).2 hu
    simp only [OrthDec.resS_apply, Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu']
  have hresB : ∀ u : WO S T, u ∈ half S T (cA D e) → ∀ i j, cA D e * (o.resS T u).2 i j = (o.resS T u).2 i j := by
    intro u hu i j
    have hu' : ∀ i j, cA D e * u i j = u i j := (isHalf_iff S T).2 hu
    simp only [OrthDec.resS_apply, Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu']
  set l0 := iterForm o ℓA ℓB with hl0
  let gen : Set (WO S T → ℂ) := {f | ∃ fA fB, IsThetaFunO ψ A T fA ∧ IsThetaFunO ψ B T fB ∧ f = o.boxS T fA fB}
  let P : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ gen

  have hPst : ∀ u ∈ half S T (cA D e), ∀ p ∈ P, heisL S T ψ u p ∈ P := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hfA, hfB, rfl⟩ := hf
      refine Submodule.subset_span ⟨_, _, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hfA (o.resS T u).1,
        GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hfB (o.resS T u).2, ?_⟩
      exact o.heisO_boxS ψ T fA fB u
    | zero => rw [map_zero]; exact P.zero_mem
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact P.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact P.smul_mem c ha
  have hl0P : ∀ u ∈ half S T (cA D e), ∀ p ∈ P, l0 (heisL S T ψ u p) = l0 p := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hfA, hfB, rfl⟩ := hf
      change l0 (heisO ψ S T u (o.boxS T fA fB)) = _
      rw [o.heisO_boxS ψ T fA fB u, hl0, iterForm_boxS, iterForm_boxS, hA _ (hresA u hu) fA hfA,
        hB _ (hresB u hu) fB hfB]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha]

  let K : Submodule ℂ (WO S T → ℂ) :=
    Submodule.span ℂ {m | ∃ u ∈ half S T (cA D e), ∃ g ∈ {g | IsThetaFunO ψ S T g}, m = heisL S T ψ u g - g}
  have hsm : ∀ u ∈ half S T (cA D e), ∀ g ∈ {g | IsThetaFunO ψ S T g}, ∃ k : ℕ, 0 < k ∧ heisL S T ψ (k • u) g = g := by
    intro u hu g hg
    obtain ⟨U, hU, h⟩ := (show IsThetaFunO ψ S T g from hg).level
    obtain ⟨k, hk, hkU⟩ := GlobalTheory.SplitScalar.exists_nsmul_mem U hU (infPart_half hε heε' hu)
    exact ⟨k, hk, h _ hkU (infPart_half hε heε' ((half S T (cA D e)).nsmul_mem hu k))⟩
  have hPK : ∀ m ∈ P, m ∈ K → l0 m = 0 := by
    intro m hmP hmK
    obtain ⟨ι, s, y, hy, ⟨i, hi, hi0⟩, h⟩ := GlobalTheory.HalfCoinv.exists_sum_eq_zero (heisL_half S T ψ c2)
      (GlobalTheory.SplitScalar.heisO_zero ψ S T) hsm hmK
    have h1 : l0 (∑ j ∈ s, heisL S T ψ (y j) m) = (s.card : ℂ) * l0 m := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_congr rfl (fun j _ => hl0P (y j) (hy j) m hmP), Finset.sum_const, nsmul_eq_mul]
    rw [h, map_zero] at h1
    have hc : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, hi⟩)
    exact (mul_eq_zero.1 h1.symm).resolve_left hc

  let fP : (WO S T → ℂ) →ₗ.[ℂ] ℂ := ⟨P, l0 ∘ₗ P.subtype⟩
  let fK : (WO S T → ℂ) →ₗ.[ℂ] ℂ := ⟨K, 0⟩
  have H : ∀ (x : fP.domain) (y : fK.domain), (x : WO S T → ℂ) = y → fP x = fK y := by
    intro x y hxy
    change l0 (x : WO S T → ℂ) = 0
    exact hPK _ x.2 (hxy ▸ y.2)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (fP.sup fK H).toFun
  have hLv : ∀ z : (fP.sup fK H).domain, L z = (fP.sup fK H) z := fun z => LinearMap.congr_fun hL z
  refine ⟨L, fun u hu f hf => ?_, fun fA fB hfA hfB => ?_⟩
  · have huY : u ∈ half S T (cA D e) := (isHalf_iff S T).1 hu
    have hk : heisO ψ S T u f - f ∈ K := Submodule.subset_span ⟨u, huY, f, hf, rfl⟩
    have hz : heisO ψ S T u f - f ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_right hk
    have : L (heisO ψ S T u f - f) = 0 := by
      refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H (0 : fP.domain) ⟨_, hk⟩ ⟨_, hz⟩ (by simp)).trans ?_)
      change l0 0 + 0 = 0
      simp
    rwa [map_sub, sub_eq_zero] at this
  · have hp : o.boxS T fA fB ∈ P := Submodule.subset_span ⟨fA, fB, hfA, hfB, rfl⟩
    have hz : o.boxS T fA fB ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_left hp
    refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H ⟨_, hp⟩ (0 : fK.domain) ⟨_, hz⟩ (by simp)).trans ?_)
    change l0 (o.boxS T fA fB) + 0 = _
    rw [add_zero, hl0, iterForm_boxS]

end GlobalTheory.ProdForm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), (∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (o.boxS T fA fB)) ∧ (∀ fA fB, o.boxS T fA fB 0 = fA 0 * fB 0) ∧ (∀ fA fB, (∀ u, heisO ψ S T ((o.resS T).symm (u, 0)) (o.boxS T fA fB) = o.boxS T (heisO ψ A T u fA) fB) ∧ ∀ v, heisO ψ S T ((o.resS T).symm (0, v)) (o.boxS T fA fB) = o.boxS T fA (heisO ψ B T v fB)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ v, IsThetaFunO ψ A T fun u => f ((o.resS T).symm (u, v))) ∧ ∀ u, IsThetaFunO ψ B T fun v => f ((o.resS T).symm (u, v)) := by
  first | exact @GlobalTheory.BoxSlice.main | exact GlobalTheory.BoxSlice.main | (intros; apply GlobalTheory.BoxSlice.main <;> assumption)
end

section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
open scoped Pointwise

namespace GlobalTheory.LatPair.Det

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem det_mem_of_mem_latStab_std {g : GL n k} (hg : g ∈ latStab (stdLat k n)) : g.val.det ∈ 𝒪[k] := by
  rw [MulAction.mem_stabilizer_iff] at hg
  have t2 : ∀ v : n → k, v ∈ stdLat k n ↔ ∀ i, v i ∈ 𝒪[k] := by
    intro v
    simp only [stdLat, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact (y i).2
    · intro h
      exact ⟨fun i => ⟨v i, h i⟩, rfl⟩
  have hent : ∀ i j, (g : Matrix n n k) i j ∈ 𝒪[k] := by
    intro i j
    have hs : Pi.single j (1 : k) ∈ stdLat k n := by
      rw [t2]
      intro i'
      by_cases h : i' = j
      · subst h
        simp only [Pi.single_eq_same]
        exact one_mem _
      · simp only [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h1 : g • Pi.single j (1 : k) ∈ stdLat k n := by
      rw [← hg]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hs
    rw [t2] at h1
    have h2 := h1 i
    change ((g : Matrix n n k) *ᵥ Pi.single j 1) i ∈ 𝒪[k] at h2
    simpa [Matrix.mulVec_single] using h2
  let A : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨(g : Matrix n n k) i j, hent i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = (g : Matrix n n k) := by
    ext i j
    rfl
  rw [← hA, ← RingHom.map_det]
  exact (A.det).2

theorem exists_smul_stdLat_eq (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] : ∃ h : GL n k, h • stdLat k n = L := by
  classical
  letI : Module.Free 𝒪[k] L := Submodule.IsLattice.free k L
  letI : Module.Finite 𝒪[k] L := Submodule.IsLattice.finite k L
  let b := Module.Free.chooseBasis 𝒪[k] L
  let B := b.extendOfIsFullLattice k
  have hc : Fintype.card (Module.Free.ChooseBasisIndex 𝒪[k] L) = Fintype.card n := by
    have := Module.finrank_eq_card_basis B
    simpa using this.symm
  let e := Fintype.equivOfCardEq hc
  let B' := B.reindex e
  let P := (Pi.basisFun k n).toMatrix B'
  let Q := B'.toMatrix (Pi.basisFun k n)
  let h : GL n k := ⟨P, Q, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have hB' : ∀ j, B' j = (b (e.symm j) : n → k) := by
    intro j
    simp [B', B]
  have key : ∀ y : n → k, h • y = ∑ j, y j • B' j := by
    intro y
    change P *ᵥ y = _
    ext i
    simp [P, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, mul_comm]
  refine ⟨h, ?_⟩
  ext x
  simp only [HSMul.hSMul, SMul.smul]
  rw [Submodule.mem_map]
  simp only [DistribSMul.toLinearMap_apply]
  change (∃ y ∈ stdLat k n, h • y = x) ↔ x ∈ L
  simp only [key]
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    refine L.sum_mem fun j _ => ?_
    rw [hB']
    change algebraMap 𝒪[k] k (c j) • (b (e.symm j) : n → k) ∈ L
    rw [algebraMap_smul]
    exact L.smul_mem (c j) (b (e.symm j)).2
  · intro hx
    let c := b.repr ⟨x, hx⟩
    refine ⟨fun j => (c (e.symm j) : k), ⟨fun j => c (e.symm j), rfl⟩, ?_⟩
    simp_rw [hB']
    have hsum := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at hsum
    rw [Equiv.sum_comp e.symm (fun i => ((c i : 𝒪[k]) : k) • (b i : n → k))]
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact algebraMap_smul k (c i) _

theorem det_mem_of_mem_latStab {L : Submodule 𝒪[k] (n → k)} [L.IsFullLattice k] {g : GL n k} (hg : g ∈ latStab L) :
    ((Matrix.GeneralLinearGroup.det g : kˣ) : k) ∈ 𝒪[k] := by
  obtain ⟨h, rfl⟩ := exists_smul_stdLat_eq L
  have hs : h⁻¹ * g * h ∈ latStab (stdLat k n) := by
    simp only [latStab, MulAction.mem_stabilizer_iff] at hg ⊢
    rw [mul_smul, mul_smul, hg, inv_smul_smul]
  have h1 := det_mem_of_mem_latStab_std hs
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at h1
  have hdet : Matrix.GeneralLinearGroup.det (h⁻¹ * g * h) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [hdet] at h1

theorem valuation_det_of_mem_latStab {L : Submodule 𝒪[k] (n → k)} [L.IsFullLattice k] {g : GL n k} (hg : g ∈ latStab L) :
    valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  have h1 := det_mem_of_mem_latStab hg
  have h2 := det_mem_of_mem_latStab (inv_mem hg)
  rw [map_inv, Units.val_inv_eq_inv_val] at h2
  set d : k := ((Matrix.GeneralLinearGroup.det g : kˣ) : k) with hd
  have hd0 : d ≠ 0 := Units.ne_zero _
  have hu : IsUnit (⟨d, h1⟩ : 𝒪[k]) :=
    ⟨⟨⟨d, h1⟩, ⟨d⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hd0), Subtype.ext (inv_mul_cancel₀ hd0)⟩, rfl⟩
  exact ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).1 hu

end

theorem isUnram_det_latStab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → ∀ g ∈ latStab L, ∀ μ : kˣ →* ℂˣ, IsUnram μ → μ (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n _ _ L hL g hg μ hμ
  exact hμ _ (valuation_det_of_mem_latStab hg)

end GlobalTheory.LatPair.Det
end
