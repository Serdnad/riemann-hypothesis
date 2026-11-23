module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle331
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows posDef_dual)
open GlobalTheory.SepRows
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopLineProof

theorem bilin_prop {X Y ι κ : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (fx : ι → X) (fy : κ → Y)
    (hx : Submodule.span ℂ (Set.range fx) = ⊤) (hy : Submodule.span ℂ (Set.range fy) = ⊤) (b b₀ : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (f : ι → κ → ℂ) (l l₀ : ℂ) (hb : ∀ i j, b (fx i) (fy j) = f i j * l) (hb₀ : ∀ i j, b₀ (fx i) (fy j) = f i j * l₀)
    (hne : b₀ ≠ 0) : b = (l / l₀) • b₀ := by
  have hl₀ : l₀ ≠ 0 := by
    rintro rfl
    refine hne (LinearMap.ext_on_range hx fun i => LinearMap.ext_on_range hy fun j => ?_)
    simp [hb₀]
  refine LinearMap.ext_on_range hx fun i => LinearMap.ext_on_range hy fun j => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hb, hb₀, smul_eq_mul]
  field_simp

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem coefPlus_is (G : GridData L sc) {θ : InfFam D} (hθ : IsInfFam θ) : (coefPlus G θ).Is := by
  obtain ⟨hc, hs⟩ := GlobalTheory.CoefModel.realGL_laws hθ (G.V (.top 0))
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  refine GlobalTheory.CoefModel.coefOf_is _ _ _ (fun h hh => ?_) (fun h τ => ?_) (fun τ => ?_) (fun g hg => ?_)
  · have : GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom (G.V (.top 0)) h) = 1
      rw [show infHom (G.V (.top 0)) h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, this, map_one]
  · exact GlobalTheory.CoefModel.invTr_unitary (g := GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h τ)
      (GlobalTheory.RecDictModel.archM_unitary (G.V (.top 0)) (hθ τ) h)
  · refine ((hc τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h⁻¹ τ : Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ) = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (invTrK g) fun τ => by
      have := GlobalTheory.CoefModel.invTr_unitary (hg τ)
      rwa [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.FunObj.posDef_Xp G (tauE D τ)).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, e]
    exact funext fun τ => GlobalTheory.CoefModel.invTr_invTr _

end GlobalTheory.TopLineProof
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel

variable {D : D7}

theorem gram_det_ne_zero (S : HSp D) : S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv0
  set x : S.V := ∑ j, v j • S.frame j with hxdef
  have hfr : ∀ i, S.hT (S.frame i) x = 0 := by
    intro i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this

    rw [hxdef, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Formalism.BasicNotions.HSpace.gram, mul_comm]
  have hx : S.hT.flip x = 0 := S.frame.ext fun i => by simpa using hfr i
  have hx0 : x = 0 := S.nondeg.2 x fun y => by
    have := LinearMap.congr_fun hx y
    simpa using this
  funext j
  exact Fintype.linearIndependent_iff.1 S.frame.linearIndependent v hx0 j

theorem isUnit_det_incM (S : HSp D) (c : D.host.E) (hc : c ≠ 0) :
    IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)).det := by
  have h1 : (c • S.gram).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) (gram_det_ne_zero S)
  have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)).det =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) (c • S.gram).det := by
    rw [RingHom.map_det]; rfl
  rw [h2]
  exact (isUnit_iff_ne_zero.2 h1).map _

variable {R : Type} [CommRing R]

def coordsEquiv {n m d : ℕ} (e : Fin m ≃ Fin d) (G : Matrix (Fin n) (Fin n) R) (hG : IsUnit G.det) :
    Matrix (Fin n) (Fin d) R ≃+ Matrix (Fin m) (Fin n) R where
  toFun u := uᵀ.submatrix e id * G
  invFun x := ((x * G⁻¹).submatrix e.symm id)ᵀ
  left_inv u := by
    dsimp only
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ hG, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
      Function.comp_id, Matrix.submatrix_id_id, Matrix.transpose_transpose]
  right_inv x := by
    dsimp only
    rw [Matrix.transpose_transpose, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id,
      Matrix.submatrix_id_id, Matrix.nonsing_inv_mul_cancel_right _ _ hG]
  map_add' u v := by
    show (u + v)ᵀ.submatrix e id * G = uᵀ.submatrix e id * G + vᵀ.submatrix e id * G
    rw [Matrix.transpose_add, ← Matrix.add_mul]
    rfl

theorem coords (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (c : D.host.E) (hc : c ≠ 0) :
    ∃ f : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      ∀ u, f u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)) :
        Matrix (Fin X.rank) (Fin S.rank) (AE D)) :=
  ⟨coordsEquiv e _ (isUnit_det_incM S c hc), fun _ => rfl⟩

end GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree

theorem conjU_one_eq {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

end GlobalTheory.SquareAgree

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ArchLinePreimage

variable {D : D7}



theorem smul_eq_zero_of_finPart_eq_zero (t : AE D) (ht : finPart D t = 0) (a : AF D.host.F)
    (ha : a.1 = 0) : a • t = 0 := by
  let ι : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F →ₗ[D.host.F] AF D.host.F :=
    (LinearMap.inr D.host.F (InfiniteAdeleRing D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)).comp
      (LinearMap.mulLeft D.host.F a.2)
  let g : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
    TensorProduct.map ι LinearMap.id
  let fL : AE D →ₗ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    TensorProduct.map (sndA D.host.F).toLinearMap LinearMap.id
  have hfL : fL t = finPart D t := rfl
  have key : ∀ s : AF D.host.F ⊗[D.host.F] D.host.E, a • s = g (fL s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [smul_zero, LinearMap.map_zero, LinearMap.map_zero]
    | tmul b x =>
      have hab : a * b = ι b.2 := by
        refine Prod.ext ?_ ?_
        · show a.1 * b.1 = 0
          rw [ha, zero_mul]
        · rfl
      have h1 : a • (b ⊗ₜ[D.host.F] x : AE D) = (a * b) ⊗ₜ[D.host.F] x := rfl
      rw [h1, hab]
      rfl
    | add s₁ s₂ h₁ h₂ =>
      rw [smul_add, h₁, h₂, LinearMap.map_add (f := _), LinearMap.map_add (f := _)]
  rw [key, hfL, ht, LinearMap.map_zero]

theorem arch_symm_lineAt : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (cS.symm (lineAt θ τ z 1)) := by
  intro D θ hθ ε S X d e cS hcS τ z u hu
  have hx : (lineAt θ τ z 1).map (finPart D) = 0 :=
    funext fun i => funext fun j => congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z).2.1 1) i) j
  set y := cS.symm (lineAt θ τ z 1) with hydef
  have hy := cS.apply_symm_apply (lineAt θ τ z 1)
  rw [← hydef, hcS] at hy
  set c : D.host.E := if ε then -1 else 1 with hc
  have hc0 : c ≠ 0 := by rw [hc]; split_ifs <;> norm_num
  set N : Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (c • S.gram).map ((finPart D).comp (inclR (AF D.host.F))) with hN
  have hNdet : IsUnit N.det := by
    have hd : N.det = ((finPart D).comp (inclR (AF D.host.F))) (c • S.gram).det :=
      (RingHom.map_det ((finPart D).comp (inclR (AF D.host.F))) _).symm
    rw [hd]
    refine IsUnit.map _ (Ne.isUnit ?_)
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc0) (gram_det_ne S)
  have hM : (HMul.hMul ((y.map (finPart D))ᵀ.submatrix e id) N :
      Matrix (Fin X.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = 0 := by
    have h3 := congrArg (fun m => Matrix.map m (finPart D)) hy
    simp only [Matrix.map_mul] at h3
    rw [hx] at h3
    exact h3
  have hM0 : (y.map (finPart D))ᵀ.submatrix e id = 0 := by
    calc _ = HMul.hMul (HMul.hMul ((y.map (finPart D))ᵀ.submatrix e id) N :
          Matrix (Fin X.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) N⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right N _ hNdet).symm
      _ = 0 := by rw [hM, Matrix.zero_mul]
  have hent : ∀ i j, finPart D (y i j) = 0 := by
    intro i j
    have h4 := congrFun (congrFun hM0 (e.symm j)) i
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply, Equiv.apply_symm_apply,
      id, Matrix.zero_apply] at h4
    exact h4
  have hu1 : u.1 = 0 := by
    have h5 : (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) u.1 = 0 := hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective).1 h5
  funext i j
  exact smul_eq_zero_of_finPart_eq_zero (y i j) (hent i j) u hu1

end GlobalTheory.ArchLinePreimage
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.archSupported_smul_conjugateUnitary_sub_one_eq_zero : ∀ (D : D7) (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hJ : J = c • V.gram)
    (g : GA D V), g ∈ GfC V → ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
  first | exact @GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one | exact GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one | (intros; apply GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.LatStab

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gen_mul_transpose {n d : ℕ} (x : Fin n → E) (y : Fin d → E) (a : AF F)
    (K : Matrix (Fin d) (Fin d) (AE F E)) :
    (a • incM F (Matrix.vecMulVec x y)) * Kᵀ =
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i))
        (a • (K *ᵥ fun i => inclR (F := F) (AF F) (y i))) := by
  ext i j
  simp only [incM, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply,
    Matrix.transpose_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, map_mul, Finset.smul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  ring

theorem vecMulVec_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (x : Fin n → E) (hx : x ∈ X.L) (u : Fin d → AE F E)
    (hu : u ∈ AddSubgroup.closure {z | ∃ b : AF F, At (evFin F w) b ∧
          evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => inclR (F := F) (AF F) (y' i)}) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u ∈ latAtV X W w := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨b, hb, hbi, y', hy', rfl⟩ := hu
    apply AddSubgroup.subset_closure
    refine ⟨b, hb, hbi, x, hx, y', hy', ?_⟩
    ext i j
    simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, map_mul]
    rw [mul_smul_comm]
  | zero =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [this]; exact zero_mem _
  | add u v _ _ hu hv =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (u + v) =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u +
          Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) v := by
      ext i j; simp [Matrix.vecMulVec_apply, mul_add]
    rw [this]; exact add_mem hu hv
  | neg u _ hu =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (-u) =
        -Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [this]; exact neg_mem hu

theorem mul_transpose_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (K : Matrix (Fin d) (Fin d) (AE F E))
    (hK : ∀ a : AF F, At (evFin F w) a → evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, At (evFin F w) b ∧
          evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => inclR (F := F) (AF F) (y' i)})
    (γ : Matrix (Fin n) (Fin d) (AE F E)) (hγ : γ ∈ latAtV X W w) : γ * Kᵀ ∈ latAtV X W w := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    rw [gen_mul_transpose]
    exact vecMulVec_mem X W w x hx _ (hK a ha hai y hy)
  | zero => simp
  | add u v _ _ hu hv => rw [Matrix.add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [Matrix.neg_mul]; exact neg_mem hu

theorem latAtV_mul_transpose_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (K K' : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), K' * K = 1 →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K' *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    ∀ γ, γ * Kᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w := by
  intro F E _ _ _ _ _ n d X W w K K' hKK hK hK' γ
  constructor
  · intro h
    have h2 := mul_transpose_mem X W w K' hK' _ h
    rwa [Matrix.mul_assoc, ← Matrix.transpose_mul, hKK, Matrix.transpose_one, Matrix.mul_one] at h2
  · exact mul_transpose_mem X W w K hK γ

end GlobalTheory.LatStab
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LineDerivSplit

theorem pure_add₀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul₀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pure_listSum {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} (l : List ι)
    (h : ι → SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (l.map h).sum φ = (l.map fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (h i) φ).sum := by
  induction l with
  | nil => funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  | cons a l ih => simp [pure_add₀, ih]

theorem sum_listSum {α ι : Type} [AddCommMonoid α] {m : ℕ} (l : List ι) (a : Fin m → ι → α) :
    ∑ j, (l.map (a j)).sum = (l.map fun i => ∑ j, a j i).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [Finset.sum_add_distrib, ih]

end GlobalTheory.LineDerivSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaRestriction_invariant_rationalLeviGL : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (d : GlobalTheory.MixModel.HypDec V V' r), d.e = C → d.i₀ = B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) D.host.E) (f : WO V W → ℂ), IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (d.levi (Matrix.GeneralLinearGroup.map (incA D) a), 1) f) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  first | exact @GlobalTheory.LeviGLRes.res_levi_GL | exact GlobalTheory.LeviGLRes.res_levi_GL | (intros; apply GlobalTheory.LeviGLRes.res_levi_GL <;> assumption)
end
