module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFrameCharacterFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

namespace GlobalTheory.DiagNonvan

open scoped Classical
open GlobalTheory.DiagForm GlobalTheory.StdCharFromIsStd

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eq_zero_of_psi_mul {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (b : AF F) (h : ∀ y : AF F, ψ (b * y) = 1) :
    b = 0 := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have h1 : b.1 = 0 := by
    refine e.injective ?_
    rw [map_zero]
    refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun s => ?_
    by_contra hT
    set T := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e b.1 * s) with hTdef
    have h2 := h (pairA F (e.symm ((1 / (2 * T)) • s)) 0)
    have e1 : b * pairA F (e.symm ((1 / (2 * T)) • s)) 0 = pairA F (b.1 * e.symm ((1 / (2 * T)) • s)) 0 := by
      show ((b.1 * _, b.2 * 0) : Ainf F × Af F) = (_, 0)
      rw [mul_zero]
      rfl
    have e2 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e (b.1 * e.symm ((1 / (2 * T)) • s))) = 1 / 2 := by
      rw [map_mul, RingEquiv.apply_symm_apply, mul_smul_comm, map_smul, ← hTdef, smul_eq_mul]
      field_simp
    rw [e1, psi_pairA hψ] at h2
    change Complex.exp (_ * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (e (b.1 * e.symm ((1 / (2 * T)) • s))) : ℝ) : ℂ)) = 1 at h2
    have e3 : -(2 * (Real.pi : ℂ) * Complex.I) * ((1 / 2 : ℝ) : ℂ) = -(Real.pi * Complex.I) := by push_cast; ring
    rw [e2, e3, Complex.exp_neg, Complex.exp_pi_mul_I] at h2
    norm_num at h2
  have h2 : b.2 = 0 := by
    refine _root_.GlobalTheory.AdelicU.af_ext fun v => ?_
    rw [map_zero]
    by_contra hv
    apply GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v
    ext t
    rw [GlobalTheory.VacAny.psiV_apply, AddChar.one_apply, ← h (pairA F 0 (singleFin v ((evalV F v b.2)⁻¹ * t)))]
    congr 1
    show ((0, singleFin v t) : Ainf F × Af F) = (b.1 * 0, b.2 * singleFin v ((evalV F v b.2)⁻¹ * t))
    rw [mul_zero]
    congr 1
    refine _root_.GlobalTheory.AdelicU.af_ext fun u => ?_
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  exact Prod.ext h1 h2

theorem continuous_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_glue : Continuous (glue : Vi F κ × Vf F κ → κ → AdeleRing (𝓞 F) F) :=
  continuous_pi fun i =>
    (continuous_symm.comp ((continuous_apply i).comp ((eI F κ).continuous.comp continuous_fst))).prodMk
      ((continuous_apply i).comp continuous_snd)

theorem glue_add (p q : Vi F κ × Vf F κ) : glue (p + q) = glue p + glue q := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ (p.1 + q.1) i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i) +
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ q.1 i)
  rw [map_add (f := _), Pi.add_apply, map_add (f := _)]

theorem glue_zero : glue (0 : Vi F κ × Vf F κ) = 0 := by
  have h := glue_add (0 : Vi F κ × Vf F κ) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem eq_zero_of_glue {p : Vi F κ × Vf F κ} (h : glue p = 0) : p = 0 := by
  refine Prod.ext ?_ (funext fun i => congrArg Prod.snd (congrFun h i))
  refine (eI F κ).injective ?_
  rw [Prod.fst_zero, map_zero]
  funext i
  refine (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.injective ?_
  rw [Pi.zero_apply, map_zero]
  exact congrArg Prod.fst (congrFun h i)

theorem continuous_resD {φ : (κ ⊕ κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) :
    Continuous (resD F κ φ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    have hd : Continuous fun v : Vf F κ => (Sum.elim v v : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
      continuous_pi fun i => by cases i <;> exact continuous_apply _
    rw [show resD F κ (pureA F f g) = fun p => compD F κ f p.1 * g (Sum.elim p.2 p.2) from funext (resD_pureA f g)]
    exact ((compD F κ f).continuous.comp continuous_fst).mul ((hg.1.continuous.comp hd).comp continuous_snd)
  | zero => rw [map_zero]; exact continuous_zero
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact hx.add hy
  | smul c x _ hx => rw [map_smul]; exact hx.const_smul c

instance mu_haar : (mu F κ).IsAddHaarMeasure := by unfold mu; infer_instance

theorem dot_left (a c : κ → AF F) : Sum.elim a a ⬝ᵥ Sum.elim c (0 : κ → AF F) = a ⬝ᵥ c := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem exists_lDiag_schr_ne {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {f : (κ ⊕ κ → AF F) → ℂ}
    (hf : f ∈ schA F (κ ⊕ κ)) (hf0 : f ≠ 0) : ∃ w, lDiag F κ (schr ψ w f) ≠ 0 := by
  obtain ⟨p, hp⟩ := Function.ne_iff.1 hf0
  by_contra hcon
  push_neg at hcon
  have hmem := fun w => GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w f hf
  let N : Vi F κ × Vf F κ → ℂ := resD F κ (schr ψ (p, 0) f)
  have hN : ∀ q, N q = f (Sum.elim (glue q) (glue q) + p) := fun q => by
    show ψ (_ ⬝ᵥ 0 + _ * (p ⬝ᵥ 0)) * _ = _
    rw [dotProduct_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  let χ : (κ → AF F) → Vi F κ × Vf F κ → ℂ := fun c q => ψ (glue q ⬝ᵥ c)
  have key : N = 0 := by
    refine GlobalTheory.CharFourierInj.eq_zero χ (fun c => hψ.1.comp (continuous_glue.dotProduct continuous_const))
      (fun c q q' => ?_) (fun c c' q => ?_) (fun q => ?_) (fun c q => norm_psi hψ _) (fun q hq => ?_) (mu F κ) N
      (continuous_resD (hmem _)) (integrable_resD (hmem _)) fun c => ?_
    · simp only [χ, glue_add, add_dotProduct, AddChar.map_add_eq_mul]
    · simp only [χ, dotProduct_add, AddChar.map_add_eq_mul]
    · simp only [χ, dotProduct_zero, AddChar.map_zero_eq_one]
    · refine eq_zero_of_glue (funext fun i => eq_zero_of_psi_mul hψ _ fun y => ?_)
      have := hq (Pi.single i y)
      simp only [χ] at this
      rwa [dotProduct_single] at this
    · have h1 := hcon (p, Sum.elim c 0)
      rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD (hmem _))] at h1
      have e : ∀ q, resD F κ (schr ψ (p, Sum.elim c 0) f) q =
          ψ (⅟(2 : AF F) * (p ⬝ᵥ Sum.elim c 0)) * (χ c q * N q) := fun q => by
        rw [hN]
        show ψ (Sum.elim (glue q) (glue q) ⬝ᵥ Sum.elim c 0 + ⅟(2 : AF F) * (p ⬝ᵥ Sum.elim c 0)) *
          f (Sum.elim (glue q) (glue q) + p) = _
        rw [dot_left, AddChar.map_add_eq_mul]
        simp only [χ]
        ring
      simp only [e] at h1
      rw [integral_const_mul] at h1
      refine (mul_eq_zero.1 h1).resolve_left fun h0 => ?_
      have := norm_psi hψ (⅟(2 : AF F) * (p ⬝ᵥ Sum.elim c 0))
      rw [h0, norm_zero] at this
      exact zero_ne_one this
  have h0 := hN 0
  rw [key, glue_zero, Sum.elim_zero_zero, zero_add] at h0
  exact hp h0.symm

theorem exists_invForm_rho_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∀ f ∈ schA F (κ ⊕ κ), f ≠ 0 →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ schA F (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = l φ) ∧
      ∃ w : Matrix α (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), l (dd.rho ψ w f) ≠ 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d dd hψ hdd f hf hf0
  refine ⟨lDiag F κ, lDiag_adm, fun z φ hφ => ?_, ?_⟩
  · have hz : z * (diagCols β : Matrix (β ⊕ β) β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one]
    rw [hz, Darboux.rho, hdd z z, lDiag_schr ψ _ _ hφ]
  · obtain ⟨w, hw⟩ := exists_lDiag_schr_ne hψ hf hf0
    exact ⟨dd.e.symm w, by rwa [Darboux.rho, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.DiagNonvan

end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem continuous_atPlace : Continuous (atPlace (F := F) v) :=
  Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_linear_prod (f : Fv F v × Fv F v →ₗ[Fv F v] Fv F v) : Continuous f := by
  have e : ∀ p : Fv F v × Fv F v, f p = p.1 * f (1, 0) + p.2 * f (0, 1) := by
    intro p
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add (f := _)]
    congr 1
    ext <;> simp
  have : (f : Fv F v × Fv F v → Fv F v) = fun p => p.1 * f (1, 0) + p.2 * f (0, 1) := funext e
  rw [this]
  exact (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)

theorem continuous_tensAt_split (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) :
    Continuous fun p : Fv F v × Fv F v => tensAt E v ((splitAlgEquiv h t).symm p) := by
  let b := Module.Free.chooseBasis F E
  let bv := Algebra.TensorProduct.basis (Fv F v) b
  have key : ∀ y : TensorProduct F (Fv F v) E,
      tensAt E v y = ∑ i, atPlace v (bv.repr y i) • ((1 : AF F) ⊗ₜ[F] b i) := by
    intro y
    conv_lhs => rw [← bv.sum_repr y]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, tensAt_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have : (fun p : Fv F v × Fv F v => tensAt E v ((splitAlgEquiv h t).symm p)) =
      fun p => ∑ i, atPlace v (bv.repr ((splitAlgEquiv h t).symm p) i) • ((1 : AF F) ⊗ₜ[F] b i) :=
    funext fun p => key _
  rw [this]
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  refine continuous_finsetSum _ fun i _ => ?_
  have hc : Continuous fun p : Fv F v × Fv F v => atPlace v (bv.repr ((splitAlgEquiv h t).symm p) i) :=
    continuous_atPlace.comp (continuous_linear_prod ((bv.coord i).comp (splitAlgEquiv h t).symm.toLinearMap))
  exact hc.smul (continuous_const : Continuous fun _ : Fv F v × Fv F v => ((1 : AF F) ⊗ₜ[F] b i : AE F E))

end GlobalTheory.SkewLeviNear

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem continuous_lift_locMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) :
    Continuous fun g : GL (Fin n) (Fv F v) => lift v (locMat h t J g) := by
  have hc : Continuous fun g : GL (Fin n) (Fv F v) => conjComp t J g :=
    (continuous_const.matrix_mul Units.continuous_coe_inv.matrix_transpose).matrix_mul continuous_const
  refine continuous_matrix fun i j => ?_
  have e : (fun g : GL (Fin n) (Fv F v) => lift v (locMat h t J g) i j) = fun g : GL (Fin n) (Fv F v) =>
      (1 : Matrix (Fin n) (Fin n) (AE F E)) i j +
        (tensAt E v ((splitAlgEquiv h t).symm ((g : Matrix (Fin n) (Fin n) (Fv F v)) i j, conjComp t J g i j)) +
          -tensAt E v ((1 : Matrix (Fin n) (Fin n) (TensorProduct F (Fv F v) E)) i j)) := by
    funext g
    simp only [lift, ext0, Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, map_sub]
    rw [sub_eq_add_neg]
    rfl
  rw [e]
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  refine continuous_const.add (Continuous.add ?_ continuous_const)
  refine (continuous_tensAt_split h t).comp (Continuous.prodMk ?_ ?_)
  · exact (Units.continuous_val.matrix_elem i j)
  · exact hc.matrix_elem i j

end GlobalTheory.SkewLeviNear

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

theorem near_one_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ U ∈ 𝓝 (1 : UA σ G.W.J), ∃ V ∈ 𝓝 (1 : (Fv F v)ˣ), ∀ x ∈ V,
      ∃ h ∈ UAt σ G.W (evFin F v), h ∈ U ∧ ((mat h).map (piW t)).det = (x : Fv F v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t U hU
  have h := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  let Ψ : GL (Fin (a + a')) (Fv F v) → UA σ G.W.J := fun g =>
    ⟨adelicGL h t G.W.J hJ g, lift_unitary v σ G.W.J _ (locMat_unitary_skew h t G.W.J hJ hTr.geo.hW.skew g)⟩
  have hΨc : Continuous Ψ := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨continuous_lift_locMat h t G.W.J, ?_⟩) _
    exact (continuous_lift_locMat h t G.W.J).comp continuous_inv
  have hΨ1 : Ψ 1 = 1 := Subtype.ext (Units.ext (by
    change lift v (LeviAtPlace.locMat h t G.W.J 1) = 1
    rw [locMat_one h t G.W.J hJ, lift_one]))
  have hΨt : ∀ g, (mat (Ψ g)).map (piW t) = g.1 := by
    intro g
    change (lift v (LeviAtPlace.locMat h t G.W.J g)).map (piW t) = g.1
    have key : (lift v (LeviAtPlace.locMat h t G.W.J g)).map (piW t) =
        (LeviAtPlace.locMat h t G.W.J g).map (splitProj t) := by
      conv_rhs => rw [← compFin_lift v (LeviAtPlace.locMat h t G.W.J g), Matrix.map_map]
      rfl
    rw [key]
    exact pairMat_fst h t _ _
  have i0 : Fin (a + a') := ⟨0, by have := hTr.geo.lt; omega⟩
  let D : (Fv F v)ˣ →* GL (Fin (a + a')) (Fv F v) :=
    Units.map ((Matrix.diagonalRingHom (Fin (a + a')) (Fv F v)).toMonoidHom.comp
      (MonoidHom.mulSingle (fun _ => Fv F v) i0))
  have hDv : ∀ x : (Fv F v)ˣ, ((D x : GL (Fin (a + a')) (Fv F v)) : Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v)) =
      Matrix.diagonal (Pi.mulSingle i0 (x : Fv F v)) := fun x => rfl
  have hDc : Continuous D := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have : (Units.val ∘ D) = fun x : (Fv F v)ˣ => Matrix.diagonal (Pi.mulSingle i0 (x : Fv F v)) := funext hDv
      rw [this]
      exact (continuous_mulSingle i0 |>.comp Units.continuous_val).matrix_diagonal
    · have : (fun x => ((D x)⁻¹ : GL (Fin (a + a')) (Fv F v)).1) =
          fun x : (Fv F v)ˣ => Matrix.diagonal (Pi.mulSingle i0 ((x⁻¹ : (Fv F v)ˣ) : Fv F v)) := by
        funext x; rw [← map_inv]; rfl
      rw [this]
      exact (continuous_mulSingle i0 |>.comp Units.continuous_coe_inv).matrix_diagonal
  have hf : Continuous fun x => Ψ (D x) := hΨc.comp hDc
  have hf1 : Ψ (D 1) = 1 := by rw [map_one, hΨ1]
  refine ⟨(fun x => Ψ (D x)) ⁻¹' U, hf.continuousAt.preimage_mem_nhds (by rw [hf1]; exact hU), fun x hx => ?_⟩
  refine ⟨Ψ (D x), lift_sub_one_at v _, hx, ?_⟩
  rw [hΨt, hDv, Matrix.det_diagonal]
  simp

end GlobalTheory.SkewLeviNear
end
end

section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil


theorem _root_.GlobalTheory.T.lintegral_sq_latticeModelRep_fundamentalDomain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.FinLatUnitF.lintegral_sq_Om | exact GlobalTheory.FinLatUnitF.lintegral_sq_Om | (intros; apply GlobalTheory.FinLatUnitF.lintegral_sq_Om <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.archimedean_frame_character_factorization : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) → At (evI F) ((h.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGen τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  first | exact @GlobalTheory.RealLift.CharTrace.deriv_char | exact GlobalTheory.RealLift.CharTrace.deriv_char | (intros; apply GlobalTheory.RealLift.CharTrace.deriv_char <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.KeyUnitModels.SplitLoc

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open scoped CategoryTheory.Obj

theorem isIso_residueFieldMap {Z X : Scheme.{0}} (i : Z ⟶ X) [SurjectiveOnStalks i] (z : Z) :
    IsIso (i.residueFieldMap z) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective _, fun u => ?_⟩
  obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
  obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
  exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩

theorem split_of_pullback {Z X : Scheme.{0}} (i : Z ⟶ X) [SurjectiveOnStalks i] {G : Over X} {G' : Over Z} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G i φ) (z : Z)
    (h : ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField (i z)) k),
      FiniteDimensional (X.residueField (i z)) k ∧ Algebra.IsSeparable (X.residueField (i z)) k ∧
      ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (i z)) k)) ≫ X.fromSpecResidueField (i z))).obj G)) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField z) k),
      FiniteDimensional (Z.residueField z) k ∧ Algebra.IsSeparable (Z.residueField z) k ∧
      ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) k)) ≫ Z.fromSpecResidueField z)).obj G') := by
  obtain ⟨k, _, _, hfin, hsep, S, hS⟩ := h
  have := isIso_residueFieldMap i z
  let e : X.residueField (i z) ≃+* Z.residueField z := (asIso (i.residueFieldMap z)).commRingCatIsoToRingEquiv
  let _ : Algebra (Z.residueField z) k := ((algebraMap (X.residueField (i z)) k).comp e.symm.toRingHom).toAlgebra
  have he : (algebraMap (Z.residueField z) k).comp (e : _ →+* _) =
      ((RingEquiv.refl k : k ≃+* k) : k →+* k).comp (algebraMap (X.residueField (i z)) k) :=
    RingHom.ext fun a => congrArg (algebraMap (X.residueField (i z)) k) (e.symm_apply_apply a)
  refine ⟨k, inferInstance, inferInstance, Module.Finite.of_equiv_equiv e (RingEquiv.refl k) he,
    Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl k) he, S, ?_⟩
  have hc : i.residueFieldMap z ≫ CommRingCat.ofHom (algebraMap (Z.residueField z) k) =
      CommRingCat.ofHom (algebraMap (X.residueField (i z)) k) := CommRingCat.hom_ext he
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) k)) ≫ Z.fromSpecResidueField z) ≫ i =
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (i z)) k)) ≫ X.fromSpecResidueField (i z) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.fromSpecResidueField (i z)) (Spec.map_comp _ _).symm)
  obtain ⟨j, hj, -⟩ := grpPullback_iso (isGrpPullback_pullback G _)
    (((isGrpPullback_pullback G' _).comp hφ).congr key rfl)
  exact isGt_of_iso j hS

theorem locModel_splitFibres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)]
    [Flat (spMap b)], Y.SplitFibres → (locModel Y b hb).SplitFibres := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' b hb _ _ h x
  exact split_of_pullback (pullback.fst Y.s (spMap b)) (locMap Y b).cart x (h _)

end GlobalTheory.KeyUnitModels.SplitLoc
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.cusp_rep_paired_with_itself : GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.CuspFormsBoundedGL → GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, GlobalTheory.DiscSpec.IsNormalised π → Paired π π invTOp := by
  first | exact @GlobalTheory.GKPair.paired_invTOp | exact GlobalTheory.GKPair.paired_invTOp | (intros; apply GlobalTheory.GKPair.paired_invTOp <;> assumption)
end
