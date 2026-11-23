module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.Adele.Topology
import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.HaarPull

open GlobalTheory.DiagForm GlobalTheory.DiagUniq

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

variable {F : Type} [Field F] [NumberField F] {ι κ : Type} [Fintype ι] [Fintype κ]

theorem pureA_mulVec_glue (D : Matrix κ ι F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (p : Vi F ι × Vf F ι) :
    pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p) =
      f (fun k => ∑ i, mixedEmbedding F (D k i) * eI F ι p.1 i) *
      g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ p.2) := by
  unfold pureA
  congr 2 <;> funext k
  · refine ((map_sum ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
        (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
        (fun i => algebraMap F (AF F) (D k i) * glue p i) Finset.univ)).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (map_mul _ _ _).trans ?_
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (D k i)) *
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F ι p.1 i)) = _
    rw [RingEquiv.apply_symm_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  · exact (map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => algebraMap F (AF F) (D k i) * glue p i) Finset.univ)

theorem integrable_SB {g : Vf F ι → ℂ} (hg : g ∈ SB (Vf F ι)) : Integrable g Measure.addHaar :=
  hg.1.continuous.integrable_of_hasCompactSupport hg.2

theorem pureA_glue_eq (D : Matrix κ ι F)
    (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ)
    (hT : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : ι → mixedEmbedding.mixedSpace F),
        T f a = f (fun k => ∑ i, mixedEmbedding F (D k i) * a i))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    (fun p : Vi F ι × Vf F ι => pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p)) =
      fun p => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f) p.1 *
        g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ p.2) := by
  funext p
  rw [pureA_mulVec_glue, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hT]

theorem integrable_glue (D : Matrix κ ι F) (hD : ∀ z : ι → F, D *ᵥ z = 0 → z = 0)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Integrable (fun p : Vi F ι × Vf F ι => Φ (D.map (algebraMap F (AF F)) *ᵥ glue p)) (mu F ι) := by
  obtain ⟨T, hT⟩ := GlobalTheory.ArchPull.exists_pull F ι κ D hD
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    rw [pureA_glue_eq D T hT f g]
    exact (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f)).integrable.mul_prod
      (integrable_SB (GlobalTheory.FinPull.pullback_mem_SB F ι κ D hD g hg))
  | zero => exact integrable_zero _ _ _
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

end GlobalTheory.HaarPull

namespace GlobalTheory

open GlobalTheory.DiagForm GlobalTheory.DiagUniq GlobalTheory.HaarPull

theorem integral_pull_injective : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∀ ν : @Measure (ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      (∀ Φ ∈ schA F κ, (letI : MeasurableSpace (ι → AF F) := borel _;
        Integrable (fun w => Φ (D.map (algebraMap F (AF F)) *ᵥ w)) ν)) ∧
      ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, (letI : MeasurableSpace (ι → AF F) := borel _;
          ∫ w, pureA F f g (D.map (algebraMap F (AF F)) *ᵥ w) ∂ν) = T f := by
  intro F _ _ ι κ _ _ D hD ν hν
  letI : MeasurableSpace (ι → AF F) := borel _
  haveI : BorelSpace (ι → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hν
  haveI : ((mu F ι).map (glueE F ι)).IsAddHaarMeasure := (glueE F ι).isAddHaarMeasure_map _
  have h := Measure.isAddLeftInvariant_eq_smul ν ((mu F ι).map (glueE F ι))
  set c := Measure.addHaarScalarFactor ν ((mu F ι).map (glueE F ι))
  have me := (glueE F ι).toHomeomorph.measurableEmbedding
  refine ⟨fun Φ hΦ => ?_, fun g hg => ?_⟩
  · rw [h]
    refine Integrable.smul_measure_nnreal ?_
    exact me.integrable_map_iff.2 (integrable_glue D hD hΦ)
  · obtain ⟨T, hT⟩ := GlobalTheory.ArchPull.exists_pull F ι κ D hD
    refine ⟨(((c : ℝ) : ℂ) * ∫ v, g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ v) ∂(Measure.addHaar : Measure (Vf F ι))) •
      ((SchwartzMap.integralCLM ℂ (volume : Measure (Vi F ι))).comp
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι)).comp T)), fun f => ?_⟩
    rw [h, integral_smul_nnreal_measure]
    change c • ∫ x, pureA F f g (D.map (algebraMap F (AF F)) *ᵥ x) ∂((mu F ι).map (glueE F ι).toHomeomorph) = _
    rw [me.integral_map]
    have e := pureA_glue_eq D T hT f g
    change c • ∫ p, (fun p : Vi F ι × Vf F ι => pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p)) p ∂(mu F ι) = _
    rw [e, mu, integral_prod_mul (fun u : Vi F ι => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f) u)
      (fun v : Vf F ι => g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ v))]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
      smul_eq_mul, NNReal.smul_def, Complex.real_smul]
    ring

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.DiagSiegelUniq

open GlobalTheory.WeilM

theorem diagMat_eq_mul {A : Type} [CommRing A] {m n : ℕ} (w : Matrix (Fin m) (Fin n) A) :
    GlobalTheory.DiagSiegel.diagMat w =
      w * ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A).submatrix finSumFinEquiv.symm id)ᵀ := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j <;>
    simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, id] <;>
    simp [diagCols, Matrix.one_apply]

theorem transpose_transport (D : D7) (S T : HSp D) (ν : Measure (Formalism.IndefR.Datum.WO T S))
    (𝓕 : Set (Formalism.IndefR.Datum.WO T S)) (h : Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕) :
    ∃ (ν' : Measure (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank))
      (𝓕' : Set (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank)),
      ν'.IsAddHaarMeasure ∧ IsAddFundamentalDomain (Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank) 𝓕' ν' ∧
      ∀ f : Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E) → ℂ,
        ∫ u in 𝓕', f u ∂ν' = ∫ w in 𝓕, f wᵀ ∂ν := by
  classical
  haveI : BorelSpace (Formalism.IndefR.Datum.WO T S) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank) := ⟨rfl⟩
  obtain ⟨hH, hF, -⟩ := h
  let e : Formalism.IndefR.Datum.WO T S ≃+ Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank :=
    Matrix.transposeAddEquiv _ _ _
  have hc : Continuous e := Continuous.matrix_transpose continuous_id
  have hcs : Continuous e.symm := Continuous.matrix_transpose continuous_id
  let E' : Formalism.IndefR.Datum.WO T S ≃ᵐ Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank :=
    (Homeomorph.mk e.toEquiv hc hcs).toMeasurableEquiv
  have hE' : ∀ w, E' w = wᵀ := fun _ => rfl
  let eG : Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank ≃ ratL S T :=
    { toFun := fun g => ⟨(g : Matrix (Fin T.rank) (Fin S.rank) _)ᵀ, by
        obtain ⟨γ, hγ⟩ := g.2
        exact ⟨γᵀ, by rw [← hγ]; rfl⟩⟩
      invFun := fun g => ⟨(g : Matrix (Fin S.rank) (Fin T.rank) _)ᵀ, by
        obtain ⟨γ, hγ⟩ := g.2
        exact ⟨γᵀ, by rw [← hγ]; rfl⟩⟩
      left_inv := fun g => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun g => Subtype.ext (Matrix.transpose_transpose _) }
  refine ⟨ν.map E', E' '' 𝓕, ?_, ?_, fun f => ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map ν e hc hcs
  · refine hF.image_of_equiv E'.toEquiv (E'.quasiMeasurePreserving_symm ν) eG fun g x => ?_
    show (((eG g : ratL S T) : Matrix (Fin S.rank) (Fin T.rank) _) + x)ᵀ = (g : Matrix (Fin T.rank) (Fin S.rank) _) + xᵀ
    rw [Matrix.transpose_add]
    exact congrArg (· + xᵀ) (Matrix.transpose_transpose _)
  · rw [E'.restrict_map, E'.preimage_image, MeasureTheory.integral_map_equiv]
    rfl

theorem lubinTateSeries_eq_of_coeff_one_eq (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hξ : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (κ : Type) [Fintype κ]
    (J' : Matrix (Fin (T.rank + T.rank)) (Fin (T.rank + T.rank)) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hJ : incM D.host.F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG T.gram)ᵀ = J')
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ J' (incM D.host.F JB)) κ)
    (hrat : ∀ x : Matrix (Fin (T.rank + T.rank)) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i)))
    (ν' : Measure (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank))
    (𝓕' : Set (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank)) (hν' : ν'.IsAddHaarMeasure)
    (h𝓕' : IsAddFundamentalDomain (Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank) 𝓕' ν')
    (l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ)
    (hinv : ∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
          (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) :
    ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν' 𝓕'
      ((diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank)
        (AF D.host.F ⊗[D.host.F] D.host.E)).submatrix finSumFinEquiv.symm id)
      (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) := by
  subst hJ
  classical
  obtain ⟨v₁, -, -, ⟨τ₁⟩⟩ := GlobalTheory.TripleDarboux.exists_good_place D ∅
  let B : Base D.host.F D.host.E :=
    { ψ := ψ, emb := fun _ => Classical.arbitrary _, mα := 0, mβ := 0, P := ∅,
      τ := fun v => absurd v.2 (Finset.notMem_empty _), v₁ := v₁, τ₁ := τ₁ }
  have hB : B.IsGood D.sp.cm.sig :=
    GlobalTheory.TripleDarboux.base_isGood B hψ fun v hv => absurd hv (Finset.notMem_empty _)
  exact GlobalTheory.T.diagonalLagrangian_invariantForm_unique D.host.F D.host.E D.sp.cm.sig B hB S.rank T.rank S.gram T.gram
    (GlobalTheory.Doubling.isHermND_gram S) (GlobalTheory.Doubling.isHermND_gram T) D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    (Formalism.L2.Pj.conj_xi0_alt D) JB ξ hξ κ co hrat ν' 𝓕' hν' h𝓕' l hl fun z Φ hΦ => by
      rw [← diagMat_eq_mul]
      exact hinv z Φ hΦ

theorem uniq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO T S)) (𝓕 : Set (Formalism.IndefR.Datum.WO T S)),
            Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕 →
          ∀ l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ →
            (∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
              ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
                  (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) →
            ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕
              (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Φ) := by
  intro D ψ hψ S T JB ξ hξ κ _ co hrat ν 𝓕 hcov l hl hinv
  obtain ⟨ν', 𝓕', hν', h𝓕', hint⟩ := transpose_transport D S T ν 𝓕 hcov
  have hJ : incM D.host.F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG T.gram)ᵀ =
      incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ) := by
    rw [← GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM (F := D.host.F) (J := T.gram) rfl,
      GlobalTheory.WeilSchrodinger.DblTarget.reindex_dbl_incM T rfl]
  obtain ⟨c, hc⟩ := lubinTateSeries_eq_of_coeff_one_eq D ψ hψ S T JB ξ hξ κ _ hJ co hrat ν' 𝓕' hν' h𝓕' l hl hinv
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [hc Φ hΦ, GlobalTheory.LagrTheta.lagrInt, hint, GlobalTheory.DiagSiegel.thetaDiagInt]
  congr 2
  funext w
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilSchrodinger.transD_rho,
    diagMat_eq_mul, Matrix.transpose_mul, Matrix.transpose_transpose]

end GlobalTheory.DiagSiegelUniq

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

theorem _root_.GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S : Finset (Fin r), GlobalTheory.Cusp.Cocompact (ratPts σ J) (GlobalTheory.StdPar.unip σ J X S) := by
  first | exact @GlobalTheory.CuspCocpt.cocompact_unip | exact GlobalTheory.CuspCocpt.cocompact_unip | (intros; apply GlobalTheory.CuspCocpt.cocompact_unip <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

theorem _root_.GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S T : Finset (Fin r), S ⊆ T → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T →
        ∃ m ∈ ratPts σ J, m ∈ GlobalTheory.StdPar.levi σ J X Y S ∧ ∃ ν ∈ GlobalTheory.StdPar.unip σ J X S, γ = m * ν := by
  first | exact @GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip | exact GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip | (intros; apply GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof.FiniteInertiaImage

theorem galTate_eq_of_agree {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)) (E : ℕ) (hE0 : 0 < E)
    (hE : ∀ σ ∈ I, galTate A l σ ^ E = 1) {σ τ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ I) (hτ : τ ∈ I)
    (h : ∀ x : ptOver K Ω ⟶ A, x ^ (l ^ 2) = 1 → galPts A σ x = galPts A τ x) :
    galTate A l σ = galTate A l τ := by
  have hu : galTate A l (σ * τ⁻¹) = 1 := by
    refine GlobalTheory.T.eq_one_of_finite_order_of_trivial_mod_sq_tateModule l (ptOver K Ω ⟶ A) _ E hE0 (hE _ (I.mul_mem hσ (I.inv_mem hτ))) fun t => ?_
    rw [lev_galTate]
    have hy : galPts A τ⁻¹ (t.lev 2) ^ (l ^ 2) = 1 := by rw [← map_pow, t.lev_pow, map_one]
    have e1 : galPts A (σ * τ⁻¹) (t.lev 2) = galPts A σ (galPts A τ⁻¹ (t.lev 2)) := by
      change specAut (σ * τ⁻¹) ≫ t.lev 2 = specAut σ ≫ specAut τ⁻¹ ≫ t.lev 2
      rw [specAut_mul, Category.assoc]
    have e2 : galPts A τ (galPts A τ⁻¹ (t.lev 2)) = t.lev 2 := by
      change specAut τ ≫ specAut τ⁻¹ ≫ t.lev 2 = t.lev 2
      rw [← Category.assoc, ← specAut_mul, mul_inv_cancel, specAut_one, Category.id_comp]
    rw [e1, h _ hy, e2]
  calc galTate A l σ = galTate A l (σ * τ⁻¹ * τ) := by rw [inv_mul_cancel_right]
    _ = galTate A l τ := by rw [map_mul, hu, _root_.one_mul]

theorem finite_image_galTate : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)),
    Finite {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1} →
    (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) →
    (∃ E : ℕ, 0 < E ∧ ∀ σ ∈ I, galTate A l σ ^ E = 1) →
    (galTate A l '' (I : Set (Ω ≃ₐ[K] Ω))).Finite := by
  intro K Ω _ _ _ A _ _ l _ I hS _ ⟨E, hE0, hE⟩
  let S := {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1}
  have hmap : ∀ (σ : Ω ≃ₐ[K] Ω) (x : S), galPts A σ x.1 ^ (l ^ 2) = 1 := fun σ x => by
    rw [← map_pow, x.2, map_one]
  let g : (Ω ≃ₐ[K] Ω) → S → S := fun σ x => ⟨galPts A σ x.1, hmap σ x⟩
  let F : galTate A l '' (I : Set (Ω ≃ₐ[K] Ω)) → S → S := fun u => g u.2.choose
  have hF : Function.Injective F := by
    rintro ⟨u, hu⟩ ⟨u', hu'⟩ e
    have h1 := hu.choose_spec
    have h2 := hu'.choose_spec
    refine Subtype.ext ?_
    change u = u'
    rw [← h1.2, ← h2.2]
    refine galTate_eq_of_agree A l I E hE0 hE h1.1 h2.1 fun x hx => ?_
    have := congrFun e ⟨x, hx⟩
    exact congrArg Subtype.val this
  exact Set.finite_coe_iff.1 (Finite.of_injective F hF)

end GlobalTheory.Proof.FiniteInertiaImage
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRedCut

theorem exists_finiteDimensional_galTate_eq_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], LocallyOfFiniteType A.hom →
    ∀ (l : ℕ) [Fact l.Prime] (I : Set (Ω ≃ₐ[K] Ω)), (galTate A l '' I).Finite →
      ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
        ∀ σ ∈ I, (∀ a ∈ L, σ a = a) → galTate A l σ = 1 := by
  intro K Ω _ _ _ _ A _ _ hA l _ I hI
  classical
  have key : ∀ s : Module.End ℤ_[l] (Tate l (ptOver K Ω ⟶ A)), ∃ F : Finset Ω,
      ∀ σ : Ω ≃ₐ[K] Ω, galTate A l σ = s → (∀ a ∈ F, σ a = a) → s = 1 := by
    intro s
    by_cases hs : s = 1
    · exact ⟨∅, fun _ _ _ => hs⟩
    · have hex : ∃ (t : Tate l (ptOver K Ω ⟶ A)) (n : ℕ), (s t).lev n ≠ t.lev n := by
        by_contra h
        push_neg at h
        exact hs (LinearMap.ext fun t => Tate.ext fun n => h t n)
      obtain ⟨t, n, htn⟩ := hex
      obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_fixing_point_locallyFiniteType K Ω A hA (t.lev n)
      refine ⟨F, fun σ hσ hfix => ?_⟩
      exfalso
      apply htn
      rw [← hσ, lev_galTate]
      exact hF σ hfix
  choose F hF using key
  refine ⟨IntermediateField.adjoin K ((hI.toFinset.biUnion F : Finset Ω) : Set Ω), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  · intro σ hσ hfix
    refine hF (galTate A l σ) σ rfl fun a ha => hfix a (IntermediateField.subset_adjoin _ _ ?_)
    rw [Finset.mem_coe]
    exact Finset.mem_biUnion.2 ⟨_, hI.mem_toFinset.2 ⟨σ, hσ, rfl⟩, ha⟩

end GlobalTheory.AbVarRedCut
end

section

open scoped Pointwise
open GlobalTheory.Published GlobalTheory.Published.AbVarRed

namespace GlobalTheory.ValConj

theorem isLocallyConstant_apply {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] (x : Ω) :
    IsLocallyConstant (fun g : Ω ≃ₐ[K] Ω => g x) := by
  let : TopologicalSpace Ω := ⊥
  have : DiscreteTopology Ω := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) Ω :=
    continuousSMul_iff_stabilizer_isOpen.mpr fun y => stabilizer_isOpen_of_isIntegral y
  rw [IsLocallyConstant.iff_continuous]
  exact (continuous_id.smul continuous_const : Continuous fun g : Ω ≃ₐ[K] Ω => g • x)

theorem exists_smul_eq_of_isAbove (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (V V' : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) (hV' : IsAbove R K V'.toSubring) :
    ∃ g : Ω ≃ₐ[K] Ω, g • V = V' := by
  classical
  have key := (isCompact_univ (X := Ω ≃ₐ[K] Ω)).inter_iInter_nonempty
    (fun x : Ω => {g : Ω ≃ₐ[K] Ω | g x ∈ V' ↔ x ∈ V})
    (fun x => ((isLocallyConstant_apply (K := K) x).comp (fun y => y ∈ V' ↔ x ∈ V)).isClosed_fiber True
      |> fun h => by simpa using h)
    (fun u => by
      let L : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K (u : Set Ω)).toIntermediateField
      have hL : ∀ x ∈ u, x ∈ L := fun x hx => FiniteGaloisIntermediateField.subset_adjoin K (u : Set Ω) hx
      have hc : ∀ W : ValuationSubring Ω, IsAbove R K W.toSubring →
          IsAbove R K (W.comap (algebraMap L Ω)).toSubring := fun W hW => by
        unfold IsAbove at hW ⊢
        rw [← hW]
        ext y
        rfl
      obtain ⟨τ, hτ⟩ := GlobalTheory.T.galois_transitive_on_valuation_rings R K L _ _ (hc V hV) (hc V' hV')
      refine ⟨τ.liftNormal Ω, trivial, Set.mem_iInter₂.2 fun x hx => ?_⟩
      have h1 : τ.liftNormal Ω x = algebraMap L Ω (τ ⟨x, hL x hx⟩) := τ.liftNormal_commutes Ω ⟨x, hL x hx⟩
      change τ.liftNormal Ω x ∈ V' ↔ x ∈ V
      rw [h1, ← ValuationSubring.mem_comap, ← hτ]
      exact ValuationSubring.smul_mem_pointwise_smul_iff (g := τ) (x := (⟨x, hL x hx⟩ : L))
        (S := V.comap (algebraMap L Ω)))
  obtain ⟨g, -, hg⟩ := key
  refine ⟨g, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := g.surjective y
  have := Set.mem_iInter.1 hg x
  exact (ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (x := x)).trans (Iff.symm this)

end GlobalTheory.ValConj
end
