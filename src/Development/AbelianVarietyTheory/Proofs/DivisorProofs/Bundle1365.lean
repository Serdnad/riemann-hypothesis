module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.Points GlobalTheory.SemiPosBir

namespace GlobalTheory.SemiPosEtale

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Z ⟶ Sp k} {σ : k →+* ℂ}
  {D : ℕ}

theorem exists_map_eq_of_etale (j : Z ⟶ X) [Etale j] (hj : j ≫ p = q) {y : CxPts p σ}
    (hy : y.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range j) :
    ∃ z : CxPts q σ, PtsOver.map j hj _ z = y := by
  obtain ⟨v, hv⟩ := hy
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := y.1) v _ hv
  have : JacobsonSpace ↥(pullback j y.1) := LocallyOfFiniteType.jacobsonSpace (pullback.snd j y.1)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback j y.1)))
    ⟨w, trivial⟩ isOpen_univ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨⟨pointOfClosedPoint (pullback.snd j y.1) c hc ≫ pullback.fst j y.1, ?_⟩, Subtype.ext ?_⟩
  · rw [← hj, Category.assoc, pullback.condition_assoc, pointOfClosedPoint_comp_assoc]
    exact y.2
  · change (pointOfClosedPoint (pullback.snd j y.1) c hc ≫ pullback.fst j y.1) ≫ j = y.1
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

def img (j : Z ⟶ X) [Etale j] : X.Opens := ⟨Set.range j, j.isOpenMap.isOpen_range⟩

theorem PosOn.of_etale (j : Z ⟶ X) [Etale j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)}
    (h : PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S)) :
    PosOn D f (S ∩ ptsIn p σ (img j)) := fun c y hy ξ => by
  obtain ⟨z, rfl⟩ := exists_map_eq_of_etale j hj (mem_ptsIn.1 hy.2.2)
  obtain ⟨W, hW, hzW, e⟩ := exists_isAffineOpen_le z.1 (V := j ⁻¹ᵁ c.U) (c.source_subset hy.1)
  have h₂ : (MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE _ W e).hom (c.x a)).Etale := by
    rw [← appLE_comp_eval hj e]
    exact RingHom.Etale.stableUnderComposition _ _ c.etale
      (HasRingHomProperty.appLE @Etale j inferInstance ⟨c.U, c.affine⟩ ⟨W, hW⟩ e)
  obtain ⟨c', hc, rfl, hcx⟩ := AlgChart.exists_of_etale (y := z) hW _ h₂ hzW
  rw [← levi_pull hj f c c' e (congrFun hcx) hc hy.1]
  exact h c' _ ⟨hc, hy.2.1⟩ ξ

end GlobalTheory.SemiPosEtale

namespace GlobalTheory.SemiPosEtale

theorem semiPos_of_pull_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, (L.pull π hπ).SemiPos D → L.SemiPos D := by
  intro k _ X Y _ _ p q D hp _ π hπ V hV hE L hL σ i
  have := hp.isDomain
  have := hp.finite
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have : Etale (V.ι ≫ π) := hE
  have hj : (V.ι ≫ π) ≫ p = V.ι ≫ q := by rw [Category.assoc, hπ]
  have hU : ((img (V.ι ≫ π) : X.Opens) : Set X).Nonempty := by
    obtain ⟨v, hv⟩ := hV
    exact ⟨_, ⟨v, hv⟩, rfl⟩
  change PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i))
  refine PosOn.of_inter hσ (isOpen_ptsIn _) (L.cInf σ i) hU (PosOn.of_etale (V.ι ≫ π) hj ?_)
  let J : (L.B.pull π).ι := fun _ => i
  have h₀ : PosOn D (((L.φ σ).pull π hπ).φ J) (ptsIn q σ ((L.B.pull π).U J)) := hL σ J
  have e₁ : ptsIn q σ ((L.B.pull π).U J) =
      PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U i) := Set.ext fun z => by
    rw [Set.mem_preimage, mem_ptsIn, mem_ptsIn]
    exact ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩
  have e₂ : ((L.φ σ).pull π hπ).φ J = fun w => (L.φ σ).φ i (PtsOver.map π hπ _ w) :=
    funext ((L.φ σ).pull_φ π hπ J)
  rw [e₁, e₂] at h₀
  have h₁ := h₀.pull V.ι (q := V.ι ≫ q) rfl
  have e₃ (w : CxPts (V.ι ≫ q) σ) : PtsOver.map π hπ _ (PtsOver.map V.ι rfl _ w) =
      PtsOver.map (V.ι ≫ π) hj _ w := Subtype.ext (Category.assoc _ _ _)
  simp only [e₃] at h₁
  exact h₁

end GlobalTheory.SemiPosEtale
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section
attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

namespace GlobalTheory.DiagLagrNorm
open MeasureTheory GlobalTheory.DiagForm IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem map_eI_eq : ∃ k : NNReal, k ≠ 0 ∧
    Measure.map (eI F κ) (volume : Measure (Vi F κ)) = k • (volume : Measure (κ → mixedEmbedding.mixedSpace F)) := by
  have : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  have : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance
  have : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have : (Measure.map (eI F κ) (volume : Measure (Vi F κ))).IsAddHaarMeasure :=
    (eI F κ).isAddHaarMeasure_map volume
  exact ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem integral_compD {k : NNReal}
    (hk : Measure.map (eI F κ) (volume : Measure (Vi F κ)) = k • (volume : Measure (κ → mixedEmbedding.mixedSpace F)))
    (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) :
    SchwartzMap.integralCLM ℂ (volume : Measure (Vi F κ)) (compD F κ f) =
      (k : ℂ) * ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  rw [SchwartzMap.integralCLM_apply]
  have e : ∀ u, compD F κ f u = (fun x : κ → mixedEmbedding.mixedSpace F => f (Sum.elim x x)) (eI F κ u) :=
    fun u => rfl
  simp only [e]
  have h1 := integral_map_equiv (μ := (volume : Measure (Vi F κ))) (eI F κ).toHomeomorph.toMeasurableEquiv
    (fun x : κ → mixedEmbedding.mixedSpace F => f (Sum.elim x x))
  change ∫ y, f (Sum.elim y y) ∂(Measure.map (eI F κ) volume) = ∫ x, f (Sum.elim (eI F κ x) (eI F κ x)) at h1
  rw [hk, integral_smul_nnreal_measure] at h1
  rw [← h1, NNReal.smul_def, Complex.real_smul]

theorem exists_SB_ne : ∃ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F),
    (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) ≠ 0 := by
  obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
  set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
  have h0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun v => (v.adicCompletionIntegers F).zero_mem
  set U : Set (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => O
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hUc : IsCompact U := isCompact_univ_pi fun _ => hK
  set g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ := U.indicator fun _ => 1
  have hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hUc.isClosed, hUo⟩).isLocallyConstant,
      HasCompactSupport.intro hUc fun z hz => Set.indicator_of_notMem hz _⟩
  set V : Set (Vf F κ) := Set.univ.pi fun _ => O
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hVc : IsCompact V := isCompact_univ_pi fun _ => hK
  have hgV : (fun v : Vf F κ => g (Sum.elim v v)) = V.indicator fun _ => (1 : ℂ) := by
    funext v
    simp only [g, U, V, Set.indicator_apply, Set.mem_univ_pi, Sum.forall, Sum.elim_inl, Sum.elim_inr, and_self]
  refine ⟨g, hg, ?_⟩
  rw [hgV, integral_indicator_const _ hVo.measurableSet]
  have hpos : 0 < (Measure.addHaar : Measure (Vf F κ)) V := hVo.measure_pos _ ⟨0, fun i _ => h0⟩
  have hfin : (Measure.addHaar : Measure (Vf F κ)) V < ⊤ := hVc.measure_lt_top
  have : 0 < (Measure.addHaar : Measure (Vf F κ)).real V := ENNReal.toReal_pos hpos.ne' hfin.ne
  simpa using this.ne'

end GlobalTheory.DiagLagrNorm

namespace GlobalTheory.RealLift

open MeasureTheory GlobalTheory.DiagForm GlobalTheory.DiagLagrNorm

theorem diagLagr_invForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (AE F E), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d dd _ hdd
  obtain ⟨k, hk0, hk⟩ := map_eI_eq (F := F) (κ := κ)
  obtain ⟨g, hg, hc⟩ := exists_SB_ne (F := F) (κ := κ)
  set c : ℂ := (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) * (k : ℂ) with hcdef
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hc0 : c ≠ 0 := mul_ne_zero hc hk'
  refine ⟨c⁻¹ • lDiag F κ, ?_, ?_, g, hg, ?_⟩
  · intro g' hg'
    obtain ⟨T, hT⟩ := lDiag_adm (F := F) (κ := κ) g' hg'
    exact ⟨c⁻¹ • T, fun f => by simp [hT f]⟩
  · intro z φ hφ
    have hz : z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one]
    have hr : dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ =
        schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) φ := by
      rw [hz, Darboux.rho, hdd z z]
    simp only [LinearMap.smul_apply]
    rw [hr, lDiag_schr ψ _ _ hφ]
  · intro f
    simp only [LinearMap.smul_apply]
    rw [lDiag_pureA f hg, integral_compD hk, smul_eq_mul, hcdef]
    field_simp

end GlobalTheory.RealLift
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.DiagFormGlue

open GlobalTheory.DiagForm

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

theorem shiftOf_glue (p : Vi F κ × Vf F κ) : shiftOf (glue p) = p := by
  refine Prod.ext ?_ rfl
  change (eI F κ).symm (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i))) = p.1
  simp only [RingEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem glue_shiftOf (x : κ → AdeleRing (𝓞 F) F) : glue (shiftOf x) = x := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ ((eI F κ).symm _) i) = (x i).1
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact RingEquiv.symm_apply_apply _ _

theorem glue_add (p q : Vi F κ × Vf F κ) : glue (p + q) = glue p + glue q := by
  conv_lhs => rw [← shiftOf_glue q]
  exact glue_add_shiftOf p (glue q)

theorem ringEquiv_symm_eq :
    ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace F).symm := by
  funext z
  apply (GroundTheory.Global.homeomorphMixedSpace F).injective
  rw [Homeomorph.apply_symm_apply, GroundTheory.Global.homeomorphMixedSpace_apply, RingEquiv.apply_symm_apply]

theorem continuous_glue : Continuous (glue : Vi F κ × Vf F κ → κ → AdeleRing (𝓞 F) F) := by
  refine continuous_pi fun i => ?_
  show Continuous fun p : Vi F κ × Vf F κ =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i), p.2 i) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  rw [ringEquiv_symm_eq]
  exact ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp
    ((continuous_apply i).comp ((eI F κ).continuous.comp continuous_fst))).prodMk
    ((continuous_apply i).comp continuous_snd)

theorem continuous_shiftOf : Continuous (shiftOf : (κ → AdeleRing (𝓞 F) F) → Vi F κ × Vf F κ) := by
  refine Continuous.prodMk ((eI F κ).symm.continuous.comp (continuous_pi fun i => ?_))
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  show Continuous fun x : κ → AdeleRing (𝓞 F) F => GroundTheory.Global.homeomorphMixedSpace F (x i).1
  exact (GroundTheory.Global.homeomorphMixedSpace F).continuous.comp (continuous_fst.comp (continuous_apply i))


variable (F κ) in
def glueEquiv : (Vi F κ × Vf F κ) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun := glue
  invFun := shiftOf
  left_inv := shiftOf_glue
  right_inv := glue_shiftOf
  map_add' := glue_add

theorem exists_glue_measure :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
    ∃ c : NNReal, 0 < c ∧ (mu F κ).map glue = c • (adeleMeasurePi F (ι := κ)) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : (mu F κ).IsAddHaarMeasure := by unfold mu; infer_instance
  haveI : ((mu F κ).map (glueEquiv F κ)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map _ (glueEquiv F κ) continuous_glue continuous_shiftOf
  have h := Measure.isAddLeftInvariant_eq_smul ((mu F κ).map (glueEquiv F κ)) (adeleMeasurePi F (ι := κ))
  refine ⟨_, ?_, h⟩
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_smul] at h
  exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := (mu F κ).map (glueEquiv F κ))).open_pos
    Set.univ isOpen_univ Set.univ_nonempty (by rw [h]; rfl)


variable (F κ) in
def glueMEquiv :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
    (Vi F κ × Vf F κ) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  (Homeomorph.mk (glueEquiv F κ).toEquiv continuous_glue continuous_shiftOf).toMeasurableEquiv

end GlobalTheory.DiagFormGlue

namespace GlobalTheory

theorem diagForm_glue_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ H : (κ → AF F) → ℂ, (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔
      Integrable H (adeleMeasurePi F)) ∧
      ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F) := by
  intro F _ _ κ _
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  obtain ⟨c, hc, hmap⟩ := DiagFormGlue.exists_glue_measure (F := F) (κ := κ)
  have hmap' : (GlobalTheory.DiagForm.mu F κ).map (DiagFormGlue.glueMEquiv F κ) = c • adeleMeasurePi F (ι := κ) := hmap
  refine ⟨c, hc, fun H => ⟨?_, ?_⟩⟩
  · rw [← (integrable_smul_measure (f := H) (μ := adeleMeasurePi F (ι := κ)) (c := (c : ENNReal))
      (by exact_mod_cast hc.ne') ENNReal.coe_ne_top)]
    have e2 : (c : ENNReal) • adeleMeasurePi F (ι := κ) = c • adeleMeasurePi F (ι := κ) := rfl
    rw [e2, ← hmap', integrable_map_equiv]
    rfl
  · have h1 := integral_map_equiv (μ := GlobalTheory.DiagForm.mu F κ) (DiagFormGlue.glueMEquiv F κ) H
    rw [hmap', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h1
    exact h1.symm
end GlobalTheory
end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.StdPairCone

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk₁ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a) k :=
  Matrix.of fun i j => X i (Fin.castAdd a' j)

def blk₂ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a') k :=
  Matrix.of fun i j => X i (Fin.natAdd a j)

def IsGLO {n : ℕ} (g : Matrix (Fin n) (Fin n) k) : Prop := (∀ i j, g i j ∈ 𝒪[k]) ∧ valuation k g.det = 1


open Classical in
def stdA (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (X : Matrix (Fin a) (Fin (a + a')) k) : ℂ :=
  if h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0


open Classical in
def stdB (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (Y : Matrix (Fin a') (Fin (a + a')) k) : ℂ :=
  if h : (blk₂ Y).det ≠ 0 ∧ IsGLO (blk₂ Y) ∧ ∀ i j, blk₁ Y i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0


open Classical in
def unitInd (ν : kˣ →* ℂˣ) (y : k) : ℂ :=
  if h : y ≠ 0 ∧ valuation k y = 1 then (((ν (Units.mk0 y h.1))⁻¹ : ℂˣ) : ℂ) else 0

def sgn (s : ℤˣ) : kˣ := Units.map (Int.castRingHom k).toMonoidHom s

end Local

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Glob

end GlobalTheory.StdPairCone
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProperCentre

theorem exists_regAt_centre : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsProper s]
    (V : ValuationSubring Y.functionField) (x : X), (∀ f, RegAt x f → functionFieldMap s f ∈ V) →
    ∃ y : Y, s y ⤳ x ∧ ∀ f, RegAt y f → f ∈ V := by
  intro X Y _ _ s _ _ V x h
  let ψ : X.presheaf.stalk x →+* V :=
    ((GlobalTheory.functionFieldMap s).comp (algebraMap (X.presheaf.stalk x) X.functionField)).codRestrict
      V.toSubring (fun a => h _ ⟨a, rfl⟩)
  let r : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x
  have hc : GlobalTheory.genericFieldPoint Y ≫ s = GlobalTheory.specAlgebraMap V Y.functionField ≫ r := by
    rw [← GlobalTheory.specMap_functionFieldMap, ← GlobalTheory.specAlgebraMap_fromSpecStalk x]
    simp only [r, GlobalTheory.specAlgebraMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨GlobalTheory.valCentre s r (GlobalTheory.genericFieldPoint Y) hc, ?_, ?_⟩
  · rw [GlobalTheory.apply_valCentre_base]
    have := (IsLocalRing.specializes_closedPoint (R := X.presheaf.stalk x)
      (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint V))).map
      (X.fromSpecStalk x).continuous
    rw [Scheme.fromSpecStalk_closedPoint] at this
    exact this
  · have hd : GlobalTheory.DominatesStalk V (GlobalTheory.valCentre s r (GlobalTheory.genericFieldPoint Y) hc) :=
      GlobalTheory.dominatesStalk_iff_exists_hom.mpr
        ⟨_, GlobalTheory.specAlgebraMap_valExt s r (GlobalTheory.genericFieldPoint Y) hc, rfl⟩
    rintro f ⟨a, rfl⟩
    exact hd.1 a

end GlobalTheory.ProperCentre
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → Function.Bijective (functionFieldMap s) := by
  first | exact @GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict | exact GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict | (intros; apply GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict <;> assumption)
end
