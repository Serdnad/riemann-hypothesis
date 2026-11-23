module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

open scoped ContDiff

namespace GlobalTheory.CxForm.FormMul

theorem isForm_mul : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld),
    A.IsForm α → A.IsForm β → A.IsForm (α * β) := by
  intro M _ n A α β hα hβ
  refine ⟨fun i S => ?_, fun x x' h => ?_⟩
  · have e : (fun v => (bas n).repr (A.loc (α * β) i v) S) = fun v => ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
        (bas n).repr (A.loc α i v) p.1 * (bas n).repr (A.loc β i v) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
      funext fun v => by rw [loc_mul, repr_mul]
    rw [e]
    exact ContDiffOn.sum fun p _ => ((hα.smooth i p.1).mul (hβ.smooth i p.2)).mul contDiffOn_const
  · show α x * β x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (α x' * β x')
    rw [map_mul, ← hα.compat x x' h, ← hβ.compat x x' h]

end GlobalTheory.CxForm.FormMul
end

section

open GlobalTheory GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem pull_comp_linear : ∀ (n n' n'' : ℕ) (L : V n →L[ℂ] V n') (L' : V n' →L[ℂ] V n'') (α : Alt n''),
    pull (L'.comp L) α = pull L (pull L' α) :=
  fun n n' n'' L L' α => GlobalTheory.CxForm.pull_comp n'' n' n L L' α

end GlobalTheory.FlagCell2
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.pullbackComplexFormsLinearMap_comp : ∀ (k m n : ℕ) (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (γ : Alt k), pull (L'.comp L) γ = pull L (pull L' γ) := by
  first | exact @GlobalTheory.CxForm.pull_comp | exact GlobalTheory.CxForm.pull_comp | (intros; apply GlobalTheory.CxForm.pull_comp <;> assumption)
end

section

open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.topDegreeDensity_pullback_eq_normSq_det_mul : ∀ {n : ℕ} (L : V n →L[ℂ] V n) (ω : GlobalTheory.CxForm.Alt n), GlobalTheory.CxForm.dens (GlobalTheory.CxForm.pull L ω) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) * GlobalTheory.CxForm.dens ω := by
  first | exact @GlobalTheory.CxForm.dens_pull | exact GlobalTheory.CxForm.dens_pull | (intros; apply GlobalTheory.CxForm.dens_pull <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.CxForm.HolAtlas

theorem integral_eq_integral_chart_of_support : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld)
    (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) →
    A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  intro M _ _ _ _ _ _ n A α i K hα hK hKs h0
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set r : A.ι → V n → ℝ := fun j v => (dens (A.loc α j v)).re with hr
  have dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

  have hc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      r j (A.e j y) = ‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2 * r k (A.e k y) := by
    intro j k y hj hk
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    have h2 := A.loc_crd α (⟨(k, y), hk⟩ : A.Pt)
    have h3 := hα.compat (⟨(j, y), hj⟩ : A.Pt) ⟨(k, y), hk⟩ rfl
    simp only [hr]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul]
    rfl

  have hz : ∀ j y, y ∈ (A.e j).source → y ∉ K → r j (A.e j y) = 0 := by
    intro j y hj hy
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    simp only [hr]
    erw [h1, h0 _ hy, dens_zero]
    rfl

  have hpart : ∀ ε : ℤˣ, A.part α ε univ =
      ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    set ρ : A.ι → M → ENNReal := fun j y => ENNReal.ofReal (((ε : ℤ) : ℝ) * r j (A.e j y)) with hρ
    have hp : A.part α ε = ChartGlue.glueMeas A.e ρ := rfl
    have hρc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
        ρ j y = ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) * ρ k y := by
      intro j k y hj hk
      simp only [hρ]
      rw [hc j k y hj hk, ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    have hcompl : ChartGlue.glueMeas A.e ρ Kᶜ = 0 := by
      have key : ChartGlue.glueMeas A.e ρ ≤ (ChartGlue.glueMeas A.e ρ).restrict K := iSup_le fun j => by
        have e : ChartGlue.chartMeas (A.e j) (ρ j) Kᶜ = 0 := by
          rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
          refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
            ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
          rintro _ ⟨y, hy, rfl⟩
          simp only [hρ, (A.e j).left_inv hy.1, hz j y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero, Pi.zero_apply]
        rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
        exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j) (ρ j)) j)
      refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
      rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
    rw [hp, ← measure_add_measure_compl hKm, hcompl, add_zero,
      ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hKm hKs, ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs]
    refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hKm hKs) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [hρ, (A.e i).left_inv (hKs hy)]

  have hBc : IsCompact (A.e i '' K) := hK.image_of_continuousOn ((A.e i).continuousOn.mono hKs)
  have hBt : A.e i '' K ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hKs hy)
  have hH0 : ∀ v ∉ A.e i '' K, r i v = 0 := by
    intro v hv
    by_cases ht : v ∈ (A.e i).target
    · have hs := (A.e i).map_target ht
      have hnK : (A.e i).symm v ∉ K := fun hk => hv ⟨_, hk, (A.e i).right_inv ht⟩
      have := hz i _ hs hnK
      rwa [(A.e i).right_inv ht] at this
    · have hl : A.loc α i v = 0 := by
        unfold loc
        exact dif_neg ht
      simp only [hr, hl, dens_zero, Complex.zero_re]
  have hcon : ContinuousOn (r i) (A.e i).target :=
    Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)
  have hHc : Continuous (r i) := continuous_iff_continuousAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact hcon.continuousAt ((A.e i).open_target.mem_nhds ht)
    · have : r i =ᶠ[𝓝 v] fun _ => 0 := by
        filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds (fun h => ht (hBt h))] with w hw
        exact hH0 w hw
      exact continuousAt_const.congr this.symm
  have hHi : Integrable (r i) := hHc.integrable_of_hasCompactSupport (HasCompactSupport.intro hBc hH0)
  have hl : ∀ ε : ℤˣ, ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) =
      ∫⁻ v, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    rw [← lintegral_indicator hBc.measurableSet]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A.e i '' K
    · rw [Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem hv, hH0 v hv, mul_zero, ENNReal.ofReal_zero]
  have e1 := hpart 1
  have e2 := hpart (-1)
  rw [hl] at e1 e2
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_one_mul] at e1 e2
  simp only [GlobalTheory.CxForm.HolAtlas.integral, Measure.real, e1, e2]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hHi).symm

end GlobalTheory.CxForm.HolAtlas
end
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.wirtingerDerivs_comp_holomorphic_pullback_dz : ∀ (m n : ℕ) (τ : V m → V n) (c : V n → ℂ) (v : V m), DifferentiableAt ℂ τ v → DifferentiableAt ℝ c (τ v) →
    (∑ a, del (fun x => c (τ x)) v (coordVec a) • dz a : Alt m) = pull (fderiv ℂ τ v) (∑ a, del c (τ v) (coordVec a) • dz a) ∧
    (∑ a, dbar (fun x => c (τ x)) v (coordVec a) • dzb a : Alt m) = pull (fderiv ℂ τ v) (∑ a, dbar c (τ v) (coordVec a) • dzb a) := by
  first | exact @GlobalTheory.LineForm.del_dbar_comp_holo_pull | exact GlobalTheory.LineForm.del_dbar_comp_holo_pull | (intros; apply GlobalTheory.LineForm.del_dbar_comp_holo_pull <;> assumption)
end

section

namespace GlobalTheory.Published

theorem arDegree_of_heightProjection : HeightProjection → ChernDegreeComplex → ArDegree :=
  fun H H' => ⟨arBirational_of_arProj (GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula H), GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case H'⟩

end GlobalTheory.Published
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.infinityType_unitaryHeckeCharCM_restricting_to_eta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E), μ.IsUnitary →
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    ∃ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) ∧
      ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v := by
  first | exact @GlobalTheory.MuInfType.infType | exact GlobalTheory.MuInfType.infType | (intros; apply GlobalTheory.MuInfType.infType <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GKNorm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_splitCentre_eigen (π : CuspSub E a) : ∃ c : ℂ, ∀ φ ∈ π.V, ∀ (t : ℝ) (g : GA E a),
    φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  obtain ⟨c, hc⟩ := GlobalTheory.CuspRep.Central.lie_scalar π (1 : Cinf E)
  refine ⟨c, fun φ hφ t g => ?_⟩
  have e3 : GlobalTheory.CuspRep.Central.scL a (fun _ : InfinitePlace E => (t : ℂ)) =
      t • GlobalTheory.CuspRep.Central.scL (E := E) a 1 := by
    ext i j w
    by_cases hij : i = j <;> simp [hij]
  have h1 := GlobalTheory.CuspRep.Central.rs_exp (fun _ : InfinitePlace E => (t : ℂ)) (c * t) φ (by
    rw [e3, map_smul, LinearMap.smul_apply, hc φ hφ, mul_comm, mul_smul, Complex.coe_smul])
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar]
  exact congrFun (congrArg Subtype.val h1) g

theorem exists_twist_isNormalised : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, ∃ χ : HChar E, GlobalTheory.DiscSpec.IsNormalised (π.twist χ) := by
  intro E _ _ _ a ha π
  obtain ⟨c, hs⟩ := exists_splitCentre_eigen π
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) (a := a) (by omega) (-c)
  refine ⟨χ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩ t g
  change (mulChi a χ φ).1 _ = (mulChi a χ φ).1 _
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hχ, hs φ hφ, mul_mul_mul_comm, ← Complex.exp_add]
  simp

end GlobalTheory.GKNorm

end
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.voganNormSq_lt_of_remove_noncompactRoot : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StrictAnti lam → IsHolChamber ε lam → ∀ a b : Fin n, ε a = true → ε b = false → vNormSq ε (lowK ε lam - root a b) < vNormSq ε (lowK ε lam) := by
  first | exact @GlobalTheory.HolomorphicRootNormBound.vNormSq_lt_of_root | exact GlobalTheory.HolomorphicRootNormBound.vNormSq_lt_of_root | (intros; apply GlobalTheory.HolomorphicRootNormBound.vNormSq_lt_of_root <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.strong_approximation_SL2_adeles : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : Matrix (Fin 2) (Fin 2) (AF F), g.det = 1 → g ∈ closure {x : Matrix (Fin 2) (Fin 2) (AF F) | ∃ γ : Matrix (Fin 2) (Fin 2) F, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) (AF F), h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map (algebraMap F (AF F)) * h} := by
  first | exact @GlobalTheory.StrongApproximationSL2.strongApprox_SL2 | exact GlobalTheory.StrongApproximationSL2.strongApprox_SL2 | (intros; apply GlobalTheory.StrongApproximationSL2.strongApprox_SL2 <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SUSuppCompact

theorem isCompact_SUSupp_of_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (∀ w ∈ S₁, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g = JR w.Completion J → ∀ i j, g i j ∈ C) → (∀ v ∈ S₂, ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g = JR (Fv F v) J → ∀ i j, g i j ∈ C) → IsCompact (SUSupp σ J ε) := by
  intro F E _ _ _ _ _ σ hCM M J hJ S₁ S₂ ε hε h₁ h₂
  classical
  haveI : FiniteDimensional F E := inferInstance
  have h₁' : ∀ w : InfinitePlace F, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ (w ∈ S₁ →
      ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g =
        JR w.Completion J → ∀ i j, g i j ∈ C) := by
    intro w
    by_cases hw : w ∈ S₁
    · obtain ⟨C, hC, hC'⟩ := h₁ w hw
      exact ⟨C, hC, fun _ => hC'⟩
    · exact ⟨∅, isCompact_empty, fun h => absurd h hw⟩
  have h₂' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ (v ∈ S₂ →
      ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g =
        JR (Fv F v) J → ∀ i j, g i j ∈ C) := by
    intro v
    by_cases hv : v ∈ S₂
    · obtain ⟨C, hC, hC'⟩ := h₂ v hv
      exact ⟨C, hC, fun _ => hC'⟩
    · exact ⟨∅, isCompact_empty, fun h => absurd h hv⟩
  choose C₁ hC₁ hC₁' using h₁'
  choose C₂ hC₂ hC₂' using h₂'
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Set (AF F ⊗[F] E)), (∀ i ∈ s, IsCompact (f i)) →
      IsCompact (∑ i ∈ s, f i) := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, ← Set.singleton_zero]; exact isCompact_singleton
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  set e := algebraMap (AF F) (AF F ⊗[F] E) ε with he
  let X : Set (AF F ⊗[F] E) := (fun δ => δ * (1 - e)) '' ({0, 1} : Set (AF F ⊗[F] E)) +
    (∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w) '' C₁ w) +
    ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v) '' C₂ v
  have hX : IsCompact X :=
    ((((Set.toFinite _).isCompact).image (continuous_id.mul continuous_const)).add
      (hsum _ _ fun w _ => (hC₁ w).image (GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place _))).add (hsum _ _ fun v _ => (hC₂ v).image (GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place _))
  refine GlobalTheory.T.isCompact_specialUnitarySupportedAtPlaces σ J ε X hX (GlobalTheory.T.isClosed_specialUnitarySupportedAtPlaces σ J ε) fun g hg i j => ?_
  have hu : Formalism.UG.cT (sigR (AF F) σ) ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      JR (AF F) J * ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = JR (AF F) J := by
    let g' : HR (AF F) σ J := g
    exact g'.2
  set a := ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j with ha
  set δ := (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j with hδ
  have hfix : e * (a - δ) = a - δ := by
    have := hg.2 i j
    simpa only [Matrix.sub_apply] using this
  have hdec : a = δ * (1 - e) + e * a := by linear_combination (-1 : AF F ⊗[F] E) * hfix
  rw [hdec, GlobalTheory.T.idempotentAdeleOfPlaces_mul_eq_sum_components S₁ S₂ ε hε a, ← add_assoc]
  refine Set.add_mem_add (Set.add_mem_add ⟨δ, ?_, rfl⟩ (Set.finsetSum_mem_finsetSum _ _ _ fun w hw => ⟨_, ?_, rfl⟩))
    (Set.finsetSum_mem_finsetSum _ _ _ fun v hv => ⟨_, ?_, rfl⟩)
  · rw [hδ, Matrix.one_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact hC₁' w hw _ (GlobalTheory.T.unitaryEquation_baseChange_algHom σ J _ _ hu) i j
  · exact hC₂' v hv _ (GlobalTheory.T.unitaryEquation_baseChange_algHom σ J _ _ hu) i j

end GlobalTheory.SUSuppCompact

end
end
