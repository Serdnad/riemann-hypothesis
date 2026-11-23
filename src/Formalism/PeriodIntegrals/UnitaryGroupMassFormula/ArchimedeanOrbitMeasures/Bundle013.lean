module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushLF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul
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
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.AprimeInfK

open MeasureTheory Topology Set
open scoped ENNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {X : Type} [MulAction G X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem ker_meas (x0 : X) (hc : Continuous fun g : G => g • x0)
    (ν : Measure (MulAction.stabilizer G x0)) [ν.IsMulLeftInvariant] [SFinite ν] (s : X → G)
    (hs : ∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) (h1 : ∀ y, ¬ (∃ g : G, g • x0 = y) → s y = 1) :
    Measurable (fun y => Measure.map (fun h : MulAction.stabilizer G x0 => s y * (h : G)) ν) := by
  classical
  have hcl : IsClosed ((MulAction.stabilizer G x0 : Subgroup G) : Set G) := isClosed_singleton.preimage hc
  haveI : IsClosed ((MulAction.stabilizer G x0 : Subgroup G) : Set G) := hcl
  haveI : PolishSpace G := PI.AprimeInfA.polish_of_lcsc G
  haveI : PolishSpace (G ⧸ MulAction.stabilizer G x0) := PI.AprimeInfA.polish_of_lcsc _
  haveI : BorelSpace (G ⧸ MulAction.stabilizer G x0) := CosetSpace.borelSpace
  set ι : G ⧸ MulAction.stabilizer G x0 → X := fun q => q.out • x0 with hιdef
  have hemb : MeasurableEmbedding ι := (PI.AprimeInfA.orb_cont x0 hc).measurableEmbedding (PI.AprimeInfA.orb_inj x0)
  have hmv : ∀ t : G, Measurable (fun h : MulAction.stabilizer G x0 => t * (h : G)) :=
    fun t => (continuous_const_mul t |>.comp continuous_subtype_val).measurable
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hf : Measurable (A.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hA
  have eq : (fun y => Measure.map (fun h : MulAction.stabilizer G x0 => s y * (h : G)) ν A) =
      Function.extend ι (fun q : G ⧸ MulAction.stabilizer G x0 =>
        ∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (q.out * (h : G)) ∂ν)
        (fun _ => ∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (h : G) ∂ν) := by
    funext y
    have e0 : Measure.map (fun h : MulAction.stabilizer G x0 => s y * (h : G)) ν A = ∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (s y * (h : G)) ∂ν := by
      rw [Measure.map_apply (hmv _) hA, ← lintegral_indicator_one ((hmv _) hA)]
      rfl
    rw [e0]
    by_cases hy : ∃ q, ι q = y
    · obtain ⟨q, rfl⟩ := hy
      rw [hemb.injective.extend_apply]
      have hsq : s (ι q) • x0 = q.out • x0 := hs (ι q) ⟨q.out, rfl⟩
      have hk : q.out⁻¹ * s (ι q) ∈ MulAction.stabilizer G x0 := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, hsq, inv_smul_smul]
      have hsk : s (ι q) = q.out * (q.out⁻¹ * s (ι q)) := by group
      rw [hsk]
      exact PI.AprimeInfA.avg_mul_mem (MulAction.stabilizer G x0) ν _ q.out ⟨_, hk⟩
    · rw [Function.extend_apply' _ _ _ (by simpa using hy)]
      have hno : ¬ ∃ g : G, g • x0 = y := by
        rintro ⟨g, rfl⟩
        exact hy ⟨(g : G ⧸ MulAction.stabilizer G x0), PI.AprimeInfA.orb_mk x0 g⟩
      rw [h1 y hno]
      simp only [one_mul]
  rw [eq]
  exact hemb.measurable_extend (PI.AprimeInfA.meas_avg_q (MulAction.stabilizer G x0) ν hf) measurable_const

end PI.AprimeInfK

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem kerMeas_holds : KerMeas := by
  intro D X u' ψ hT μinf νinf fibInf hP
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  set x0 := ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) with hx0
  have hc : Continuous fun g : GI X => g • x0 :=
    PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J _
  have hcl : IsClosed ((MulAction.stabilizer (GI X) x0 : Subgroup (GI X)) : Set (GI X)) :=
    isClosed_singleton.preimage hc
  haveI : LocallyCompactSpace (MulAction.stabilizer (GI X) x0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let ν : Measure (MulAction.stabilizer (GI X) x0) := (X.measW u').μHinf
  haveI hH : ν.IsHaarMeasure := (X.measW_norm u').2.1
  haveI : SecondCountableTopology (MulAction.stabilizer (GI X) x0) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace (MulAction.stabilizer (GI X) x0) := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hs : ∀ y, (∃ g : GI X, g • x0 = y) → sect X u' y • x0 = y := fun y hy => sect_spec X u' y hy
  have h1 : ∀ y, ¬ (∃ g : GI X, g • x0 = y) → sect X u' y = 1 := by
    intro y hy
    unfold sect
    exact dif_neg hy
  exact PI.AprimeInfK.ker_meas (G := GI X) x0 hc ν (sect X u') hs h1

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem kPos_holds : KPos := by
  intro D X u' ψ hT μinf νinf fibInf hH
  have hg : 0 < Formalism.MainNotions.S.AutInst.gaugeU X.B.I := by
    unfold Formalism.MainNotions.S.AutInst.gaugeU
    exact Finset.prod_pos fun v _ => (hH.2.2.2.1 v).2
  have hv : 0 < Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k := by
    unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
    exact Finset.prod_pos fun i _ => by positivity
  have ht : 0 < Tw u' := by
    unfold Tw
    exact_mod_cast (D.mem u').A.T_prime.pos
  unfold KVal
  exact mul_pos (mul_pos hg (pow_pos hv _)) (zpow_pos ht _)

theorem orbMeas_holds : OrbMeas := fun X u' => measurable_orbM X u'

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def sigLin (σ : E →ₐ[F] E) : (R ⊗[F] E) →ₗ[R] (R ⊗[F] E) where
  toFun := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ
  map_add' := map_add _
  map_smul' r x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    simp [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) :=
  IsModuleTopology.continuous_of_linearMap (sigLin R σ)

theorem isClosed_hermR [T2Space (R ⊗[F] E)] (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed ((HermR R σ n : AddSubgroup (Matrix (Fin n) (Fin n) (R ⊗[F] E))) :
      Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  have : ((HermR R σ n : AddSubgroup (Matrix (Fin n) (Fin n) (R ⊗[F] E))) :
      Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ⋂ a, ⋂ b, {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S b a) = S a b} := by
    ext S; simp [HermR]
  rw [this]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
  · exact (continuous_sigR R σ).comp ((continuous_apply a).comp (continuous_apply b))
  · exact (continuous_apply b).comp (continuous_apply a)

end Herm

theorem hermLF_holds : HermLF := by
  intro D X u' ψ hT μinf νinf fibInf hH
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : νinf.IsAddHaarMeasure := hH.2.2.2.2.2.1.1
  have : LocallyCompactSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : LocallyCompactSpace (HmI X) :=
    (isClosed_hermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨K, hK, hKc⟩ := exists_compact_mem_nhds (TI X u' hT)
  exact ⟨K, hKc, hK.measure_lt_top⟩

theorem continuous_gramI {D : D7} (X : HidaSetting D) :
    Continuous (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :
      TupI X → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hs := continuous_sigR (Ainf X.B.I.F) X.B.I.cm.sig
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gramR, hR, Formalism.UG.hform]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
    ((continuous_apply j).comp (continuous_apply b))

theorem gramMeas_holds : GramMeas := by
  intro D X S hS
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hS' : MeasurableSet[(borel (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))).comap Subtype.val] S := by
    rw [← borel_comap]; exact hS
  obtain ⟨A, hA, rfl⟩ := hS'
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, Set.preimage_inter]
  have hg : @Measurable (TupI X) (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) _ (borel _) (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := by
    let _ : MeasurableSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := borel _
    have : BorelSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := ⟨rfl⟩
    exact (continuous_gramI X).measurable
  have hC : MeasurableSet[borel (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))]
      ((HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) : AddSubgroup _) : Set _) :=
    MeasurableSet.of_compl (MeasurableSpace.measurableSet_generateFrom
      (isClosed_hermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)).isOpen_compl)
  exact (hg hA).inter (hg hC)

theorem constTest_of_polar (hP : PolarLoc) (hC : PushCont) : ConstTest :=
  constTest_of gramMeas_holds orbMeas_holds kPos_holds hP hC hermLF_holds

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def cTI {D : D7} (X : HidaSetting D) (a : MfI X) : MfI X :=
  Matrix.transpose (a.map (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf X.B.I.F) X.B.I.cm.sig))

def RmulFacts : Prop := ∀ {D : D7} (X : HidaSetting D),
    (∀ a : MfI X, Measurable (rmulT X a)) ∧ (∀ a b : MfI X, ∀ Y, rmulT X a (rmulT X b Y) = rmulT X (b * a) Y) ∧
    (∀ (g : GI X) (a : MfI X) (Y : TupI X), g • rmulT X a Y = rmulT X a (g • Y)) ∧
    (∀ (a : MfI X) (Y : TupI X), gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X a Y) =
      cTI X a * gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y * a) ∧
    (∀ a b : MfI X, cTI X (a * b) = cTI X b * cTI X a) ∧ cTI X 1 = 1 ∧
    (∀ K : Set (TupI X), IsCompact K → MeasurableSet K) ∧ (∀ a : MfI X, Continuous (rmulT X a))

def NearFacts : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∀ T ∈ Ω₁, IsUnit (a T) ∧
      ∀ Y : TupI X, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = (T : Matrix _ _ _) → Y ∈ IndI X

def FibAllT : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ T : HmI X, InvI X (fibInf T) ∧ LFI X (fibInf T)

end PI.AprimeInfW
end
end
