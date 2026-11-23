module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushLF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle020
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle019
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PI.AprimeInfW

theorem pushInf_of_pushLFin_of_orbUniq_of_constTest (hL : PushLFin) (hU : OrbUniq) (hC : ConstTest) : PushInf :=
  pushInf_of invPush_holds invFib_holds (lfPush_of detNZ_holds hL) lfFib_holds hU hC

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem lfFib_at {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf
    (hP : PushHyp X u' ψ hT μinf νinf fibInf) (T : HmI X) : LFI X (fibInf T) := by
  intro K hK hKU
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨k, -, hkcl, hKk, hkU⟩ := exists_compact_closed_between hK (isOpen_IndI X) hKU
  obtain ⟨f, hf1, hf0, hfc, -⟩ := exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.mpr hKk)
  have hts : tsupport f ⊆ IndI X := by
    refine (closure_minimal ?_ hkcl).trans hkU
    intro y hy
    by_contra h
    exact hy (hf0 (fun h' => h (interior_subset h')))
  have hI := ((hP.2.2.2.2.2.2).2.2 f f.continuous hfc hts).1 T (Set.mem_univ _)
  calc fibInf T K ≤ fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} :=
        measure_mono fun y hy => by
          simp only [Set.mem_ofPred_eq]
          rw [hf1 hy]
          simp
    _ = 1 * fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} := (one_mul _).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(fibInf T) :=
        mul_meas_ge_le_lintegral₀ f.continuous.measurable.ennreal_ofReal.aemeasurable 1
    _ < ⊤ := hI.lintegral_lt_top

theorem fibAllT_holds : FibAllT := by
  intro D X u' ψ hT μinf νinf fibInf hP T
  refine ⟨fun g => ?_, lfFib_at X u' ψ hT μinf νinf fibInf hP T⟩
  have hfib := hP.2.2.2.2.2.2
  have h := fibEqI X ψ μinf νinf _ _ hP.2.2.2.2.1 hP.2.2.2.2.2.1
    (fibTrans X μinf νinf fibInf hfib g (sdInvG_of sdTestI_holds X u' ψ hT μinf νinf fibInf hP g)) hfib
  exact congrFun h T

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem gramR_Y0_eq_TI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) :
    gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
  rw [show Y0 X u' = orbM X u' 1 from (one_smul _ _).symm, orbM, gramR_smul, gramR_ratTup]
  rfl

theorem indI_of_gram {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) (Y : TupI X)
    (hY : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _)) :
    Y ∈ IndI X := by
  have e1 := orbM_mem X u' hT hd 1
  have e0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y =
      gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (orbM X u' 1) := by rw [hY, e1.1]
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [e0, e1.1]
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem fib_near (hR : RmulFacts) (hF : FibAllT) (hC : MassDataMassesW.HinfCompact) {D : D7} (X : HidaSetting D)
    (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf
    (hP : PushHyp X u' ψ hT μinf νinf fibInf) (T : HmI X) (a : MfI X) (hunit : IsUnit a)
    (hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X a (Y0 X u')) = (T : Matrix _ _ _))
    (hind : ∀ Y : TupI X, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = (T : Matrix _ _ _) → Y ∈ IndI X) :
    ∃ c : ENNReal, fibInf T = c • X.measG.μGinf.map (fun g => g • rmulT X a (Y0 X u')) := by
  obtain ⟨hmr, hcomp, hsmul, hgram, hcTmul, hcT1, hKm, hrc⟩ := hR X
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hfib := hP.2.2.2.2.2.2
  obtain ⟨hinvT, hlfT⟩ := hF X u' ψ hT μinf νinf fibInf hP T
  set b : MfI X := ↑hunit.unit⁻¹ with hb
  have hab : a * b = 1 := hunit.mul_val_inv
  have hba : b * a = 1 := hunit.val_inv_mul
  have hab' : ∀ Y, rmulT X a (rmulT X b Y) = Y := fun Y => by rw [hcomp, hba, rmulT_one]
  have hba' : ∀ Y, rmulT X b (rmulT X a Y) = Y := fun Y => by rw [hcomp, hab, rmulT_one]
  set ν := (fibInf T).map (rmulT X b) with hν
  have i1 : InvI X ν := by
    intro g
    rw [hν, Measure.map_map (measurable_smul_tupI X g) (hmr b)]
    have : ((fun y => g • y) ∘ rmulT X b) = rmulT X b ∘ (fun y => g • y) := funext fun y => hsmul g b y
    rw [this, ← Measure.map_map (hmr b) (measurable_smul_tupI X g), hinvT g]
  have hS : fibInf T (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1} ∩ IndI X)ᶜ = 0 :=
    hfib.1 T
  have s1 : ν (FbI X u' hT)ᶜ = 0 := by
    rw [hν, Measure.map_apply (hmr b) (measurableSet_FbI X u' hT).compl]
    refine measure_mono_null ?_ hS
    intro y hy hy2
    apply hy
    have hg : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X b y) = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
      rw [hgram, hy2.1, ← hgT, hgram, gramR_Y0_eq_TI X u' hT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hcTmul,
        Matrix.mul_assoc, hab, hcT1, Matrix.one_mul, Matrix.mul_one]
    exact ⟨hg, indI_of_gram X u' hT hd _ hg⟩
  have l1 : LFI X ν := by
    intro K hK hKI
    rw [hν, Measure.map_apply (hmr b) (hKm K hK)]
    have hpre : rmulT X b ⁻¹' K = rmulT X a '' K := by
      ext y
      constructor
      · intro hy; exact ⟨rmulT X b y, hy, hab' y⟩
      · rintro ⟨k, hk, rfl⟩; show rmulT X b (rmulT X a k) ∈ K; rw [hba']; exact hk
    rw [hpre]
    have hcl : IsClosed (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) := by
      haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
      exact isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    have hK2 : IsCompact (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) :=
      (hK.image (hrc a)).inter_right hcl
    calc fibInf T (rmulT X a '' K)
        ≤ fibInf T (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) +
          fibInf T (rmulT X a '' K \ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) :=
          measure_le_inter_add_sdiff _ _ _
      _ = fibInf T (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) := by
          have h0 : fibInf T (rmulT X a '' K \ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) = 0 := by
            refine measure_mono_null ?_ hS
            intro y hy hy2
            exact hy.2 hy2.1
          rw [h0, add_zero]
      _ < ⊤ := hlfT _ hK2 (fun y hy => hind y hy.2)
  obtain ⟨c, -, hc⟩ := orbRep_of_witt wittInf_holds hC X u' ψ hT μinf νinf fibInf hP ν i1 s1 l1
  refine ⟨c, ?_⟩
  have e1 : fibInf T = ν.map (rmulT X a) := by
    rw [hν, Measure.map_map (hmr a) (hmr b)]
    have : rmulT X a ∘ rmulT X b = id := funext hab'
    rw [this, Measure.map_id]
  have e2 : (fun g => g • rmulT X a (Y0 X u')) = rmulT X a ∘ orbM X u' :=
    funext fun g => hsmul g a (Y0 X u')
  rw [e1, hc, Measure.map_smul, e2, Measure.map_map (hmr a) (measurable_orbM X u')]
  exact (hmr a).aemeasurable

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

section Lie

variable {V : Type} [Fintype V] {n : ℕ}

def lieK (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) : Submodule ℝ (V → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
    ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0}
  zero_mem' := by intro v; simp
  add_mem' := by
    intro A B hA hB v
    refine ⟨?_, fun i hi j hj => ?_⟩
    · have e : (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) =
          ((A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * A v) +
            ((B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * B v) := by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
      show (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) = 0
      rw [e, (hA v).1, (hB v).1, add_zero]
    · show A v i j + B v i j = 0
      rw [(hA v).2 i hi j hj, (hB v).2 i hi j hj, add_zero]
  smul_mem' := by
    intro c A hA v
    refine ⟨?_, fun i hi j hj => ?_⟩
    · show (c • A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (c • A v) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hA v).1,
        smul_zero]
    · show c • A v i j = 0
      rw [(hA v).2 i hi j hj, smul_zero]

def entL (V : Type) [Fintype V] (n : ℕ) :
    (V → Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] EuclideanSpace ℂ (V × Fin n × Fin n) :=
  ({ toFun := fun M p => M p.1 p.2.1 p.2.2
     invFun := fun f v i j => f (v, i, j)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } : (V → Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] (V × Fin n × Fin n → ℂ)).trans
    ((EuclideanSpace.equiv (V × Fin n × Fin n) ℂ).toLinearEquiv.restrictScalars ℝ).symm

theorem entL_apply (M : V → Matrix (Fin n) (Fin n) ℂ) (p : V × Fin n × Fin n) :
    (EuclideanSpace.equiv (V × Fin n × Fin n) ℂ) (entL V n M) p = M p.1 p.2.1 p.2.2 := by
  simp [entL] <;> rfl

theorem norm_entL_sq (M : V → Matrix (Fin n) (Fin n) ℂ) :
    ‖entL V n M‖ ^ 2 = ∑ v, ∑ i, ∑ j, ‖M v i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := entL_apply M (v, i, j)
  simp only [EuclideanSpace.equiv] at this
  rw [← this]
  rfl

theorem exists_lieCompl (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)),
      (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧
        ∀ i ∈ S v, ∀ j ∈ S v, L x v i j = 0) ∧
      (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
      ∀ M : V → Matrix (Fin n) (Fin n) ℂ,
        (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0) →
          ∃ x, L x = M := by
  set K' : Submodule ℝ (EuclideanSpace ℂ (V × Fin n × Fin n)) := (lieK ε S).map (entL V n).toLinearMap with hK'
  let b := stdOrthonormalBasis ℝ K'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ K')) →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    (entL V n).symm.toLinearMap ∘ₗ K'.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap
  have hLe : ∀ x, entL V n (L x) = (b.repr.symm x : EuclideanSpace ℂ (V × Fin n × Fin n)) := by
    intro x; simp [L]
  have hLK : ∀ x, L x ∈ lieK ε S := by
    intro x
    obtain ⟨M, hM, hMe⟩ := (b.repr.symm x).2
    have : L x = M := by
      apply (entL V n).injective
      rw [hLe]; exact hMe.symm
    rw [this]; exact hM
  refine ⟨Fin (Module.finrank ℝ K'), inferInstance, L, fun x v => hLK x v, fun x => ?_, fun M hM => ?_⟩
  · rw [← norm_entL_sq, hLe]
    exact congrArg (· ^ 2) (b.repr.symm.norm_map x)
  · have hM' : entL V n M ∈ K' := ⟨M, hM, rfl⟩
    refine ⟨b.repr ⟨entL V n M, hM'⟩, ?_⟩
    apply (entL V n).injective
    rw [hLe, LinearIsometryEquiv.symm_apply_apply]

end Lie

def StdConjEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    ∃ (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)), StdConj X hb u' c S

theorem stdDataEx_of (h : StdConjEx) : StdDataEx := by
  intro D X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨c, S, hc⟩ := h X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨ι, hι, L, h1, h2, h3⟩ := exists_lieCompl X.B.I.ε S
  exact ⟨c, S, ι, hι, L, hc, ⟨h1, h2, h3⟩⟩

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

abbrev KapI {D : D7} (X : HidaSetting D) : Type :=
  Fin (D.R.rS + 1 + D.R.rS) × Fin X.B.I.n ×
    Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F

def betaI {D : D7} (X : HidaSetting D) (x y : EuclideanSpace ℝ (KapI X)) : ℝ :=
  ∑ w : InfinitePlace X.B.I.F, (InfinitePlace.Completion.extensionEmbedding w
    (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w)).re


open Classical in
def matI {D : D7} (X : HidaSetting D) : Matrix (KapI X) (KapI X) ℝ :=
  fun i j => betaI X (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)


open Classical in
def DensMu : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    μinf.map (tupCoord X) = ENNReal.ofReal (Real.sqrt |(matI X).det|) • volume

end PI.AprimeInfW
end
end
