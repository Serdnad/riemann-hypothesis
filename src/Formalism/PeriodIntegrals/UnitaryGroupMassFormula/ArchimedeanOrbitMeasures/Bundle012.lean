module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushLF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem orbRep_of (hK : KerMeas) (hU : HaarUniqInf) (hR : RegI) (hF : HinfFin) : OrbRep := by
  intro D X u' ψ hT μinf νinf fibInf hP ν hinv hsupp hlf
  obtain ⟨hb, FdN, FdN', u, hX⟩ := hP.1
  obtain ⟨horb, hsm, hmul, hhm, hcpt, hW, hInd⟩ := hR X u' ψ hT μinf νinf fibInf hP
  have hk := hK X u' ψ hT μinf νinf fibInf hP
  let μH : Measure (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) := (X.measW u').μHinf
  have hH : μH.IsHaarMeasure := (X.measW_norm u').2.1
  have hfin : μH Set.univ < ⊤ := hF X hb FdN FdN' u u' hX
  have hne : μH Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μH Set.univ_nonempty
  have hne0 : μH ≠ 0 := fun h => hne (by rw [h]; rfl)
  have hae : ∀ᵐ y ∂ν, ∃ g : GI X, orbM X u' g = y := by
    rw [ae_iff]
    exact measure_mono_null (fun y hy => fun h => hy (hW h)) hsupp

  have kapp : ∀ y A, MeasurableSet A →
      kerI X u' y A = μH ((fun h : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') =>
        sect X u' y * (h : GI X)) ⁻¹' A) := fun y A hA => Measure.map_apply (hhm _) hA
  set m : Measure (GI X) := ν.bind (kerI X u') with hm

  have minv : ∀ g : GI X, m.map (fun x => g * x) = m := by
    intro g
    ext A hA
    have hA' : MeasurableSet ((fun x => g * x) ⁻¹' A) := hmul g hA
    rw [Measure.map_apply (hmul g) hA, hm, Measure.bind_apply hA' hk.aemeasurable,
      Measure.bind_apply hA hk.aemeasurable]
    have hFm : Measurable fun y => kerI X u' y A := (Measure.measurable_coe hA).comp hk
    calc ∫⁻ y, kerI X u' y ((fun x => g * x) ⁻¹' A) ∂ν = ∫⁻ y, kerI X u' (g • y) A ∂ν := by
          refine lintegral_congr_ae (hae.mono fun y hy => ?_)
          obtain ⟨h0, e⟩ := sect_smul X u' g y hy
          show kerI X u' y ((fun x => g * x) ⁻¹' A) = kerI X u' (g • y) A
          rw [kapp _ _ hA, kapp _ _ hA', e]
          have hS : MeasurableSet ((fun h : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') =>
              sect X u' y * (h : GI X)) ⁻¹' ((fun x => g * x) ⁻¹' A)) := hhm _ hA'
          rw [← muH_preimage X u' μH hne0 h0 _ hS]
          congr 1
          ext h
          simp only [Set.mem_preimage, Subgroup.coe_mul, mul_assoc]
      _ = ∫⁻ y, kerI X u' y A ∂(ν.map fun y => g • y) := (lintegral_map hFm (hsm g)).symm
      _ = ∫⁻ y, kerI X u' y A ∂ν := by rw [hinv g]

  have mfin : ∀ C : Set (GI X), IsCompact C → m C < ⊤ := by
    intro C hC
    obtain ⟨hCm, hCc, hCim⟩ := hcpt C hC
    rw [hm, Measure.bind_apply hCm hk.aemeasurable]
    calc ∫⁻ y, kerI X u' y C ∂ν ≤ ∫⁻ y, μH Set.univ * (orbM X u' '' C).indicator 1 y ∂ν := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          by_cases hyC : y ∈ orbM X u' '' C
          · rw [Set.indicator_of_mem hyC, Pi.one_apply, mul_one, kapp _ _ hCm]
            exact measure_mono (Set.subset_univ _)
          · rw [Set.indicator_of_notMem hyC, mul_zero, kapp _ _ hCm, nonpos_iff_eq_zero]
            convert measure_empty (μ := μH)
            ext h
            simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
            intro hh
            exact hyC ⟨_, hh, orbM_sect_mul X u' y hy h⟩
      _ = μH Set.univ * ν (orbM X u' '' C) := by
          rw [lintegral_const_mul _ (measurable_one.indicator hCim), lintegral_indicator_one hCim]
      _ < ⊤ := ENNReal.mul_lt_top hfin
          (hlf _ hCc ((Set.image_subset_range _ _).trans hInd))
  obtain ⟨c, hc, hmc⟩ := hU X u' ψ hT μinf νinf fibInf hP m minv mfin
  refine ⟨c / μH Set.univ, ENNReal.div_ne_top hc hne, Measure.ext fun B hB => ?_⟩
  have e : μH Set.univ * ν B = c * X.measG.μGinf.map (orbM X u') B := by
    rw [Measure.map_apply horb hB, show c * X.measG.μGinf (orbM X u' ⁻¹' B) =
        (c • X.measG.μGinf) (orbM X u' ⁻¹' B) by rw [Measure.smul_apply, smul_eq_mul], ← hmc, hm,
      Measure.bind_apply (horb hB) hk.aemeasurable, ← lintegral_indicator_one hB, ← lintegral_const_mul _
        (measurable_one.indicator hB)]
    refine lintegral_congr_ae (hae.mono fun y hy => ?_)
    show μH Set.univ * B.indicator 1 y = kerI X u' y (orbM X u' ⁻¹' B)
    symm
    rw [kapp _ _ (horb hB)]
    by_cases hyB : y ∈ B
    · rw [Set.indicator_of_mem hyB, Pi.one_apply, mul_one]
      congr 1
      ext h
      simp only [Set.mem_preimage, Set.mem_univ, iff_true, orbM_sect_mul X u' y hy h]
      exact hyB
    · rw [Set.indicator_of_notMem hyB, mul_zero]
      convert measure_empty (μ := μH)
      ext h
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false, orbM_sect_mul X u' y hy h]
      exact hyB
  rw [Measure.smul_apply, smul_eq_mul]
  calc ν B = (μH Set.univ)⁻¹ * (μH Set.univ * ν B) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne hfin.ne, one_mul]
    _ = (μH Set.univ)⁻¹ * (c * X.measG.μGinf.map (orbM X u') B) := by rw [e]
    _ = c / μH Set.univ * X.measG.μGinf.map (orbM X u') B := by rw [div_eq_mul_inv]; ring

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem hR_eq (x y : Fin M → R ⊗[F] E) :
    hR R σ J x y = ((fun i => _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (x i)) ⬝ᵥ (JR R J *ᵥ y)) := by
  simp only [hR, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sigR_mulVec (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (x : Fin M → R ⊗[F] E) :
    (fun i => _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ ((G *ᵥ x) i)) = (G.map (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ)) *ᵥ (fun i => _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (x i)) := by
  funext i

  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem hR_smul (g : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y := by
  have hg : ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ))ᵀ * JR R J *
      (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := g.2
  rw [hR_eq, hR_eq, sigR_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

theorem gramR_smul {m : ℕ} (g : HA R σ J) (Y : Fin m → Fin M → R ⊗[F] E) :
    gramR R σ J (g • Y) = gramR R σ J Y := by
  funext a b
  exact hR_smul R σ J g (Y a) (Y b)

theorem gramR_ratTup {m : ℕ} (Y : Fin m → Fin M → E) :
    gramR R σ J (ratTup R Y) = (gramE σ J Y).map (inclR R) := by
  funext a b

  simp [gramR, gramE, hR, hE, Formalism.UG.hform, ratTup, JR, inclR, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, map_sum, map_mul]

def hLin (x : Fin M → R ⊗[F] E) : (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun := hR R σ J x
  map_add' y z := by
    simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem linIndep_of_isUnit_det {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (h : IsUnit (gramR R σ J X).det) :
    LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : (gramR R σ J X).mulVec g = 0 := by
    funext a
    have e := map_sum (hLin R σ J (X a)) (fun b => g b • X b) Finset.univ
    rw [hg, map_zero] at e
    simp only [map_smul, smul_eq_mul] at e
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [e]
    exact Finset.sum_congr rfl fun b _ => by simp only [hLin, LinearMap.coe_mk, gramR]; exact mul_comm _ _
  have h2 : g = 0 := by
    have := congrArg (fun v => (gramR R σ J X)⁻¹.mulVec v) h1
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  intro a; rw [h2]; rfl

theorem continuous_sigRP [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) := by
  have h : ∀ x : R ⊗[F] E, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x = (σ.toLinearMap.baseChange R) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ : R ⊗[F] E → R ⊗[F] E) = (σ.toLinearMap.baseChange R) := funext h
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_gramRP [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} :
    Continuous (gramR R σ J : (Fin m → Fin M → R ⊗[F] E) → Matrix (Fin m) (Fin m) (R ⊗[F] E)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  show Continuous fun Y : Fin m → Fin M → R ⊗[F] E => ∑ i, ∑ j, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (Y a i) * JR R J i j * Y b j
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((continuous_sigRP R σ).comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))

end Alg

def DetNZ : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0

theorem orbM_mem {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    orbM X u' g ∈ FbI X u' hT := by
  have e : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (orbM X u' g) =
      ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
    rw [orbM, gramR_smul, gramR_ratTup]
    rfl
  refine ⟨e, ?_⟩
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [e]
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem measurableSet_FbI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) : MeasurableSet (FbI X u' hT) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact (isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurableSet.inter
    (isOpen_IndI X).measurableSet

theorem pushSupp_of (hD : DetNZ) : ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    X.measG.μGinf.map (orbM X u') (FbI X u' hT)ᶜ = 0 := by
  intro D X u' ψ hT μinf νinf fibInf hP
  rw [Measure.map_apply (measurable_orbM X u') (measurableSet_FbI X u' hT).compl]
  have : orbM X u' ⁻¹' (FbI X u' hT)ᶜ = ∅ := by
    ext g
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact orbM_mem X u' hT (hD X u' ψ hT μinf νinf fibInf hP) g
  rw [this, measure_empty]

def PushLFin : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    LFI X (X.measG.μGinf.map (orbM X u'))

theorem lfPush_of (hD : DetNZ) (hL : PushLFin) : LFPush := by
  intro D X u' ψ hT μinf νinf fibInf hP
  exact ⟨pushSupp_of hD X u' ψ hT μinf νinf fibInf hP, hL X u' ψ hT μinf νinf fibInf hP⟩

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def FrameIndependentAtInfinity : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → Y0 X u' ∈ IndI X

def ProperOrb : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ K : Set (TupI X), IsCompact K → K ⊆ IndI X →
      ∃ N ∈ 𝓝 (1 : MfI X), ∃ C : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J), IsCompact C ∧
        ∀ b ∈ N, ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • rmulT X b (Y0 X u') ∈ K → g ∈ C

theorem continuous_smul_left {D : D7} (X : HidaSetting D) (y : TupI X) :
    Continuous (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (y a)
  exact (MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).matrix_mulVec continuous_const

theorem continuous_rmulT {D : D7} (X : HidaSetting D) (Y : TupI X) : Continuous (fun b : MfI X => rmulT X b Y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun b => continuous_pi fun i => ?_
  simp only [rmulT]
  exact continuous_finsetSum _ fun c _ => (continuous_apply_apply c b).mul continuous_const

theorem pushCont_of (hY : FrameIndependentAtInfinity) (hPr : ProperOrb) : PushCont := by
  intro D X u' ψ hT μinf νinf fibInf hH a ha1 hac
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have : SecondCountableTopology (MfI X) :=
    inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : SecondCountableTopology (HmI X) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hY0 := hY X u' ψ hT μinf νinf fibInf hH
  obtain ⟨V, hVo, hYV, hVc, -⟩ := exists_open_between_and_isCompact_closure isCompact_singleton (isOpen_IndI X)
    (Set.singleton_subset_iff.2 hY0)
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact isCompact_singleton hVo.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 hYV)
  have hsupp : Function.support f ⊆ V := fun y hy => by
    by_contra h; exact hy (hf0 h)
  have htsupp : tsupport f ⊆ IndI X := (closure_mono hsupp).trans hVc
  have hfY : f (Y0 X u') = 1 := hf1 (Set.mem_singleton _)
  obtain ⟨N, hN, C, hC, hNC⟩ := hPr X u' ψ hT μinf νinf fibInf hH (tsupport f) hfc.isCompact htsupp
  have hbound : ∀ b ∈ N, ∀ g, ENNReal.ofReal (f (g • rmulT X b (Y0 X u'))) ≤ C.indicator 1 g := by
    intro b hb g
    by_cases hg : f (g • rmulT X b (Y0 X u')) = 0
    · rw [hg, ENNReal.ofReal_zero]; exact bot_le
    · have hgC : g ∈ C := hNC b hb g (subset_tsupport _ hg)
      rw [Set.indicator_of_mem hgC, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (hfI _).2
  have h1N : (1 : MfI X) ∈ N := mem_of_mem_nhds hN
  have hCfin : ∫⁻ g, C.indicator 1 g ∂X.measG.μGinf < ⊤ :=
    lt_of_le_of_lt (lintegral_indicator_one_le C) hC.measure_lt_top
  refine ⟨f, f.continuous, f.continuous.measurable, hfc, htsupp, fun y => (hfI y).1, ?_, ?_, ?_⟩
  · have hm : Measurable fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => ENNReal.ofReal (f (g • Y0 X u')) :=
      ENNReal.measurable_ofReal.comp (f.continuous.comp (continuous_smul_left X (Y0 X u'))).measurable
    rw [lintegral_pos_iff_support hm]
    have hOo : IsOpen ((fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {y | 0 < f y}) :=
      (isOpen_lt continuous_const f.continuous).preimage (continuous_smul_left X (Y0 X u'))
    have h1O : (1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
        (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {y | 0 < f y} := by
      show 0 < f ((1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) • Y0 X u')
      rw [one_smul, hfY]; exact one_pos
    refine lt_of_lt_of_le (hOo.measure_pos _ ⟨1, h1O⟩) (measure_mono fun g hg => ?_)
    exact (ENNReal.ofReal_pos.2 hg).ne'
  · refine lt_of_le_of_lt (lintegral_mono fun g => ?_) hCfin
    have := hbound 1 h1N g
    rwa [rmulT_one] at this
  · have hev : ∀ᶠ T in 𝓝 (TI X u' hT), a T ∈ N := hac.preimage_mem_nhds (by rw [ha1]; exact hN)
    refine tendsto_lintegral_filter_of_dominated_convergence (C.indicator 1) ?_ ?_ hCfin.ne ?_
    · exact Eventually.of_forall fun T => ENNReal.measurable_ofReal.comp
        (f.continuous.comp (continuous_smul_left X _)).measurable
    · exact hev.mono fun T hT' => Eventually.of_forall fun g => hbound _ hT' g
    · refine Eventually.of_forall fun g => ?_
      exact (ENNReal.continuous_ofReal.comp (f.continuous.comp ((continuous_smul_tupI X g).comp
        (continuous_rmulT X (Y0 X u'))))).continuousAt.comp hac

end PI.AprimeInfW
end
end
