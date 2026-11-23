module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTube
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpChartC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
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

@[expose] public section

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

theorem square_chart_c1_local {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M m : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin m → Fin M → E) (hT : ∀ i j, σ (gramE σ J Y j i) = gramE σ J Y i j) (hdet : (gramE σ J Y).det ≠ 0)
    {N : ℕ} (e : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) :
    ∃ (Ω : Set (HermR (Ainf F) σ m)) (a : HermR (Ainf F) σ m → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)),
      Ω ∈ 𝓝 (hermOf (Ainf F) σ (gramE σ J Y) hT) ∧ a (hermOf (Ainf F) σ (gramE σ J Y) hT) = 1 ∧
      ContinuousAt a (hermOf (Ainf F) σ (gramE σ J Y) hT) ∧
      (∀ T ∈ Ω, gramR (Ainf F) σ J (fun b i => ∑ c, a T c b * ratTup (Ainf F) Y c i) = (T : Matrix _ _ _)) ∧
      ∀ {η μ' : Type} [Fintype η] [Fintype μ'] (eH : HermR (Ainf F) σ m ≃ₜ EuclideanSpace ℝ η)
        (eM : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) ≃ₜ EuclideanSpace ℝ μ'),
        (∀ x y, eH (x + y) = eH x + eH y) → (∀ x y, eM (x + y) = eM x + eM y) →
        ContDiffAt ℝ 1 (fun z => eM (a (eH.symm z))) (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) ∧
        ∀ v, fderiv ℝ (fun z => eM (a (eH.symm z))) (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) v =
          (1 / 2 : ℝ) • eM ((gramE σ J Y)⁻¹.map (inclR (Ainf F)) *
            ((eH.symm v : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))) := by
  classical
  set G := gramE σ J Y with hG
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
  set Tm : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := G.map (inclR (Ainf F)) with hTm
  set Ti : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := G⁻¹.map (inclR (Ainf F)) with hTi
  have hTTi : Tm * Ti = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.mul_nonsing_inv G hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hTiT : Ti * Tm = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.nonsing_inv_mul G hu, Matrix.map_one _ (map_zero _) (map_one _)]
  set c : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) :=
    Formalism.UG.cT (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf F) σ) with hc
  have hsig := sq_sig_inv (Ainf F) σ hσ
  have hcc : ∀ P, c (c P) = P := by intro P; ext i j; simp [hc, Formalism.UG.cT, hsig]
  have hcadd : ∀ P Q, c (P + Q) = c P + c Q := by intro P Q; ext i j; simp [hc, Formalism.UG.cT]
  have hcsub : ∀ P Q, c (P - Q) = c P - c Q := by intro P Q; ext i j; simp [hc, Formalism.UG.cT]
  have hcmul : ∀ P Q, c (P * Q) = c Q * c P := fun P Q => Formalism.UG.cT_mul _ P Q
  have hc1 : c 1 = 1 := Formalism.UG.cT_one _
  have hcT : c Tm = Tm := by
    ext i j
    simp only [hc, Formalism.UG.cT, hTm, Matrix.transpose_apply, Matrix.map_apply]
    rw [← hT i j]
    simp [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR]
  have hcTi : c Ti * Tm = 1 := by
    calc c Ti * Tm = c Ti * c Tm := by rw [hcT]
      _ = c (Tm * Ti) := (hcmul Tm Ti).symm
      _ = 1 := by rw [hTTi, hc1]
  have hcont_c : Continuous c := by
    show Continuous fun P : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) => (P.map (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf F) σ))ᵀ
    exact (continuous_id.matrix_map (continuous_sigRP (Ainf F) σ)).matrix_transpose
  set Bq : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) →
      Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := fun h k => c (Ti * h) * Tm * (Ti * k) with hBq
  set Lq : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) :=
    fun h => h - c h with hLq
  have hD : ∀ u, Bq Tm u + Bq u Tm + Lq u = u + u := by
    intro u
    simp only [hBq, hLq]
    rw [hTiT, hc1, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc Tm Ti u, hTTi, Matrix.one_mul, hcmul Ti u,
      Matrix.mul_assoc (c u) (c Ti) Tm, hcTi, Matrix.mul_one]
    abel
  obtain ⟨g, hgc, hg0, hgev, hgcd, hgd⟩ := exists_local_solution_contDiffAt e he Bq
    (by intro x x' y; simp only [hBq, Matrix.mul_add, hcadd, Matrix.add_mul])
    (by intro x y y'; simp only [hBq, Matrix.mul_add])
    (((hcont_c.comp (continuous_const.matrix_mul continuous_fst)).matrix_mul continuous_const).matrix_mul
      (continuous_const.matrix_mul continuous_snd))
    Lq (by intro x y; simp only [hLq, hcadd]; abel) (continuous_id.sub hcont_c) Tm hD
  have hy0 : Bq Tm Tm + Lq Tm = Tm := by
    simp only [hBq, hLq]
    rw [hTiT, hc1, Matrix.one_mul, Matrix.mul_one, hcT, sub_self, add_zero]
  rw [hy0] at hgc hg0 hgev hgcd hgd
  refine ⟨Subtype.val ⁻¹' {y | Bq (g y) (g y) + Lq (g y) = y}, fun T => Ti * g T.val, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds hgev
  · show Ti * g Tm = 1
    rw [hg0, hTiT]
  · exact (continuous_const.matrix_mul continuous_id).continuousAt.comp
      (ContinuousAt.comp_of_eq hgc continuous_subtype_val.continuousAt rfl)
  · intro T hT'
    have hT'' : Bq (g T.val) (g T.val) + Lq (g T.val) = T.val := hT'
    show gramR (Ainf F) σ J (fun b i => ∑ c, (Ti * g T.val) c b * ratTup (Ainf F) Y c i) = T.val
    rw [sq_gramR_rmul (Ainf F) σ J (Ti * g T.val) (ratTup (Ainf F) Y), gramR_ratTup]
    set h := g T.val
    have hP : c (Bq h h) = Bq h h := by
      simp only [hBq]
      rw [hcmul (c (Ti * h) * Tm) (Ti * h), hcmul (c (Ti * h)) Tm, hcc, hcT, Matrix.mul_assoc]
    have hTh : c T.val = T.val := by
      ext i j
      exact T.2 i j
    have hLL : c (Lq h) = -(Lq h) := by
      simp only [hLq]
      rw [hcsub, hcc]
      abel
    have h2 : Lq h + Lq h = 0 := by
      have e1 := congrArg c hT''
      rw [hcadd, hP, hLL, hTh] at e1
      have e2 := add_left_cancel (hT''.trans e1.symm)
      exact eq_neg_iff_add_eq_zero.mp e2
    have h0 : Lq h = 0 := by
      calc Lq h = ((1 / 2 : F) * 2) • Lq h := by norm_num
        _ = (1 / 2 : F) • (Lq h + Lq h) := by rw [mul_smul, two_smul]
        _ = 0 := by rw [h2, smul_zero]
    rw [h0, add_zero] at hT''
    exact hT''
  · intro η μ' _ _ eH eM heH heM
    have hHs : ∀ x y, eH.symm (x + y) = eH.symm x + eH.symm y := by
      intro x y; apply eH.injective; rw [heH]; simp
    have hes : ∀ x y, e.symm (x + y) = e.symm x + e.symm y := by
      intro x y; apply e.injective; rw [he]; simp
    let L₁ : EuclideanSpace ℝ η →L[ℝ] (Fin N → ℝ) :=
      (AddMonoidHom.mk' (fun z => e ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)))
        (by intro x y; simp only [hHs, AddSubgroup.coe_add, he])).toRealLinearMap
        (e.continuous.comp (continuous_subtype_val.comp eH.symm.continuous))
    let L₂ : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ μ' :=
      (AddMonoidHom.mk' (fun y => eM (Ti * e.symm y)) (by intro x y; simp only [hes, Matrix.mul_add, heM])).toRealLinearMap
        (eM.continuous.comp ((continuous_const.matrix_mul continuous_id).comp e.symm.continuous))
    have hL₁ : ∀ z, L₁ z = e ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)) := fun z => rfl
    have hL₂ : ∀ y, L₂ y = eM (Ti * e.symm y) := fun y => rfl
    have hfun : (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)))) =
        fun z => L₂ ((fun y => e (g (e.symm y))) (L₁ z)) := by
      funext z
      rw [hL₁, hL₂]
      simp only [Homeomorph.symm_apply_apply]
    have hpt : L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) = e Tm := by
      rw [hL₁, Homeomorph.symm_apply_apply]; rfl
    have hgcd' : ContDiffAt ℝ 1 (fun y => e (g (e.symm y))) (L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))) := by
      rw [hpt]; exact hgcd
    have hgd' : HasFDerivAt (fun y => e (g (e.symm y))) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
        (L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))) := by
      rw [hpt]; exact hgd
    have hD := L₂.hasFDerivAt.comp (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) (hgd'.comp _ L₁.hasFDerivAt)
    refine ⟨?_, ?_⟩
    · show ContDiffAt ℝ 1 (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))))
        (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))
      rw [hfun]
      exact L₂.contDiff.contDiffAt.comp _ (hgcd'.comp _ L₁.contDiff.contDiffAt)
    · intro v
      show fderiv ℝ (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))))
        (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) v = _
      have hD' : HasFDerivAt (fun z => L₂ ((fun y => e (g (e.symm y))) (L₁ z))) _
          (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) := hD
      rw [hfun, hD'.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        map_smul]
      rw [hL₂, hL₁, Homeomorph.symm_apply_apply]

def TinvI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : MfI X :=
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))⁻¹.map (inclR (Ainf X.B.I.F))

def SquareChartC1 : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a ∧
      ∀ {η μ' : Type} [Fintype η] [Fintype μ'] (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
        (eM : MfI X ≃ₜ EuclideanSpace ℝ μ'),
        (∀ x y, eH (x + y) = eH x + eH y) → (∀ x y, eM (x + y) = eM x + eM y) →
        ContDiffAt ℝ 1 (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) ∧
        ∀ v, fderiv ℝ (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) v =
          (1 / 2 : ℝ) • eM (TinvI X u' * ((eH.symm v : HmI X) : Matrix _ _ _))

theorem square_chart_c1 : SquareChartC1 := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨k, eK, hK⟩ := sq_coord_tens X.B.I.F X.B.I.E
  obtain ⟨k1, e1, h1⟩ := sq_coord_pi eK hK (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨N, eM, hM⟩ := sq_coord_pi e1 h1 (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨Ω, a, h1', h2', h3', h4', h5'⟩ :=
    square_chart_c1_local X.B.I.cm.sig hσ X.B.I.J (tupH (frameOf X u')) hT hdet eM hM
  exact ⟨Ω, a, ⟨h1', h2', h3', fun T hT' => h4' T hT'⟩, fun eH eM' heH heM => h5' eH eM' heH heM⟩

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ActMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (Z : TupI X),
    Measurable (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Z)

def FibOrbAt : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∀ T ∈ Ω₁, ∃ k : ENNReal,
      fibInf T = k • X.measG.μGinf.map (fun g => g • rmulT X (a T) (Y0 X u'))

def OrbCont : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∃ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) ∧
      PolId X u' μinf νinf a Ω₁ c

def JacOneC : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) →
      PolId X u' μinf νinf a Ω₂ c → c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹

theorem isOpen_ne_zero_top : IsOpen (({0}ᶜ ∩ {⊤}ᶜ : Set ENNReal)) :=
  isOpen_compl_singleton.inter isOpen_compl_singleton

theorem polar_local_of_orbit (hK : KPos) (h2 : OrbCont) (h4 : JacOneC) : PolarLoc := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω, a, hC⟩ := sqChart_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, c, hcc, hc⟩ := h2 X u' ψ hT μinf νinf fibInf hP Ω a hC
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  have hc0 : c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹ :=
    h4 X u' ψ hT μinf νinf fibInf hP Ω a hC Ω₁ hΩ₁ hΩ₁n c hcc hc
  have hne0 : c (TI X u' hT) ≠ 0 := by rw [hc0]; exact ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hneT : c (TI X u' hT) ≠ ⊤ := by rw [hc0]; exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK0).ne'
  have hN : c ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ) ∈ 𝓝 (TI X u' hT) :=
    hcc (isOpen_ne_zero_top.mem_nhds ⟨Set.mem_compl_singleton_iff.2 hne0, Set.mem_compl_singleton_iff.2 hneT⟩)
  refine ⟨Ω₁ ∩ c ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ), a, fun T => ((c T)⁻¹).toReal, inter_mem hΩ₁n hN, hC.2.1, hC.2.2.1,
    ?_, ?_, ?_⟩
  · show ((c (TI X u' hT))⁻¹).toReal = KVal X u'
    rw [hc0, inv_inv, ENNReal.toReal_ofReal hK0.le]
  · have ht : (c (TI X u' hT))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne0
    have hinv : ContinuousAt (fun T => (c T)⁻¹) (TI X u' hT) := tendsto_inv_iff.2 hcc
    exact ContinuousAt.comp (g := ENNReal.toReal) (f := fun T => (c T)⁻¹) (ENNReal.continuousAt_toReal ht) hinv
  · intro φ hφ S hS hSm
    rw [hc φ hφ S (hS.trans Set.inter_subset_left) hSm]
    refine setLIntegral_congr_fun hSm ?_
    intro T hTS
    have hT2 := (hS hTS).2
    have h0 : c T ≠ 0 := Set.mem_compl_singleton_iff.1 hT2.1
    show c T * _ = (ENNReal.ofReal ((c T)⁻¹).toReal)⁻¹ * _
    rw [ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 h0), inv_inv]

theorem orbCont_of (hG : GramMeas) (hA : ActMeas) (h1 : FibOrbAt) (h2 : PushCont) : OrbCont := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, hk⟩ := h1 X u' ψ hT μinf νinf fibInf hP Ω a hC
  obtain ⟨φ, hφc, hφm, hφs, hφU, hφ0, hIpos, hIfin, hIc⟩ := h2 X u' ψ hT μinf νinf fibInf hP a hC.2.1 hC.2.2.1
  have hfib := hP.2.2.2.2.2.2
  have hΦm : Measurable fun y => ENNReal.ofReal (φ y) := ENNReal.measurable_ofReal.comp hφm
  set I : HmI X → ENNReal := fun T =>
    ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a T) (Y0 X u'))) ∂X.measG.μGinf with hIdef
  set Nf : HmI X → ENNReal := fun T => ∫⁻ y, ENNReal.ofReal (φ y) ∂(fibInf T) with hNdef
  have hI1 : I (TI X u' hT) = ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf := by
    simp only [hIdef]; rw [hC.2.1, rmulT_one]
  have hI0 : I (TI X u' hT) ≠ 0 := by rw [hI1]; exact hIpos.ne'
  have hIT : I (TI X u' hT) ≠ ⊤ := by rw [hI1]; exact hIfin.ne
  have hIN : I ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ) ∈ 𝓝 (TI X u' hT) :=
    hIc (isOpen_ne_zero_top.mem_nhds ⟨Set.mem_compl_singleton_iff.2 hI0, Set.mem_compl_singleton_iff.2 hIT⟩)

  have c3 := hfib.2.2 φ hφc hφs hφU
  have hNeq : Nf = fun T => ENNReal.ofReal (∫ v, φ v ∂(fibInf T)) := by
    funext T
    exact (ofReal_integral_eq_lintegral_ofReal (c3.1 T (Set.mem_univ _))
      (Eventually.of_forall fun y => hφ0 y)).symm
  have hNc : ContinuousAt Nf (TI X u' hT) := by
    rw [hNeq]
    exact (ENNReal.continuous_ofReal.comp (continuousOn_univ.1 c3.2)).continuousAt
  refine ⟨Ω₁ ∩ I ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ), Set.inter_subset_left.trans hΩ₁, inter_mem hΩ₁n hIN,
    fun T => Nf T / I T, ENNReal.Tendsto.div hNc (Or.inr hI0) hIc (Or.inl hIT), ?_⟩
  intro φ' hφ' S hS hSm
  have hGS := hG X S hSm
  have c2 := hfib.2.1 ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator φ')
    (hφ'.indicator hGS)
  rw [lintegral_indicator hGS, Measure.restrict_restrict hGS] at c2
  rw [c2]
  have inner : ∀ b, ∫⁻ v, (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator φ' v
      ∂(fibInf b) = S.indicator (fun T => ∫⁻ v, φ' v ∂(fibInf T)) b := by
    intro b
    have hae : ∀ᵐ y ∂(fibInf b), y ∈ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {Subtype.val b} ∩ IndI X :=
      ae_iff.2 (hfib.1 b)
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      apply lintegral_congr_ae
      filter_upwards [hae] with y hy
      have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
      exact Set.indicator_of_mem (Set.mem_preimage.2 (show gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y ∈
        Subtype.val '' S from ⟨b, hb, hy1.symm⟩)) _
    · rw [Set.indicator_of_notMem hb]
      calc _ = ∫⁻ _, (0 : ENNReal) ∂(fibInf b) := by
              apply lintegral_congr_ae
              filter_upwards [hae] with y hy
              have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
              refine Set.indicator_of_notMem ?_ _
              rintro ⟨c, hc, hcy⟩
              have hcb : c = b := Subtype.val_injective (hcy.trans hy1)
              exact hb (hcb ▸ hc)
        _ = 0 := lintegral_zero
  simp_rw [inner]
  rw [lintegral_indicator hSm]
  refine setLIntegral_congr_fun hSm ?_
  intro T hTS
  obtain ⟨k, hkT⟩ := hk T (hS hTS).1
  have hIT2 := (hS hTS).2
  have h0 : I T ≠ 0 := Set.mem_compl_singleton_iff.1 hIT2.1
  have hTop : I T ≠ ⊤ := Set.mem_compl_singleton_iff.1 hIT2.2
  have hm := hA X (rmulT X (a T) (Y0 X u'))
  have e1 : ∀ ψ' : TupI X → ENNReal, Measurable ψ' →
      ∫⁻ v, ψ' v ∂(fibInf T) = k * ∫⁻ g, ψ' (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf := by
    intro ψ' hψ'
    rw [hkT, lintegral_smul_measure, lintegral_map hψ' hm, smul_eq_mul]
  have hNk : Nf T = k * I T := e1 _ hΦm
  show ∫⁻ v, φ' v ∂(fibInf T) = Nf T / I T * ∫⁻ g, φ' (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf
  rw [hNk, ENNReal.mul_div_cancel_right h0 hTop, e1 φ' hφ']

theorem polar_local_of_action (hK : KPos) (hG : GramMeas) (hA : ActMeas) (h1 : FibOrbAt) (h2 : PushCont) (h4 : JacOneC) :
    PolarLoc :=
  polar_local_of_orbit hK (orbCont_of hG hA h1 h2) h4

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def UnimodInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (f : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal) (h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J),
      ∫⁻ g, f (g * h) ∂X.measG.μGinf = ∫⁻ g, f g ∂X.measG.μGinf

def WittNear : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a Ω' a₂, IsChart X u' hT Ω a → IsChart X u' hT Ω' a₂ →
    ∀ T ∈ Ω ∩ Ω', IsUnit (a₂ T) → ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')

def GoodChartEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω' a₂, IsChart X u' hT Ω' a₂ ∧ GoodP X u' hT μinf νinf a₂

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem tubeG_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
    TubeG X u' V = PI.AprimeInfG.tubeS (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
      V Set.univ := by
  ext g
  constructor
  · rintro ⟨g', hg', he⟩
    have hs : g'⁻¹ * g ∈ MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, he, inv_smul_smul]
    exact ⟨g', hg', ⟨_, hs⟩, Set.mem_univ _, by simp⟩
  · rintro ⟨a, ha, h, -, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [mul_smul, MulAction.mem_stabilizer_iff.1 h.2]

def GrpChart {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  ∃ (η : Type) (_ : Fintype η)
    (χ : EuclideanSpace ℝ η → MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
    (r0 : ℝ) (d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ) (e : EuclideanSpace ℝ η → ℝ)
    (ν : Measure (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))),
    ν.IsMulLeftInvariant ∧ SFinite ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≠ ⊤ ∧
    PI.AprimeInfG.TubeChart X.measG.μGinf (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
      ν κ χ r0 d e ∧
    ContinuousAt d 0 ∧ 0 < d 0 ∧ ContinuousAt e 0 ∧ 0 < e 0 ∧ d 0 / e 0 * (ν Set.univ).toReal = gVal X

theorem grpLim_of_chart {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (h : GrpChart X u' κ) : GrpLim X u' κ := by
  obtain ⟨η, hη, χ, r0, d, e, ν, hL, hSF, h0, hf, hC, hd, hd0, he, he0, hval⟩ := h
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have := hL
  have := hSF
  obtain ⟨⟨ρ0, hρ0, hP⟩, hT⟩ := PI.AprimeInfG.tube_ratio X.measG.μGinf _ ν h0 hf hC hd hd0 he he0
  refine ⟨⟨ρ0, hρ0, fun ρ hρ hρ' => ?_⟩, fun ρ hρ hρl => ?_⟩
  · rw [tubeG_eq]; exact hP ρ hρ hρ'
  · simp only [tubeG_eq]
    rw [← hval]
    exact hT.comp (tendsto_nhdsWithin_iff.2 ⟨hρl, Filter.Eventually.of_forall hρ⟩)

def GrpPieces {D7' : D7} (X : HidaSetting D7') (u' : D7'.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  ∃ (η : Type) (_ : Fintype η)
    (χ : EuclideanSpace ℝ η → MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
    (r0 : ℝ) (φ : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (U : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) (D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ)
    (F : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → EuclideanSpace ℝ ι × EuclideanSpace ℝ η)
    (F' : EuclideanSpace ℝ ι × EuclideanSpace ℝ η →
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ η →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (e : EuclideanSpace ℝ η → ℝ)
    (ν : Measure (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))),
    ν.IsMulLeftInvariant ∧ SFinite ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≠ ⊤ ∧ 0 < r0 ∧
    ContinuousOn κ (ball 0 r0) ∧ ContinuousOn χ (ball 0 r0) ∧ Set.InjOn χ (ball 0 r0) ∧
    (∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r0, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r0,
      (κ a)⁻¹ * κ b ∈ MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') → a = b) ∧
    (∀ A ⊆ U, MeasurableSet A → X.measG.μGinf (φ '' A) = ∫⁻ z in A, ENNReal.ofReal (D z)) ∧
    (∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, HasFDerivWithinAt F (F' p) (ball 0 r0) p) ∧
    Set.InjOn F (ball 0 r0) ∧ F '' ball 0 r0 ⊆ U ∧
    (∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, κ p.1 * (χ p.2 : HA _ _ _) = φ (F p)) ∧
    (∀ s, 0 < s → s ≤ r0 → ν (χ '' ball 0 s) = ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)) ∧
    ContinuousAt F 0 ∧ ContinuousAt (fun p => |(F' p).det|) 0 ∧ ContinuousAt D (F 0) ∧ ContinuousAt e 0 ∧
    0 < e 0 ∧ 0 < |(F' 0).det| * D (F 0) ∧ |(F' 0).det| * D (F 0) / e 0 * (ν Set.univ).toReal = gVal X

theorem grpChart_of_pieces {D7' : D7} (X : HidaSetting D7') (u' : D7'.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (h : GrpPieces X u' κ) :
    GrpChart X u' κ := by
  obtain ⟨η, hη, χ, r0, φ, U, D, F, F', e, ν, hL, hSF, h0, hf, hr0, hκc, hχc, hχi, hinj, hφ, hF, hFi, hFU, hΦ,
    hνH, hFc, hdet, hD, he, he0, hd0, hval⟩ := h
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have hcl : IsClosed ((MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :
      Subgroup (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    by
      have hc := PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
      show IsClosed ((fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {Y0 X u'})
      exact isClosed_singleton.preimage hc
  exact ⟨η, hη, χ, r0, fun p => |(F' p).det| * D (F p), e, ν, hL, hSF, h0, hf,
    PI.AprimeInfG.tubeChart_of X.measG.μGinf _ hcl ν κ χ hr0 hκc hχc hχi hinj φ U D hφ F F' hF hFi hFU hΦ e hνH,
    PI.AprimeInfG.contAt_dens hFc hdet hD, hd0, he, he0, hval⟩

theorem grpLim_of_pieces {D7' : D7} (X : HidaSetting D7') (u' : D7'.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (h : GrpPieces X u' κ) : GrpLim X u' κ :=
  grpLim_of_chart X u' κ (grpChart_of_pieces X u' κ h)

end PI.AprimeInfW
end
end
