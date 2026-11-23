module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePosA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle033
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.DoubleCosetMeasures.StatementZ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle084
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseFin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle032
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictLat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarTranslationMeasurability

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem meas_invM : Measurable (invM : Mt k r → Mt k r) := by
  apply ReciprocityTheory.ChartRestriction.DS.Mult1.BesselPositivity.bp_meas_inv <;> assumption

theorem meas_mulM : Measurable (mulM : Mt k r × Mt k r → Mt k r) := by
  unfold mulM
  have hc : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mat k r)) :=
    Continuous.matrix_mul continuous_fst continuous_snd
  exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
    ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable

def Cm (g : Mt k r) (p : SS k r) : Mt k r := mulM (mulM (mulM (mulM (p.1.1, p.1.2), g), p.2.2), p.2.1)

def Tm (g : Mt k r) (p : Mt k r × Mt k r) : Mt k r := mulM (mulM (p.1, g), invM p.2)

theorem meas_Cm (g : Mt k r) : Measurable (Cm g) := by
  unfold Cm
  have hm := meas_mulM (k := k) (r := r)
  exact hm.comp ((hm.comp ((hm.comp ((hm.comp (measurable_fst.fst.prodMk measurable_fst.snd)).prodMk
    measurable_const)).prodMk measurable_snd.snd)).prodMk measurable_snd.fst)

theorem meas_Tm (g : Mt k r) : Measurable (Tm g) := by
  unfold Tm
  have hm := meas_mulM (k := k) (r := r)
  exact hm.comp ((hm.comp (measurable_fst.prodMk measurable_const)).prodMk (meas_invM.comp measurable_snd))

theorem tgt_eq (A B A' : Measure (Mt k r)) [SFinite A] [SFinite B] [SFinite A']
    (hB : B.map invM = B) (hA' : A'.map invM = A') (g : Mt k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ s, ∫⁻ s', φ (Tm g (s, s')) ∂(Formalism.MainNotions.S.muS A' B) ∂(Formalism.MainNotions.S.muS A B) =
      ∫⁻ p, φ (Cm g p) ∂((A.prod B).prod (A'.prod B)) := by
  have hm := meas_mulM (k := k) (r := r)
  have hi := meas_invM (k := k) (r := r)
  have hT := meas_Tm g
  have hmu : ∀ X Y : Measure (Mt k r), Formalism.MainNotions.S.muS X Y = (X.prod Y).map mulM := fun _ _ => rfl
  rw [hmu, hmu]
  have step1 : ∀ s, ∫⁻ s', φ (Tm g (s, s')) ∂((A'.prod B).map mulM) =
      ∫⁻ y, φ (Tm g (s, mulM y)) ∂(A'.prod B) := fun s =>
    lintegral_map (hφ.comp (hT.comp (measurable_const.prodMk measurable_id))) hm
  rw [lintegral_congr step1]
  have hH : Measurable fun s => ∫⁻ y, φ (Tm g (s, mulM y)) ∂(A'.prod B) :=
    Measurable.lintegral_prod_right' (f := fun q : Mt k r × (Mt k r × Mt k r) => φ (Tm g (q.1, mulM q.2)))
      (hφ.comp (hT.comp (measurable_fst.prodMk (hm.comp measurable_snd))))
  rw [lintegral_map hH hm]
  have hF : Measurable fun p : (Mt k r × Mt k r) × (Mt k r × Mt k r) => φ (Tm g (mulM p.1, mulM p.2)) :=
    hφ.comp (hT.comp ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd)))
  rw [← lintegral_prod _ hF.aemeasurable]
  have hpt : ∀ p : (Mt k r × Mt k r) × (Mt k r × Mt k r),
      Tm g (mulM p.1, mulM p.2) = Cm g (Prod.map id (Prod.map invM invM) p) := by
    intro p
    show (Matrix.of p.1.1 * Matrix.of p.1.2 * Matrix.of g * (Matrix.of p.2.1 * Matrix.of p.2.2)⁻¹ : Mat k r) =
      Matrix.of p.1.1 * Matrix.of p.1.2 * Matrix.of g * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹
    rw [Matrix.mul_inv_rev]
    exact (mul_assoc _ _ _).symm
  simp only [hpt]
  have h2 : (A'.prod B).map (Prod.map invM invM) = A'.prod B := by
    rw [← Measure.map_prod_map A' B hi hi, hA', hB]
  have hP : ((A.prod B).prod (A'.prod B)).map (Prod.map id (Prod.map invM invM)) = (A.prod B).prod (A'.prod B) := by
    rw [← Measure.map_prod_map _ _ measurable_id (hi.prodMap hi), Measure.map_id, h2]
  refine (lintegral_map (f := φ ∘ Cm g) (hφ.comp (meas_Cm g)) (measurable_id.prodMap (hi.prodMap hi))).symm.trans ?_
  rw [hP]
  rfl

theorem src_eq (A B A' : Measure (Mt k r)) [SFinite A] [SFinite B] [SFinite A']
    (hA : A.map invM = A) (hB : B.map invM = B) (g : Mat k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ p, φ (sgs p g) ∂((A.prod B).prod (A'.prod B)) = ∫⁻ p, φ (Cm g p) ∂((A.prod B).prod (A'.prod B)) := by
  have hi := meas_invM (k := k) (r := r)
  have hpt : ∀ p : SS k r, (sgs p g : Mt k r) = Cm g (Prod.map (Prod.map invM invM) id p) := fun _ => rfl
  simp only [hpt]
  have h1 : (A.prod B).map (Prod.map invM invM) = A.prod B := by
    rw [← Measure.map_prod_map A B hi hi, hA, hB]
  have hP : ((A.prod B).prod (A'.prod B)).map (Prod.map (Prod.map invM invM) id) = (A.prod B).prod (A'.prod B) := by
    rw [← Measure.map_prod_map _ _ (hi.prodMap hi) measurable_id, Measure.map_id, h1]
  refine (lintegral_map (f := φ ∘ Cm g) (hφ.comp (meas_Cm g)) ((hi.prodMap hi).prodMap measurable_id)).symm.trans ?_
  rw [hP]
  rfl

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarTranslationMeasurability

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 HaarTranslationMeasurability

theorem hpkEx_holds : HpkEx := by
  intro k r z z' hk hz hz' hT hT' μ μW μW' μN hμ hW hW' hN μsec hsec
  obtain ⟨μG0, hG0⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨μW0, hW0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  obtain ⟨μW0', hW0'⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z' hz' hT'
  obtain ⟨μN0, hN0⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  have hD : IsMeasData k r z z' μsec μG0 μW0 μN0 μW0' := ⟨hk, hz, hz', hT, hT', hG0, hW0, hN0, hW0', hsec⟩
  obtain ⟨C, hC, hInt⟩ := Formalism.FourierDecayAlt.P.integration_formula_constant k r z z' μsec μG0 μW0 μN0 μW0' hD
  have cG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have cW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have cW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have cN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  obtain ⟨a, ha0, hat, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cG hG0 hμ
  obtain ⟨b, hb0, hbt, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cW hW0 hW
  obtain ⟨b', hb0', hbt', rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cW' hW0' hW'
  obtain ⟨d, hd0, hdt, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cN hN0 hN
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW0
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW0'
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hN0
  have iW := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μW0 cW hW0
  have iW' := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μW0' cW' hW0'
  have iN := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μN0 cN hN0
  have jW' : (b' • μW0').map invM = b' • μW0' := by
    rw [Measure.map_smul b' meas_invM.aemeasurable, iW']
  have jN : (d • μN0).map invM = d • μN0 := by
    rw [Measure.map_smul d meas_invM.aemeasurable, iN]
  set κ : ℝ≥0∞ := b * d * (b' * d) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ, hb0, hd0, hb0']
  have hκt : κ ≠ ⊤ := by simp [hκ, ENNReal.mul_eq_top, hbt, hdt, hbt']
  have key : ∀ (g : Mat k r) (φ : Mt k r → ℝ≥0∞), Measurable φ →
      ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * g * (Matrix.of s')⁻¹) i j)
          ∂(Formalism.MainNotions.S.muS (b' • μW0') (d • μN0)) ∂(Formalism.MainNotions.S.muS (b • μW0) (d • μN0)) =
        κ * ∫⁻ p, φ (sgs p g) ∂((μW0.prod μN0).prod (μW0'.prod μN0)) := by
    intro g φ hφ
    have := tgt_eq (b • μW0) (d • μN0) (b' • μW0') jN jW' g φ hφ
    refine this.trans ?_
    rw [src_eq μW0 μN0 μW0' iW iN g φ hφ]
    simp only [Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure, smul_eq_mul, hκ]
    ring
  have hne : a * (C : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top hat ENNReal.coe_ne_top
  have hne0 : a * (C : ℝ≥0∞) ≠ 0 := mul_ne_zero ha0 (by exact_mod_cast hC.ne')
  refine ⟨(a * C / κ).toReal, ENNReal.toReal_pos (by simp [ENNReal.div_eq_zero_iff, hne0, hκt])
    (ENNReal.div_lt_top hne hκ0).ne, fun φ hφ => ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.div_lt_top hne hκ0).ne, lintegral_smul_measure, hInt φ hφ, smul_eq_mul]
  simp_rw [key _ φ hφ]
  have hc : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
      (κ * ∫⁻ p, φ (sgs p (bigCell k r q.1 (μsec q.2))) ∂((μW0.prod μN0).prod (μW0'.prod μN0))) =
      κ * (ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
        ∫⁻ p, φ (sgs p (bigCell k r q.1 (μsec q.2))) ∂((μW0.prod μN0).prod (μW0'.prod μN0))) := fun q => by ring
  simp_rw [hc]
  rw [lintegral_const_mul' _ _ hκt, ← mul_assoc, ← mul_assoc, ENNReal.div_mul_cancel hκ0 hκt]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB PIW.AdelClassFin

attribute [local instance] starRA

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem mulVec_cols' {m p : Type*} [Fintype p] [DecidableEq p] (M : Matrix m p (RA X)) (c : p → RA X) :
    M *ᵥ c = ∑ k, c k • (M *ᵥ Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single c]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (c k) : p → RA X) = c k • Pi.single k 1 by ext j; simp [Pi.single_apply],
    Matrix.mulVec_smul]

theorem Bf_col (k : Kap X) : Bf X *ᵥ Pi.single k 1 = incl X.B.I (bv X k) := by
  rw [mulVec_single_one]
  rfl

theorem Bf'_incl (k : Kap X) : Bf' X *ᵥ incl X.B.I (bv X k) = Pi.single k 1 := by
  rw [← Bf_col, Matrix.mulVec_mulVec, Bf'_mul_Bf, Matrix.one_mulVec]

theorem hA_sum' (x : VA X.B.I) (s : Finset (Kap X)) (c : Kap X → RA X) (v : Kap X → VA X.B.I) :
    hA X.B.I x (∑ k ∈ s, c k • v k) = ∑ k ∈ s, c k * hA X.B.I x (v k) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact DictLat.hhat_zero_right X.B.I x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rw [show hA X.B.I x (c a • v a + ∑ k ∈ s, c k • v k) =
        hA X.B.I x (c a • v a) + hA X.B.I x (∑ k ∈ s, c k • v k) from DictLat.hhat_add_right X.B.I _ _ _]
    rw [show hA X.B.I x (c a • v a) = c a * hA X.B.I x (v a) from DictLat.hhat_smul_right X.B.I _ _ _]

theorem hA_incl (v w : Fin X.B.I.n → X.B.I.E) :
    hA X.B.I (incl X.B.I v) (incl X.B.I w) = ic X (_root_.Formalism.L2.SG.Pf.UnipB.hE X v w) := DictLat.hhat_iv X.B.I v w

theorem hA_e_Bf (a : Fin D.R.rS) (c : Kap X → RA X) :
    hA X.B.I (incl X.B.I (X.eR a)) (Bf X *ᵥ c) = c (Sum.inr (Sum.inr a)) := by
  rw [mulVec_cols', hA_sum']
  have e : ∀ k, hA X.B.I (incl X.B.I (X.eR a)) (Bf X *ᵥ Pi.single k 1) = ic X (JB X (Sum.inl a) k) := by
    intro k
    rw [Bf_col]
    exact hA_incl X (X.eR a) (bv X k)
  simp only [e, JB_e_row]
  simp

theorem hA_e_w (a : Fin D.R.rS) (i : Fin (mW X)) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (bv X (Sum.inr (Sum.inl i)))) = 0 := by
  rw [hA_incl]
  have := (wb_mem X i a).1
  simp only [bv, Sum.elim_inr, Sum.elim_inl]
  rw [this, map_zero]

theorem adelicHermitian_hyperbolicE_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.zR u)) = 0 := by
  rw [hA_incl, hE_ez X u a, map_zero]

theorem Bf_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → RA X) (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    Bf X *ᵥ c ∈ Submodule.span (RA X) ((fun b => incl X.B.I (X.eR b)) '' S) := by
  rw [mulVec_cols']
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    rw [Bf_col]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

theorem Bf'_mulVec_supp (S : Set (Fin D.R.rS)) {y : VA X.B.I}
    (hy : y ∈ Submodule.span (RA X) ((fun b => incl X.B.I (X.eR b)) '' S)) :
    ∀ k, k ∉ Sum.inl '' S → (Bf' X *ᵥ y) k = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro k hk
    show (Bf' X *ᵥ incl X.B.I (bv X (Sum.inl b))) k = 0
    rw [Bf'_incl, Pi.single_apply, if_neg]
    rintro rfl
    exact hk ⟨b, hb, rfl⟩
  | zero => intro k _; simp
  | add x y _ _ hx hy => intro k hk; rw [Matrix.mulVec_add, Pi.add_apply, hx k hk, hy k hk, add_zero]
  | smul c x _ hx => intro k hk; rw [Matrix.mulVec_smul, Pi.smul_apply, hx k hk, smul_zero]

theorem nf_of_pat (x : X.B.I.Gf) (hpat : InPat (lvk X) 1 (Mf X x - 1)) : x ∈ X.NfinU u := by
  set M := Mf X x with hM
  have hg : X.B.I.fmat x - 1 = Bf X * (M - 1) * Bf' X := by
    rw [hM, Mf, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bf_mul_Bf']
    simp only [← Matrix.mul_assoc, Bf_mul_Bf', Matrix.one_mul]
    rw [Matrix.mul_assoc, Bf_mul_Bf', Matrix.mul_one]
  have hgv : ∀ y, (X.B.I.fmat x - 1) *ᵥ y = Bf X *ᵥ ((M - 1) *ᵥ (Bf' X *ᵥ y)) := by
    intro y
    rw [hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hperp : ∀ y : VA X.B.I, (∀ a, hA X.B.I (incl X.B.I (X.eR a)) y = 0) →
      (X.B.I.fmat x - 1) *ᵥ y ∈ Submodule.span (RA X) (Set.range fun b => incl X.B.I (X.eR b)) := by
    intro y hy
    set c := Bf' X *ᵥ y with hc
    have hyc : y = Bf X *ᵥ c := by rw [hc, Matrix.mulVec_mulVec, Bf_mul_Bf', Matrix.one_mulVec]
    have hcf : ∀ a, c (Sum.inr (Sum.inr a)) = 0 := by
      intro a
      have := hA_e_Bf X a c
      rw [← hyc, hy a] at this
      exact this.symm
    rw [hgv, ← hc, ← Set.image_univ]
    refine Bf_mulVec_mem X Set.univ _ fun k hk => ?_
    have hk' : ∀ b, k ≠ Sum.inl b := by
      rintro b rfl
      exact hk ⟨b, Set.mem_univ _, rfl⟩
    rw [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hlk := lvk_notinl X k hk'
    rcases j with b | i | b
    · rw [hpat k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
    · rw [hpat k _ (by rw [lvk_w]; omega), zero_mul]
    · rw [hcf b, mul_zero]
  show _ ∧ _ ∧ _
  refine ⟨fun a => ?_, hperp _ fun a => adelicHermitian_hyperbolicE_anisotropic_eq_zero X u a, hperp⟩
  rw [hgv]
  rw [show incl X.B.I (X.eR a) = incl X.B.I (bv X (Sum.inl a)) from rfl, Bf'_incl]
  refine Bf_mulVec_mem X {b | b.1 < a.1} _ fun k hk => ?_
  rw [mulVec_single_one]
  refine hpat k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

theorem half_fin {y : X.B.I.Gf} (hy : y ∈ X.NfinU u) :
    ∀ i j, lvk X j ≤ D.R.rS + 1 → lvk X j < lvk X i + 1 → (Mf X y - 1) i j = 0 := by
  intro i j hj hij
  have hM : Mf X y - 1 = Bf' X * (X.B.I.fmat y - 1) * Bf X := by
    unfold Mf
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bf'_mul_Bf]
  have hcol : (Mf X y - 1) i j = (Bf' X *ᵥ ((X.B.I.fmat y - 1) *ᵥ incl X.B.I (bv X j))) i := by
    rw [hM, ← Bf_col, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mulVec_single_one]
    rfl
  rw [hcol]
  rcases j with a | w | a
  · refine Bf'_mulVec_supp X {b | b.1 < a.1} (hy.1 a) i ?_
    rintro ⟨b, hb, rfl⟩
    simp only [lvk, Sum.elim_inl, Set.mem_setOf_eq] at hij hb
    omega
  · have h := hy.2.2 _ fun a => hA_e_w X a w
    rw [← Set.image_univ] at h
    refine Bf'_mulVec_supp X Set.univ h i ?_
    rintro ⟨b, -, rfl⟩
    simp only [lvk, Sum.elim_inl, Sum.elim_inr] at hij
    have := b.2
    omega
  · simp only [lvk, Sum.elim_inr] at hj
    have := a.2
    omega

theorem pat_of_nf {x : X.B.I.Gf} (hx : x ∈ X.NfinU u) : InPat (lvk X) 1 (Mf X x - 1) := by
  have hx' : x⁻¹ ∈ X.NfinU u := (Formalism.L2.SG.Pf.NfinSub X.eR (X.zR u)).inv_mem hx
  have hMN : Mf X x = sharp (JBf X) (JBf' X) (Mf X x⁻¹) := by
    have := Mf_inv X x⁻¹
    rwa [inv_inv] at this
  exact half_to_full (JBf_graded X) (JBf'_graded X) (JBf'_mul X) (h₀ := D.R.rS + 1) (by omega) hMN
    (half_fin X u hx') (half_fin X u hx)

theorem pattern_of_nilradical : NfPat := fun _ X u _ hx => pat_of_nf X u hx

theorem nilradical_of_pattern : NfOfPat := fun _ X u x h => nf_of_pat X u x h

theorem cay_inv_R (x : X.B.I.Gf) (hT : InPat (lvk X) 1 (Mf X x - 1)) :
    ∃ Z : Matrix (Kap X) (Kap X) (RA X), InPat (lvk X) 1 Z ∧
      Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -(JBf X * Z) ∧
        cay (2 * D.R.rS + 2) Z = Mf X x := by
  set N := 2 * D.R.rS + 2 with hN
  have hZpat : InPat (lvk X) 1 (icay N (Mf X x)) :=
    inPat_mul hT (inPat_geo (inPat_neg (inPat_smul _ hT)) N)
  have hP : sharp (JBf X) (JBf' X) (Mf X x) = Mf X x⁻¹ := (Mf_inv X x).symm
  have hPM : Mf X x⁻¹ * Mf X x = 1 := by rw [← Mf_mul, inv_mul_cancel, Mf_one]
  have hT' : InPat (lvk X) 1 (Mf X x⁻¹ - 1) := by
    have e : Mf X x⁻¹ - 1 = sharp (JBf X) (JBf' X) (Mf X x - 1) := by
      rw [sharp_sub, hP, sharp_one (JBf'_mul X)]
    rw [e]
    exact inPat_sharp (JBf_graded X) (JBf'_graded X) hT
  have hs := icay_skew (JBf_mul X) (JBf'_mul X) hP hPM (nil_of_pat X le_rfl hT _) (nil_of_pat X le_rfl hT' _)
  refine ⟨icay N (Mf X x), hZpat, ?_, cay_icay (nil_of_pat X le_rfl hT _) (nil_of_pat X le_rfl hZpat _)⟩
  rw [cT_eqR]
  calc (icay N (Mf X x))ᴴ * JBf X = JBf X * sharp (JBf X) (JBf' X) (icay N (Mf X x)) := by
        unfold sharp
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, JBf_mul, Matrix.one_mul]
    _ = -(JBf X * icay N (Mf X x)) := by rw [hs, Matrix.mul_neg]

theorem cayley_inverse_right : CayInvR := fun _ X x h => cay_inv_R X x h

end Formalism.L2.SG.Pf.SlabNDensePf
end
end

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaDictAllC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
      (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
        IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D))

theorem levi_split_iff {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) {u u' : D.what₂.Word}
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam') :
    (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
      AdTriv X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt * s₁.pt⁻¹).2 *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u))) := by
  obtain ⟨gδ, -, hs⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  rw [hb2, AdTriv, ← IotaDictPf.levi_one_iff Y.TR gδ, hs]
  constructor
  · intro h
    exact mul_right_cancel (h.symm.trans (one_mul _).symm)
  · intro h
    rw [h, one_mul]

theorem iotaDict_fwd {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) {u u' : D.what₂.Word}
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam')
    (h : iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂) :
    IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D) := by
  obtain ⟨gδ, nδ, -⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  have hRL : RatLink X (s₂.pt * s₁.pt⁻¹) (s₂.lin * s₁.lin⁻¹) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X s₂.rep.2.1 (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X s₁.rep.2.1)
  rw [Formalism.L2.SG.Pf.Act.ratIotaC' Y u u' s₁ s₂ hl hl']
  refine iotaBridgeARC_holds _ X Y u s₁.lam s₁.mem _ _ hRL (by rw [hb2]; exact gδ.1.1) (by rw [hb2]; exact nδ) ?_
  exact (levi_split_iff Y s₁ s₂ hl hl').1 h

theorem iotaDictAllC_of (h2 : IotaBridgeRAC) : IotaDictAllC := by
  intro D X Y u u' s₁ s₂ hl hl'
  refine ⟨iotaDict_fwd Y s₁ s₂ hl hl', fun h => ?_⟩
  obtain ⟨gδ, nδ, -⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  have hRL : RatLink X (s₂.pt * s₁.pt⁻¹) (s₂.lin * s₁.lin⁻¹) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X s₂.rep.2.1 (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X s₁.rep.2.1)
  rw [Formalism.L2.SG.Pf.Act.ratIotaC' Y u u' s₁ s₂ hl hl'] at h
  exact (levi_split_iff Y s₁ s₂ hl hl').2
    (h2 D X Y u s₁.lam s₁.mem _ _ hRL (by rw [hb2]; exact gδ.1.1) (by rw [hb2]; exact nδ) h)

theorem iotaDictC_holds_of (h2 : IotaBridgeRAC) : IotaDictC :=
  fun D X Y u u' s₁ s₂ _ _ _ _ hl hl' => iotaDictAllC_of h2 D X Y u u' s₁ s₂ hl hl'

end Formalism.L2.SG.Pf
end
end
