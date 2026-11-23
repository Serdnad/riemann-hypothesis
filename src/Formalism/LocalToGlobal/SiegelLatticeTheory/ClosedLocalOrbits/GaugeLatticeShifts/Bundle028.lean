module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PhaseAtPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle026
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DualCoords
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

theorem hinfConjC_holds : HinfConjC := by
  intro D X u h hh Ω hΩ
  obtain ⟨h1, hmul, hinvN⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  let N : Subgroup X.B.I.Ginf :=
    Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.subOf (X.NinfU u) h1 (fun x hx y hy => (hmul x hx y hy).1) hinvN
  have hNc : IsClosed (N : Set X.B.I.Ginf) := Formalism.L2.SG.Pf.Vanish2.ninf_closed X.B.I X.eR (X.zR u)
  have hH : IsHaarOnSet X.B.I (N : Set X.B.I.Ginf) (X.muN u) := X.muN_haar u
  have hHa := Formalism.L2.SG.Pf.haarOnSet_isHaar_inst X.B.I N hNc (X.muN u) hH
  obtain ⟨_, h0, hc, hl⟩ := hH
  have hfin : IsFiniteMeasureOnCompacts (X.muN u) := ⟨hHa.2.1⟩
  have hconj : ∀ g ∈ Hinf X u, ∀ n ∈ X.NinfU u, g * n * g⁻¹ ∈ X.NinfU u := fun g hg n hn => by
    have hi : g⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hg
    have hfix : ∀ v, ∀ x ∈ fixSet X u, (uMat (g⁻¹ v)).mulVec (rv X.B.I v x) = rv X.B.I v x := hi
    have := Formalism.L2.SG.CovariantRepresentation.ninf_conj X u g⁻¹ (fun v a => hfix v _ (Or.inl (Or.inl ⟨a, rfl⟩)))
      (fun v => hfix v _ (Or.inr rfl)) hn
    simpa using this
  have hcont : ∀ g : X.B.I.Ginf, Continuous fun s : X.B.I.Ginf => g * s * g⁻¹ := fun g =>
    (continuous_const.mul continuous_id).mul continuous_const

  obtain ⟨K0, hK0c, hK0n⟩ := exists_compact_mem_nhds (1 : X.B.I.Ginf)
  have hK0pos : 0 < X.muN u K0 := by
    have hpos := hHa.2.2 (interior K0) isOpen_interior ⟨1, mem_interior_iff_mem_nhds.2 hK0n, h1⟩
    exact lt_of_lt_of_le hpos (measure_mono interior_subset)
  let K : Set X.B.I.Ginf :=
    (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2 * p.1⁻¹) '' ((Hinf X u : Set X.B.I.Ginf) ×ˢ K0)
  have hKc : IsCompact K :=
    ((Formalism.L2.SG.Pf.hinf_compact X u).prod hK0c).image
      ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  have hK0K : K0 ⊆ K := fun k hk => ⟨(1, k), ⟨(Hinf X u).one_mem, hk⟩, by simp⟩
  have hKpos : 0 < X.muN u K := lt_of_lt_of_le hK0pos (measure_mono hK0K)
  have hKfin : X.muN u K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKinv : ∀ g ∈ Hinf X u, (fun s => g * s * g⁻¹) ⁻¹' K = K := by
    intro g hg
    ext x
    constructor
    · rintro ⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩
      refine ⟨(g⁻¹ * a, k), ⟨(Hinf X u).mul_mem ((Hinf X u).inv_mem hg) ha, hk⟩, ?_⟩
      have hx' : a * k * a⁻¹ = g * x * g⁻¹ := hx
      show g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = x
      calc g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = g⁻¹ * (a * k * a⁻¹) * g := by group
        _ = x := by rw [hx']; group
    · rintro ⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩
      refine ⟨(g * a, k), ⟨(Hinf X u).mul_mem hg ha, hk⟩, ?_⟩
      have hx' : a * k * a⁻¹ = x := hx
      show g * a * k * (g * a)⁻¹ = g * x * g⁻¹
      calc g * a * k * (g * a)⁻¹ = g * (a * k * a⁻¹) * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [hx']

  have key : ∀ g ∈ Hinf X u, (X.muN u).map (fun s => g * s * g⁻¹) = X.muN u := by
    intro g hg
    have hm : Measurable fun s : X.B.I.Ginf => g * s * g⁻¹ := (hcont g).measurable
    have hpre : ∀ S : Set X.B.I.Ginf, (fun s => g * s * g⁻¹) ⁻¹' S = (fun s => g⁻¹ * s * g⁻¹⁻¹) '' S := by
      intro S
      exact (congrFun (Set.image_eq_preimage_of_inverse (f := fun s => g⁻¹ * s * g⁻¹⁻¹)
        (g := fun s => g * s * g⁻¹) (fun s => by show g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s; group)
        (fun s => by show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s; group)) S).symm
    have hν0 : (X.muN u).map (fun s => g * s * g⁻¹) ≠ 0 := by
      intro hz
      apply h0
      have := congrArg (fun m : Measure X.B.I.Ginf => m Set.univ) hz
      simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    have hνc : (X.muN u).map (fun s => g * s * g⁻¹) (N : Set X.B.I.Ginf)ᶜ = 0 := by
      rw [Measure.map_apply hm hNc.measurableSet.compl]
      exact measure_mono_null (t := (N : Set X.B.I.Ginf)ᶜ) (fun ⦃s⦄ hs hsN => hs (hconj g hg s hsN)) hc
    have hνi : ∀ t ∈ N, ((X.muN u).map (fun s => g * s * g⁻¹)).map (fun x => t * x) =
        (X.muN u).map (fun s => g * s * g⁻¹) := by
      intro t ht
      have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ X.NinfU u := hconj g⁻¹ ((Hinf X u).inv_mem hg) t ht
      rw [Measure.map_map (measurable_const_mul t) hm]
      have e : (fun x => t * x) ∘ (fun s => g * s * g⁻¹) =
          (fun s => g * s * g⁻¹) ∘ (fun x => (g⁻¹ * t * g⁻¹⁻¹) * x) := by
        funext s
        show t * (g * s * g⁻¹) = g * (g⁻¹ * t * g⁻¹⁻¹ * s) * g⁻¹
        group
      rw [e, ← Measure.map_map hm (measurable_const_mul _), hl _ ht']
    have hνf : IsFiniteMeasureOnCompacts ((X.muN u).map (fun s => g * s * g⁻¹)) := ⟨fun C hC => by
      rw [Measure.map_apply hm hC.isClosed.measurableSet, hpre]
      exact (hC.image (hcont _)).measure_lt_top⟩
    obtain ⟨c, _, hceq⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.haar_unique N hNc (X.muN u)
      ((X.muN u).map (fun s => g * s * g⁻¹)) h0 hc hl hfin hνc hνi hνf
    have hK' : (X.muN u).map (fun s => g * s * g⁻¹) K = X.muN u K := by
      rw [Measure.map_apply hm hKc.isClosed.measurableSet, hKinv g hg]
    rw [hceq, Measure.smul_apply, smul_eq_mul] at hK'
    have hc1 : c = 1 := (ENNReal.mul_left_inj hKpos.ne' hKfin).1 (hK'.trans (one_mul _).symm)
    rw [hceq, hc1, one_smul]
  have hinv' : h⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hh
  have e : (fun s => h * s * h⁻¹) '' Ω = (fun s => h⁻¹ * s * h⁻¹⁻¹) ⁻¹' Ω :=
    congrFun (Set.image_eq_preimage_of_inverse (f := fun s => h * s * h⁻¹) (g := fun s => h⁻¹ * s * h⁻¹⁻¹)
      (fun s => by show h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s; group)
      (fun s => by show h * (h⁻¹ * s * h⁻¹⁻¹) * h⁻¹ = s; group)) Ω
  rw [e, ← Measure.map_apply (hcont _).measurable hΩ, key _ hinv']

end Formalism.L2.SG.Pf.IdMeet
end
end

section

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem StepReal_holds : StepReal :=
  stepReal_of_witt (fun _ _ ε x y hG hnd => Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.witt_of_gram ε x y hG hnd)

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end

section

noncomputable section

open MeasureTheory Topology

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n : ℕ} {ε : Fin n → Bool}

def haarSub (G : Subgroup (Formalism.REAL.UJ ε)) (hG : IsClosed (G : Set (Formalism.REAL.UJ ε))) : Measure (Formalism.REAL.UJ ε) :=
  haveI : LocallyCompactSpace G := hG.isClosedEmbedding_subtypeVal.locallyCompactSpace
  (Measure.haar : Measure G).map Subtype.val

theorem haarSub_isHaarS (G : Subgroup (Formalism.REAL.UJ ε)) (hG : IsClosed (G : Set (Formalism.REAL.UJ ε))) :
    IsHaarS (G : Set (Formalism.REAL.UJ ε)) (haarSub G hG) := by
  have : LocallyCompactSpace G := hG.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hemb := hG.isClosedEmbedding_subtypeVal
  have hι : Measurable (Subtype.val : G → Formalism.REAL.UJ ε) := measurable_subtype_coe
  have hfin : IsFiniteMeasureOnCompacts (haarSub G hG) := by
    refine ⟨fun K hK => ?_⟩
    rw [haarSub, Measure.map_apply hι hK.measurableSet]
    exact (hemb.isCompact_preimage hK).measure_lt_top
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin⟩
  · have := hfin
    infer_instance
  · rw [haarSub, Ne, Measure.map_eq_zero_iff hι.aemeasurable]
    exact NeZero.ne _
  · rw [haarSub, Measure.map_apply hι hG.measurableSet.compl]
    have hempty : (Subtype.val : G → Formalism.REAL.UJ ε) ⁻¹' (G : Set (Formalism.REAL.UJ ε))ᶜ = ∅ := by
      ext x
      simp
    rw [hempty, measure_empty]
  · intro s hs
    rw [haarSub, Measure.map_map (measurable_const_mul s) hι]
    have hcomp : (fun x => s * x) ∘ (Subtype.val : G → Formalism.REAL.UJ ε) =
        Subtype.val ∘ (fun y : G => (⟨s, hs⟩ : G) * y) := rfl
    rw [hcomp, ← Measure.map_map hι (measurable_const_mul _), map_mul_left_eq_self]

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem dl_diagonal {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (h : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE h i) := by
  unfold Dl
  simp only [dif_pos h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective h), Matrix.det_diagonal,
    Function.comp_apply]

theorem dcLoc_eq (r : ℕ) : dcLoc (r := r) = (2 : ℝ≥0∞) ^ (r + 1) • (volume : Measure (Fin (r + 1) → ℂ)) := by
  haveI : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by rw [two_smul]; infer_instance
  unfold dcLoc
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.IotaDictPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem levi_one_iff {δ : X.B.I.Gf} (gδ : Good X δ) :
    levi TR δ = 1 ↔ ∀ j, (X.B.I.fmat δ - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  refine ⟨fun h1 i => ?_, fun h => Formalism.L2.SG.Pf.AmpIota.levi_eq_one_of TR gδ h⟩
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  set w := X.B.I.fmat δ *ᵥ X.bw i with hwdef
  have hwL : w ∈ X.B.I.Lf := K_mv X.B.I gδ.1.1 (hB i)
  have hwM := gδ.1.2.2 i
  have hd := dual_coords X hwL
  have hZe : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) w) := fun a =>
    Z_pair_Mo X (hE0 a) (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · exact (X.gramIntegral a b).1
      · exact ((X.weightVectorsIntegral l).2.2 a).1) _ hwM
  have hZz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 w) :=
    Z_pair_Mo X hZ0 (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · rw [hA_symm]; exact Z_sig X.B.I X.B.g ((X.formsAtZero).2 b).1
      · exact (X.weightVectorsIntegral l).1) _ hwM
  have hbw0 : ∀ j, hA X.B.I (X.bw j) w = 0 := fun j => by
    rw [hwdef, X.bw_w j, X.bw_w i, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
    have := X.ew_orth
    linear_combination (hA X.B.I (X.bw j) (X.B.I.fmat δ *ᵥ X.bw i)) * this
  have hcoef : ∀ j : Fin D.R.k, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) := by
    intro j
    have hI := hA_int X.B.I (hBd j) hwL
    have hIt : ((if j = i then 1 else 0 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := by
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have hres : ∀ v, TR.res v ⟨_, sub_mem hI hIt⟩ = 0 := by
      intro v
      have hent : leviM TR δ v j i = if j = i then 1 else 0 := by
        rw [← levi_coe TR gδ, h1, Pi.one_apply, Units.val_one, Matrix.one_apply]
      have e : (⟨_, sub_mem hI hIt⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, hI⟩ - ⟨_, hIt⟩ := by
        apply Subtype.ext; simp
      rw [e, map_sub]
      have h2 : TR.res v ⟨_, hI⟩ = leviM TR δ v j i := by
        show _ = resT TR v (hA X.B.I (X.bwd j) (X.B.I.fmat δ *ᵥ X.bw i))
        rw [resT_of_mem TR v hI]
      rw [h2, hent]
      by_cases h : j = i
      · subst h
        have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 1 := by apply Subtype.ext; simp
        rw [if_pos rfl, this, map_one, sub_self]
      · have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 0 := by apply Subtype.ext; simp [h]
        rw [if_neg h, this, map_zero, sub_self]
    have hZ := (TR.res_ker ⟨_, sub_mem hI hIt⟩).1 hres
    have e : X.ew * (hA X.B.I (X.bwd j) w - if j = i then 1 else 0) =
        hA X.B.I (X.bwd j) w - if j = i then X.ew else 0 := by
      rw [mul_sub, ← bwc_ew δ j i]
      split_ifs <;> ring
    simpa [e] using hZ
  have e1 : (X.B.I.fmat δ - 1) *ᵥ X.bw i = (w - repr0 X w) +
      ((∑ a, hA X.B.I (X.f0 a) w • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) w • X.f0 a) - hA X.B.I X.z0 w • X.z0 +
        (∑ j, (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) • X.bw j) +
        (∑ j, hA X.B.I (X.bw j) w • X.bwd j)) := by
    have hbi : (∑ j, (if j = i then X.ew else 0) • X.bw j) = X.bw i := by
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact (X.bw_w i).symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hwdef]
    unfold repr0
    simp only [sub_smul, Finset.sum_sub_distrib, hbi]
    abel
  rw [e1]
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (s : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      s ∈ Set.range X.e0 → c • s ∈ Mo X.B.I X.B.g (Set.range X.e0) := fun c s hc hs => by
    have : c • s = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • s := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hs)
  refine add_mem (mL_Mo X.B.I hd) (add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_)
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF0 a) hwL) ⟨a, rfl⟩
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (hZe a) (hF0 a))
  · exact mL_Mo X.B.I (Z_smul_mL X hZz hZ0)
  · exact sum_mem fun j _ => mL_Mo X.B.I (Z_smul_mL X (hcoef j) (hB j))
  · refine sum_mem fun j _ => ?_
    rw [hbw0, zero_smul]; exact zero_mem _

theorem iotaOf_split {u u' : D.what₂.Word} (Y : Formalism.L2.SG.Full.Full X)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam') :
    Good X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) ∧
      NCong X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) ∧
      iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ = levi Y.TR ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
        (s₂.pt.2 * s₁.pt.2⁻¹) * (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) *
        iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ := by
  have hTF := Formalism.L2.SG.Full.Full.frameTie (X := X) u u'
  have hN := adm_norm_of_fixed_frames (Y.cs u) (Y.cs u') hTF (Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u')) (Formalism.L2.SG.Pf.modGAt X)
  have hA := adm_parity_of_norm (Y.cs u) (Y.cs u') (Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u')) hN
  have g1 := hA s₁
  have g2 := hA s₂
  have n1 := hN s₁
  have n2 := hN s₂
  have k1 := Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u') (F0 := X.Fu u) (F0' := X.Fu u') s₁
  have k2 := Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u') (F0 := X.Fu u) (F0' := X.Fu u') s₂
  rw [← hl, ← hl'] at g2 n2 k2
  have e : (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
      (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u) =
      kOf X u u' ((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s₁.lam') : X.B.I.Gf) s₂.pt *
      (kOf X u u' ((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s₁.lam') : X.B.I.Gf) s₁.pt)⁻¹ := by
    unfold kOf; group
  rw [e]
  refine ⟨good_mul X g2 (good_inv X g1), ncong_mul X k2 n2 (ncong_inv X k1 n1), ?_⟩
  unfold iotaOf
  rw [← hl, ← hl', levi_mul Y.TR g2 (good_inv X g1), mul_assoc, ← levi_mul Y.TR (good_inv X g1) g1, inv_mul_cancel,
    levi_one, mul_one]

end Formalism.L2.SG.Pf.IotaDictPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.IotaDictPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AdTriv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (δ : X.B.I.Gf) : Prop :=
  ∀ j, (X.B.I.fmat δ - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0)

def RatTriv {D : D7} (u : D.what₂.Word) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ x ∈ Lrep Λ (lf D (X.Fu u)), β x - x ∈ NgX Λ (gS D) (lf D (X.Fu u)) (lf D (X.Fu u))

def IotaDictC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    s₁.G ≠ 0 → s₂.G ≠ 0 → s₁.generic → s₂.generic → s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
      (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
        IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D))

end Formalism.L2.SG.Pf
end
end
