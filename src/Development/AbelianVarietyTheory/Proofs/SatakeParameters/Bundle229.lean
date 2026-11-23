module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle220
public import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
public import Formalism.LocalRingCardinality.DataForced
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle004
public import Formalism.LocalRingCardinality.FactDelDualNabla
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.LocalToGlobal.InertKernelTheory.KernelDifferenceOfFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle221
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.KerTh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle222
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool
import Formalism.GaussJetBounds.Bundle001
public import Formalism.GaussJetBounds.Bundle003
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.IsPairFrame
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementG
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong.LevAway

open Matrix GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.SplitPts GroundTheory.Automorphic GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem integral_iff (x : UA E a) :
    GeneralLinearGroup.map (pFin E) (x : GA E a) ∈ AdelicGLn.integralFiniteGL E a ↔
      ∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rw [AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem exists_compact_integral : ∃ C : Set (UA E a), IsCompact C ∧
    ∀ x ∈ finU (E := E) (n := a), (∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a)) → x ∈ C := by
  let Kf : Subgroup (finU (E := E) (n := a)) := (AdelicGLn.integralFiniteGL E a).comap (finPart E a)
  have hO : IsOpen (Kf : Set (finU (E := E) (n := a))) := (AdelicGLn.isOpen_integralFiniteGL E a).preimage continuous_finPart
  have hc : IsCompact (Kf : Set (finU (E := E) (n := a))) := by
    refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E a x, hx, ?_⟩
    have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  refine ⟨Subtype.val '' (Kf : Set (finU (E := E) (n := a))), hc.image continuous_subtype_val, fun x hx hi => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (integral_iff x).2 hi

theorem exists_loc (w : HeightOneSpectrum (𝓞 E)) : ∃ f : UA E a → UA E a, Continuous f ∧
    ∀ x, f x ∈ locU a w ∧ cLoc w (f x) = cLoc w x := by
  by_cases hw : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
    refine ⟨fun x => (e.symm (cLoc w x)).1, continuous_subtype_val.comp (e.symm.continuous.comp (continuous_cLoc w)),
      fun x => ⟨(e.symm _).2, ?_⟩⟩
    rw [← he]; exact e.apply_symm_apply _
  · have hc : conjSrc (conjE E) w = w := conjSrc_eq_of_not_split hw
    have key : ∀ x : UA E a, finGL E a (locGL E a w (cLoc w x)) ∈ UA E a := by
      intro x
      refine finGL_mem_UA _ fun u => ?_
      by_cases hu : u = w
      · subst hu
        have e1 : ∀ v, v = u → GeneralLinearGroup.map (pLoc E v) (locGL E a u (cLoc u x)) = cLoc v x := by
          rintro v rfl; exact pLoc_locGL _ _
        rw [e1 _ hc, e1 u rfl]
        exact comp_eq x u
      · have h3 : conjSrc (conjE E) u ≠ w := fun e => hu (by rw [← conjSrc_conjSrc_cm u, e, hc])
        rw [pLoc_locGL_of_ne hu, pLoc_locGL_of_ne h3]
        simp
    refine ⟨fun x => ⟨finGL E a (locGL E a w (cLoc w x)), key x⟩, ?_, fun x => ⟨?_, ?_⟩⟩
    · exact Continuous.subtype_mk (continuous_finGL_ad.comp ((CuspSub.continuous_locGL w).comp (continuous_cLoc w))) _
    · refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (pInf_finGL _), Subgroup.mem_iInf.2 fun u =>
        Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
      rw [cLoc_finGL]
      exact pLoc_locGL_of_ne (fun e => hu (by rw [e])) _
    · rw [cLoc_finGL]; exact pLoc_locGL _ _

theorem isClosed_finU : IsClosed ((finU (E := E) (n := a) : Subgroup (UA E a)) : Set (UA E a)) := by
  haveI : T2Space (GL (Fin a) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : Continuous (cInf (E := E) (n := a)) :=
    (Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_ad)).comp continuous_subtype_val
  exact isClosed_eq hc continuous_const

theorem t2GL (w : HeightOneSpectrum (𝓞 E)) : T2Space (GL (Fin a) (w.adicCompletion E)) :=
  Units.isEmbedding_embedProduct.t2Space

theorem isClosed_levelOf (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a))
    (hc : ∀ w, IsCompact (H w : Set (UA E a))) : IsClosed (levelOf a w₀ H : Set (UA E a)) := by
  have e : (levelOf a w₀ H : Set (UA E a)) = (finU (E := E) (n := a) : Set (UA E a)) ∩
      ((⋂ u, ⋂ (_ : ¬ Apart u w₀), {x | cLoc u x = 1}) ∩
        ⋂ w, ⋂ (_ : Apart w w₀), cLoc w ⁻¹' (cLoc w '' (H w : Set (UA E a)))) := by
    ext x
    simp only [SetLike.mem_coe, mem_levelOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_image]
  rw [e]
  refine isClosed_finU.inter (IsClosed.inter (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    (isClosed_iInter fun w => isClosed_iInter fun _ => ?_))
  · haveI := t2GL (E := E) (a := a) u
    exact isClosed_eq (continuous_cLoc u) continuous_const
  · haveI := t2GL (E := E) (a := a) w
    exact ((hc w).image (continuous_cLoc w)).isClosed.preimage (continuous_cLoc w)

theorem exists_compact_of_finset (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) (hle : ∀ w, H w ≤ locU a w)
    (hc : ∀ w, IsCompact (H w : Set (UA E a))) (R : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ C : Set (UA E a), IsCompact C ∧ ∀ x ∈ finU (E := E) (n := a), (∀ u, (∀ r ∈ R, Apart u r) → cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a)) →
      (∀ r ∈ R, ∃ y ∈ H r, cLoc r y = cLoc r x) → x ∈ C := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    obtain ⟨C, hC, hsub⟩ := exists_compact_integral (E := E) (a := a)
    exact ⟨C, hC, fun x hx hi _ => hsub x hx fun u => hi u (by simp)⟩
  | insert r R hr ih =>
    obtain ⟨C, hC, hsub⟩ := ih
    refine ⟨C * (H r : Set (UA E a)), hC.mul (hc r), fun x hx hi hH => ?_⟩
    obtain ⟨y, hy, hyx⟩ := hH r (Finset.mem_insert_self r R)
    by_cases hap : ∀ r' ∈ R, Apart r' r
    · have hyl := hle r hy
      have hy1 : ∀ u, Apart u r → cLoc u y = 1 := fun u hu => ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).2 u hu
      have hyf : y ∈ finU (E := E) (n := a) := (Subgroup.mem_inf.1 hyl).1
      refine ⟨x * y⁻¹, hsub _ (mul_mem hx (inv_mem hyf)) ?_ ?_, y, hy, inv_mul_cancel_right x y⟩
      · intro u hu
        by_cases hur : Apart u r
        · rw [map_mul, map_inv, hy1 u hur, inv_one, mul_one]
          refine hi u fun r' hr' => ?_
          rcases Finset.mem_insert.1 hr' with rfl | h
          · exact hur
          · exact hu r' h
        · have hz : cLoc r (x * y⁻¹) ∈ GlobalTheory.LFun.KGL r (n := a) := by
            rw [map_mul, map_inv, hyx, mul_inv_cancel]; exact one_mem _
          rcases eq_or_eq_conjSrc (not_not.1 hur) with rfl | rfl
          · exact hz
          · exact integral_conjSrc _ r hz
      · intro r' h
        obtain ⟨y', hy', e'⟩ := hH r' (Finset.mem_insert_of_mem h)
        exact ⟨y', hy', by rw [map_mul, map_inv, hy1 r' (hap r' h), inv_one, mul_one]; exact e'⟩
    · push_neg at hap
      obtain ⟨r', hr', hnr⟩ := hap
      have hxC : x ∈ C := by
        refine hsub x hx (fun u hu => hi u fun r'' hr'' => ?_) (fun r'' h => hH r'' (Finset.mem_insert_of_mem h))
        rcases Finset.mem_insert.1 hr'' with rfl | h
        · intro hh
          exact not_apart_trans (not_not.2 hh) (not_apart_symm hnr) (hu r' hr')
        · exact hu r'' h
      exact ⟨x, hxC, 1, one_mem _, mul_one x⟩

theorem isLevelAway_levelOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → IsLevelAway w₀ (GlobalTheory.Cong.AdaptLev.levelOf a w₀ H) := by
  intro E _ _ _ a w₀ H hle _ hc ho hcof
  have hT := Filter.eventually_cofinite.1 hcof
  refine ⟨levelOf_le_finU w₀ H, fun x hx => (mem_levelOf.1 hx).2.1, ?_, ?_⟩
  · obtain ⟨C, hC, hsub⟩ := exists_compact_of_finset H hle hc hT.toFinset
    refine hC.of_isClosed_subset (isClosed_levelOf w₀ H hc) fun x hx => ?_
    obtain ⟨hf, h1, hw⟩ := mem_levelOf.1 hx
    refine hsub x hf (fun u hu => ?_) (fun r _ => ?_)
    · have hHu : H u = intU a u := by
        by_contra h
        exact hu u (hT.mem_toFinset.2 h) rfl
      by_cases h0 : Apart u w₀
      · obtain ⟨y, hy, e⟩ := hw u h0
        rw [hHu] at hy
        rw [← e]
        exact (mem_intU.1 hy).2 u (fun h => h rfl)
      · rw [h1 u h0]; exact one_mem _
    · by_cases h0 : Apart r w₀
      · exact hw r h0
      · exact ⟨1, one_mem _, by rw [map_one, h1 r h0]⟩
  · choose f hfc hf using fun w => exists_loc (E := E) (a := a) w
    let g : ∀ w, UA E a → locU a w := fun w x => ⟨f w x, (hf w x).1⟩
    have hg : ∀ w, Continuous (g w) := fun w => (hfc w).subtype_mk _
    have hpf : Continuous fun x : UA E a => GeneralLinearGroup.map (pFin E) (x : GA E a) :=
      (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
        continuous_subtype_val
    refine ⟨{x | GeneralLinearGroup.map (pFin E) (x : GA E a) ∈ AdelicGLn.integralFiniteGL E a} ∩
      ⋂ w ∈ hT.toFinset, g w ⁻¹' ((H w).subgroupOf (locU a w) : Set (locU a w)), ?_, ?_, ?_⟩
    · exact ((AdelicGLn.isOpen_integralFiniteGL E a).preimage hpf).inter
        (isOpen_biInter_finset fun w _ => (ho w).preimage (hg w))
    · refine ⟨(integral_iff 1).2 fun u => by rw [map_one]; exact one_mem _, Set.mem_iInter₂.2 fun w _ => ?_⟩
      have h1 : f w 1 = 1 := eq_one_of_cLoc_eq_one (hf w 1).1 (by rw [(hf w 1).2, map_one])
      show (g w 1).1 ∈ H w
      show f w 1 ∈ H w
      rw [h1]; exact one_mem _
    · intro x hxN hxf hx1
      obtain ⟨hxi, hxH⟩ := hxN
      have hxi' := (integral_iff x).1 hxi
      refine mem_levelOf.2 ⟨hxf, hx1, fun w _ => ⟨f w x, ?_, (hf w x).2⟩⟩
      by_cases hwT : H w = intU a w
      · rw [hwT]; exact mem_intU_of (hf w x).1 (by rw [(hf w x).2]; exact hxi' w)
      · exact Set.mem_iInter₂.1 hxH w (hT.mem_toFinset.2 hwT)

end GlobalTheory.Cong.LevAway
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

section HostLemmas

variable {R : Ranks} (H : Host R)

theorem sigmaOf_mul (g h : R.GG) : H.sigmaOf (g * h) = H.sigmaOf g * H.sigmaOf h := by
  unfold Host.sigmaOf
  exact map_mul _ g h

theorem sigmaOf_one : H.sigmaOf 1 = 1 := by
  unfold Host.sigmaOf
  exact map_one _

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g := by
  unfold Host.sigmaOf
  exact MulEquiv.apply_symm_apply _ _

theorem sigmaOf_sqrt_neg (g : R.GG) (h : g.1.2 = -1) : H.sigmaOf g H.sqrtMinusD = -H.sqrtMinusD := by
  have := H.galE_bE (H.sigmaOf g)
  rw [galE_sigmaOf, h] at this
  unfold Host.sqrtMinusD
  rw [this]
  simp

theorem sigmaOf_sqrt_pos (g : R.GG) (h : g.1.2 = 1) : H.sigmaOf g H.sqrtMinusD = H.sqrtMinusD := by
  have := H.galE_bE (H.sigmaOf g)
  rw [galE_sigmaOf, h] at this
  unfold Host.sqrtMinusD
  rw [this]
  simp

theorem sqrt_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem emb_sigmaOf (g h : R.GG) (x : H.E) : H.emb g (H.sigmaOf h x) = H.emb (g * h) x := by
  unfold Host.emb
  rw [sigmaOf_mul]
  rfl

end HostLemmas

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Polynomial
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section KurLemmas

variable {p : ℕ} [Fact p.Prime]

theorem mem_Kur_of_pow {x : ℂ_[p]} (n : ℕ) (hn : 0 < n) (hd : ¬ p ∣ n) (hx : x ^ n = 1) : x ∈ MaximalUnramifiedExtension p :=
  Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, hn, hd, hx⟩)

variable {R : Ranks} (H : Host R) (J : H.E →+* ℂ_[p])

end KurLemmas

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section Fixed

variable {R : Ranks} (H : Host R)

def sInv (R : Ranks) : R.GG := ((1, -1), 1)

end Fixed

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.MainNotions.G (plGG)

theorem embT_tauPl (D : D7) (z : Bool × HH D) : TaylorLogMetric.embT D (tauPl D z) = D.host.emb (plGG D z) := by
  unfold TaylorLogMetric.embT tauPl
  rw [Equiv.apply_symm_apply]

theorem eTau_tauPl (D : D7) (z : Bool × HH D) : (D.eTau (tauPl D z) : D.R.GG) = plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem tauSg_tauPl (D : D7) (b : Bool) (t : HH D) : TaylorLogMetric.tauSg D (tauPl D (b, t)) = tauPl D (!b, t) := by
  have hm : plGG D (b, t) * TaylorLogMetric.sgm D = plGG D (!b, t) := by
    cases b <;> refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, TaylorLogMetric.sgm]
  have hmem : (D.eTau (tauPl D (b, t)) : D.R.GG) * TaylorLogMetric.sgm D ∈ D.R.Psi := by
    rw [eTau_tauPl, hm]; exact plGG_mem_Psi D _
  rw [show TaylorLogMetric.tauSg D (tauPl D (b, t)) = D.eTau.symm ⟨_, hmem⟩ from dif_pos hmem]
  refine (Equiv.symm_apply_eq _).2 (Subtype.ext ?_)
  simp only [eTau_tauPl, hm]

theorem inertia_pairs : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p],
    ∃ (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) ∧ δ ^ 2 = -(p : D.host.E) ∧
    cE δ = -δ ∧ s δ = -δ ∧ (∀ y, s (s y) = y) ∧ (∀ y, s (cE y) = cE (s y)) ∧
    Function.Injective (fun z : Bool × HH D => TaylorLogMetric.embT D (tauPl D z)) ∧
    (∀ τ ρ, TaylorLogMetric.embT D τ δ = TaylorLogMetric.embT D ρ δ) ∧
    (∀ (t : HH D) y, TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) ∧
    (∀ τ y, s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) ∧ Function.Bijective (tauPl D) ∧
    ∀ t : HH D, TaylorLogMetric.tauSg D (tauPl D (false, t)) = tauPl D (true, t) ∧
      TaylorLogMetric.tauSg D (tauPl D (true, t)) = tauPl D (false, t) := by
  intro D p _ hp ι
  have hp2 : p ≠ 2 := by rw [hp]; exact D.host.hypOdd.2.2.2.2
  have hpq : D.host.q ≠ p := by rw [hp]; exact D.host.hypOdd.2.2.1
  refine ⟨D.host.conj.toRingEquiv, (D.host.sigmaOf (sInv D.R)).toRingEquiv, D.host.sqrtMinusD, fun y => rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, tauPl_bij D, fun t => ⟨tauSg_tauPl D false t, tauSg_tauPl D true t⟩⟩
  · rw [sqrt_sq, hp]
  · exact sigmaOf_sqrt_neg D.host (D.R.cc) rfl
  · exact sigmaOf_sqrt_neg D.host (sInv D.R) rfl
  · intro y
    change D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (sInv D.R) y) = y
    rw [← AlgEquiv.mul_apply, ← sigmaOf_mul]
    have : sInv D.R * sInv D.R = 1 := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [sInv]
    rw [this, sigmaOf_one]
    rfl
  · intro y
    change D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (D.R.cc) y) = D.host.sigmaOf (D.R.cc) (D.host.sigmaOf (sInv D.R) y)
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← sigmaOf_mul, ← sigmaOf_mul, mul_comm]
  · intro z z' h
    have h' : ∀ x, D.host.φ₀ (D.host.sigmaOf (plGG D z) x) = D.host.φ₀ (D.host.sigmaOf (plGG D z') x) := fun x => by
      have := RingHom.congr_fun h x
      simp only [embT_tauPl] at this
      exact this
    have hs : D.host.sigmaOf (plGG D z) = D.host.sigmaOf (plGG D z') :=
      AlgEquiv.ext fun x => D.host.φ₀.injective (h' x)
    have hg : plGG D z = plGG D z' := by
      unfold Host.sigmaOf at hs
      exact (D.host.gal).symm.injective hs
    apply (tauPl_bij D).1
    unfold tauPl
    congr 1
    exact Subtype.ext hg
  · intro τ ρ
    change D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) D.host.sqrtMinusD) =
      D.host.φ₀ (D.host.sigmaOf (D.eTau ρ : D.R.GG) D.host.sqrtMinusD)
    rw [sigmaOf_sqrt_pos D.host _ (D.eTau τ).2, sigmaOf_sqrt_pos D.host _ (D.eTau ρ).2]
  · intro t y
    change D.host.emb _ y = D.host.emb _ (D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (D.R.cc) y))
    rw [eTau_tauPl, eTau_tauPl, emb_sigmaOf, emb_sigmaOf]
    have hg : plGG D (false, t) * sInv D.R * D.R.cc = plGG D (true, t) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, sInv, Formalism.HC.Frame.cc, c0]
    rw [hg]
  · intro τ y hy
    have hy' : D.host.sigmaOf (sInv D.R) y = y := hy
    exact UpperTheory.Ram.image_mem_of_fixed_iod D.host ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D τ)) (MaximalUnramifiedExtension p)
      (fun z hz => mem_Kur_of_pow _ (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos)
        (by rw [hp]; exact D.host.toHostRaw.d_not_dvd_QSq) hz) y hy'

end GlobalTheory.InertiaPairs
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.operatorOnFrame_and_classSummand_polynomial : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame ∧ Formalism.L2.KerInert.SecondKernelDifference.EntQFrame := by
  first | exact @GlobalTheory.TwV.DelA.applyFrame_and_entQFrame | exact GlobalTheory.TwV.DelA.applyFrame_and_entQFrame | (intros; apply GlobalTheory.TwV.DelA.applyFrame_and_entQFrame <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.L2.KerInert.RepComb Formalism.L2.Th1.H

namespace GlobalTheory

theorem kerTh_entire_algCoef : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (S : Finset ℕ), TaylorLogMetric.admitted D a b N N' → SNum S cl → (∀ x, IntOff S (Ξ x)) → Differentiable ℂ (kerTh B χ SS cl N N' Ξ) ∧ TaylorLogMetric.CoefIn D (kerTh B χ SS cl N N' Ξ) TaylorLogMetric.Qbar := by
  intro D cc δ B χ hcc hδ hχ a b SS cl N N' Ξ S hA hS hΞ
  have hL := lattice_integral_of_facts D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' (laFacts_of_adm B hcc hδ hA)
  have hLFG := period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' hA.2.2.2.1
    hA.2.2.1.2.1 (aaOf_fg cc)
  obtain ⟨hi1, hi2, hi3⟩ := finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N'
    cl hS.1 hLFG
  obtain ⟨n, r, t, hr, ht, hΘ⟩ := theta_coset_kernel D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl S Ξ (B.eNat χ a b N N') hL hi1 hi2 hi3 hS hΞ
  have hfun : kerTh B χ SS cl N N' Ξ =
      fun z => ∑ k, r k * TaylorLogMetric.U D B.tor (t k) (B.eNat χ a b N N') z := by
    funext z
    simp only [Formalism.L2.KerInert.RepComb.U_eq_opU]
    exact congrFun hΘ z
  rw [hfun]
  refine entire_algCoef_comb D r _ (fun k => (hr k).1) fun k => ?_
  obtain ⟨m, hm, hmt⟩ := ht k
  exact TwV.translate_entire_algebraic D cc δ B χ hcc hδ hχ a b N N' hA (t k) ⟨m, hm.1, lambda_in_lattice_pair cc δ N N' hmt⟩

end GlobalTheory
end
end
