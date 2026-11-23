module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle135
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle152
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle242
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle241
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QuadSignLocal

theorem primesOver_eq_image (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Ideal.primesOver v.asIdeal (𝓞 D.host.E) =
      HeightOneSpectrum.asIdeal '' {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} := by
  ext P
  constructor
  · rintro ⟨hP, hlo⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ?_, rfl⟩
    ext1
    simp only [HeightOneSpectrum.under_asIdeal]
    exact (Ideal.LiesOver.over (P := P) (p := v.asIdeal)).symm
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.isPrime, ⟨?_⟩⟩
    have := congrArg HeightOneSpectrum.asIdeal hu
    simp only [HeightOneSpectrum.under_asIdeal] at this
    exact this.symm

theorem ncard_primesOver (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard =
      {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v}.ncard := by
  rw [primesOver_eq_image]
  exact Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)

theorem quadSign_split_inert : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → quadSign D v = 1) ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.E), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → quadSign D v = -1) := by
  intro D v
  constructor
  · intro w w' hne h
    have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} = {w, w'} := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]; exact h u
    have h2 : (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 2 := by
      rw [ncard_primesOver, hs, Set.ncard_pair hne]
    unfold quadSign
    rw [if_pos h2]
  · intro w h
    have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} = {w} := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]; exact h u
    have h1 : (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 1 := by
      rw [ncard_primesOver, hs, Set.ncard_singleton]
    unfold quadSign
    rw [if_neg (by rw [h1]; decide)]

end GlobalTheory.QuadSignLocal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)



noncomputable section

namespace GlobalTheory.LevelInLatStab

theorem mulVec_mem_of_integral {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A ≃+* B) (S : Subring B)
    (β : GL (Fin n) B) {P : AddSubgroup (Fin n → A)}
    (hP : ∀ z, z ∈ P ↔ ∀ i, ((β⁻¹).val *ᵥ fun i => e (z i)) i ∈ S) (m : Matrix (Fin n) (Fin n) A)
    (T : Matrix (Fin n) (Fin n) S) (hm : m.map e = β.val * T.map S.subtype * (β⁻¹).val) :
    ∀ z ∈ P, m *ᵥ z ∈ P := by
  intro z hz
  rw [hP] at hz ⊢
  intro i
  rw [GlobalTheory.LevelActionPinned.equiv_mulVec, hm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (T i j).2 (hz j)

theorem lev_le_latLev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → Formalism.L2.DIV.lev D.sp.cm V.gram β L ≤ GlobalTheory.Mass.Levels.latLev V := by
  intro D V β Λ L hβ x hx
  have hp := Formalism.L2.DIV.lev_le_parLev hx
  have hUA := Formalism.L2.DIV.parLev_UA hp
  have hSt := Formalism.L2.DIV.parLev_St hp
  have hSD : Formalism.IndefR.Links.IsSDFrame V β Λ 1 := ⟨0, by rwa [pow_zero]⟩
  have hP : ∀ z, z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D (z i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
    intro z
    rw [← GlobalTheory.StdFrameCong.pj_latHat_eq]
    exact GlobalTheory.LevelActionPinned.mem_latHat_iff hSD z
  obtain ⟨t', ht'⟩ := (Formalism.L2.DIV.St β).inv_mem hSt
  obtain ⟨t, ht⟩ := hSt
  let u : UA D.sp.cm V.gram := ⟨x, hUA⟩
  let g := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).symm u
  have hg : ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D)) = x := by
    simp only [g, MulEquiv.apply_symm_apply, u]
  have hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val := by
    have h1 := congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)
    rw [← hg]
    exact h1.symm
  refine ⟨GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g, ⟨g, ?_, rfl⟩, hg⟩
  refine (GlobalTheory.Mass.Levels.mem_latStab V g).2 fun y => ?_
  constructor
  · intro hy
    exact mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP _ t.val
      (by rw [hmat, ← ht]; rfl) y hy
  · intro hy
    let m' := (x⁻¹).val.map (GlobalTheory.LevelActionPinned.sw D).symm
    have hm' : m'.map (GlobalTheory.LevelActionPinned.sw D) = (x⁻¹).val := by
      ext i j; simp only [m', Matrix.map_apply, RingEquiv.apply_symm_apply]
    have hinv : m' * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 = 1 := by
      apply Matrix.map_injective (GlobalTheory.LevelActionPinned.sw D).injective
      have e := Matrix.map_mul (f := (GlobalTheory.LevelActionPinned.sw D).toRingHom) (L := m')
        (M := (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1)
      have e1 := Matrix.map_one (GlobalTheory.LevelActionPinned.sw D) (map_zero _) (map_one _) (n := Fin V.rank)
      refine (e.trans ?_).trans e1.symm
      change m'.map (GlobalTheory.LevelActionPinned.sw D) * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = 1
      rw [hm', hmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP m' t'.val
      (by rw [hm', ← ht']; rfl) _ hy
    rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2

end GlobalTheory.LevelInLatStab
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.LevelVecNorm.NormFac

variable {E : Type} [Field E] [NumberField E]

instance finKP (PP : Pl E) : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot

theorem norm_char_fin {G : Type} [Group G] [Finite G] (f : G →* ℂˣ) (g : G) : ‖((f g : ℂˣ) : ℂ)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card G) ?_ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

theorem mem_blockTri_blkOf {κ : Type} [CommRing κ] {r t : ℕ} (g : GL (Fin r) κ) : g ∈ blockTri (blkOf r t) := by
  rw [mem_blockTri]
  intro i j h
  simp [blkOf, i.2, j.2] at h

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {r : ℕ} (hr : r ≤ r) (g : GL (Fin r) κ) : upperLeftBlock hr g = g := by
  have hm : g ∈ blockTri (blk2 r) := by
    rw [mem_blockTri]
    intro i j h
    simp [blk2, i.2, j.2] at h
  ext i j
  rw [upper_block_val_submatrix hr hm]
  rfl

theorem exists_GL_iff {κ : Type} [CommRing κ] {r : ℕ} (M : Matrix (Fin r) (Fin r) κ) :
    (∃ g : GL (Fin r) κ, (g : Matrix (Fin r) (Fin r) κ) = M) ↔ IsUnit M.det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨g, hg⟩⟩

theorem locH_of_mem (Pg : Finset (Pl E)) {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) {PP : Pl E}
    (h : PP ∈ Pg) : locH Pg Hl PP = Hl ⟨PP, h⟩ := dif_pos h

theorem locH_of_not (Pg : Finset (Pl E)) {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) {PP : Pl E}
    (h : PP ∉ Pg) : locH Pg Hl PP = ⊤ := dif_neg h

theorem norm_omegaQ {D : D7} {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    ‖omegaQ Q r ξ k y‖ = if ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then 1 else 0 := by
  unfold omegaQ
  split
  · rename_i h
    simp only [norm_prod, norm_zpow, norm_char_fin, _root_.one_zpow, Finset.prod_const_one]
  · rename_i h
    rw [norm_zero]

theorem norm_omegaG {D : D7} {b r t : ℕ} (hr : r ≤ r) (Pg : Finset (Pl D.host.E))
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* ℂˣ)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin r) (kP PP)) :
    ‖omegaG (Lev.datY r r t 0 hr Pg ∅ (LevelP.ofLocal Hl cl) χ ξ Lev.Frm.B) m y‖ =
      if ∀ PP (h : PP ∈ Pg), LowZero r (y PP) ∧
          ∃ g ∈ Hl ⟨PP, h⟩, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP) then 1 else 0 := by
  by_cases hc : ∀ PP (h : PP ∈ Pg), LowZero r (y PP) ∧
      ∃ g ∈ Hl ⟨PP, h⟩, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP)
  · rw [if_pos hc]
    unfold omegaG
    split
    · simp only [norm_mul, norm_prod, norm_inv, norm_char_fin, Finset.prod_const_one, inv_one, mul_one]
    · rename_i h
      exfalso
      apply h
      refine ⟨fun PP hP => (hc PP hP).1, fun PP => (hc PP.1 PP.2).2.choose,
        fun PP => (hc PP.1 PP.2).2.choose_spec.2, fun PP => mem_blockTri_blkOf _, ?_⟩
      show (fun PP : ↥Pg => upperLeftBlock hr ((hc PP.1 PP.2).2.choose)) ∈ Subgroup.pi Set.univ Hl
      intro PP _
      simp only [restrictedBlock_self_apply]
      exact (hc PP.1 PP.2).2.choose_spec.1
  · rw [if_neg hc]
    unfold omegaG
    split
    · rename_i h
      exfalso
      obtain ⟨hlow, g, hg1, -, hg3⟩ := h
      apply hc
      intro PP hP
      have h3 : (fun PP : ↥Pg => upperLeftBlock hr (g PP)) ∈ Subgroup.pi Set.univ Hl := hg3
      have h4 := h3 ⟨PP, hP⟩ (Set.mem_univ _)
      simp only [restrictedBlock_self_apply] at h4
      exact ⟨hlow PP hP, g ⟨PP, hP⟩, h4, hg1 ⟨PP, hP⟩⟩
    · rw [norm_zero]

theorem norm_omegaG_mul_omegaQ {D : D7} {b a r t : ℕ} (hr : r ≤ a) (har : a = r) (Pg Q : Finset (Pl D.host.E))
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* ℂˣ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    ‖omegaG (Lev.datY a r t 0 hr Pg ∅ (LevelP.ofLocal Hl cl) (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) m y *
        omegaQ Q a m (-1) y‖ = ∏ PP ∈ Pg ∪ Q, suppInd r (locH Pg Hl PP) (y PP) := by
  subst a
  rw [norm_mul, norm_omegaG, norm_omegaQ, ite_zero_mul_ite_zero, mul_one]
  unfold suppInd
  rw [Finset.prod_ite_zero, Finset.prod_const_one]
  by_cases hc : ∀ PP ∈ Pg ∪ Q, LowZero r (y PP) ∧
      ∃ g ∈ locH Pg Hl PP, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP)
  · rw [if_pos hc, if_pos]
    refine ⟨fun PP hP => ?_, fun PP hP => ?_⟩
    · have h1 := hc PP (Finset.mem_union_left _ hP)
      rwa [locH_of_mem Pg Hl hP] at h1
    · have h1 := hc PP (Finset.mem_union_right _ hP)
      refine ⟨h1.1, ?_⟩
      obtain ⟨g, -, hg⟩ := h1.2
      exact (exists_GL_iff _).1 ⟨g, hg⟩
  · rw [if_neg hc, if_neg]
    rintro ⟨hA, hB⟩
    apply hc
    intro PP hP
    by_cases hg : PP ∈ Pg
    · rw [locH_of_mem Pg Hl hg]
      exact hA PP hg
    · rw [locH_of_not Pg Hl hg]
      have hq : PP ∈ Q := (Finset.mem_union.1 hP).resolve_left hg
      obtain ⟨g, hg'⟩ := (exists_GL_iff _).2 (hB PP hq).2
      exact ⟨(hB PP hq).1, g, Subgroup.mem_top _, hg'⟩

end GlobalTheory.LevelVecNorm.NormFac

namespace GlobalTheory.LevelVecNorm

theorem normFac : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)),
  ‖omegaG (R.datWp i (LevelP.ofLocal Hl cl)) m y * omegaQ (R.Q t) (Wc D i).rank m (-1) y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, GlobalTheory.LevelVecNorm.suppInd D.R.r (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP) (y PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t Hl cl m y
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  exact NormFac.norm_omegaG_mul_omegaQ (le_of_eq hW.symm) hW R.Pg (R.Q t) Hl cl m y

end GlobalTheory.LevelVecNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeInt

section Frame

open Formalism.L2.SG.InstExistsPf

def frP (D : D7) (τ : D.what₂.Tau) : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
  (instOf D).P (Formalism.L2.Host.tauPl D τ)

theorem frP_unit (D : D7) (τ : D.what₂.Tau) : IsUnit (frP D τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp ((instOf D).P_unit _)

theorem fr_gram (D : D7) (τ : D.what₂.Tau) :
    ((frP D τ)⁻¹)ᴴ * Formalism.REAL.Jm (epsV D) * (frP D τ)⁻¹ = gramAt D (D.sp.Y 0) τ := by
  have h : (frP D τ)ᴴ * gramAt D (D.sp.Y 0) τ * frP D τ = Formalism.REAL.Jm (epsV D) := by
    have h0 := (instOf D).P_spec (Formalism.L2.Host.tauPl D τ)
    have hJ : (instOf D).J.map ((instOf D).φ (Formalism.L2.Host.tauPl D τ)) = gramAt D (D.sp.Y 0) τ := by
      show (Jv D).map (embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D τ))) = _
      rw [Equiv.symm_apply_apply]; rfl
    rw [hJ] at h0
    exact h0
  rw [← h]
  have h1 := Matrix.mul_nonsing_inv (frP D τ) (frP_unit D τ)
  have h2 : ((frP D τ)⁻¹)ᴴ * (frP D τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  rw [Matrix.mul_assoc, Matrix.mul_assoc _ (frP D τ), h1, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem exists_conj_intertwiner (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) (hmult : GlobalTheory.Dec.LowKMultOne)
    (hstrict : GlobalTheory.DSId.StrictLow) {D : D7} (I : AutInst) (hI : I = instOf D)
    (pl : InfinitePlace I.F ≃ D.what₂.Tau) (n_eq : I.n = D.R.r)
    (eps_eq : ∀ v (i : Fin I.n), I.ε v i = epsS D.R (Fin.cast n_eq i))
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (lam_eq : ∀ v (i : Fin I.n), lam v i = lamS D.R (D.hc (pl v)) (Fin.cast n_eq i))
    (ds : ∀ v, IsDS (I.ε v) (lam v) (σ v)) (low : ∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v))
    (N : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) :
    ∃ c : ∀ τ, N.H τ ≃ₗᵢ⋆[ℂ] H (pl.symm τ),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ m : Matrix (Fin I.n) (Fin I.n) ℂ,
        HEq m ((frP D τ)⁻¹ * g * frP D τ) → ∀ x, c τ (N.rep τ g x) = σ (pl.symm τ) m (c τ x)) ∧
      ∀ τ, (c τ).symm (w (pl.symm τ)) ∈ N.sm τ := by
  subst hI
  let M0 : DSModel (D.sp.Y 0) (parA (tparRec D) 0) :=
    { H := fun τ => H (pl.symm τ)
      σ := fun τ => σ (pl.symm τ)
      lam := fun τ => lam (pl.symm τ)
      ε := fun τ => (instOf D).ε (pl.symm τ)
      fr := fun τ => (frP D τ)⁻¹
      enum := fun τ => by
        have e1 : lam (pl.symm τ) = fun i => lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by rw [lam_eq, Equiv.apply_symm_apply]
        have e2 : (instOf D).ε (pl.symm τ) = fun i => epsS D.R (Fin.cast n_eq i) := funext fun i => eps_eq _ i
        rw [e1, e2]
        exact GlobalTheory.RowLev.isEnum_parA_zero D n_eq τ
      ds := fun τ => ds _
      fr_unit := fun τ => Matrix.isUnit_nonsing_inv_iff.mpr ((instOf D).P_unit _)
      fr_gram := fun τ => fr_gram D τ }
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M0
  obtain ⟨U, hUi⟩ := hU.exists_intertwiner (M := (M' : DSModel (D.sp.Y 0) (parB (tparRec D) 0))) (M' := N)
  have key : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ x,
      c τ (U τ (N.rep τ g x)) = M0.rep τ g (c τ (U τ x)) := by
    intro τ g hg x
    exact (congrArg (c τ) (hUi τ g hg x)).trans (hc τ g hg _)
  refine ⟨fun τ => (U τ).trans (c τ), ?_, ?_⟩
  · intro τ g hg m hm x
    have hm' : m = (frP D τ)⁻¹ * g * frP D τ := eq_of_heq hm
    show c τ (U τ (N.rep τ g x)) = σ (pl.symm τ) m (c τ (U τ x))
    rw [key τ g hg x, hm']
    show σ (pl.symm τ) ((frP D τ)⁻¹ * g * ((frP D τ)⁻¹)⁻¹) _ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ (frP_unit D τ)]
  · intro τ
    have hw : w (pl.symm τ) ∈ M0.sm τ := by
      obtain ⟨S, hS, hSle⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D _ _ M0 τ
      have hHC := GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M0.enum τ).1 (M0.ds τ)
      have : CompleteSpace (H (pl.symm τ)) := (ds _).1
      have h1 := (hstrict _ _ _ hHC (H (pl.symm τ)) (σ (pl.symm τ)) (ds _)).1
      have h2 := hmult _ _ _ _ (σ (pl.symm τ)) hHC (ds _) _ _ h1 hS
      exact hSle (h2 ▸ (low _).2)
    set e := (U τ).trans (c τ) with he
    have hint : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ y,
        e.symm (M0.rep τ g y) = N.rep τ g (e.symm y) := by
      intro g hg y
      apply e.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      have := key τ g hg (e.symm y)
      change e (N.rep τ g (e.symm y)) = M0.rep τ g (e (e.symm y)) at this
      rw [this, LinearIsometryEquiv.apply_symm_apply]
    exact GlobalTheory.ConjMult.span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit _ τ) e.symm hint hw

end Frame

theorem conjModel_of_setting : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  intro hcl D G _ _ Pl0 T A Ks _ _ _ R F X h hlev hgrp hmod _hhost hιE
  obtain ⟨-, hreal, -⟩ := GlobalTheory.T.adelicIdentification_respects_real_finite R F X h hlev hgrp hmod hιE
  obtain ⟨-, -, -, -, hmult, -, hstrict⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hcl
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_of_classification hcl
  obtain ⟨c, hc1, hc2⟩ := exists_conj_intertwiner hU hmult hstrict X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ X.B.w
    X.B.lam X.lam_eq X.ds X.low (MP R)
  exact ⟨c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x, hc2⟩

end GlobalTheory.SeeInt
end
end

section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_kEquivariant_graph_goursat : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S S' U : Submodule ℂ H), Formalism.MainNotions.S.IsKStableOn ε ρ S → Formalism.MainNotions.S.IsKStableOn ε ρ S' → Formalism.MainNotions.S.IsKStableOn ε ρ U → (∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S) → (∀ T : Submodule ℂ H, T ≤ S' → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S') → S ⊓ S' = ⊥ → U ≤ S ⊔ S' → U ⊓ S = ⊥ → U ⊓ S' = ⊥ → U ≠ ⊥ → ∃ φ : H →ₗ[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u ∈ S, φ (ρ k u) = ρ k (φ u)) ∧ S.map φ = S' := by
  first | exact @GlobalTheory.KStableGraph.exists_kMap_onto | exact GlobalTheory.KStableGraph.exists_kMap_onto | (intros; apply GlobalTheory.KStableGraph.exists_kMap_onto <;> assumption)
end

section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.finite_torusWeights_finiteDimensional_subspace : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), FiniteDimensional ℂ S → ∃ F : Finset (Fin n → ℝ), ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v → μ ∈ F := by
  first | exact @GlobalTheory.TorusWtFin.finite_weights | exact GlobalTheory.TorusWtFin.finite_weights | (intros; apply GlobalTheory.TorusWtFin.finite_weights <;> assumption)
end

section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.maxCompactSpan_highestWeight_line : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → (∀ v, ContinuousOn (fun g => ρ g v) (Formalism.MainNotions.S.UJset ε)) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε ρ S → ∀ (Λ : Fin n → ℝ) (w : H), w ∈ S → w ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ w → (∀ a b : Fin n, a < b → ε a = ε b → ∀ x ∈ S, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ (Λ + Formalism.REAL.root a b) x → x = 0) → (∀ (μ : Fin n → ℝ) (x : H), x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε) → x ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ x → Formalism.MainNotions.S.CDom ε μ Λ) ∧ (∀ x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ x → ∃ c : ℂ, x = c • w) := by
  first | exact @GlobalTheory.KSpanHighest.kspan_highest | exact GlobalTheory.KSpanHighest.kspan_highest | (intros; apply GlobalTheory.KSpanHighest.kspan_highest <;> assumption)
end
