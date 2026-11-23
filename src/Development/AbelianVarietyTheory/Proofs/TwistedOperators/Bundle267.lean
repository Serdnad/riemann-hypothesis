module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle135
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle253
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtremalVectorValuesLoweringAndTorus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle251

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


theorem _root_.GlobalTheory.T.conj_localTwistedLFactor_ratio_split_eq_zetaSum : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → (B w).map star = (B w).map (·⁻¹) → m w * m w' = 1 → ‖(m w : ℂ)‖ = 1 → quadSign D v = 1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac ((B w).map (star (m w) * ·)) (npow w (-((1 + (D.R.t : ℂ)) / 2))) * eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) (npow w (-((1 + (D.R.t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹) := by
  first | exact @GlobalTheory.LocZetaSplit.conj_LvTw_div_dLoc | exact GlobalTheory.LocZetaSplit.conj_LvTw_div_dLoc | (intros; apply GlobalTheory.LocZetaSplit.conj_LvTw_div_dLoc <;> assumption)
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

namespace GlobalTheory.LatLevEq

theorem conj_apply_mem {B : Type} [CommRing B] {n : ℕ} (S : Subring B) (β : GL (Fin n) B)
    (X : Matrix (Fin n) (Fin n) B)
    (hX : ∀ w : Fin n → B, (∀ i, ((β⁻¹).val *ᵥ w) i ∈ S) → ∀ i, ((β⁻¹).val *ᵥ (X *ᵥ w)) i ∈ S) :
    ∀ i j, ((β⁻¹).val * X * β.val) i j ∈ S := by
  intro i j
  have hw : ∀ k, ((β⁻¹).val *ᵥ (β.val *ᵥ Pi.single j 1)) k ∈ S := by
    intro k
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  have := hX _ hw i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
  exact this

theorem exists_integral_conj {B : Type} [CommRing B] {n : ℕ} (S : Subring B) (β x : GL (Fin n) B)
    (h1 : ∀ i j, ((β⁻¹).val * x.val * β.val) i j ∈ S) (h2 : ∀ i j, ((β⁻¹).val * (x⁻¹).val * β.val) i j ∈ S) :
    ∃ y : GL (Fin n) S, β.val * y.val.map S.subtype * (β⁻¹).val = x.val := by
  let M : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let M' : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hM : M.map S.subtype = (β⁻¹).val * x.val * β.val := by ext i j; rfl
  have hM' : M'.map S.subtype = (β⁻¹).val * (x⁻¹).val * β.val := by ext i j; rfl
  have key : ∀ (P Q : Matrix (Fin n) (Fin n) S), P.map S.subtype * Q.map S.subtype = 1 → P * Q = 1 := by
    intro P Q h
    apply Matrix.map_injective Subtype.val_injective
    have e := Matrix.map_mul (f := S.subtype) (L := P) (M := Q)
    have e1 := Matrix.map_one S.subtype (map_zero _) (map_one _) (n := Fin n)
    exact e.trans (h.trans e1.symm)
  have hu : ∀ a b : GL (Fin n) B, a * b = 1 → ((β⁻¹).val * a.val * β.val) * ((β⁻¹).val * b.val * β.val) = 1 := by
    intro a b hab
    have : β⁻¹ * a * β * (β⁻¹ * b * β) = 1 := by
      calc β⁻¹ * a * β * (β⁻¹ * b * β) = β⁻¹ * (a * b) * β := by group
        _ = 1 := by rw [hab]; group
    simpa only [Units.val_mul, Units.val_one] using congrArg Units.val this
  refine ⟨⟨M, M', key M M' ?_, key M' M ?_⟩, ?_⟩
  · rw [hM, hM']; exact hu x x⁻¹ (mul_inv_cancel x)
  · rw [hM, hM']; exact hu x⁻¹ x (inv_mul_cancel x)
  · show β.val * M.map S.subtype * (β⁻¹).val = x.val
    rw [hM]
    have : β * (β⁻¹ * x * β) * β⁻¹ = x := by group
    simpa only [Units.val_mul] using congrArg Units.val this

end GlobalTheory.LatLevEq

namespace GlobalTheory.LatLevEq

theorem latLev_eq_UA_inf_St : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → GlobalTheory.Mass.Levels.latLev V = Formalism.L2.DIV.UA D.sp.cm V.gram ⊓ Formalism.L2.DIV.St β := by
  intro D V β Λ hβ
  have hSD : Formalism.IndefR.Links.IsSDFrame V β Λ 1 := ⟨0, by rwa [pow_zero]⟩
  have hP : ∀ z, z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D (z i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
    intro z
    rw [← GlobalTheory.StdFrameCong.pj_latHat_eq]
    exact GlobalTheory.LevelActionPinned.mem_latHat_iff hSD z
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hu
    refine ⟨(GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).2, ?_⟩
    set x : GL (Fin V.rank) (Lev.EAf D) :=
      ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) :
        GL (Fin V.rank) (Lev.EAf D)) with hxdef
    have hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val := by
      have h1 := congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)
      exact h1.symm
    have hst := (GlobalTheory.Mass.Levels.mem_latStab V g).1 hg
    have tr : ∀ w : Fin V.rank → Lev.EAf D,
        (fun i => GlobalTheory.LevelActionPinned.sw D
          (((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ
            fun i => (GlobalTheory.LevelActionPinned.sw D).symm (w i)) i)) = x.val *ᵥ w := by
      intro w
      rw [GlobalTheory.LevelActionPinned.equiv_mulVec, hmat]
      simp only [RingEquiv.apply_symm_apply]
    have hz : ∀ w : Fin V.rank → Lev.EAf D,
        (fun i => GlobalTheory.LevelActionPinned.sw D ((GlobalTheory.LevelActionPinned.sw D).symm (w i))) = w := by
      intro w; funext i; simp only [RingEquiv.apply_symm_apply]
    have h1 := conj_apply_mem (GlobalTheory.LevelActionPinned.SI D) β x.val fun w hw => by
      have hzm := (hP _).2 (by rw [hz]; exact hw)
      have := (hP _).1 ((hst _).1 hzm)
      rwa [tr] at this
    have h2 := conj_apply_mem (GlobalTheory.LevelActionPinned.SI D) β (x⁻¹).val fun w hw => by
      have hw' : ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D
          (((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ
            fun i => (GlobalTheory.LevelActionPinned.sw D).symm (((x⁻¹).val *ᵥ w) i)) i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
        rw [tr, show x.val *ᵥ ((x⁻¹).val *ᵥ w) = w by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]]
        exact hw
      have := (hP _).1 ((hst _).2 ((hP _).2 hw'))
      rwa [hz] at this
    obtain ⟨y, hy⟩ := exists_integral_conj (GlobalTheory.LevelActionPinned.SI D) β x h1 h2
    exact ⟨y, Units.ext hy⟩
  · rintro x ⟨hUA, hSt⟩
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
      exact GlobalTheory.LevelInLatStab.mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP _ t.val
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
      have h2 := GlobalTheory.LevelInLatStab.mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP m' t'.val
        (by rw [hm', ← ht']; rfl) _ hy
      rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2

end GlobalTheory.LatLevEq
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


theorem _root_.GlobalTheory.T.level_le_stabilizer_selfDual_lattice_frame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → Formalism.L2.DIV.lev D.sp.cm V.gram β L ≤ GlobalTheory.Mass.Levels.latLev V := by
  first | exact @GlobalTheory.LevelInLatStab.lev_le_latLev | exact GlobalTheory.LevelInLatStab.lev_le_latLev | (intros; apply GlobalTheory.LevelInLatStab.lev_le_latLev <;> assumption)
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


theorem _root_.GlobalTheory.T.norm_finiteThetaDatum_eq_indicator_product : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)),
  ‖omegaG (R.datWp i (LevelP.ofLocal Hl cl)) m y * omegaQ (R.Q t) (Wc D i).rank m (-1) y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, GlobalTheory.LevelVecNorm.suppInd D.R.r (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP) (y PP) := by
  first | exact @GlobalTheory.LevelVecNorm.normFac | exact GlobalTheory.LevelVecNorm.normFac | (intros; apply GlobalTheory.LevelVecNorm.normFac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.FockVac

variable {D : D7}

theorem continuous_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Continuous (reW S T b) := by
  unfold reW
  exact Continuous.matrix_mul continuous_id continuous_const

theorem compAt_frPinv {θ : InfFam D} (hθ : IsInfFam θ) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) : compAt θ τ ((frPinv S b).map (incA D)) = (frPinv S b).map (tauE D τ) := by
  unfold compAt
  rw [Matrix.map_map]
  congr 1
  funext e
  exact GlobalTheory.FockCompare.comp_incA hθ τ e

theorem lineAt_reW {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    reW S T b (lineAt θ τ z t) = lineAt θ τ (z * (frPinv S b).map (tauE D τ)) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let R : WO (reS S b) T →+ WO S T := AddMonoidHom.mk' (reW S T b) (fun x y => Matrix.add_mul x y _)
  let L : ℝ →+ WO S T := R.comp (lineAt θ τ z)
  have hL' : IsLineAt θ τ (z * (frPinv S b).map (tauE D τ)) L := by
    refine ⟨(continuous_reW S T b).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (reW S T b (lineAt θ τ z t)).map (finPart D) = 0
      unfold reW
      rw [Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' (reW S T b (lineAt θ τ z t)) = _
      unfold reW
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2, compAt_frPinv hθ]
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

theorem lineAt_reW' {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin (reS S b).rank) ℂ) (t : ℝ) :
    reW S T b (lineAt θ τ z t) =
      lineAt θ τ (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) z ((frPinv S b).map (tauE D τ))) t :=
  lineAt_reW hθ S T b τ z t

theorem dRho_reF (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D)
    (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (hs : ∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin (reS S b).rank) ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ (reS S b) T) θ τ z (reF S T b f) =
      reF S T b (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ
        (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) z ((frPinv S b).map (tauE D τ))) f) := by
  funext x
  rw [reF_apply]
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [← lineAt_reW' hθ]
  have hadd (u v : WO (reS S b) T) : reW S T b (u + v) = reW S T b u + reW S T b v :=
    Matrix.add_mul _ _ _
  simp only [heisO, reF_apply, symplOH, hs, hadd]

theorem isFockVacAt_reF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (b : Module.Basis (Fin S.rank) D.host.E S.V), IsInfFam θ →
    (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) →
    ∀ (τ : D.what₂.Tau) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
      IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 sT) f → IsFockVacAt (heisO ψ (reS S b) T) θ τ (cplxO 1 sT) (reF S T b f) := by
  intro D ψ θ S T b hθ hs τ sT f hf z
  let P' : Matrix (Fin S.rank) (Fin S.rank) ℂ := (frPinv S b).map (tauE D τ)
  let z' : Matrix (Fin T.rank) (Fin S.rank) ℂ := z
  have hJ : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) (cplxO 1 sT z) P' = cplxO 1 sT (z' * P') := by
    show Complex.I • (sT * z' * 1) * P' = Complex.I • (sT * (z' * P') * 1)
    rw [Matrix.mul_one, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
  funext x
  have h0 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z' * P') f (reW S T b x) +
      Complex.I • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO 1 sT (z' * P')) f (reW S T b x) = 0 :=
    congrFun (hf (z' * P')) (reW S T b x)
  rw [← hJ] at h0
  have e1 := congrFun (dRho_reF ψ hθ S T b hs τ z f) x
  have e2 := congrFun (dRho_reF ψ hθ S T b hs τ (cplxO 1 sT z) f) x
  refine (congrArg₂ (fun a c : ℂ => a + Complex.I • c) e1 e2).trans ?_
  exact h0

end GlobalTheory.AdSpan.ReVec.FockVac

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

variable {D : D7} {S T : HSp D}

def torProd (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (s : D.what₂.Tau → Fin V.rank → ℝ) : GA D V :=
  (Finset.univ.toList.map fun ρ => torAt θ V B ρ (s ρ)).prod

def conjL {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} : Frame Ψ r →ₗ[ℝ] Frame Ψ r where
  toFun Z := fun τ a b => conj (Z τ a b)
  map_add' Z Z' := funext fun τ => funext fun a => funext fun b => map_add (starRingEnd ℂ) _ _
  map_smul' c Z := funext fun τ => funext fun a => funext fun b => by
    change conj ((c : ℂ) * Z τ a b) = (c : ℂ) * conj (Z τ a b)
    rw [map_mul, Complex.conj_ofReal]

theorem mat_conjL {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) (τ : Ψ) :
    mat (conjL Z) τ = (mat Z τ).map (starRingEnd ℂ) := rfl

def toLieC (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas) :
    Frame C.X.Ψ T.rank →ₗ[ℝ] GlobalTheory.SmoothForms.LieN T :=
  (GlobalTheory.HolRead.AdExt.toLie R B (fun ρ => C.m.e ρ)).comp conjL

theorem isUnit_det_B (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau) : IsUnit (B ρ).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have := congrArg det (hB ρ)
  rw [det_mul, det_mul, h0, mul_zero, sgnM, det_diagonal] at this
  refine Finset.prod_ne_zero_iff.2 (fun c _ => ?_) this.symm
  unfold sgn
  split_ifs <;> norm_num

theorem exp_map_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp A).map (starRingEnd ℂ) = NormedSpace.exp (A.map (starRingEnd ℂ)) := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = Mᴴᵀ := fun M => by
    ext i j
    simp [conjTranspose_apply]
  rw [h, h, Matrix.exp_transpose, Matrix.exp_conjTranspose]

def trLin (V : HSp D) (m : D.what₂.Tau → ℤ) : GlobalTheory.SmoothForms.LieN V →ₗ[ℝ] ℂ where
  toFun Y := ∑ ρ, (m ρ : ℂ) * trace (Y ρ).1
  map_add' Y Y' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    change (m ρ : ℂ) * trace ((Y ρ).1 + (Y' ρ).1) = _
    rw [trace_add, mul_add]
  map_smul' c Y := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    change (m ρ : ℂ) * trace (c • (Y ρ).1) = c • ((m ρ : ℂ) * trace (Y ρ).1)
    rw [trace_smul, mul_smul_comm]

def trCL (V : HSp D) (m : D.what₂.Tau → ℤ) : GlobalTheory.SmoothForms.LieN V →L[ℝ] ℂ where
  toLinearMap := trLin V m
  cont := continuous_finsetSum _ fun ρ _ =>
    continuous_const.mul ((continuous_subtype_val.comp (continuous_apply ρ)).matrix_trace)

theorem trCL_apply (V : HSp D) (m : D.what₂.Tau → ℤ) (Y : GlobalTheory.SmoothForms.LieN V) : trCL V m Y = trLin V m Y := rfl

end GlobalTheory.AdSpan.ConjHol

namespace GlobalTheory.AdSpan.ConjHol

variable {D : D7} {S T : HSp D}

theorem apply_mul_torProd (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Fin V.rank → ℤ) (ψ : GA D V → ℂ)
    (h : ∀ (ρ : D.what₂.Tau) (t : Fin V.rank → ℝ) (g : GA D V),
      ψ (g * torAt θ V B ρ t) = cexp (((∑ a, (w ρ a : ℝ) * t a : ℝ) : ℂ) * I) * ψ g)
    (s : D.what₂.Tau → Fin V.rank → ℝ) (g : GA D V) :
    ψ (g * torProd θ V B s) = cexp (((∑ ρ, ∑ a, (w ρ a : ℝ) * s ρ a : ℝ) : ℂ) * I) * ψ g := by
  unfold torProd
  suffices H : ∀ l : List D.what₂.Tau, l.Nodup → ∀ g, ψ (g * (l.map fun ρ => torAt θ V B ρ (s ρ)).prod) =
      cexp (((∑ ρ ∈ l.toFinset, ∑ a, (w ρ a : ℝ) * s ρ a : ℝ) : ℂ) * I) * ψ g by
    have := H (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _) g
    rwa [Finset.toList_toFinset] at this
  intro l hl
  induction l with
  | nil => intro g; simp
  | cons ρ l ih =>
    intro g
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, ← mul_assoc, ih hl.2, h, List.toFinset_cons,
      Finset.sum_insert (by simpa using hl.1), ← mul_assoc, ← Complex.exp_add, ← add_mul]
    congr 3
    push_cast
    ring

theorem xB_mvB_mul (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (a k : GA D T) (b : Frame C.X.Ψ T.rank)
    (hk : ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T k) = B ρ * (mat b (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) :
    C.xB (C.mvB (a * k) B) = rmul (C.xB (C.mvB a B)) b := by
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  funext σ i j
  obtain ⟨ρ, rfl⟩ := C.m.e.surjective σ
  have e1 : C.mvB (a * k) B ρ = C.mvB a B ρ * (mat b (C.m.e ρ)).map (starRingEnd ℂ) := by
    have hm : compAt C.θ ρ (Formalism.L2.Theta.mt T (a * k)) =
        compAt C.θ ρ (Formalism.L2.Theta.mt T a) * compAt C.θ ρ (Formalism.L2.Theta.mt T k) := R.2.2.2.1 a k ρ
    simp only [Ctx.mvB]
    rw [hm, hk]
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.mul_one]

  simp only [Ctx.xB, rmul, mat, Equiv.symm_apply_apply, e1, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply,
  map_sum, map_mul, Complex.conj_conj]

end GlobalTheory.AdSpan.ConjHol
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extremalVector_values_lowering_and_torus : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) (p : ℕ), (∀ τ, ((Wc D i).sig (tauE D τ)).1 = p) → p ≤ (Wc D i).rank → IsExtVec (R.MW i (sg0 D A)) (fun ρ => u ρ) → ∀ T ∈ R.Wall i (sg0 D A), LowKilled R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) (T fun ρ => u ρ) ∧ ∀ (ρ : D.what₂.Tau) (s : Fin (Wc D i).rank → ℝ), ∃ l : ℂ, R.ωP i t (1, torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) = l • R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w) ∧ ∀ g, T (fun ρ => u ρ) (g * torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) = l * T (fun ρ => u ρ) g := by
  first | exact @GlobalTheory.ExtFock.ext_values | exact GlobalTheory.ExtFock.ext_values | (intros; apply GlobalTheory.ExtFock.ext_values <;> assumption)
end
