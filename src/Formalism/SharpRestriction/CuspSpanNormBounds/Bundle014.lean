module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle010

@[expose] public section

section

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Alg2

variable {k r : ℕ} {κ τ : ℝ}

theorem tV_eI (a : Fin r) : tV k r κ τ (eI k r a) = tF r κ τ a.val := by
  unfold tV eI; rw [if_pos a.isLt]

theorem tV_esI (a : Fin r) : tV k r κ τ (esI k r a) = (tF r κ τ a.val)⁻¹ := by
  unfold tV esI
  have h := a.isLt
  rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
  congr 2; simp only; omega

theorem tV_wb (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : tV k r κ τ i = 1 := by
  unfold tV; rw [if_neg (by omega), if_pos h2]

theorem dM_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (dM k r κ τ *ᵥ v) i = ((tV k r κ τ i : ℝ) : ℂ) * v i := by
  rw [dM, Matrix.mulVec_diagonal]

theorem dMi_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (dMi k r κ τ *ᵥ v) i = (((tV k r κ τ i)⁻¹ : ℝ) : ℂ) * v i := by
  rw [dMi, Matrix.mulVec_diagonal]

theorem dM_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : dM k r κ τ *ᵥ z = z := by
  funext i; rw [dM_mulVec_apply]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · rw [tV_wb i (by omega) (by omega)]; simp

theorem dMi_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : dMi k r κ τ *ᵥ z = z := by
  funext i; rw [dMi_mulVec_apply]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · rw [tV_wb i (by omega) (by omega)]; simp

theorem dM_mulVec_bvec (i : Fin (2 * r + k + 1)) :
    dM k r κ τ *ᵥ bvec i = ((tV k r κ τ i : ℝ) : ℂ) • bvec i := by
  funext j; rw [dM_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [bvec, h]

theorem dMi_mulVec_bvec (i : Fin (2 * r + k + 1)) :
    dMi k r κ τ *ᵥ bvec i = (((tV k r κ τ i)⁻¹ : ℝ) : ℂ) • bvec i := by
  funext j; rw [dMi_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [bvec, h]

theorem inWb_smul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : ℂ) : inWb k r (a • z) := by
  intro i hi; rw [Pi.smul_apply, hz i hi, smul_zero]

theorem cj_mulVec (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    cj k r κ τ x *ᵥ v = dMi k r κ τ *ᵥ (x *ᵥ (dM k r κ τ *ᵥ v)) := by
  rw [cj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem dM_mulVec_fvec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin (r + 1)) :
    dM k r κ τ *ᵥ fvec k r ((τ : ℂ) • z) a = ((tF r κ τ a.val : ℝ) : ℂ) • fvec k r z a := by
  unfold fvec
  by_cases h : a.val < r
  · rw [dite_eq_left h, dite_eq_left h, dM_mulVec_bvec, tV_eI]
  · rw [dite_eq_right h, dite_eq_right h, dM_mulVec_wb (inWb_smul hz _)]
    have : a.val = r := by omega
    simp [tF, this]

theorem ell_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Mx k r) :
    ell k r ((τ : ℂ) • z) (cj k r κ τ x) = (κ : ℂ)⁻¹ * ell k r z x := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a.val + 1 < r
  · rw [dite_eq_left h, dite_eq_left h, cj_apply, tV_eI, tV_eI]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    have hk := pow_pos hκ (r - (a.val + 1))
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    have hkc : (κ : ℂ) ^ (r - (a.val + 1)) ≠ 0 := pow_ne_zero _ hκc
    simp only [tF]
    rw [e, pow_succ]
    push_cast
    field_simp
  · rw [dite_eq_right h, dite_eq_right h, cj_mulVec, dM_mulVec_wb (inWb_smul hz _), Matrix.mulVec_smul,
      dMi_mulVec_apply, tV_eI, Pi.smul_apply, smul_eq_mul]
    have e : r - a.val = 1 := by omega
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    simp only [tF, e, pow_one]
    push_cast
    field_simp

theorem psi_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (x : Mx k r) :
    psi k r ((τ : ℂ) • z) ((κ : ℂ) * c) (cj k r κ τ x) = psi k r z c x := by
  unfold psi
  rw [ell_cj hκ hτ hz]
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have : (κ : ℂ) * c * ((κ : ℂ)⁻¹ * ell k r z x) = c * ell k r z x := by
    field_simp
  rw [this]

theorem delta_iff {s y : ℂ} {i j : Fin (2 * r + k + 1)} (hs : s ≠ 0) (h1 : i = j → s = 1) :
    (s * y = if i = j then 1 else 0) ↔ (y = if i = j then 1 else 0) := by
  by_cases h : i = j
  · rw [h1 h, one_mul]
  · simp only [h, if_false, mul_eq_zero, hs, false_or]

theorem cj_fac_ne (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) :
    ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) ≠ 0 := by
  have := tV_pos (k := k) (r := r) hκ hτ i
  have := tV_pos (k := k) (r := r) hκ hτ j
  exact_mod_cast (mul_pos (inv_pos.mpr ‹0 < tV k r κ τ i›) this).ne'

theorem cj_fac_diag (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) (h : i = j) :
    ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) = 1 := by
  subst h; rw [inv_mul_cancel₀ (tV_pos hκ hτ i).ne']; simp

theorem cj_mem_Nset_iff (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) :
    cj k r κ τ x ∈ Nset k r ↔ x ∈ Nset k r := by
  simp only [Nset, Set.mem_ofPred_eq, cj_mem_UH_iff hκ hτ, cj_apply]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall_congr' fun a => forall_congr' fun i => imp_congr_right fun _ => ?_
    exact delta_iff (cj_fac_ne hκ hτ _ _) (cj_fac_diag hκ hτ _ _)
  · refine forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ => ?_
    exact delta_iff (cj_fac_ne hκ hτ _ _) (cj_fac_diag hκ hτ _ _)

theorem UWset_smul {z : Fin (2 * r + k + 1) → ℂ} (hτ : 0 < τ) : UWset k r ((τ : ℂ) • z) = UWset k r z := by
  ext g
  simp only [UWset, Set.mem_ofPred_eq, Matrix.mulVec_smul]
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact smul_right_injective _ hτ' h

theorem cj_fix_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (hs : s ≠ 0)
    (h1 : dM k r κ τ *ᵥ v = s • v) (h2 : dMi k r κ τ *ᵥ v = s⁻¹ • v) :
    cj k r κ τ g *ᵥ v = v ↔ g *ᵥ v = v := by
  rw [cj_mulVec, h1, Matrix.mulVec_smul, Matrix.mulVec_smul]
  constructor
  · intro h
    have h3 : dM k r κ τ *ᵥ (s • (dMi k r κ τ *ᵥ (g *ᵥ v))) = dM k r κ τ *ᵥ v := by rw [h]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, dM_mul_dMi hκ hτ, Matrix.one_mulVec, h1] at h3
    exact smul_right_injective _ hs h3
  · intro h; rw [h, h2, smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem cj_fix_bvec_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) (i : Fin (2 * r + k + 1)) :
    cj k r κ τ g *ᵥ bvec i = bvec i ↔ g *ᵥ bvec i = bvec i := by
  refine cj_fix_iff hκ hτ g _ ((tV k r κ τ i : ℝ) : ℂ) (by exact_mod_cast (tV_pos hκ hτ i).ne')
    (dM_mulVec_bvec i) ?_
  rw [dMi_mulVec_bvec, Complex.ofReal_inv]

theorem cj_mem_UWset_iff (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Mx k r) :
    cj k r κ τ g ∈ UWset k r z ↔ g ∈ UWset k r z := by
  simp only [UWset, Set.mem_ofPred_eq, cj_mem_UH_iff hκ hτ]
  refine and_congr Iff.rfl (and_congr (forall_congr' fun a =>
    and_congr (cj_fix_bvec_iff hκ hτ g _) (cj_fix_bvec_iff hκ hτ g _)) ?_)
  exact cj_fix_iff hκ hτ g z 1 one_ne_zero (by rw [one_smul, dM_mulVec_wb hz])
    (by rw [inv_one, one_smul, dMi_mulVec_wb hz])

theorem cj_mem_RStab_iff (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) :
    cj k r κ τ a ∈ RStab k r (cj k r κ τ g) ↔ a ∈ RStab k r g := by
  simp only [RStab, Set.mem_ofPred_eq]
  rw [← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, cj_mem_Nset_iff hκ hτ, cj_mem_Nset_iff hκ hτ]

end Alg2

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

section

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {k r : ℕ}

def trD (L : LocBessel k r) (κ τ : ℝ) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1) : LocBessel k r where
  ε := L.ε
  lam := L.lam
  hlam := L.hlam
  z := (τ : ℂ) • L.z
  z' := (τ : ℂ) • L.z'
  hz := hz
  hz' := hz'
  u := L.u
  u' := L.u'
  Hs := L.Hs
  σ := L.σ
  hσ := L.hσ
  Wp := L.Wp
  π := fun x => L.π (cjI k r κ τ x)
  hπ := hπ
  Wq := L.Wq
  π' := fun x => L.π' (cjI k r κ τ x)
  hπ' := hπ'
  c := (κ : ℂ) * L.c
  μW := L.μW.map (cjT k r κ τ)
  μW' := L.μW'.map (cjT k r κ τ)
  hμW := hμW
  hμW' := hμW'
  κN := κN₁

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

section

noncomputable section

namespace Formalism.MainNotions.AuxiliaryNormPrimes

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt NumberField Matrix Module
open scoped ENNReal NNReal InnerProductSpace

section B3

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def aux₃ (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A c : ℝ) : Prop :=
  UnitaryVolumeMass.VolumeRatioBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c

end B3

section Mass

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FamilySchurFormalDegree (D : D7) : Prop :=
  UnitaryVolumeMass.stMassRatio D

def GL5LogLValueBoundByZeta (D : D7) : Prop :=
  UnitaryVolumeMass.stMassL D

def RankTwoMassBound (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def MassVolumeForGaugeFamily (D : D7) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig) : Prop :=
  UnitaryVolumeMass.stMassVol D G

end Mass

section BR

def UnitaryBranchingMultiplicityOne : Prop :=
  UnitaryVolumeMass.stBRmult

def HadamardDeterminantInequality : Prop :=
  UnitaryVolumeMass.stBRhad

def BanaszczykTransferenceBound : Prop :=
  UnitaryVolumeMass.stBRtrans

def MinkowskiFiniteSubgroupOrder : Prop :=
  UnitaryVolumeMass.stBRmink

end BR

section Rows

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def CharacterCutVolume (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def SpectralWeightsCM (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  UnitaryVolumeMass.stForm D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

end Rows

def TemperatureProductAsymptotic (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ

def CriticalTemperatureLowerBound (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def PlancherelBoundOneParameter (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def PlancherelBoundFiniteSums (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTsum D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def PlancherelBoundDifferenceOperator (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTDl D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def BesselDegreeNormalization (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  UnitaryVolumeMass.PieriNormDegreeFormula D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1

def DegreeRatioUnitStepBound (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.FormalDegreeUnitStepRatio D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def ArchimedeanMomentBound (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  UnitaryVolumeMass.stMOM D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def DimensionConstantBound (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stCONST D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

end Loc

section Comparison₂

open Formalism.MainNotions.S.Lat MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TermVolumeSmallCellBound (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (Y : LoopTie D large₂ X u u' C1) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stVol D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A C

end Comparison₂

section Stmt

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ) (Y : LoopTie D large₂ X u u' C1)
  (G : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

def admitted (C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CK CV : ℝ) : Prop :=
  FamilySchurFormalDegree D ∧ GL5LogLValueBoundByZeta D ∧ RankTwoMassBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CM ∧ MassVolumeForGaugeFamily D G ∧
  UnitaryBranchingMultiplicityOne ∧ HadamardDeterminantInequality ∧ BanaszczykTransferenceBound ∧ MinkowskiFiniteSubgroupOrder ∧
  CharacterCutVolume D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CSW ∧ SpectralWeightsCM D large₂ u u' C' Cl Cg cb Cu cT CT C0 A ∧
  TemperatureProductAsymptotic D large₂ C' Cl Cg cb Cu cT CT C0 δ ∧ CriticalTemperatureLowerBound D large₂ C' Cl Cg cb Cu cT CT C0 ∧
  PlancherelBoundOneParameter D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ PlancherelBoundFiniteSums D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧
  PlancherelBoundDifferenceOperator D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl ∧ BesselDegreeNormalization D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 ∧
  DegreeRatioUnitStepBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant ∧ ArchimedeanMomentBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CMo ∧
  DimensionConstantBound D large₂ C' Cl Cg cb Cu cT CT C0 C1 CK ∧ TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A CV

def Stmt (C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CK CV c : ℝ) : Prop :=
  admitted D large₂ X u u' C1 Y G C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CK CV →
    aux₃ D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c

end Stmt

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FamilyTemperatureProductAsymptotic (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ δ > 0, OwnEv Fm fun C' Cl x i => TemperatureProductAsymptotic (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 δ

variable (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Family

end Formalism.MainNotions.AuxiliaryNormPrimes
end
end
