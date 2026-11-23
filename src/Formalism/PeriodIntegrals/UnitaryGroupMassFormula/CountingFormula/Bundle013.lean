module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.DdSNeZero
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Induced

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem flag_Xa_top : F0.Xa D.R.rS = F0.X := by
  simp only [Formalism.MainNotions.S.FlagG.Xa, Formalism.MainNotions.S.FlagG.X]
  congr 1
  ext x
  simp

variable {D F0}

theorem stabF_isom {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y := fun x y => hγ.1 x y

theorem stabF_mapX {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    F0.X.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
  have h := hγ.2.1 D.R.rS
  rwa [flag_Xa_top D F0] at h

theorem apply_z_eq_z_of_mem_stabF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : γ F0.z = F0.z := hγ.2.2

theorem stabF_mem_X {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V}
    (hx : x ∈ F0.X) : γ x ∈ F0.X := by
  rw [← stabF_mapX hγ]
  exact Submodule.mem_map_of_mem hx

theorem stabF_symm_mem_X {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V}
    (hx : x ∈ F0.X) : γ.symm x ∈ F0.X := by
  rw [← stabF_mapX hγ] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem stabF_mem_perp {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ y ∈ perpS (VS D) F0.X := by
  show ∀ x ∈ F0.X, (VS D).hT x (γ y) = 0
  intro x hx
  have h1 := stabF_isom hγ (γ.symm x) y
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  exact hy _ (stabF_symm_mem_X hγ hx)

theorem stabF_symm_mem_perp {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ.symm y ∈ perpS (VS D) F0.X := by
  show ∀ x ∈ F0.X, (VS D).hT x (γ.symm y) = 0
  intro x hx
  have h1 := stabF_isom hγ x (γ.symm y)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  exact hy _ (stabF_mem_X hγ hx)

theorem stabF_map_perp {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    (perpS (VS D) F0.X).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = perpS (VS D) F0.X := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact stabF_mem_perp hγ hy
  · intro y hy
    exact Submodule.mem_map.2 ⟨γ.symm y, stabF_symm_mem_perp hγ hy, by simp⟩

def gPerp {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    perpS (VS D) F0.X ≃ₗ[D.host.E] perpS (VS D) F0.X :=
  γ.ofSubmodules (perpS (VS D) F0.X) (perpS (VS D) F0.X) (stabF_map_perp hγ)

theorem gPerp_apply {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (x : perpS (VS D) F0.X) :
    ((gPerp hγ x : perpS (VS D) F0.X) : (VS D).V) = γ x.1 := rfl

theorem gPerp_map_nX {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    (nX D F0).map (gPerp hγ : perpS (VS D) F0.X →ₗ[D.host.E] perpS (VS D) F0.X) = nX D F0 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    show ((gPerp hγ x : perpS (VS D) F0.X) : (VS D).V) ∈ F0.X
    rw [gPerp_apply]
    exact stabF_mem_X hγ (x := x.1) hx
  · intro x hx
    refine Submodule.mem_map.2 ⟨⟨γ.symm x.1, stabF_symm_mem_perp hγ x.2⟩,
      stabF_symm_mem_X hγ (x := x.1) hx, ?_⟩
    apply Subtype.ext
    show ((gPerp hγ ⟨γ.symm x.1, stabF_symm_mem_perp hγ x.2⟩ : perpS (VS D) F0.X) : (VS D).V) = x.1
    rw [gPerp_apply]
    simp

def gWb {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0 :=
  Submodule.Quotient.equiv (nX D F0) (nX D F0) (gPerp hγ) (gPerp_map_nX hγ)

theorem gWb_mk {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (x : perpS (VS D) F0.X) :
    gWb hγ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (gPerp hγ x) := rfl

theorem gWb_isom {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    gWb hγ ∈ Formalism.HermitianLatticesTheory.isom (hWb D F0) := by
  intro x y
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  rw [gWb_mk, gWb_mk]
  rw [hWb_mk, hWb_mk, gPerp_apply, gPerp_apply]
  exact stabF_isom hγ a.1 b.1

theorem gWb_zbar {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    gWb hγ (zbar D F0) = zbar D F0 := by
  unfold zbar
  rw [gWb_mk]
  congr 1
  apply Subtype.ext
  rw [gPerp_apply]
  exact apply_z_eq_z_of_mem_stabF hγ

theorem gWb_mem_hz {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    gWb hγ ∈ hz (hWb D F0) (zbar D F0) := ⟨gWb_isom hγ, gWb_zbar hγ⟩

theorem gWb_Mof {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (gWb hγ) (Mof D F0 Λ) = Mof D F0 (Formalism.HermitianLatticesTheory.gmap γ Λ) := by
  ext x
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  constructor
  · rintro ⟨w, hw, hwx⟩
    obtain ⟨c, hc, rfl⟩ := hw
    refine ⟨gPerp hγ c, ?_, ?_⟩
    · show ((gPerp hγ c : perpS (VS D) F0.X) : (VS D).V) ∈ Formalism.HermitianLatticesTheory.gmap γ Λ
      rw [gPerp_apply]
      exact Submodule.mem_map_of_mem hc
    · rw [← hwx]
      rfl
  · rintro ⟨c, hc, hca⟩
    obtain ⟨d, hd, hdc⟩ := hc
    have hdp : d ∈ perpS (VS D) F0.X := by
      have e : d = γ.symm c.1 := by
        have h := congrArg γ.symm hdc
        simpa using h
      rw [e]
      exact stabF_symm_mem_perp hγ c.2
    refine ⟨Submodule.Quotient.mk ⟨d, hdp⟩, ⟨⟨d, hdp⟩, hd, rfl⟩, ?_⟩
    rw [← hca]
    show gWb hγ (Submodule.Quotient.mk ⟨d, hdp⟩) = Submodule.Quotient.mk c
    rw [gWb_mk]
    congr 1
    apply Subtype.ext
    rw [gPerp_apply]
    first
    | exact hdc
    | simpa using hdc

end Induced

def RowClassBack : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IsRowLat D F0 Λ' →
      ∀ σ ∈ hz (hWb D F0) (zbar D F0), Formalism.HermitianLatticesTheory.gmap σ (Mof D F0 Λ) = Mof D F0 Λ' →
        ∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ'

theorem rowClass_fwd (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (h : ∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ') :
    ∃ σ ∈ hz (hWb D F0) (zbar D F0), Formalism.HermitianLatticesTheory.gmap σ (Mof D F0 Λ) = Mof D F0 Λ' := by
  obtain ⟨γ, hγ, hΛ⟩ := h
  exact ⟨gWb hγ, gWb_mem_hz hγ, by rw [gWb_Mof, hΛ]⟩

theorem rowClass_of (hB : RowClassBack) : RowClass := by
  intro D u F0 Λ Λ' h1 h2
  exact ⟨fun h => rowClass_fwd D F0 Λ Λ' h, fun ⟨σ, hσ, e⟩ => hB D u F0 Λ Λ' h1 h2 σ hσ e⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fix_X_of {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (he : ∀ a, n (F0.e a) = F0.e a) :
    ∀ x ∈ F0.X, n x = x := by
  have hle : F0.X ≤ LinearMap.eqLocus (n : (VS D).V →ₗ[D.host.E] (VS D).V) LinearMap.id := by
    show Submodule.span _ (Set.range F0.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simpa [LinearMap.mem_eqLocus] using he a
  intro x hx
  simpa [LinearMap.mem_eqLocus] using hle hx

theorem Xa_le_X {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (k : ℕ) : F0.Xa k ≤ F0.X := by
  show Submodule.span _ _ ≤ Submodule.span _ _
  exact Submodule.span_mono (Set.image_subset_range _ _)

theorem mem_orth_iff {D : Formalism.BasicNotions.D7} (U : Submodule D.host.E (VS D).V) (y : (VS D).V) :
    y ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem orth_map_of {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hi : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y)
    (he : ∀ a, n (F0.e a) = F0.e a) (y : (VS D).V) :
    y ∈ orth (VS D) F0.X ↔ n y ∈ orth (VS D) F0.X := by
  rw [mem_orth_iff, mem_orth_iff]
  constructor
  · intro H x hx
    rw [← fix_X_of F0 n he x hx, hi]
    exact H x hx
  · intro H x hx
    rw [← hi, fix_X_of F0 n he x hx]
    exact H x hx

theorem gmap_mem {D : Formalism.BasicNotions.D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap n Λ = Λ) {y : (VS D).V} (hy : y ∈ Λ) :
    n y ∈ Λ := by
  rw [← h]
  exact ⟨y, hy, rfl⟩

theorem gmap_surj {D : Formalism.BasicNotions.D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap n Λ = Λ) {x : (VS D).V} (hx : x ∈ Λ) :
    ∃ y ∈ Λ, n y = x := by
  rw [← h] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩

theorem refl_mem_unipotentIntegral {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) : LinearEquiv.refl D.host.E (VS D).V ∈ N0 F0 Λ := by
  refine ⟨⟨⟨fun x y => rfl, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩, fun a => rfl, rfl⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · simp
  · simp

theorem symm_mem_unipotentIntegral {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ N0 F0 Λ) :
    n.symm ∈ N0 F0 Λ := by
  obtain ⟨⟨⟨hi, hΛ⟩, -, horth⟩, he, hz⟩ := hn
  have hi' : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hi
  have hfix : ∀ x ∈ F0.X, n.symm x = x := fun x hx =>
    n.symm_apply_eq.2 (fix_X_of F0 n he x hx).symm
  refine ⟨⟨⟨fun x y => ?_, ?_⟩, fun j x hx => ?_, fun x hx => ?_⟩, fun a => ?_, ?_⟩
  · rw [← hi' (n.symm x) (n.symm y), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := gmap_surj Λ n hΛ hy
      show n.symm (n w) ∈ Λ
      rw [LinearEquiv.symm_apply_apply]
      exact hw
    · intro hx
      exact ⟨n x, gmap_mem Λ n hΛ hx, n.symm_apply_apply x⟩
  · rw [hfix x (Xa_le_X F0 (j + 1) hx), sub_self]
    exact Submodule.zero_mem _
  · have hy : n.symm x ∈ orth (VS D) F0.X := by
      rw [orth_map_of F0 n hi' he, LinearEquiv.apply_symm_apply]
      exact hx
    have e := horth (n.symm x) hy
    rw [LinearEquiv.apply_symm_apply] at e
    have e' : n.symm x - x = -(x - n.symm x) := by abel
    rw [e']
    exact Submodule.neg_mem _ e
  · exact n.symm_apply_eq.2 (he a).symm
  · exact n.symm_apply_eq.2 hz.symm

theorem trans_mem_unipotentIntegral {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ N0 F0 Λ)
    (hm : m ∈ N0 F0 Λ) : n.trans m ∈ N0 F0 Λ := by
  obtain ⟨⟨⟨hin, hΛn⟩, -, horthn⟩, hen, hzn⟩ := hn
  obtain ⟨⟨⟨him, hΛm⟩, -, horthm⟩, hem, hzm⟩ := hm
  have hin' : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hin
  have him' : ∀ x y, (VS D).hT (m x) (m y) = (VS D).hT x y := him
  refine ⟨⟨⟨fun x y => ?_, ?_⟩, fun j x hx => ?_, fun x hx => ?_⟩, fun a => ?_, ?_⟩
  · show (VS D).hT (m (n x)) (m (n y)) = (VS D).hT x y
    rw [him', hin']
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact gmap_mem Λ m hΛm (gmap_mem Λ n hΛn hy)
    · intro hx
      obtain ⟨w, hw, rfl⟩ := gmap_surj Λ m hΛm hx
      obtain ⟨v, hv, rfl⟩ := gmap_surj Λ n hΛn hw
      exact ⟨v, hv, rfl⟩
  · have hX := Xa_le_X F0 (j + 1) hx
    show m (n x) - x ∈ _
    rw [fix_X_of F0 n hen x hX, fix_X_of F0 m hem x hX, sub_self]
    exact Submodule.zero_mem _
  · have h1 := horthn x hx
    have h2 := horthm (n x) ((orth_map_of F0 n hin' hen x).1 hx)
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      show m (n x) - x = _
      abel
    rw [e]
    exact Submodule.add_mem _ h2 h1
  · show m (n (F0.e a)) = F0.e a
    rw [hen, hem]
  · show m (n F0.z) = F0.z
    rw [hzn, hzm]

theorem unipotent_integral_isGroup : UnipotentIntegralIsGroup := by
  intro D T F0 Λ
  exact ⟨refl_mem_unipotentIntegral F0 Λ, fun n hn => symm_mem_unipotentIntegral F0 Λ n hn,
    fun n hn m hm => trans_mem_unipotentIntegral F0 Λ n m hn hm⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pos

end Pos

section Generic

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

end Generic

section Bridge

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem hWb_isSymm : (hWb D F0).IsSymm := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  rw [hWb_mk, hWb_mk]
  exact (VS D).herm.eq a.1 b.1

theorem one_mem_stabF : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := by
  refine ⟨Subgroup.one_mem _, fun j => ?_, rfl⟩
  ext x
  simp

theorem one_mem_hz {V1 : Type} [AddCommGroup V1] [Module D.host.E V1]
    (h1 : V1 →ₗ⋆[D.host.E] V1 →ₗ[D.host.E] D.host.E) (z : V1) :
    (1 : V1 ≃ₗ[D.host.E] V1) ∈ hz h1 z :=
  ⟨Subgroup.one_mem _, rfl⟩

theorem gmap_one' {V1 : Type} [AddCommGroup V1] [Module D.host.E V1] [Module (𝓞 D.host.E) V1]
    [IsScalarTower (𝓞 D.host.E) D.host.E V1] (M : Submodule (𝓞 D.host.E) V1) :
    Formalism.HermitianLatticesTheory.gmap (1 : V1 ≃ₗ[D.host.E] V1) M = M := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

end Bridge

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_mem_ddS_zpow (D : Formalism.BasicNotions.D7) (k : ℕ) :
    (1 : D.host.E) ∈ ((ddS D) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h0 : ddS D ≠ 0 := PI.TripleFrameDeterminant.W.ddS_ne_zero D
  have hle : ddS D ^ k ≤ 1 := by
    rw [ddS, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  have h := FractionalIdeal.inv_anti_mono (pow_ne_zero k h0) hle
  rw [inv_one] at h
  rw [zpow_neg, zpow_natCast]
  exact h (FractionalIdeal.one_mem_one _)

theorem flag_gram (D : Formalism.BasicNotions.D7) {T' : D.host.E} (G : FlagG (VS D) D.R.rS T') (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (G.fvec a) (G.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0 := by
  have hs : ∀ x y, (VS D).hT y x = starRingEnd D.host.E ((VS D).hT x y) :=
    fun x y => ((VS D).herm.eq x y).symm
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_norm]
    | cast j =>
      rw [hs]
      simp [FlagG.fvec, G.z_orth j]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_orth i]
    | cast j => simp [FlagG.fvec, G.e_iso i j]

theorem good_places_integral : GoodEZ := by
  intro D T T' F0 Λ Z F' hF'
  obtain ⟨hT, -, -, hFr, hZ⟩ := hF'
  have hfr : fr D (F'.fl.e, F'.fl.z) = F'.fl.fvec := rfl
  refine ⟨fun b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [hfr]
    have h := PI.CntNotIntW.frame_mem Λ F' hFr.2 hT.1.1 b 1 (one_mem_ddS_zpow D _)
    rwa [one_smul] at h
  · rw [hfr, ← hZ]
    rfl
  · rw [hfr]
    exact flag_gram D F'.fl a b

end PI.UnitaryGroupMassFormula.CntFormula
end
end
