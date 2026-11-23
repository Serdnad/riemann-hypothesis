module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle009
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.XLeOrthXplus
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle015
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan

@[expose] public section

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem perpS_eq_orth (D : D7) (U : Submodule D.host.E (VS D).V) : perpS (VS D) U = orth (VS D) U := by
  ext v
  rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
  rfl

theorem e_mem_perp (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) :
    F0.e a ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact F0.e_iso b a
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem X_le_perp (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : F0.X ≤ perpS (VS D) F0.X := by
  unfold FlagG.X
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact e_mem_perp D F0 a

theorem mem_Mof (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (x : WbQ D F0) :
    x ∈ Mof D F0 Λ ↔ ∃ a : perpS (VS D) F0.X, (a : (VS D).V) ∈ Λ ∧ Submodule.Quotient.mk a = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem mk_eq_mk (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a b : perpS (VS D) F0.X) :
    (Submodule.Quotient.mk a : WbQ D F0) = Submodule.Quotient.mk b ↔ (a : (VS D).V) - b ∈ F0.X := by
  rw [Submodule.Quotient.eq]
  rfl

theorem Mof_fg (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hfg : Λ.FG) : (Mof D F0 Λ).FG := by
  apply Submodule.FG.map
  apply Submodule.fg_of_fg_map_injective ((perpS (VS D) F0.X).subtype.restrictScalars (𝓞 D.host.E))
    Subtype.val_injective
  refine Submodule.FG.of_le hfg ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hy

theorem Mof_span (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hsp : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤) :
    Submodule.span D.host.E (Mof D F0 Λ : Set (WbQ D F0)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  obtain ⟨d, hd, hdm⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hsp (a : (VS D).V)
  have hdE : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).mpr hd
  have hmem : (Submodule.Quotient.mk (d • a) : WbQ D F0) ∈ Mof D F0 Λ := by
    rw [mem_Mof]
    refine ⟨d • a, ?_, rfl⟩
    rw [Submodule.coe_smul_of_tower]
    exact hdm
  have e : (Submodule.Quotient.mk a : WbQ D F0) =
      (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ • (Submodule.Quotient.mk (d • a) : WbQ D F0) := by
    rw [← algebraMap_smul D.host.E d a, Submodule.Quotient.mk_smul, smul_smul, inv_mul_cancel₀ hdE, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem Mof_isLattice (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : Submodule.IsLattice D.host.E Λ) : Submodule.IsLattice D.host.E (Mof D F0 Λ) :=
  Submodule.IsLattice.of_fg D.host.E (Mof_fg D F0 Λ hL.fg)

theorem Mof_unimod (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : Submodule.IsLattice D.host.E Λ) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Formalism.HermitianLatticesTheory.IsUnimodular (hWb D F0) (Mof D F0 Λ) := by
  have hsp : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ :=
    Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hU (VS D).herm hL.fg
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
  show Formalism.HermitianLatticesTheory.dual (hWb D F0) (Mof D F0 Λ) = Mof D F0 Λ
  apply le_antisymm
  · intro x hx
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hx
    induction x using Submodule.Quotient.induction_on with | H a => ?_

    have hint : ∀ l : perpS (VS D) F0.X, (l : (VS D).V) ∈ Λ →
        (VS D).hT (l : (VS D).V) (a : (VS D).V) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro l hl
      have := hx (Submodule.Quotient.mk l) ((mem_Mof D F0 Λ _).2 ⟨l, hl, rfl⟩)
      rwa [hWb_mk] at this
    obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract Λ hL.fg (perpS (VS D) F0.X)
    let f : Λ →ₗ[𝓞 D.host.E] D.host.E :=
      ((VS D).hT (a : (VS D).V)).restrictScalars (𝓞 D.host.E) ∘ₗ Λ.subtype ∘ₗ ρ
    obtain ⟨w, hw⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.riesz (VS D).hT (VS D).herm (VS D).nondeg Λ hL.fg
      hsp f

    have hwΛ : w ∈ Λ := by
      rw [← hU', Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (S := VS D) w y, hw y hy]
      have e1 : f ⟨y, hy⟩ = (VS D).hT (a : (VS D).V) ((ρ ⟨y, hy⟩ : Λ) : (VS D).V) := rfl
      rw [e1, ← PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (S := VS D)]
      exact hint ⟨_, hρX ⟨y, hy⟩⟩ (ρ ⟨y, hy⟩).2

    have hwv : ∀ v ∈ perpS (VS D) F0.X, (VS D).hT (w - (a : (VS D).V)) v = 0 := by
      intro v hv
      obtain ⟨d, hd, hdm⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hsp v
      have hdE : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).mpr hd
      have hdp : d • v ∈ perpS (VS D) F0.X := by
        rw [← algebraMap_smul D.host.E d v]
        exact Submodule.smul_mem _ _ hv
      have h1 := hw (d • v) hdm
      have e1 : f ⟨d • v, hdm⟩ = (VS D).hT (a : (VS D).V) ((ρ ⟨d • v, hdm⟩ : Λ) : (VS D).V) := rfl
      rw [e1, hρid ⟨d • v, hdm⟩ hdp] at h1
      have h2 : (VS D).hT (w - (a : (VS D).V)) (d • v) = 0 := by
        rw [map_sub, LinearMap.sub_apply, h1]
        simp
      rw [← algebraMap_smul D.host.E d v, LinearMap.map_smul, smul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_left hdE

    have hwX : w - (a : (VS D).V) ∈ F0.X := by
      have : w - (a : (VS D).V) ∈ orth (VS D) (orth (VS D) F0.X) := by
        rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
        intro v hv
        rw [← perpS_eq_orth] at hv
        rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (S := VS D), hwv v hv, star_zero]
      rwa [PI.ScalarPairDr.W.orth_orth] at this
    have hwp : w ∈ perpS (VS D) F0.X := by
      have e : w = (a : (VS D).V) + (w - (a : (VS D).V)) := by abel
      rw [e]
      exact Submodule.add_mem _ a.2 (X_le_perp D F0 hwX)
    rw [mem_Mof]
    refine ⟨⟨w, hwp⟩, hwΛ, ?_⟩
    rw [mk_eq_mk]
    exact hwX
  · intro x hx
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_Mof D F0 Λ x).1 hx
    obtain ⟨b, hb, rfl⟩ := (mem_Mof D F0 Λ y).1 hy
    rw [hWb_mk]
    obtain ⟨o, ho⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val (S := VS D) hU hb ha
    exact Submodule.mem_one.2 ⟨o, ho⟩

theorem zbar_mem (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hz : F0.z ∈ Λ) : zbar D F0 ∈ Mof D F0 Λ :=
  (mem_Mof D F0 Λ _).2 ⟨⟨F0.z, z_mem_perp D F0⟩, hz, rfl⟩

theorem zbar_prim (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hprim : ∀ c : D.host.E, c • F0.z ∈ Lsub Λ (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c)
    (c : D.host.E) (hc : c • zbar D F0 ∈ Mof D F0 Λ) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  apply hprim
  obtain ⟨a, ha, hae⟩ := (mem_Mof D F0 Λ _).1 hc
  rw [zbar, ← Submodule.Quotient.mk_smul, mk_eq_mk] at hae
  have hzo : F0.z ∈ orth (VS D) F0.X := by
    rw [← perpS_eq_orth]
    exact z_mem_perp D F0
  have hao : (a : (VS D).V) ∈ orth (VS D) F0.X := by
    rw [← perpS_eq_orth]
    exact a.2
  have hcz : c • F0.z = (a : (VS D).V) + -((a : (VS D).V) - c • F0.z) := by abel
  refine ⟨?_, ?_⟩
  · rw [hcz]
    refine Submodule.add_mem_sup ?_ ?_
    · exact ⟨ha, hao⟩
    · exact Submodule.neg_mem _ (by simpa using hae)
  · exact (orth (VS D) F0.X).smul_mem c hzo

theorem row_lattice_mass_holds : RowM := by
  intro D u F0 Λ hrow
  obtain ⟨_, ⟨hL, hU, ⟨hz, _⟩, hconv⟩, _⟩ := hrow
  exact ⟨Mof_isLattice D F0 Λ hL, Mof_unimod D F0 Λ hL hU, zbar_mem D F0 Λ hz,
    zbar_prim D F0 Λ hconv.2⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

theorem PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_lattice_mass_holds : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowM :=
  PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.row_lattice_mass_holds
end
end

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Flag

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {f : Fin D.R.rS → (VS D).V}
  {M : Submodule (𝓞 D.host.E) (WbQ D F0)}

theorem rs_mem_lamC_perp {v : (VS D).V} (hv : v ∈ perpS (VS D) F0.X) :
    v ∈ lamC D F0 f M ↔ (Submodule.Quotient.mk (⟨v, hv⟩ : perpS (VS D) F0.X) : WbQ D F0) ∈ M ∧
      ∀ a, (VS D).hT (f a) v ∈ aaI D a := by
  have h0 : ∀ a, (VS D).hT (F0.e a) v = 0 := fun a => hv _ (Submodule.subset_span ⟨a, rfl⟩)
  have hvPr : vPr D F0 f v = v := by simp [vPr, h0]
  constructor
  · rintro ⟨-, ⟨w, hw, hwM⟩, h3⟩
    have hwv : w = ⟨v, hv⟩ := Subtype.ext (hw.trans hvPr)
    subst hwv
    exact ⟨hwM, fun a => by rw [← hvPr]; exact h3 a⟩
  · rintro ⟨hM, h3⟩
    refine ⟨fun a => ?_, ⟨⟨v, hv⟩, hvPr.symm, hM⟩, fun a => ?_⟩
    · simp only [h0, star_zero]
      exact fi_zero D _
    · rw [hvPr]
      exact h3 a

theorem rs_orth_perp {y : (VS D).V} (hy : y ∈ orth (VS D) F0.X) : y ∈ perpS (VS D) F0.X := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy
  exact fun x hx => hy x hx

theorem rs_z_mem (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) :
    F0.z ∈ lamC D F0 f M := by
  rw [rs_mem_lamC_perp (z_mem_perp D F0)]
  refine ⟨hM.2.2.1, fun a => ?_⟩
  rw [hf.2.2 a]
  exact fi_zero D _

theorem rs_smul_e_mem (hf : PartnerOK D F0 f) {a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ aaI D a) :
    x • F0.e a ∈ lamC D F0 f M := by
  have hXe : ∀ y ∈ F0.X, ∀ b, (VS D).hT y (F0.e b) = 0 := by
    intro y hy b
    have hy' : y ∈ Submodule.span D.host.E (Set.range F0.e) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, rfl⟩ := hz
      exact F0.e_iso c b
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply, hy, hz, add_zero]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]
  have hperp : x • F0.e a ∈ perpS (VS D) F0.X := by
    intro y hy
    rw [map_smul, hXe y hy a, smul_zero]
  rw [rs_mem_lamC_perp hperp]
  refine ⟨?_, fun b => ?_⟩
  · have hmem : x • F0.e a ∈ F0.X := Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    have h0 : (Submodule.Quotient.mk (⟨x • F0.e a, hperp⟩ : perpS (VS D) F0.X) : WbQ D F0) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hmem
    rw [h0]
    exact zero_mem _
  · have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f b)) = (VS D).hT (f b) (F0.e a) := by
      first
        | exact (VS D).herm (F0.e a) (f b)
        | exact (VS D).herm.eq (F0.e a) (f b)
    rw [map_smul, ← hs, hf.1 a b, smul_eq_mul]
    split_ifs with hab
    · subst hab
      simpa using hx
    · simp only [map_zero, mul_zero]
      exact FractionalIdeal.zero_mem _

theorem rs_xlam (hf : PartnerOK D F0 f) : XLam (lamC D F0 f M) (lf D F0) = XS D F0 := by
  apply le_antisymm
  · rintro v ⟨hvΛ, hvX⟩
    have hvX' : v ∈ F0.X := hvX
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hvX'
    have hα := ((rs_mem_lamC_perp (rs_X_le_perp D F0 hvX')).1 hvΛ).2
    have hca : ∀ a, c a ∈ aaI D a := by
      intro a
      have h := hα a

      rw [← hc, map_sum] at h
      simp only [map_smul, rs_hT_f_e hf, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h
      exact h
    rw [← hc]
    refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, c a, hca a, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    exact ⟨rs_smul_e_mem hf hx, Submodule.smul_mem _ x (rs_e_mem_X D F0 a)⟩

theorem rs_prim (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) (c : D.host.E)
    (hc : c • F0.z ∈ Lsub (lamC D F0 f M) (lf D F0)) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  obtain ⟨y, hy, x, hx, hyx⟩ := Submodule.mem_sup.1 hc.1
  have hyΛ : y ∈ lamC D F0 f M := hy.1
  have hyp : y ∈ perpS (VS D) F0.X := rs_orth_perp hy.2
  have hxX : x ∈ F0.X := hx
  have hxp : x ∈ perpS (VS D) F0.X := rs_X_le_perp D F0 hxX
  have hyM := ((rs_mem_lamC_perp hyp).1 hyΛ).1
  apply hM.2.2.2 c
  have hsum : c • (⟨F0.z, z_mem_perp D F0⟩ : perpS (VS D) F0.X) = ⟨y, hyp⟩ + ⟨x, hxp⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_add]
    exact hyx.symm
  rw [zbar, ← Submodule.Quotient.mk_smul, hsum, Submodule.Quotient.mk_add, rs_mk_X_zero D F0 hxX, add_zero]
  exact hyM

def rsLift (w : perpS (VS D) F0.X) : (VS D).V := (w : (VS D).V) - ∑ a, (VS D).hT (f a) w • F0.e a

theorem rs_lift_perp (w : perpS (VS D) F0.X) : rsLift (f := f) w ∈ perpS (VS D) F0.X := by
  show ∀ x ∈ F0.X, (VS D).hT x (rsLift (f := f) w) = 0
  intro x hx
  have hxe : ∀ b, (VS D).hT x (F0.e b) = 0 := by
    intro b
    have hx' : x ∈ Submodule.span D.host.E (Set.range F0.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact F0.e_iso a b
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply, hy, hz, add_zero]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]

  simp only [rsLift, map_sub, map_sum, map_smul, hxe, smul_zero, Finset.sum_const_zero, sub_zero]
  exact w.2 x hx

theorem rs_lift_mk (w : perpS (VS D) F0.X) :
    (Submodule.Quotient.mk (⟨rsLift (f := f) w, rs_lift_perp w⟩ : perpS (VS D) F0.X) : WbQ D F0) =
      Submodule.Quotient.mk w := by
  apply (Submodule.Quotient.eq _).mpr
  show (((⟨rsLift (f := f) w, rs_lift_perp w⟩ : perpS (VS D) F0.X) - w : perpS (VS D) F0.X) : (VS D).V) ∈ F0.X
  simp only [Submodule.coe_sub, rsLift, sub_sub_cancel_left]
  exact neg_mem (sum_mem fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem rs_hT_f_lift (hf : PartnerOK D F0 f) (w : perpS (VS D) F0.X) (b : Fin D.R.rS) :
    (VS D).hT (f b) (rsLift (f := f) w) = 0 := by
  have hfe : ∀ a, (VS D).hT (f b) (F0.e a) = if a = b then 1 else 0 := by
    intro a
    have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f b)) = (VS D).hT (f b) (F0.e a) := by
      first
        | exact (VS D).herm (F0.e a) (f b)
        | exact (VS D).herm.eq (F0.e a) (f b)
    rw [← hs, hf.1 a b]
    split_ifs <;> simp

  simp only [rsLift, map_sub, map_sum, map_smul, hfe, smul_eq_mul, mul_ite, mul_one, mul_zero,
  Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

theorem rs_lift_mem (hf : PartnerOK D F0 f) (w : perpS (VS D) F0.X)
    (hw : (Submodule.Quotient.mk w : WbQ D F0) ∈ M) : rsLift (f := f) w ∈ lamC D F0 f M := by
  rw [rs_mem_lamC_perp (rs_lift_perp w)]
  refine ⟨?_, fun a => ?_⟩
  · rw [rs_lift_mk]
    exact hw
  · rw [rs_hT_f_lift hf w a]
    exact FractionalIdeal.zero_mem _

theorem rs_mof (hf : PartnerOK D F0 f) : Mof D F0 (lamC D F0 f M) = M := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : (VS D).V) ∈ lamC D F0 f M := hw
    exact ((rs_mem_lamC_perp w.2).1 hw').1
  · intro m hm
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨⟨rsLift (f := f) w, rs_lift_perp w⟩, rs_lift_mem hf w hm, ?_⟩
    exact rs_lift_mk w

end Flag

theorem lattice_flag_exists : LamFlag := by
  intro D u F0 f M hf hM
  exact ⟨rs_z_mem hf hM, rs_xlam hf, rs_prim hf hM, rs_mof hf⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section

open NumberField Module IsDedekindDomain Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

theorem nMPseudo_of (hE : JordanExists) (hD : DetLocal) (hC : CountExt) (hA : NormAssembly) : NMPseudo := by
  intro K F V ι _ _ _ _ _ _ _ _ _ _ _ _ _ h X x 𝔞 hcm hfix h2 hsymm hstar hne hind hspan hdet hint
  have hJ0 : (∏ i, 𝔞 i ^ 2) * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hne i))
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdet)
  have key : ∀ (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)), 𝔭.IsMaximal →
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          ((P.asIdeal.ramificationIdx (𝓞 F) * vJ h X (pbLat x 𝔞) 𝔭 : ℕ) : ℤ) := by
    intro 𝔭 P h𝔭 hP
    obtain ⟨b, a, hba⟩ := hE K F V ι h X x 𝔞 hcm hfix h2 hsymm hstar hne hind hspan hdet hint 𝔭 h𝔭
    have hcount : ∀ b' a', IsJordanIn h X (pbLat x 𝔞) 𝔭 b' a' →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          ((P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a' : ℕ) : ℤ) := by
      intro b' a' h'
      rw [hD K F V ι h X x 𝔞 hfix hstar hne hind hspan hdet 𝔭 b' a' h𝔭 h' P hP,
        hC K F _ 𝔭 P a' h𝔭 hP h'.2.2.2.2]
      rfl
    have he : P.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := by
      haveI := P.isPrime
      exact (Ideal.ramificationIdx_pos (R := 𝓞 F) P.asIdeal).ne'
    have hv : vJ h X (pbLat x 𝔞) 𝔭 = vJof 𝔭 a := by
      unfold vJ
      have hset : {v | ∃ b a, IsJordanIn h X (pbLat x 𝔞) 𝔭 b a ∧ v = vJof 𝔭 a} = {vJof 𝔭 a} := by
        ext v
        constructor
        · rintro ⟨b', a', h', rfl⟩
          have h3 := (hcount b' a' h').symm.trans (hcount b a hba)
          have h4 : P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a' = P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a := by
            exact_mod_cast h3
          exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) h4
        · rintro rfl
          exact ⟨b, a, hba, rfl⟩
      rw [hset, csInf_singleton]
    rw [hv]
    exact hcount b a hba
  exact hA K F h2 _ (vJ h X (pbLat x 𝔞)) hJ0 key

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
