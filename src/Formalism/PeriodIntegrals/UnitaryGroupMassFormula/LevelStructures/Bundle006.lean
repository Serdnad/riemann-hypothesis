module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.StabilizerPreservesComplement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobProdOfK2Loc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uLeKfHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
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

@[expose] public section

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

def LeviComp : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X) (s : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    s ∈ Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    ∃ h ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w),
      ∀ u, InXperp (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) u →
        lin _ X.B.I.cm.sig X.B.I.J s u - lin _ X.B.I.cm.sig X.B.I.J h u ∈
          spanR (F := X.B.I.F) (Fv X.B.I.F p.1) (frameOf X w).e Set.univ

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem parabolic_unipotent_on_flag {r : ℕ} (P : Frame E n r) {s : HA R σ J} (hs : s ∈ Ssub R σ J P) (b : Fin r) :
    lin R σ J s (ratV (F := F) R (P.e b)) - ratV (F := F) R (P.e b) ∈ spanR (F := F) R P.e {a | a < b} := by
  have h := hs (Fin.castSucc b)
  have e : F0 P (Fin.castSucc b) = P.e b := by simp [F0]
  rw [e] at h
  refine (Submodule.span_le.2 ?_) h
  rintro _ ⟨a, ha, rfl⟩
  have hne : a ≠ Fin.last r := fun hl => by
    rw [hl] at ha
    exact absurd ha (not_lt.2 (Fin.castSucc_lt_last b).le)
  obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 hne
  have ha' : a' < b := Fin.castSucc_lt_castSucc_iff.1 ha
  have e' : F0 P (Fin.castSucc a') = P.e a' := by simp [F0]
  show ratV (F := F) R (F0 P (Fin.castSucc a')) ∈ spanR (F := F) R P.e {a | a < b}
  rw [e']
  exact Submodule.subset_span ⟨a', ha', rfl⟩

theorem mul_inv_mem_Nsub_of_same_perp_action {r : ℕ} (P : Frame E n r) {s h : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hh : h ∈ Hsub R σ J P)
    (hsh : ∀ u, InXperp R σ J P u → lin R σ J s u - lin R σ J h u ∈ spanR (F := F) R P.e Set.univ) :
    s * h⁻¹ ∈ Nsub R σ J P := by
  have hh' : h⁻¹ ∈ Hsub R σ J P := inv_mem hh
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [lin_mul, stabilizer_fixes_isotropic_e P hh' b]
    exact parabolic_unipotent_on_flag P hs b
  · have hu : InXperp R σ J P (lin R σ J h⁻¹ v) := by
      intro a
      rw [← stabilizer_fixes_isotropic_e P hh' a, hR_lin]
      exact hv a
    have := hsh _ hu
    rw [lin_lin_inv] at this
    rw [lin_mul]
    exact this

end Gen

theorem leviRat_of (hc : LeviComp) : LeviRat := by
  intro D X w p s hs
  obtain ⟨h, hh, hsh⟩ := hc X w p s hs
  exact ⟨s * h⁻¹, h, mul_inv_mem_Nsub_of_same_perp_action (frameOf X w) hs hh hsh, hh, by group⟩

theorem locLevi_of_comp (hc : LeviComp) (hN : UnipotentIntegralInLevel) : LocLevi :=
  locLevi_of (leviRat_of hc) leviIntH hN

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

def KgLoc : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (κ : X.B.I.Gf), κ ∈ X.B.I.Kset →
    (∀ p : TypX X, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ) = 1) → κ ∈ X.B.I.Kg X.B.g

def LevelCongruenceTypedPlaces : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized → ∀ κ : X.B.I.Gf,
    κ ∈ X.B.I.Kset →
    (∀ v, v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1) →
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ) = 1) →
    (∀ p : TypX X, ∃ κ' ∈ X.K2,
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ) =
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ')) → κ ∈ X.K2

theorem level_local_of_typed (hg : KgLoc) (ht : LevelCongruenceTypedPlaces) : LevelCongruenceLocal := by
  intro D X hb hK hL κ hκ hloc
  classical
  obtain ⟨h, hT, hO⟩ := glueHA_holds X
    (fun p => haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ))
  obtain ⟨κt, hκt⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb h
  have hκtf : finHA X hb κt = h := hκt
  have hκf : finHA X hb κ ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    finHA_mem_Kf X hb κ hκ
  have hhK : h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    refine Subgroup.mem_iInf.2 fun v => ?_
    have hv' : haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v := by
      by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
      · have e := hT ⟨v, hv⟩
        simp only at e
        rw [e]
        exact compK_holds X v _ hκf
      · rw [hO v hv]
        exact Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    exact hv'
  have hκtK : κt ∈ X.B.I.Kset := by
    refine (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb κt).1 ?_
    change finHA X hb κt ∈ _
    rw [hκtf]
    exact hhK
  have hrK : κt⁻¹ * κ ∈ X.B.I.Kset := by
    refine (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb _).1 ?_
    change finHA X hb (κt⁻¹ * κ) ∈ _
    rw [finHA_mul, finHA_inv, hκtf]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hhK) hκf
  have hrest : κt⁻¹ * κ ∈ X.B.I.Kg X.B.g := hg X hb _ hrK (fun p => by
    rw [finHA_mul, finHA_inv, map_mul, map_inv, hκtf, hT p]
    exact inv_mul_cancel _)
  have hκt2 : κt ∈ X.K2 := ht X hb hK hL κt hκtK (fun v hv => by rw [hκtf]; exact hO v hv)
    (fun p => by
      obtain ⟨κ', hκ', e⟩ := hloc p
      exact ⟨κ', hκ', by rw [hκtf, hT p]; exact e⟩)
  have hr2 : κt⁻¹ * κ ∈ X.K2 := (hL.1 _ hrest).1
  have hprod := hK.2.1 _ hκt2 _ hr2
  rwa [mul_inv_cancel_left] at hprod

theorem globProd_of_loc (hg : KgLoc) (ht : LevelCongruenceTypedPlaces) : GlobProd := globProd_of_k2Loc (level_local_of_typed hg ht)

end MassDataLevelSSteps
end
end
