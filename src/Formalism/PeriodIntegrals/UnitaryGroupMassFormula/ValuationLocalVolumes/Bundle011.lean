module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTSt
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle033
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

namespace VolTU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OS : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)

theorem mem_OEv (x : Fv F v ⊗[F] E) : x ∈ OEv (E := E) v ↔ x ∈ OS (E := E) v := Iff.rfl

theorem sc_mul (a b : Fv F v) : sc (E := E) v (a * b) = sc (E := E) v a * sc (E := E) v b := by
  simp [sc, Algebra.TensorProduct.tmul_mul_tmul]

theorem sc_one : sc (E := E) v (1 : Fv F v) = 1 := rfl

theorem sc_mul_eq_smul (c : Fv F v) (x : Fv F v ⊗[F] E) : sc (E := E) v c * x = c • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sc, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => rw [mul_add, hx, hy, smul_add]

theorem sc_mul_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : sc (E := E) v c * x ∈ OEv (E := E) v := by
  rw [mem_OEv] at hx ⊢
  rw [sc_mul_eq_smul]
  have := (OS (E := E) v).smul_mem (⟨c, hc⟩ : v.adicCompletionIntegers F) hx
  exact this

theorem val_le_one_mem {c : Fv F v} (hc : Valued.v c ≤ 1) : c ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) (v := v)).mpr hc

theorem unit_mul_mem_iff {c : Fv F v} (hc : Valued.v c = 1) (x : Fv F v ⊗[F] E) :
    sc (E := E) v c * x ∈ OEv (E := E) v ↔ x ∈ OEv (E := E) v := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  constructor
  · intro h
    have hi : Valued.v c⁻¹ ≤ 1 := by rw [map_inv₀, hc, inv_one]
    have := sc_mul_mem (E := E) v (val_le_one_mem v hi) h
    rwa [← mul_assoc, ← sc_mul, inv_mul_cancel₀ hc0, sc_one, one_mul] at this
  · intro h
    exact sc_mul_mem (E := E) v (val_le_one_mem v hc.le) h

theorem val_alp (hd : Valued.v (dV v) = 1) (r : ℕ) (a : Fin (r + 1)) : Valued.v (alp v r a) = 1 := by
  unfold alp
  split_ifs
  · rw [map_pow, map_inv₀, hd, inv_one, one_pow]
  · exact map_one _

theorem natCast_ne_zero {g : ℕ} (hg : g ≠ 0) : (g : Fv F v) ≠ 0 := Nat.cast_ne_zero.mpr hg

theorem natCast_memO (g : ℕ) : (g : Fv F v) ∈ v.adicCompletionIntegers F :=
  _root_.natCast_mem (v.adicCompletionIntegers F) g

theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem val_eq_one_of_absV {x : Fv F v} (h : absV v x = 1) : Valued.v x = 1 := by
  unfold absV at h
  split_ifs at h with h0
  · exact absurd h zero_ne_one
  · have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm v
    have hk : Multiplicative.toAdd (WithZero.unzero h0) = 0 :=
      (zpow_eq_one_iff_right₀ (by positivity) hN.ne').mp h
    have hu : WithZero.unzero h0 = 1 := by
      rw [← ofAdd_toAdd (WithZero.unzero h0), hk, ofAdd_zero]
    rw [← WithZero.coe_unzero h0, hu, WithZero.coe_one]

end VolTU


open VolTU in
theorem volTUOEq_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (hd : Valued.v (dV v) = 1) {g : ℕ} (hg : g ≠ 0) (r : ℕ) :
    VolTUOEq (E := E) v g r := by
  have key : ∀ (q : UIdx r) (y : Fv F v ⊗[F] E),
      sc (E := E) v ((alp v r q.1.1)⁻¹ * alp v r q.1.2) * y ∈ OEv (E := E) v ↔ y ∈ OEv (E := E) v := by
    intro q y
    apply VolTU.unit_mul_mem_iff
    simp only [map_mul, map_inv₀, VolTU.val_alp v hd, inv_one, one_mul]
  have e : ∀ (a b : Fv F v) (y : Fv F v ⊗[F] E),
      sc (E := E) v (a * b * (g : Fv F v)⁻¹) * y = sc (E := E) v (a * b) * (sc (E := E) v (g : Fv F v)⁻¹ * y) := by
    intro a b y
    rw [VolTU.sc_mul, mul_assoc]
  have hg0 := VolTU.natCast_ne_zero v hg
  have hgO := VolTU.natCast_memO v g
  have sw : ∀ y : Fv F v ⊗[F] E,
      y * sc (E := E) v (g : Fv F v)⁻¹ ∈ VolTU.OS (E := E) v ↔
        sc (E := E) v (g : Fv F v)⁻¹ * (-y) ∈ VolTU.OS (E := E) v := by
    intro y
    rw [mul_neg, Submodule.neg_mem_iff, mul_comm]
  unfold VolTUOEq
  ext p
  simp only [deepCongruenceVolume, VolTUSet, UO, Set.mem_setOf_eq, e, key]
  simp only [VolTU.mem_OEv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun q => ?_⟩
    rw [sw, neg_sub]
    exact h3 q
  · rintro ⟨h1, h3⟩
    have h3' : ∀ q, sc (E := E) v (g : Fv F v)⁻¹ * (p.1 q - p.2 q) ∈ VolTU.OS (E := E) v := fun q => by
      rw [← neg_sub, ← sw]
      exact h3 q
    refine ⟨h1, fun q => ?_, h3'⟩
    have h4 := (VolTU.OS (E := E) v).smul_mem (⟨(g : Fv F v), hgO⟩ : v.adicCompletionIntegers F) (h3' q)
    have h5 : p.1 q - p.2 q ∈ VolTU.OS (E := E) v := by
      have h6 : (g : Fv F v) • (sc (E := E) v (g : Fv F v)⁻¹ * (p.1 q - p.2 q)) ∈ VolTU.OS (E := E) v := h4
      rwa [← VolTU.sc_mul_eq_smul, ← mul_assoc, ← VolTU.sc_mul, mul_inv_cancel₀ hg0, VolTU.sc_one, one_mul] at h6
    have h7 : p.2 q = p.1 q - (p.1 q - p.2 q) := by abel
    rw [h7]
    exact (VolTU.OS (E := E) v).sub_mem (h1 q) h5

end Formalism.L2.SG.Pf.NcVal
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal TensorProduct

theorem volTProdU_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (g r : ℕ)
    [SFinite (sdE (E := E) ψ v (UIdx r))]
    (hM : MeasurableSet (VolTUSet (E := E) v g r)) (hMO : MeasurableSet (VolTO (E := E) v (UIdx r)))
    (hA : VolTAff (E := E) ψ v g (UIdx r)) (hO : VolTOne (E := E) ψ v (UIdx r)) :
    VolTProdU (E := E) ψ v g r := by
  unfold VolTProdU
  rw [Measure.prod_apply hM]
  have hsec : ∀ x : UIdx r → Fv F v ⊗[F] E,
      sdE (E := E) ψ v (UIdx r) (Prod.mk x ⁻¹' VolTUSet (E := E) v g r) =
        (VolTO (E := E) v (UIdx r)).indicator (fun _ => ((g : ℝ≥0∞) ^ (2 * Fintype.card (UIdx r)))⁻¹) x := by
    intro x
    by_cases hx : x ∈ VolTO (E := E) v (UIdx r)
    · rw [Set.indicator_of_mem hx]
      have hpre : Prod.mk x ⁻¹' VolTUSet (E := E) v g r =
          {w | (fun i => (w i - x i) * sc (E := E) v (g : Fv F v)⁻¹) ∈ VolTO (E := E) v (UIdx r)} := by
        ext y
        simp only [Set.mem_preimage, VolTUSet, VolTO, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
      rw [hpre, hA, hO, mul_one]
    · rw [Set.indicator_of_notMem hx]
      have hpre : Prod.mk x ⁻¹' VolTUSet (E := E) v g r = ∅ := by
        ext y
        simp only [Set.mem_preimage, VolTUSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hx h.1
      rw [hpre, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator_const hMO, mul_comm]

end Formalism.L2.SG.Pf.NcVal
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem volU_two_card_uidx (r : ℕ) : 2 * Fintype.card (UIdx r) = r * (r + 1) := by
  classical
  have hlt : Fintype.card (UIdx r) =
      (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 < p.2)).card :=
    Fintype.card_subtype _
  have hgt : (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 < p.2)).card =
      (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.2 < p.1)).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simpa using hp
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      exact ⟨(q.2, q.1), by simpa using hq, rfl⟩
  have heq : (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2)).card = r + 1 := by
    have : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2) =
        Finset.univ.map ⟨fun a : Fin (r + 1) => (a, a), fun a b h => by simpa using h⟩ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h; exact ⟨p.1, Prod.ext rfl h⟩
      · rintro ⟨a, rfl⟩; rfl
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (r + 1) × Fin (r + 1)))) (fun p => p.1 < p.2)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2)) (fun p => p.2 < p.1)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2 ∧ p.2 < p.1) =
      Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.2 < p.1) :=
    Finset.filter_congr (fun p _ => ⟨fun h => h.2, fun h => ⟨not_lt.mpr h.le, h⟩⟩)
  have e2 : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2 ∧ ¬ p.2 < p.1) =
      Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2) :=
    Finset.filter_congr (fun p _ => ⟨fun h => le_antisymm (not_lt.mp h.2) (not_lt.mp h.1),
      fun h => ⟨by rw [h]; exact lt_irrefl _, by rw [h]; exact lt_irrefl _⟩⟩)
  rw [e1, e2, heq] at h2
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
  have hsq : (r + 1) * (r + 1) = r * (r + 1) + (r + 1) := by ring
  omega

section OfX

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem volU_gAt_pos (v : PlX X) : 0 < gAt X v := by
  unfold gAt
  split_ifs
  · exact (D.host.g_prime 0).pos
  · exact (D.host.g_prime 1).pos

def VolUHyp : Prop :=
  IsCharAF X.B.I.F ψ ∧ IsStdChar ψ ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]

theorem volU_ratio (v : PlX X) (hZ : VolTZZAt X u u' ψ v) (hU : VolumeDeepCongruenceSubgroup X ψ v) :
    localVolumeUnit X ψ v / ZZX X u u' ψ v = (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) := by
  rw [hU, hZ]
  have hg : (gAt X v : ℝ) ≠ 0 := by exact_mod_cast (volU_gAt_pos X v).ne'
  rw [← zpow_sub₀ hg, ← zpow_natCast]
  congr 1
  push_cast
  ring

theorem volTypV_of' (h : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolTZZAt X u u' ψ v ∧ VolumeDeepCongruenceSubgroup X ψ v) :
    VolTypV X u u' ψ := by
  intro h1 h2 h3 v hv
  obtain ⟨hZ, hU⟩ := h ⟨h1, h2, h3⟩ v hv
  exact volU_ratio X u u' ψ v hZ hU

theorem volUZZAt_of (v : PlX X) (hv : TypAt X v)
    (hA : VolTAff (E := X.B.I.E) ψ v (gAt X v) (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (hL : VolTLocPres (E := X.B.I.E) ψ v D.R.rS)
    (hH : VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS)
    (hC : VolTTFCong X u u' v) : VolTZZAt X u u' ψ v := by
  unfold VolTZZAt ZZX volS
  rw [if_pos hv]
  have hset : ZZTyp X.B.I.cm.sig v (gAt X v) D.R.rS (TFv X u v) (TFv X u' v) =
      {z | (fun p => locZ (E := X.B.I.E) v z p.1 p.2) ∈
        {w | (fun p => (w p - TFv X u v p.1 p.2) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹) ∈
          VolTW X.B.I.cm.sig v (gAt X v) D.R.rS
            (fun i j => (TFv X u' v i j - TFv X u v i j) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹)}} := by
    rfl
  rw [hset, hL, hA, hH _ hC]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, zpow_neg, zpow_natCast, ← mul_inv, ← pow_add]
  congr 2
  ring

theorem volume_deep_congruence_of_fubini (v : PlX X) (hv : TypAt X v)
    (hE : VolTUOEq (E := X.B.I.E) v (gAt X v) D.R.rS)
    (hP : VolTProdU (E := X.B.I.E) ψ v (gAt X v) D.R.rS)
    (hO : VolTOne (E := X.B.I.E) ψ v (UIdx D.R.rS)) : VolumeDeepCongruenceSubgroup X ψ v := by
  unfold VolumeDeepCongruenceSubgroup localVolumeUnit volU
  rw [if_pos hv, hE, hP, hO, one_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    volU_two_card_uidx, zpow_neg, zpow_natCast]

def VolUSteps (v : PlX X) : Prop :=
  VolTAff (E := X.B.I.E) ψ v (gAt X v) (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ∧
      VolTLocPres (E := X.B.I.E) ψ v D.R.rS ∧ VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS ∧
      VolTTFCong X u u' v ∧ VolTUOEq (E := X.B.I.E) v (gAt X v) D.R.rS ∧
      VolTProdU (E := X.B.I.E) ψ v (gAt X v) D.R.rS ∧ VolTOne (E := X.B.I.E) ψ v (UIdx D.R.rS)

theorem volTypV_of_steps' (h : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolUSteps X u u' ψ v) :
    VolTypV X u u' ψ :=
  volTypV_of' X u u' ψ fun hh v hv =>
    ⟨volUZZAt_of X u u' ψ v hv (h hh v hv).1 (h hh v hv).2.1 (h hh v hv).2.2.1 (h hh v hv).2.2.2.1,
      volume_deep_congruence_of_fubini X ψ v hv (h hh v hv).2.2.2.2.1 (h hh v hv).2.2.2.2.2.1 (h hh v hv).2.2.2.2.2.2⟩

end OfX

end Formalism.L2.SG.Pf.NcVal
end
end
