module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FrameOp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerS2
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpRootCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle009
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpTrans
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle003

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.S.Pv.ClassCounting

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW
  PI.TermsAtPtFiniteW.HeisW PI.TermsAtPtFiniteW.LeviW PI.TermsAtPtFiniteW.FrameW Formalism.L2.SG.Saturated

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem psiF_f (e f : Fin r → S.V) (U U' : Matrix (Fin r) (Fin r) E) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0) (j : Fin r) :
    psiF e f U U' (f j) = ∑ c, U' c j • f c := by
  rw [psiF_apply]
  simp only [hff, hef, zero_smul, Finset.sum_const_zero, add_zero, ite_smul, one_smul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

theorem levi_mem (Λ : Submodule (𝓞 E) S.V) (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (e f : Fin r → S.V) (L : Submodule (𝓞 E) S.V)
    (hΛ : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
    (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
    (hL : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0)
    (haa : ∀ a c : Fin r, c ≤ a → aa a ≤ aa c) (haa0 : ∀ a, aa a ≠ 0)
    (U U' : Matrix (Fin r) (Fin r) E)
    (hU : ∀ c a, (a < c → U c a = 0) ∧ ∃ o : 𝓞 E, (o : E) = U c a)
    (hU' : ∀ c a, (c < a → U' c a = 0) ∧ ∃ o : 𝓞 E, (o : E) = U' c a)
    {v : S.V} (hv : v ∈ Λ) : psiF e f U U' v ∈ Λ := by
  have hA : ∀ y ∈ latSpan aa e, psiF e f U U' y ∈ latSpan aa e := by
    intro y hy
    unfold latSpan at hy ⊢
    induction hy using Submodule.span_induction with
    | zero => simp
    | add y y' _ _ h h' => rw [map_add (f := _)]; exact Submodule.add_mem _ h h'
    | smul o y _ h => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ o h
    | mem y hy =>
    obtain ⟨a, x, hx, rfl⟩ := hy
    rw [map_smul, psiF_e e f hef U U' hee, Finset.smul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [smul_smul]
    rcases lt_or_ge a c with h | h
    · rw [(hU c a).1 h, mul_zero, zero_smul]
      exact Submodule.zero_mem _
    · obtain ⟨o, ho⟩ := (hU c a).2
      refine Submodule.subset_span ⟨c, x * U c a, haa a c h ?_, rfl⟩
      rw [← ho, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ o hx
  have hC : ∀ y ∈ latSpan (fun a => (aa a)⁻¹) f, psiF e f U U' y ∈ latSpan (fun a => (aa a)⁻¹) f := by
    intro y hy
    unfold latSpan at hy ⊢
    induction hy using Submodule.span_induction with
    | zero => simp
    | add y y' _ _ h h' => rw [map_add (f := _)]; exact Submodule.add_mem _ h h'
    | smul o y _ h => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ o h
    | mem y hy =>
    obtain ⟨a, x, hx, rfl⟩ := hy
    rw [map_smul, psiF_f e f U U' hff hef, Finset.smul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [smul_smul]
    rcases lt_or_ge c a with h | h
    · rw [(hU' c a).1 h, mul_zero, zero_smul]
      exact Submodule.zero_mem _
    · obtain ⟨o, ho⟩ := (hU' c a).2
      refine Submodule.subset_span ⟨c, x * U' c a, ?_, rfl⟩
      have hle : (aa a)⁻¹ ≤ (aa c)⁻¹ := FractionalIdeal.inv_anti_mono (haa0 c) (haa c a h)
      refine hle ?_
      rw [← ho, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ o hx
  rw [hΛ] at hv ⊢
  obtain ⟨v12, hv12, v3, hv3, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.mp hv12
  rw [map_add (f := _), map_add (f := _), psiF_fix e f U U' v2 (fun a => (hL v2 hv2 a).2) (fun a => (hL v2 hv2 a).1)]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left (hA _ hv1)))
    (Submodule.mem_sup_left (Submodule.mem_sup_right hv2))) (Submodule.mem_sup_right (hC _ hv3))

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ddS_pow_le_one (D : D7) (n : ℕ) : ddS D ^ n ≤ 1 := by
  unfold ddS
  rw [← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

theorem aaS_mono (D : D7) (a c : Fin D.R.rS) (h : c ≤ a) : aaS D a ≤ aaS D c := by
  rw [PI.TermsAtPtFiniteW.FrameW.aaS_eq, PI.TermsAtPtFiniteW.FrameW.aaS_eq]
  refine FractionalIdeal.inv_anti_mono (pow_ne_zero _ (PI.SRW.ddS_ne D)) ?_
  have e : ddS D ^ (D.R.rS - c.1) = ddS D ^ (D.R.rS - a.1) * ddS D ^ (a.1 - c.1) := by
    rw [← pow_add]
    congr 1
    have := a.2
    have : c.1 ≤ a.1 := h
    omega
  rw [e, FractionalIdeal.mul_le]
  intro i hi j hj
  have hj1 := ddS_pow_le_one D (a.1 - c.1) hj
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).mp hj1
  rw [← ho, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ o hi

theorem aaS_ne (D : D7) (a : Fin D.R.rS) : aaS D a ≠ 0 := by
  rw [PI.TermsAtPtFiniteW.FrameW.aaS_eq]
  exact inv_ne_zero (pow_ne_zero _ (PI.SRW.ddS_ne D))

end D7

end Formalism.L2.S.Pv.ClassCounting

end
end

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal Pointwise

namespace Formalism.L2.S.Pv.FolnerG

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW PI.QuotSetU.UnitaryGroupMassFormula.ModW PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
  Formalism.L2.S.Pv.FolnerAbs Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.FolnerS

variable {k r : ℕ} {ι : Type} [Fintype ι] (z : ι → Fin (2 * r + k + 1) → ℂ)

def SP : Set (ι → GH k r) := {s | ∀ v, s v ∈ Sg k r (z v)}

def CP : Set (ι → GH k r) := {s | ∀ v, s v ∈ Cg k r (z v)}

def fP (s : ι → GH k r) : ℝ := ∑ v, fG k r (z v) (s v)

variable {z}

theorem fG_nonneg (z0 : Fin (2 * r + k + 1) → ℂ) (g : GH k r) : 0 ≤ fG k r z0 g := by
  unfold fG
  refine Real.sInf_nonneg ?_
  rintro _ ⟨c, -, rfl⟩
  unfold nrm; positivity

theorem cjB_pi (b s : ι → GH k r) (v : ι) : cjB b s v = cjB (b v) (s v) := rfl

theorem isFolner_pi (hz : ∀ v, inWb k r (z v)) (hT : ∀ v, 0 < Tz k r (z v)) (μS : Measure (ι → GH k r))
    (hμ : IsHaarSub (SP z) μS) : IsFolner (SP z) μS := by
  have hCc : IsCompact (CP z) := by
    have : CP z = Set.pi Set.univ (fun v => Cg k r (z v)) := by ext s; simp [CP, Set.mem_pi]
    rw [this]; exact isCompact_univ_pi fun v => isCompact_Cg (hz v) (hT v)
  refine isFolner_of_contract hμ (CP z) (fP z) ?_ ?_ ?_ (fun _ => aT k r) ?_ ?_
  · exact continuous_finsetSum _ fun v _ => (continuous_fG (hz v) (hT v)).comp (continuous_apply v)
  · intro c hc x
    unfold fP
    exact Finset.sum_congr rfl fun v _ => fG_mul_left (hc v) (x v)
  · intro ρ
    have hsub : {x | fP z x ≤ ρ} ∩ SP z ⊆ Set.pi Set.univ (fun v => {y | fG k r (z v) y ≤ ρ} ∩ Sg k r (z v)) := by
      rintro s ⟨hs, hsS⟩ v -
      refine ⟨?_, hsS v⟩
      show fG k r (z v) (s v) ≤ ρ
      refine le_trans ?_ hs
      exact Finset.single_le_sum (f := fun w => fG k r (z w) (s w)) (fun w _ => fG_nonneg _ _) (Finset.mem_univ v)
    refine (isCompact_univ_pi fun v => isCompact_sublevel (hz v) (hT v) ρ).of_isClosed_subset ?_ hsub
    refine (isClosed_le (continuous_finsetSum _ fun v _ => (continuous_fG (hz v) (hT v)).comp (continuous_apply v))
      continuous_const).inter ?_
    have : SP z = ⋂ v, (fun s : ι → GH k r => s v) ⁻¹' Sg k r (z v) := by ext s; simp [SP]
    rw [this]
    exact isClosed_iInter fun v => (isClosed_Sg (hz v) (hT v)).preimage (continuous_apply v)
  · intro s
    show (∀ v, s v ∈ Sg k r (z v)) ↔ ∀ v, cjB (fun _ => aT k r) s v ∈ Sg k r (z v)
    exact forall_congr' fun v => by rw [cjB_pi]; exact aT_iff (z v) (s v)
  · intro K hK hKS U hU hCU
    obtain ⟨V, hV, hCV⟩ := compact_open_separated_mul_right hCc hU hCU
    rw [nhds_pi, Filter.mem_pi'] at hV
    obtain ⟨I, t, ht, hIt⟩ := hV
    have hev : ∀ v, ∀ᶠ m : ℕ in atTop, ∀ x ∈ (fun s : ι → GH k r => s v) '' K,
        cjB (aT k r ^ m) x ∈ Cg k r (z v) * t v := fun v =>
      contractV (hz v) (hT v) _ (hK.image (continuous_apply v)) (by rintro _ ⟨s, hs, rfl⟩; exact hKS hs v) (t v) (ht v)
    filter_upwards [Filter.eventually_all.2 hev] with m hm x hx
    have hx' : ∀ v, cjB (aT k r ^ m) (x v) ∈ Cg k r (z v) * t v := fun v => hm v (x v) ⟨x, hx, rfl⟩
    choose c hc w hw hcw using hx'
    refine hCV ⟨c, hc, w, hIt (fun v _ => hw v), ?_⟩
    funext v
    show c v * w v = cjB ((fun _ => aT k r) ^ m) x v
    rw [cjB_pi, Pi.pow_apply]
    exact hcw v

end Formalism.L2.S.Pv.FolnerG
end
end

section

namespace Formalism.L2.S.Pv.AmpFinal

open Formalism.MainNotions.S.Pv.LemmaJ

theorem rootCmp_of_parts (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt) : RootCmp :=
  rootCmp_of Formalism.L2.S.Pv.AmpCell.cell_representation Formalism.MainNotions.S.Pv.AmpTrans.amplitude_transport hRJ hRH hOQ hRA

theorem ampUnif_of_parts (hAO : AmpOrbU) (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt)
    (hNZ : AmpNZ) : AmpUnif :=
  ampUnif_of' hAO (rootCmp_of_parts hRJ hRH hOQ hRA) hNZ

end Formalism.L2.S.Pv.AmpFinal
end
