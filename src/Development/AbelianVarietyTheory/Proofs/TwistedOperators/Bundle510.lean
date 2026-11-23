module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.EntireJetUniq


open Formalism.L2.KerInert.PullbackComparison in
theorem eq_of_applyAt0_monomial_eq : ∀ {D : D7} {N N' : ℕ} (Φ Ψ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ), Differentiable ℂ Φ → Differentiable ℂ Ψ → (∀ k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ, Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ = Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Ψ) → Φ = Ψ := by
  intro D N N' Φ Ψ hΦ hΨ h
  classical
  have aΦ := GlobalTheory.analyticOnNhd_of_differentiable_vc Φ hΦ
  have aΨ := GlobalTheory.analyticOnNhd_of_differentiable_vc Ψ hΨ
  have hmono : ∀ (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ),
      Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G =
        (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
    intro k G
    unfold Formalism.MainNotions.GL3Theta.applyAt0
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
      if_pos rfl, one_mul]
  have ht : ∀ α : Formalism.MainNotions.TaylorLogMetric.Mono D N N', Formalism.MainNotions.TaylorLogMetric.taylor D Φ α = Formalism.MainNotions.TaylorLogMetric.taylor D Ψ α := by
    intro α
    have h1 := h α
    rw [hmono, hmono] at h1
    have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    exact mul_left_cancel₀ hne h1
  have hd : ∀ (n : ℕ) (z : Formalism.MainNotions.TaylorLogMetric.VC D N N'),
      iteratedFDeriv ℂ n Φ 0 (fun _ => z) = iteratedFDeriv ℂ n Ψ 0 (fun _ => z) := by
    intro n z
    rw [iter_expand, iter_expand]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [iter_eq_taylor D Φ aΦ κ (ak D κ) (toMultiset_ak D κ).symm,
      iter_eq_taylor D Ψ aΨ κ (ak D κ) (toMultiset_ak D κ).symm, ht]
  obtain ⟨p, r, hp⟩ := aΦ 0 (Set.mem_univ _)
  obtain ⟨q, s, hq⟩ := aΨ 0 (Set.mem_univ _)
  refine aΦ.eq_of_eventuallyEq aΨ (z₀ := 0) ?_
  have hball : Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') (min r s) ∈ nhds 0 :=
    Metric.eball_mem_nhds 0 (lt_min hp.r_pos hq.r_pos)
  filter_upwards [hball] with y hy
  have hy1 : y ∈ Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') r :=
    Metric.eball_subset_eball (min_le_left _ _) hy
  have hy2 : y ∈ Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') s :=
    Metric.eball_subset_eball (min_le_right _ _) hy
  have s1 := hp.hasSum_iteratedFDeriv hy1
  have s2 := hq.hasSum_iteratedFDeriv hy2
  simp only [zero_add] at s1 s2
  simp only [hd] at s1
  exact s1.unique s2

end GlobalTheory.EntireJetUniq
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedDict.Entire

theorem differentiable_U' {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (U D T x G) := by
  have h : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
    unfold Hf
    fun_prop
  unfold U
  fun_prop

theorem differentiable_Iop' {D : D7} {T : Tor D} {N N' : ℕ} (A B : AddSubgroup (VC D N N'))
    {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) : Differentiable ℂ (Iop D T A B G) := by
  unfold Iop
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    simp only [finsum_eq_sum_of_fintype]
    exact (Differentiable.fun_sum fun q _ => (differentiable_U' _ hG).const_mul _).const_mul _

end GlobalTheory.MovedDict.Entire
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappaDec

theorem eqAt_refl {D : D7} {N : ℕ} (q : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : EqAt D q L L := by
  refine ⟨1, Nat.coprime_one_left q, ?_, ?_⟩ <;>
  · intro x hx
    rwa [Nat.cast_one, one_smul]

theorem eqAt_symm {D : D7} {N : ℕ} {q : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : EqAt D q L L₁) :
    EqAt D q L₁ L := by
  obtain ⟨s, hcop, hto, hback⟩ := h
  exact ⟨s, hcop, hback, hto⟩

theorem eqAt_trans {D : D7} {N : ℕ} {q : ℕ} {L L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : EqAt D q L L₁)
    (h' : EqAt D q L₁ L₂) : EqAt D q L L₂ := by
  obtain ⟨a, ha, hL₁, hL₁'⟩ := h
  obtain ⟨b, hb, hL₂, hL₂'⟩ := h'
  refine ⟨a * b, Nat.Coprime.mul_left ha hb, fun x hx => ?_, fun x hx => ?_⟩
  ·
    have h1 : ((b : D.host.E) • ((a : D.host.E) • x)) ∈ L₂ := hL₂ _ (hL₁ x hx)
    rwa [smul_smul, mul_comm, ← Nat.cast_mul] at h1
  ·
    have h1 : ((a : D.host.E) • ((b : D.host.E) • x)) ∈ L := hL₁' _ (hL₂' x hx)
    rwa [smul_smul, ← Nat.cast_mul] at h1

end GlobalTheory.MovedKappaDec

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedKappaArith

theorem selfDualIntertwiner_baseVector_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' : ℕ} {e0 : VC D N N' → ℂ} (he : oddE0 D cc δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') e0 ≠ 0 := by
  have s0 := GlobalTheory.MovedVacuum.sd_stdL D N
  have s0' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, s0, s0', rfl⟩
  have k1 : KLat D (tor0 D cc δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ k0 k1
  intro h
  exact GlobalTheory.TrueTheta.ne_zero_of_like hC ht s0 s0' he.2.2.2.1
    (by rw [← (huni e0 he.1).2.2.2, h, GlobalTheory.VacuumScalar.Iop_zero])

theorem applyAt0_monomial (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]

end GlobalTheory.MovedKappaArith

namespace GlobalTheory.MovedKappaArith

end GlobalTheory.MovedKappaArith

namespace GlobalTheory.MovedKappaArith

end GlobalTheory.MovedKappaArith
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem mem_iSup_jointEigen_inf_of_stable : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (G P : Submodule ℂ E) (C : Finset (ι → ℂ)),
    (∀ i, ∀ x ∈ G, F i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x) → P ≤ G → (∀ i, ∀ x ∈ P, F i x ∈ P) →
    (∀ x ∈ G, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h}) →
    ∀ x ∈ P, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
  intro E ι _ _ F G P C hFG hadd hsmul hPG hFP hdec
  have hF0 : ∀ i, F i 0 = 0 := by
    intro i
    have := hsmul i 0 0 G.zero_mem
    simpa using this
  obtain ⟨V, hV⟩ : ∃ V : (ι → ℂ) → Submodule ℂ E,
      ∀ c x, x ∈ V c ↔ (x ∈ G ∧ ∀ i, F i x = c i • x) :=
    ⟨fun c =>
      { carrier := {h | h ∈ G ∧ ∀ i, F i h = c i • h}
        add_mem' := by
          rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
          refine ⟨G.add_mem hx hy, fun i => ?_⟩
          rw [hadd i x hx y hy, hx' i, hy' i, smul_add]
        zero_mem' := ⟨G.zero_mem, fun i => by rw [hF0 i, smul_zero]⟩
        smul_mem' := by
          rintro a x ⟨hx, hx'⟩
          refine ⟨G.smul_mem a hx, fun i => ?_⟩
          rw [hsmul i a x hx, hx' i]
          exact smul_comm _ _ _ }, fun c x => Iff.rfl⟩
  have hVG : ∀ c, V c ≤ G := fun c x hx => ((hV c x).1 hx).1
  have hSG : ∀ s : Finset (ι → ℂ), (⨆ c ∈ s, V c) ≤ G := fun s => iSup₂_le fun c _ => hVG c
  have hmemS : ∀ (s : Finset (ι → ℂ)) c, c ∈ s → V c ≤ ⨆ c ∈ s, V c := fun s c hc =>
    le_iSup₂_of_le (f := fun c (_ : c ∈ s) => V c) c hc le_rfl
  have hT : ∀ (i : ι) (b : ℂ) (s : Finset (ι → ℂ)), ∀ z ∈ ⨆ c ∈ s, V c,
      F i z - b • z ∈ ⨆ c ∈ s, V c := by
    intro i b s
    obtain ⟨M, hM⟩ : ∃ M : Submodule ℂ E,
        ∀ v, v ∈ M ↔ (v ∈ G ∧ F i v - b • v ∈ ⨆ c ∈ s, V c) :=
      ⟨{ carrier := {v | v ∈ G ∧ F i v - b • v ∈ ⨆ c ∈ s, V c}
         add_mem' := by
           rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
           refine ⟨G.add_mem hx hy, ?_⟩
           have : F i (x + y) - b • (x + y) = (F i x - b • x) + (F i y - b • y) := by
             rw [hadd i x hx y hy, smul_add]; abel
           rw [this]; exact Submodule.add_mem _ hx' hy'
         zero_mem' := ⟨G.zero_mem, by simp [hF0 i]⟩
         smul_mem' := by
           rintro a x ⟨hx, hx'⟩
           refine ⟨G.smul_mem a hx, ?_⟩
           have : F i (a • x) - b • (a • x) = a • (F i x - b • x) := by
             rw [hsmul i a x hx, smul_sub, smul_comm b a x]
           rw [this]; exact Submodule.smul_mem _ a hx' }, fun v => Iff.rfl⟩
    have hle : (⨆ c ∈ s, V c) ≤ M := iSup₂_le fun c hc v hv => by
      rw [hM]
      obtain ⟨hvG, hv'⟩ := (hV c v).1 hv
      refine ⟨hvG, ?_⟩
      rw [hv' i, ← sub_smul]
      exact hmemS s c hc ((V c).smul_mem _ hv)
    intro z hz
    exact ((hM z).1 (hle hz)).2
  have hB : ∀ (a : ι → ℂ) (s : Finset (ι → ℂ)), a ∉ s → ∀ y ∈ V a, ∀ z ∈ ⨆ c ∈ s, V c,
      y + z ∈ P → y ∈ P := by
    intro a s
    induction s using Finset.induction_on with
    | empty =>
      intro _ y _ z hz hyz
      simp at hz
      rw [hz, add_zero] at hyz; exact hyz
    | insert b t hbt ih =>
      intro ha y hy z hz hyz
      rw [Finset.mem_insert, not_or] at ha
      obtain ⟨hab, hat⟩ := ha
      rw [Finset.iSup_insert, Submodule.mem_sup] at hz
      obtain ⟨zb, hzb, zt, hzt, rfl⟩ := hz
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hab
      obtain ⟨hyG, hy'⟩ := (hV a y).1 hy
      obtain ⟨hzbG, hzb'⟩ := (hV b zb).1 hzb
      have hztG := hSG t hzt
      have hP1 : F i (y + (zb + zt)) - b i • (y + (zb + zt)) ∈ P :=
        P.sub_mem (hFP i _ hyz) (P.smul_mem _ hyz)
      have heq : F i (y + (zb + zt)) - b i • (y + (zb + zt))
          = (a i - b i) • y + (F i zt - b i • zt) := by
        rw [hadd i y hyG _ (G.add_mem hzbG hztG), hadd i zb hzbG zt hztG, hy' i, hzb' i]
        simp only [smul_add, sub_smul]; abel
      rw [heq] at hP1
      have hy2 : (a i - b i) • y ∈ V a := (V a).smul_mem _ hy
      have h3 := ih hat _ hy2 _ (hT i (b i) t zt hzt) hP1
      have hne : a i - b i ≠ 0 := sub_ne_zero.2 hi
      have h4 := P.smul_mem (a i - b i)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
  have hspan : ∀ c, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h} = V c := fun c =>
    le_antisymm (Submodule.span_le.2 fun x hx => (hV c x).2 hx)
      fun x hx => Submodule.subset_span ((hV c x).1 hx)
  have hmain : ∀ s : Finset (ι → ℂ), ∀ x ∈ P, x ∈ ⨆ c ∈ s, V c →
      x ∈ ⨆ c ∈ s, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ hx; simpa using hx
    | insert a s has ih =>
      intro x hxP hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      have hyP : y ∈ P := hB a s has y hy z hz hxP
      have hzP : z ∈ P := by
        have := P.sub_mem hxP hyP; simpa using this
      rw [Finset.iSup_insert]
      exact Submodule.mem_sup.2 ⟨y, Submodule.subset_span ⟨hyP, ((hV a y).1 hy).2⟩, z, ih z hzP hz, rfl⟩
  intro x hx
  have h := hdec x (hPG hx)
  simp only [hspan] at h
  exact hmain C x hx h

end GlobalTheory
end
