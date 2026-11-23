module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle314
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Formalism.PeriodIntegrals.Bundle024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle129
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProductChartTangentEquivBallVolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle315
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.IsotConjFix

open Formalism.IndefR.principalLevelFrame

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem rt_apply (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) (g : Formalism.AUTREP.GAf L n) :
    Formalism.L2.NG.rt L n h f g = f (g * h) := rfl

theorem range_equivariantMap_stable {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) (h : Formalism.AUTREP.GAf L n) (y : A) (hy : y ∈ LinearMap.range Φ) :
    ρ h y ∈ LinearMap.range Φ := by
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hy
  exact ⟨_, hΦ h f⟩

theorem zero_or_inj {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) : Φ = 0 ∨ Function.Injective Φ := by
  let K : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := (LinearMap.ker Φ).map σ.S.subtype
  have hle : K ≤ σ.S := by
    rintro _ ⟨f, -, rfl⟩
    exact f.2
  have hst : ∀ h, ∀ f ∈ K, Formalism.L2.NG.rt L n h f ∈ K := by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨⟨_, σ.stable h f f.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hf ⊢
    rw [hΦ h f, hf, map_zero]
  rcases σ.irr K hle hst with hK | hK
  · right
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := ⟨f, hf, rfl⟩
    rw [hK, Submodule.mem_bot] at hm
    exact (Submodule.mem_bot _).2 (Subtype.ext hm)
  · left
    apply LinearMap.ext
    intro f
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := by rw [hK]; exact f.2
    obtain ⟨g, hg, hgf⟩ := hm
    have e : g = f := Subtype.ext hgf
    subst e
    simpa using hg

theorem inf_bot_or_le {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) (W : Submodule ℂ A) (hW : ∀ h, ∀ y ∈ W, ρ h y ∈ W) :
    LinearMap.range Φ ⊓ W = ⊥ ∨ LinearMap.range Φ ≤ W := by
  let K : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := (W.comap Φ).map σ.S.subtype
  have hle : K ≤ σ.S := by
    rintro _ ⟨f, -, rfl⟩
    exact f.2
  have hst : ∀ h, ∀ f ∈ K, Formalism.L2.NG.rt L n h f ∈ K := by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨⟨_, σ.stable h f f.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap] at hf ⊢
    rw [hΦ h f]
    exact hW h _ hf
  rcases σ.irr K hle hst with hK | hK
  · left
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf, LinearMap.mem_range] at hy
    obtain ⟨⟨f, rfl⟩, hy⟩ := hy
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := ⟨f, hy, rfl⟩
    rw [hK, Submodule.mem_bot] at hm
    have e : f = 0 := Subtype.ext hm
    rw [e, map_zero]
    exact Submodule.zero_mem _
  · right
    intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨f, rfl⟩ := hy
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := by rw [hK]; exact f.2
    obtain ⟨g, hg, hgf⟩ := hm
    have e : g = f := Subtype.ext hgf
    subst e
    exact hg

def Indep {J : Type} (R : J → Submodule ℂ A) (t : Finset J) : Prop :=
  ∀ v : J → A, (∀ j ∈ t, v j ∈ R j) → ∑ j ∈ t, v j = 0 → ∀ j ∈ t, v j = 0

theorem select {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {J : Type} [DecidableEq J] (R : J → Submodule ℂ A)
    (hst : ∀ j h, ∀ y ∈ R j, ρ h y ∈ R j)
    (hirr : ∀ j (W : Submodule ℂ A), (∀ h, ∀ y ∈ W, ρ h y ∈ W) → R j ⊓ W = ⊥ ∨ R j ≤ W) (s : Finset J) :
    ∃ t ⊆ s, Indep R t ∧ ⨆ j ∈ t, R j = ⨆ j ∈ s, R j := by
  have stab : ∀ t : Finset J, ∀ h, ∀ y ∈ ⨆ j ∈ t, R j, ρ h y ∈ ⨆ j ∈ t, R j := by
    intro t h y hy
    have hle : (⨆ j ∈ t, R j) ≤ (⨆ j ∈ t, R j).comap (ρ h) := by
      refine iSup₂_le fun j hj => ?_
      intro z hz
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => R j) j hj) (hst j h z hz)
    exact hle hy
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, subset_rfl, fun v _ _ j hj => by simp at hj, rfl⟩
  | insert k s hk ih =>
    obtain ⟨t, hts, hind, heq⟩ := ih
    rcases hirr k (⨆ j ∈ t, R j) (stab t) with hd | hle
    · have hkt : k ∉ t := fun h => hk (hts h)
      refine ⟨insert k t, Finset.insert_subset_insert k hts, ?_, ?_⟩
      · intro v hv hsum j hj
        rw [Finset.sum_insert hkt] at hsum
        have hvk : v k = 0 := by
          have h1 : v k ∈ R k ⊓ ⨆ j ∈ t, R j := by
            refine Submodule.mem_inf.2 ⟨hv k (Finset.mem_insert_self k t), ?_⟩
            have e : v k = -∑ j ∈ t, v j := eq_neg_of_add_eq_zero_left hsum
            rw [e]
            refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
            exact le_iSup₂ (f := fun j (_ : j ∈ t) => R j) j hj (hv j (Finset.mem_insert_of_mem hj))
          rw [hd] at h1
          exact (Submodule.mem_bot _).1 h1
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hvk
        · rw [hvk, zero_add] at hsum
          exact hind v (fun i hi => hv i (Finset.mem_insert_of_mem hi)) hsum j hj
      · rw [Finset.iSup_insert, Finset.iSup_insert, heq]
    · refine ⟨t, hts.trans (Finset.subset_insert k s), hind, ?_⟩
      rw [Finset.iSup_insert, ← heq, sup_eq_right.2 hle]

theorem fix_sum_of_mem {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n}
    (P : (σ.S →ₗ[ℂ] A) → Prop) (U : Set (Formalism.AUTREP.GAf L n)) {ι : Type} [Fintype ι] (b : ι → ℂ)
    (lf : ι → Formalism.AUTREP.GAf L n)
    (H : ∀ ψ ∈ σ.S, (∀ κ ∈ U, Formalism.L2.NG.rt L n κ ψ = ψ) → ∑ i, b i • Formalism.L2.NG.rt L n (lf i) ψ = ψ)
    (x : A) (hx : x ∈ ⨆ (Φ : σ.S →ₗ[ℂ] A) (_ : IsEqvA ρ σ Φ ∧ P Φ), LinearMap.range Φ)
    (hU : ∀ κ ∈ U, ρ κ x = x) : ∑ i, b i • ρ (lf i) x = x := by
  classical
  let J := {Φ : σ.S →ₗ[ℂ] A // IsEqvA ρ σ Φ ∧ P Φ}
  let R : J → Submodule ℂ A := fun j => LinearMap.range j.1
  rw [iSup_subtype'] at hx
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  obtain ⟨t, -, hind, heq⟩ := select (ρ := ρ) R (fun j h y hy => range_equivariantMap_stable j.2.1 h y hy)
    (fun j W hW => inf_bot_or_le j.2.1 W hW) s
  rw [← heq] at hs
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 hs
  have hψ : ∀ j : J, ∃ ψ : σ.S, j.1 ψ = μ j := fun j => LinearMap.mem_range.1 (μ j).2
  choose ψ hψ using hψ
  have hx' : x = ∑ j ∈ t, j.1 (ψ j) := by
    rw [← hμ]
    exact Finset.sum_congr rfl fun j _ => (hψ j).symm
  have hfix : ∀ j ∈ t, ∀ κ ∈ U, j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ = j.1 (ψ j) := by
    intro j hj κ hκ
    have h0 := hind (fun j => j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ - j.1 (ψ j))
      (fun j _ => Submodule.sub_mem _ (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)) ?_ j hj
    · exact sub_eq_zero.1 h0
    · rw [Finset.sum_sub_distrib]
      have e : ∑ j ∈ t, j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ = ρ κ x := by

        rw [hx', map_sum]
        exact Finset.sum_congr rfl fun j _ => j.2.1 κ (ψ j)
      rw [e, hU κ hκ, ← hx', sub_self]
  have hterm : ∀ j ∈ t, ∑ i, b i • ρ (lf i) (j.1 (ψ j)) = j.1 (ψ j) := by
    intro j hj
    rcases zero_or_inj j.2.1 with h0 | hinj
    · simp [h0]
    · have hψfix : ∀ κ ∈ U, Formalism.L2.NG.rt L n κ ((ψ j : σ.S) : Formalism.AUTREP.GAf L n → ℂ) = ψ j :=
        fun κ hκ => congrArg Subtype.val (hinj (hfix j hj κ hκ))
      have hH := H _ (ψ j).2 hψfix
      have e : ∑ i, b i • (⟨Formalism.L2.NG.rt L n (lf i) (ψ j), σ.stable (lf i) _ (ψ j).2⟩ : σ.S) = ψ j := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simpa using hH
      calc ∑ i, b i • ρ (lf i) (j.1 (ψ j))
          = j.1 (∑ i, b i • (⟨Formalism.L2.NG.rt L n (lf i) (ψ j), σ.stable (lf i) _ (ψ j).2⟩ : σ.S)) := by

            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_smul, j.2.1 (lf i) (ψ j)]
        _ = j.1 (ψ j) := by rw [e]
  calc ∑ i, b i • ρ (lf i) x = ∑ j ∈ t, ∑ i, b i • ρ (lf i) (j.1 (ψ j)) := by
        rw [hx']

        simp only [map_sum, Finset.smul_sum]
        exact Finset.sum_comm
    _ = x := by
        rw [Finset.sum_congr rfl hterm, ← hx']

end Gen

theorem isotIn_conjT_fix_sum : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (π : Formalism.L2.NG.FinTyp D.host.E n) (U : Set (GAf D.host.E n)) (ι : Type) [Finite ι] (a : ι → ℂ) (lf : ι → GAf D.host.E n), (∀ φ ∈ π.S, (∀ κ ∈ U, Formalism.L2.NG.rt D.host.E n κ φ = φ) → ∑ᶠ i, a i • Formalism.L2.NG.rt D.host.E n (lf i) φ = φ) → ∀ S ∈ isotIn ρ C (FinTyp.conjT π), (∀ κ ∈ U, ρ κ S = S) → ∑ᶠ i, star (a i) • ρ (lf i) S = S := by
  intro D n A _ _ ρ C π U ι _ a lf hyp S hS hU
  haveI := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype]
  refine fix_sum_of_mem (σ := FinTyp.conjT π) (fun Φ => LinearMap.range Φ ≤ C) U (fun i => star (a i)) lf ?_ S hS hU
  intro ψ hψ hfix
  have hφ : (fun g => star (ψ g)) ∈ π.S := hψ
  have h1 := hyp _ hφ (fun κ hκ => by rw [← conj_rt, hfix κ hκ])
  rw [finsum_eq_sum_of_fintype] at h1
  funext g
  have h2 := congrArg star (congrFun h1 g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul', star_star, rt_apply] at h2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rt_apply]
  exact h2

end GlobalTheory.IsotConjFix
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped Matrix

namespace GlobalTheory.RowLev

theorem exists_coords_of_frame {A κ : Type} [CommRing A] [CommRing κ] {n : ℕ} (R : Subring A)
    (L : Submodule R (Fin n → A)) (β : GL (Fin n) A)
    (hβ : ∀ y, y ∈ L ↔ ∀ i, ((β⁻¹ : GL (Fin n) A).1 *ᵥ y) i ∈ R) (r : R →+* κ) (hr : Function.Surjective r) :
    ∃ c : L →ₛₗ[r] (Fin n → κ), Function.Surjective c ∧
      (∀ y : L, c y = 0 ↔ (y : Fin n → A) ∈ RingHom.ker r • L) ∧
      ∀ (X : GL (Fin n) A) (M : Matrix (Fin n) (Fin n) κ),
        (∀ y ∈ L, X.1 *ᵥ y ∈ L) →
        (∀ i j (h : (β⁻¹ * X * β : GL (Fin n) A).1 i j ∈ R), r ⟨_, h⟩ = M i j) →
        ∀ (y : L) (h : X.1 *ᵥ (y : Fin n → A) ∈ L), c ⟨_, h⟩ = M *ᵥ c y := by
  classical
  set B : Matrix (Fin n) (Fin n) A := (β⁻¹ : GL (Fin n) A).1 with hB
  have hBβ : B * β.1 = 1 := by rw [hB]; exact Units.inv_mul β
  have hβB : β.1 * B = 1 := by rw [hB]; exact Units.mul_inv β
  have hmem : ∀ y : L, ∀ i, (B *ᵥ (y : Fin n → A)) i ∈ R := fun y => (hβ y).1 y.2

  have hcol : ∀ j, (fun k => β.1 k j) ∈ L := by
    intro j
    refine (hβ _).2 fun i => ?_
    have e : (B *ᵥ fun k => β.1 k j) i = (B * β.1) i j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    change (B *ᵥ fun k => β.1 k j) i ∈ R
    rw [e, hBβ, Matrix.one_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem

  have hexp : ∀ v : Fin n → A, v = ∑ j, (B *ᵥ v) j • (fun k => β.1 k j) := by
    intro v
    have h1 : β.1 *ᵥ (B *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hβB, Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  let c : L →ₛₗ[r] (Fin n → κ) :=
    { toFun := fun y i => r ⟨(B *ᵥ (y : Fin n → A)) i, hmem y i⟩
      map_add' := by
        intro y z
        funext i
        have e : (⟨(B *ᵥ ((y + z : L) : Fin n → A)) i, hmem (y + z) i⟩ : R) =
            ⟨_, hmem y i⟩ + ⟨_, hmem z i⟩ := Subtype.ext (by simp [Matrix.mulVec_add])
        simp only [Pi.add_apply]
        rw [e, map_add (f := _)]
      map_smul' := by
        intro a y
        funext i
        have e : (⟨(B *ᵥ ((a • y : L) : Fin n → A)) i, hmem (a • y) i⟩ : R) = a * ⟨_, hmem y i⟩ := by
          apply Subtype.ext
          change (B *ᵥ ((a : A) • (y : Fin n → A))) i = (a : A) * (B *ᵥ (y : Fin n → A)) i
          rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [e, map_mul] }
  have hc : ∀ (y : L) i, c y i = r ⟨(B *ᵥ (y : Fin n → A)) i, hmem y i⟩ := fun _ _ => rfl
  refine ⟨c, ?_, ?_, ?_⟩
  ·
    intro v
    choose x hx using fun i => hr (v i)
    set y0 : Fin n → A := β.1 *ᵥ fun i => (x i : A) with hy0
    have hc0 : ∀ i, (B *ᵥ y0) i = x i := by
      intro i
      rw [hy0, Matrix.mulVec_mulVec, hBβ, Matrix.one_mulVec]
    have hm : y0 ∈ L := (hβ y0).2 fun i => by rw [hc0 i]; exact (x i).2
    refine ⟨⟨y0, hm⟩, ?_⟩
    funext i
    rw [hc, ← hx i]
    congr 1
    exact Subtype.ext (hc0 i)
  · intro y
    constructor
    · intro hy
      have hk : ∀ j, (⟨_, hmem y j⟩ : R) ∈ RingHom.ker r := by
        intro j
        rw [RingHom.mem_ker, ← hc]
        exact congrFun hy j
      have e : (y : Fin n → A) = ∑ j, (⟨_, hmem y j⟩ : R) • (fun k => β.1 k j) := hexp _
      rw [e]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hk j) (hcol j)
    · intro hy
      have key : ∀ i, ∃ h : (B *ᵥ (y : Fin n → A)) i ∈ R, r ⟨_, h⟩ = 0 := by
        refine Submodule.smul_induction_on
          (p := fun z : Fin n → A => ∀ i, ∃ h : (B *ᵥ z) i ∈ R, r ⟨_, h⟩ = 0) hy ?_ ?_
        · intro a ha m hm i
          have e : (B *ᵥ (a • m)) i = (a : A) * (B *ᵥ m) i := by
            change (B *ᵥ ((a : A) • m)) i = _
            rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
          have hm' : (B *ᵥ m) i ∈ R := (hβ m).1 hm i
          refine ⟨e ▸ R.mul_mem a.2 hm', ?_⟩
          have e2 : (⟨(B *ᵥ (a • m)) i, e ▸ R.mul_mem a.2 hm'⟩ : R) = a * ⟨_, hm'⟩ := Subtype.ext e
          rw [e2, map_mul, (RingHom.mem_ker).1 ha, zero_mul]
        · intro u v hu hv i
          obtain ⟨h1, e1⟩ := hu i
          obtain ⟨h2, e2⟩ := hv i
          have e : (B *ᵥ (u + v)) i = (B *ᵥ u) i + (B *ᵥ v) i := by
            rw [Matrix.mulVec_add, Pi.add_apply]
          refine ⟨e ▸ R.add_mem h1 h2, ?_⟩
          have e3 : (⟨(B *ᵥ (u + v)) i, e ▸ R.add_mem h1 h2⟩ : R) = ⟨_, h1⟩ + ⟨_, h2⟩ := Subtype.ext e
          rw [e3, map_add (f := _), e1, e2, add_zero]
      funext i
      obtain ⟨_, h⟩ := key i
      rw [hc]
      exact h
  · intro X M hXL hM y h
    have hP : ∀ i j, (β⁻¹ * X * β : GL (Fin n) A).1 i j ∈ R := by
      intro i j
      have hXc : X.1 *ᵥ (fun k => β.1 k j) ∈ L := hXL _ (hcol j)
      have e : (β⁻¹ * X * β : GL (Fin n) A).1 i j = (B *ᵥ (X.1 *ᵥ fun k => β.1 k j)) i := by
        rw [Units.val_mul, Units.val_mul, ← hB, Matrix.mulVec_mulVec]
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [e]
      exact (hβ _).1 hXc i
    have hPv : B *ᵥ (X.1 *ᵥ (y : Fin n → A)) =
        (β⁻¹ * X * β : GL (Fin n) A).1 *ᵥ (B *ᵥ (y : Fin n → A)) := by
      rw [Units.val_mul, Units.val_mul, ← hB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc (B * X.1), hβB, Matrix.mul_one]
    funext i
    have e : (⟨(B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i, hmem ⟨_, h⟩ i⟩ : R) =
        ∑ j, (⟨_, hP i j⟩ : R) * ⟨_, hmem y j⟩ := by
      apply Subtype.ext
      change (B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i = _
      rw [hPv]
      simp [Matrix.mulVec, dotProduct]
    rw [hc]
    change r ⟨(B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i, hmem ⟨_, h⟩ i⟩ = _

    rw [e, map_sum]
    simp only [map_mul, hM, Matrix.mulVec, dotProduct, hc]

private theorem hatL_eq_Lf' (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf
  rw [Set.image_eq_range]
  rfl

theorem exists_plFrame_of_isFrame : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (N p : ℕ) (hN : I.n = N) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)), p.Prime → Nat.card (𝓞 I.E ⧸ w.asIdeal) = p → ∃ fr : GlobalTheory.RowLev.PlFrame I N p w, ∀ k ∈ I.Kset, ∀ M : Matrix (Fin N) (Fin N) (ZMod p), (∀ (i j : Fin N) (hij : ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (Fin.cast hN.symm i) (Fin.cast hN.symm j) ∈ Formalism.L2.Herm.intAf I.F I.E), Formalism.L2.DIV.resS I.F w ⟨_, hij⟩ = ((M i j).val : Formalism.L2.DIV.kP w)) → fr.ActsAs k M := by
  intro I β₀ hF N p hN w hp hcard
  subst hN
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hL : ∀ y, y ∈ I.Lf ↔
      ∀ i, ((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)).1 *ᵥ y) i ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    intro y
    rw [← hatL_eq_Lf' I]
    exact hF y

  have : Finite (Formalism.L2.DIV.kP w) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let : Fintype (Formalism.L2.DIV.kP w) := Fintype.ofFinite _
  have hcard' : Fintype.card (Formalism.L2.DIV.kP w) = p := by rw [Fintype.card_eq_nat_card]; exact hcard
  have : CharP (Formalism.L2.DIV.kP w) p := charP_of_card_eq_prime hcard'
  let e : ZMod p ≃+* Formalism.L2.DIV.kP w := ZMod.ringEquiv (Formalism.L2.DIV.kP w) hcard'
  let r : Formalism.MainNotions.S.IntAf I.F I.E →+* ZMod p :=
    (e.symm : Formalism.L2.DIV.kP w →+* ZMod p).comp (Formalism.L2.DIV.resS I.F w)
  have hr : ∀ s, r s = e.symm (Formalism.L2.DIV.resS I.F w s) := fun _ => rfl
  have hres : ∀ a : 𝓞 I.E, r (Formalism.L2.DIV.oToS I.F I.E a) = 0 ↔ a ∈ w.asIdeal := by
    intro a
    rw [hr, Formalism.L2.DIV.resS_oToS, map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hrs : Function.Surjective r := by
    intro q
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := w.asIdeal) (e q)
    refine ⟨Formalism.L2.DIV.oToS I.F I.E a, ?_⟩
    rw [hr, Formalism.L2.DIV.resS_oToS, ha, RingEquiv.symm_apply_apply]
  obtain ⟨c, hcs, hck, hca⟩ := exists_coords_of_frame (Formalism.MainNotions.S.IntAf I.F I.E) I.Lf β₀ hL r hrs
  have hker : RingHom.ker r = extId I w.asIdeal := by
    refine Inhab.ker_eq_extId hp.ne_zero r fun a => ?_
    have e1 : Inhab.psi I.F I.E a = Formalism.L2.DIV.oToS I.F I.E a := Subtype.ext rfl
    rw [e1]
    exact hres a
  refine ⟨{ r := r, r_ker := fun a h => ?_, c := c, c_surj := hcs, c_ker := fun y => ?_ }, ?_⟩
  · have e1 : (⟨_, h⟩ : Formalism.MainNotions.S.IntAf I.F I.E) = Formalism.L2.DIV.oToS I.F I.E a := Subtype.ext rfl
    rw [e1]
    exact hres a
  · rw [hck y, hker]
  · intro k hk M hM y h
    refine hca (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) M (fun y hy => Inhab.mulVec_mem hk hy)
      (fun i j hij => ?_) y h
    have h1 : Formalism.L2.DIV.resS I.F w ⟨_, hij⟩ = ((M i j).val : Formalism.L2.DIV.kP w) := hM i j hij
    rw [hr, h1, map_natCast, ZMod.natCast_zmod_val]

end GlobalTheory.RowLev
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (GG k r) ↔ (unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → unrealify x i j = 0)) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) → NormedSpace.exp (unrealify x) ∈ Formalism.FourierDecayAlt.B2.UWb k r) := by
  first | exact @GlobalTheory.CellLieAlg.lie_entries | exact GlobalTheory.CellLieAlg.lie_entries | (intros; apply GlobalTheory.CellLieAlg.lie_entries <;> assumption)
end

section

open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.discreteSeriesCoefficient_smooth_decay_capelliEigen_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  first | exact @GlobalTheory.eigDec_of_isKFinCoefT_gap | exact GlobalTheory.eigDec_of_isKFinCoefT_gap | (intros; apply GlobalTheory.eigDec_of_isKFinCoefT_gap <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.exists_productChart_tangentEquiv_ballVolume : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∃ L : Par k ≃L[ℝ] lieE (UH (Hd k η)), (∀ v : Par k, unrealify ((L v : lieE (UH (Hd k η))) : EuclideanSpace ℝ _) = tang η v) ∧ ∀ ρ : ℝ, 0 < ρ → volume (L '' Metric.ball (0 : Par k) ρ) = volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) ρ) * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))) := by
  first | exact @GlobalTheory.TubeLie.exists_tang_equiv | exact GlobalTheory.TubeLie.exists_tang_equiv | (intros; apply GlobalTheory.TubeLie.exists_tang_equiv <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isometry_transports_genus_orbitSum : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ φ : Submodule (𝓞 K) V' → ℝ≥0∞, (∀ (s : Formalism.HermitianLatticesTheory.isom h') (M : Submodule (𝓞 K) V'), φ (s • M) = φ M) → ∀ L : Submodule (𝓞 K) V, (∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V), φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M)) ∧ (∀ M : Submodule (𝓞 K) V, GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L) ∧ GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h') (Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L)) φ = GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h) (Formalism.HermitianLatticesTheory.genus h L) (fun M => φ (GlobalTheory.Mass.Transp.img e M)) := by
  first | exact @GlobalTheory.Mass.Transp.orbSum_img | exact GlobalTheory.Mass.Transp.orbSum_img | (intros; apply GlobalTheory.Mass.Transp.orbSum_img <;> assumption)
end
