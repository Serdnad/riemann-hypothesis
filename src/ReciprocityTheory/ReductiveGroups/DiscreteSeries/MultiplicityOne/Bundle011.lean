module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurGA
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stDichoW (h : UnitaryGroupStructuralFacts) : StDichoW := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, -, -, -, hHI, -, -, -, hClW, -⟩ := h.1
  intro k r Wp _ _ _ D X hD hX γ hγ
  obtain ⟨-, -, hgW, -, hth_mul, hth_th, -, -, hμgbar⟩ := stInvGroup h k r Wp D X hD hX γ hγ
  by_cases hWp : Subsingleton Wp
  · left
    intro x y x' y'
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  have : Nontrivial Wp := not_subsingleton_iff_nontrivial.1 hWp
  have hU : IsClosedSubgroup (UWset k r D.z) := hClW k r D.z
  have hμW := D.haarW
  have hme := MatrixSubsetMeasurability.me_val hU
  have hleft : (MatrixSubsetMeasurability.nu hU D.μW).IsMulLeftInvariant := MatrixSubsetMeasurability.nu_left hμW
  have hinvI : (MatrixSubsetMeasurability.nu hU D.μW).IsInvInvariant := MatrixSubsetMeasurability.nu_inv hHI hμW
  have hmapnu : (MatrixSubsetMeasurability.nu hU D.μW).map (fun g : MatrixSubsetMeasurability.SG hU => g.1) = D.μW := MatrixSubsetMeasurability.map_nu hμW
  have hνuniv : MatrixSubsetMeasurability.nu hU D.μW Set.univ = 1 := by
    have e := congrArg (fun m : Measure (Mt k r) => m Set.univ) hmapnu
    simp only [Measure.map_apply hme.measurable MeasurableSet.univ, Set.preimage_univ] at e
    rw [e, hD.mass]
  have hcpt : IsCompact {x : Mt k r | Matrix.of x ∈ UWset k r D.z} := hCW k r D.z D.z_mem D.T_pos
  have : CompactSpace (MatrixSubsetMeasurability.SG hU) := isCompact_iff_compactSpace.1 hcpt
  have hpos : (MatrixSubsetMeasurability.nu hU D.μW).IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact Set.univ isCompact_univ (by rw [hνuniv]; exact one_ne_zero)
  have hfin : IsFiniteMeasure (MatrixSubsetMeasurability.nu hU D.μW) := ⟨by rw [hνuniv]; exact ENNReal.one_lt_top⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : MatrixSubsetMeasurability.SG hU → MatrixSubsetMeasurability.SG hU, θ = fun g =>
      (MatrixSubsetMeasurability.mk hU (gbar k r γ (MatrixSubsetMeasurability.mat g)) (hgW _ (MatrixSubsetMeasurability.mat_mem g)))⁻¹ := ⟨_, rfl⟩
  have hmθ : ∀ g, MatrixSubsetMeasurability.mat (θ g) = th k r γ (MatrixSubsetMeasurability.mat g) := by
    intro g
    simp only [hθ]
    rw [MatrixSubsetMeasurability.mat_inv, MatrixSubsetMeasurability.mat_mk]
    rfl
  have hgc : Continuous fun A : Mat k r => gbar k r γ A := by
    have h1 : Continuous fun A : Mat k r => (embWb k r γ)⁻¹ * A := continuous_const.matrix_mul continuous_id
    have h2 : Continuous fun A : Mat k r => (embWb k r γ)⁻¹ * A * embWb k r γ := h1.matrix_mul continuous_const
    have h3 : Continuous fun A : Mat k r => ((embWb k r γ)⁻¹ * A * embWb k r γ).map (starRingEnd ℂ) :=
      h2.matrix_map Complex.continuous_conj
    have h4 : Continuous fun A : Mat k r =>
        embWb k r γ * ((embWb k r γ)⁻¹ * A * embWb k r γ).map (starRingEnd ℂ) :=
      continuous_const.matrix_mul h3
    exact h4.matrix_mul continuous_const
  have hgbc : Continuous fun g : MatrixSubsetMeasurability.SG hU =>
      MatrixSubsetMeasurability.mk hU (gbar k r γ (MatrixSubsetMeasurability.mat g)) (hgW _ (MatrixSubsetMeasurability.mat_mem g)) := by
    apply continuous_induced_rng.2
    exact hgc.comp MatrixSubsetMeasurability.continuous_mat
  have hθc : Continuous θ := by
    rw [hθ]
    exact hgbc.inv
  have hθmul : ∀ a b, θ (a * b) = θ b * θ a := by
    intro a b
    apply MatrixSubsetMeasurability.ext'
    rw [MatrixSubsetMeasurability.mat_mul, hmθ, hmθ, hmθ, MatrixSubsetMeasurability.mat_mul]
    exact hth_mul _ (MatrixSubsetMeasurability.mat_mem a).1 _ (MatrixSubsetMeasurability.mat_mem b).1
  have hθθ : ∀ g, θ (θ g) = g := by
    intro g
    apply MatrixSubsetMeasurability.ext'
    rw [hmθ, hmθ]
    exact hth_th _ (MatrixSubsetMeasurability.mat_mem g).1
  have hgF : Measurable fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp (hgc.comp continuous_id))
  have hθμ : (MatrixSubsetMeasurability.nu hU D.μW).map θ = MatrixSubsetMeasurability.nu hU D.μW := by
    have hval : (fun g : MatrixSubsetMeasurability.SG hU => g.1) ∘ θ =
        (invM ∘ fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) ∘ fun g : MatrixSubsetMeasurability.SG hU => g.1 := by
      funext g
      exact hmθ g
    have key : ((MatrixSubsetMeasurability.nu hU D.μW).map θ).map (fun g : MatrixSubsetMeasurability.SG hU => g.1) = D.μW := by
      rw [Measure.map_map hme.measurable hθc.measurable, hval,
        ← Measure.map_map (InvGrp.measurable_invM.comp hgF) hme.measurable, hmapnu,
        ← Measure.map_map InvGrp.measurable_invM hgF, hμgbar]
      exact hHI k r _ D.μW hU hμW
    rw [← hme.comap_map ((MatrixSubsetMeasurability.nu hU D.μW).map θ), key]
    rfl
  have hπc : Continuous fun g : MatrixSubsetMeasurability.SG hU => D.π (MatrixSubsetMeasurability.mat g) :=
    D.π_cont.comp_continuous MatrixSubsetMeasurability.continuous_mat fun g => MatrixSubsetMeasurability.mat_mem g
  have hρ1 : D.π (MatrixSubsetMeasurability.mat (1 : MatrixSubsetMeasurability.SG hU)) = 1 := by
    rw [MatrixSubsetMeasurability.mat_one]
    exact D.π_rep.1
  have hρmul : ∀ a b : MatrixSubsetMeasurability.SG hU,
      D.π (MatrixSubsetMeasurability.mat (a * b)) = (D.π (MatrixSubsetMeasurability.mat a)).comp (D.π (MatrixSubsetMeasurability.mat b)) := by
    intro a b
    rw [MatrixSubsetMeasurability.mat_mul]
    exact D.π_rep.2 _ (MatrixSubsetMeasurability.mat_mem a) _ (MatrixSubsetMeasurability.mat_mem b)
  have hρn : ∀ (g : MatrixSubsetMeasurability.SG hU) (v : Wp), ‖D.π (MatrixSubsetMeasurability.mat g) v‖ = ‖v‖ :=
    fun g v => D.π_unitary _ (MatrixSubsetMeasurability.mat_mem g) v
  have hρc : ∀ v : Wp, Continuous fun g : MatrixSubsetMeasurability.SG hU => D.π (MatrixSubsetMeasurability.mat g) v :=
    fun v => hπc.clm_apply continuous_const
  have hmem : ∀ v w : Wp, MemLp (fun g : MatrixSubsetMeasurability.SG hU => ⟪w, D.π (MatrixSubsetMeasurability.mat g) v⟫_ℂ) 2
      (MatrixSubsetMeasurability.nu hU D.μW) := by
    intro v w
    refine MemLp.of_bound (continuous_const.inner (hρc v)).aestronglyMeasurable (‖w‖ * ‖v‖)
      (Filter.Eventually.of_forall fun g => ?_)
    calc ‖⟪w, D.π (MatrixSubsetMeasurability.mat g) v⟫_ℂ‖ ≤ ‖w‖ * ‖D.π (MatrixSubsetMeasurability.mat g) v‖ := norm_inner_le_norm _ _
      _ = ‖w‖ * ‖v‖ := by rw [hρn]
  have hirr : ∀ S : Submodule ℂ Wp, IsClosed (S : Set Wp) →
      (∀ (g : MatrixSubsetMeasurability.SG hU), ∀ v ∈ S, D.π (MatrixSubsetMeasurability.mat g) v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hinv
    refine hD.irr S hS fun g hg v hv => ?_
    have e := hinv (MatrixSubsetMeasurability.mk hU g hg) v hv
    rwa [MatrixSubsetMeasurability.mat_mk] at e
  rcases schurDichotomy (MatrixSubsetMeasurability.SG hU) (MatrixSubsetMeasurability.nu hU D.μW) Wp θ (fun g => D.π (MatrixSubsetMeasurability.mat g))
      hθc hθmul hθθ hθμ hρ1 hρmul hρn hρc hmem hirr with hL | ⟨C, hC1, hC2⟩
  · left
    intro x y x' y'
    rw [← hmapnu, hme.integral_map]
    have e := hL x y x' y'
    simp only [hmθ] at e
    exact e
  · right
    refine ⟨C, fun g hg x y => ?_, fun g hg v => ?_⟩
    · have e := hC1 (MatrixSubsetMeasurability.mk hU g hg) x y
      simp only [hmθ, MatrixSubsetMeasurability.mat_mk] at e
      exact e
    · have e := hC2 (MatrixSubsetMeasurability.mk hU g hg) v
      simp only [MatrixSubsetMeasurability.mat_inv, hmθ, MatrixSubsetMeasurability.mat_mk] at e
      exact e

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem psiM_inv' {k r : ℕ} (u : Formalism.REAL.UJ (epsG k r)) : psiM k r u⁻¹ = (psiM k r u)⁻¹ := by
  exact (Matrix.inv_eq_right_inv (by rw [← psiM_mul, mul_inv_cancel, psiM_one])).symm

theorem stDichoG (h : UnitaryGroupStructuralFacts) : StDichoG := by
  intro k r Wp _ _ _ D X hD hSq γ hγ
  obtain ⟨hgbG, -, -, -, hanti', hinv', hμG, -, -⟩ := stInvGroup h k r Wp D X hD hSq γ hγ
  have hG := D.haarG
  haveI := nuG_left hG
  haveI := nuG_inv hG
  haveI := nuG_openPos hG
  haveI : Nontrivial X.Hs := ⟨⟨X.w, 0, fun e => by have hw := X.w_norm; simp [e] at hw⟩⟩
  have inj := (isClosedEmbedding_psiM k r).injective

  have hex : ∀ u : Formalism.REAL.UJ (epsG k r), ∃ u', psiM k r u' = gbar k r γ (psiM k r u) := by
    intro u
    have hm : gbar k r γ (psiM k r u) ∈ Set.range (psiM k r) := by
      rw [range_psiM]
      exact hgbG _ (psiM_mem u)
    exact hm
  choose G hGs using hex
  let θ : Formalism.REAL.UJ (epsG k r) → Formalism.REAL.UJ (epsG k r) := fun u => (G u)⁻¹
  have hθ : ∀ u, psiM k r (θ u) = th k r γ (psiM k r u) := by
    intro u
    simp only [θ, th, psiM_inv', hGs]
  have hanti : ∀ a b, θ (a * b) = θ b * θ a := by
    intro a b
    apply inj
    rw [hθ, psiM_mul, psiM_mul, hθ, hθ]
    exact hanti' _ (psiM_mem a) _ (psiM_mem b)
  have hinv : ∀ u, θ (θ u) = u := by
    intro u
    apply inj
    rw [hθ, hθ]
    exact hinv' _ (psiM_mem u)
  have hgbar : Continuous (gbar k r γ) := by
    unfold gbar
    exact ((continuous_const.matrix_mul ((((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).matrix_map Complex.continuous_conj))).matrix_mul continuous_const)
  have hGc : Continuous G := by
    rw [(isClosedEmbedding_psiM k r).toIsEmbedding.continuous_iff]
    have e : psiM k r ∘ G = gbar k r γ ∘ psiM k r := funext hGs
    rw [e]
    exact hgbar.comp (continuous_psiM k r)
  have hθc : Continuous θ := continuous_inv.comp hGc
  have hE := measurableEmbedding_psiG k r
  let T : Mt k r → Mt k r := fun x => fun i j => th k r γ (Matrix.of x) i j
  have hT : AEMeasurable T D.μG := by
    have hc : Continuous (fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) := by
      exact continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply j).comp ((continuous_apply i).comp (hgbar.comp continuous_id))
    exact (InvGrp.measurable_invM.comp hc.measurable).aemeasurable
  have hcomp : psiG k r ∘ θ = T ∘ psiG k r := by
    funext u
    show Matrix.of.symm (psiM k r (θ u)) = fun i j => th k r γ (Matrix.of (psiG k r u)) i j
    rw [of_psiG, hθ]
    rfl
  have key : ((nuG D.μG).map θ).map (psiG k r) = (nuG D.μG).map (psiG k r) := by
    rw [Measure.map_map hE.measurable hθc.measurable, hcomp,
      ← AEMeasurable.map_map_of_aemeasurable (by rw [map_nuG hG]; exact hT) hE.measurable.aemeasurable,
      map_nuG hG]
    exact hμG
  have hmap : (nuG D.μG).map θ = nuG D.μG := by
    calc (nuG D.μG).map θ = (((nuG D.μG).map θ).map (psiG k r)).comap (psiG k r) := (hE.comap_map _).symm
      _ = ((nuG D.μG).map (psiG k r)).comap (psiG k r) := by rw [key]
      _ = nuG D.μG := hE.comap_map _
  have hSR : Formalism.MainNotions.BridgeCSchur.SqRep (nuG D.μG)
      (fun u => X.σ (psiM k r u)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [psiM_one]; exact X.rep.1.1
    · intro a b
      rw [psiM_mul]; exact X.rep.1.2 _ (psiM_mem a) _ (psiM_mem b)
    · intro g v
      exact X.rep.2.1 _ (psiM_mem g) v
    · intro v
      exact (X.rep.2.2 v).comp_continuous (continuous_psiM k r) psiM_mem
    · intro v w
      have hs := hSq v w
      rw [← map_nuG hG] at hs
      have hs' := (hE.memLp_map_measure_iff).mp hs
      convert hs' using 1
      simp [mc, Function.comp_def, of_psiG]
  have hI : ∀ S : Submodule ℂ X.Hs, IsClosed (S : Set X.Hs) →
      (∀ u : Formalism.REAL.UJ (epsG k r), ∀ v ∈ S, X.σ (psiM k r u) v ∈ S) →
      S = ⊥ ∨ S = ⊤ := by
    intro S hS hinv
    apply X.irr S hS
    intro g hg v hv
    obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
    exact hinv u v hv
  rcases schurDichotomy (Formalism.REAL.UJ (epsG k r)) (nuG D.μG) X.Hs θ (fun u => X.σ (psiM k r u)) hθc hanti hinv
      hmap hSR.one hSR.mul hSR.iso hSR.cont hSR.sq hI with h0 | ⟨C, hC1, hC2⟩
  · left
    intro x y x' y'
    rw [← map_nuG hG, hE.integral_map]
    simp only [of_psiG, ← hθ]
    exact h0 x y x' y'
  · right
    refine ⟨C, ?_, ?_⟩
    · intro g hg x y
      obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
      rw [← hθ]
      exact hC1 u x y
    · intro g hg v
      obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
      rw [← hθ, ← psiM_inv']
      exact hC2 u v

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
