module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle057
public import GroundTheory.LocalFields.Uniqueness
import GroundTheory.AutomorphicForms.MeasuresGL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Topology ValuativeRel GlobalTheory.LocLanglands GlobalTheory.LocLanglands.InvInt
open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

namespace DiscreteGroups.sglob.LConv

theorem exists_pos_invariant_form {G : Type} [Group G] {H : Subgroup G} [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (hH : IsClosed (H : Set G))
    (uG : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsUnimodular G) (uH : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsUnimodular H) :
    ∃ I : (G → ℂ) →ₗ[ℂ] ℂ,
      ∀ f : G → ℂ, (∀ u ∈ H, ∀ g, f (u * g) = f g) → Continuous f →
        (∃ C : Set G, IsCompact C ∧ ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) →
        (∀ x, I (fun g => f (g * x)) = I f) ∧
        I (fun g => (starRingEnd ℂ) (f g)) = (starRingEnd ℂ) (I f) ∧
        ((∀ g, 0 ≤ (f g).re) → 0 ≤ (I f).re ∧ ((I f).re = 0 → ∀ g, (f g).re = 0)) := by
  borelize (G ⧸ H)
  obtain ⟨⟨μ, hμ⟩, -⟩ := GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause G H hH uG uH
  have := hμ.finiteOnCompacts
  have := hμ.invariant
  have := hμ.regular
  have : μ.IsOpenPosMeasure := ⟨fun U hU hne =>
    (measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ.ne_zero hU hne).ne'⟩
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {f | Integrable (descend H f) μ}
      zero_mem' := by simp
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
        exact hf.add hg
      smul_mem' := fun c f hf => by
        simp only [Set.mem_ofPred_eq, map_smul] at *
        exact hf.smul c }
  let J : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ q, descend H f q ∂μ
      map_add' := fun f g => integral_add f.2 g.2
      map_smul' := fun c f => integral_smul c (descend H f) }
  obtain ⟨I, hI⟩ := J.exists_extend
  have hIJ : ∀ f, Integrable (descend H f) μ → I f = ∫ q, descend H f q ∂μ := fun f hf =>
    LinearMap.congr_fun hI ⟨f, hf⟩
  refine ⟨I, fun f hf hc ⟨C, hC, hs⟩ => ?_⟩
  have hcd := continuous_descend hf hc
  have h1 : Integrable (descend H f) μ :=
    hcd.integrable_of_hasCompactSupport (hasCompactSupport_descend hf hC hs)
  refine ⟨fun x => ?_, ?_, fun hpos => ?_⟩
  · have h2 : Integrable (descend H fun g => f (g * x)) μ := by
      rw [descend_mul_right hf]
      exact (measurePreserving_smul x⁻¹ μ).integrable_comp_of_integrable h1
    rw [hIJ _ h1, hIJ _ h2, descend_mul_right hf]
    exact integral_smul_eq_self (descend H f)
  · have h2 : Integrable (descend H fun g => (starRingEnd ℂ) (f g)) μ :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp h1
    rw [hIJ _ h1, hIJ _ h2, ← integral_conj]
    rfl
  · have hre : (I f).re = ∫ q, (descend H f q).re ∂μ := by
      rw [hIJ _ h1]
      exact (integral_re h1).symm
    have hnn : 0 ≤ fun q => (descend H f q).re := fun q => hpos _
    refine ⟨hre ▸ integral_nonneg hnn, fun h0 g => ?_⟩
    rw [hre] at h0
    have hae := (integral_eq_zero_iff_of_nonneg hnn h1.re).1 h0
    have hz := (Continuous.ae_eq_iff_eq μ (Complex.continuous_re.comp hcd) continuous_zero).1 hae
    have := congrFun hz ((g⁻¹ : G) : G ⧸ H)
    simpa [descend_mk hf] using this

theorem exists_pos_isInvIntegral (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m : ℕ) :
    ∃ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I ∧
      (∀ f, IsTestFun f → I (fun g => (starRingEnd ℂ) (f g)) = (starRingEnd ℂ) (I f)) ∧
      ∀ f, IsTestFun f → (∀ g, 0 ≤ (f g).re) → 0 ≤ (I f).re ∧ ((I f).re = 0 → ∀ g, (f g).re = 0) := by
  borelize k (GL (Fin m) k)
  obtain ⟨I, h⟩ := exists_pos_invariant_form (H := unipB k (Fin m)) isClosed_unipB
    (fun μ hμ => by
      letI := hμ
      exact _root_.GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k m μ)
    (fun μ hμ => @UnipHaar.haar_isMulRightInvariant k _ _ _ _ (Fin m) (Fin m) (fun _ => Unit) _ _ _ _ _ _
      (points (Fin m)) Subtype.instMeasurableSpace
      (Subtype.borelSpace (fun g : GL (Fin m) k => g ∈ unipB k (Fin m))) μ hμ)
  exact ⟨I, fun f hf => (h f hf.1 hf.2.1.continuous hf.2.2).1,
    fun f hf => (h f hf.1 hf.2.1.continuous hf.2.2).2.1, fun f hf => (h f hf.1 hf.2.1.continuous hf.2.2).2.2⟩

end DiscreteGroups.sglob.LConv

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Filter Topology

namespace DiscreteGroups.sglob.LConv

section Matrices

variable {k : Type} [Field k] {m : ℕ}

def tv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) : GL (Fin n) k :=
  ⟨Matrix.transvection i j c, Matrix.transvection i j (-c),
    by rw [Matrix.transvection_mul_transvection_same _ _ h, add_neg_cancel, Matrix.transvection_zero],
    by rw [Matrix.transvection_mul_transvection_same _ _ h, neg_add_cancel, Matrix.transvection_zero]⟩

theorem val_tv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) :
    ((tv i j h c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.transvection i j c := rfl

theorem val_tv_inv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) :
    (((tv i j h c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.transvection i j (-c) := rfl

theorem tv_zero {n : ℕ} (i j : Fin n) (h : i ≠ j) : tv i j h (0 : k) = 1 :=
  Units.ext (by rw [val_tv, Matrix.transvection_zero, Units.val_one])

theorem continuous_tv [TopologicalSpace k] [IsTopologicalAddGroup k] {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    Continuous fun c : k => tv i j h c := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun c : k => Matrix.transvection i j c
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · show Continuous fun c : k => Matrix.transvection i j (-c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

theorem stdSum_symm_castSucc (i : Fin m) : (stdSum (rfl : m + 1 = m + 1)).symm i.castSucc = Sum.inl i := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by simp)

theorem stdSum_symm_last : (stdSum (rfl : m + 1 = m + 1)).symm (Fin.last m) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by simp)

theorem corner_cs_cs (g : GL (Fin m) k) (i j : Fin m) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.castSucc j.castSucc = (g : Matrix (Fin m) (Fin m) k) i j := by
  simp [corner, emb₂, leviEmb, leviTwo, two, stdSum_symm_castSucc]

theorem corner_last (g : GL (Fin m) k) (j : Fin (m + 1)) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [corner, emb₂, leviEmb, leviTwo, two, stdSum_symm_last]
  · simp [corner, emb₂, leviEmb, leviTwo, two, Matrix.blockDiagonal', stdSum_symm_castSucc, stdSum_symm_last,
      (Fin.castSucc_lt_last j).ne']

theorem corner_one : corner (1 : GL (Fin m) k) = 1 :=
  map_one (emb₂ k (stdSum (rfl : m + 1 = m + 1)))

theorem longElt_inv (n : ℕ) : (longElt n k)⁻¹ = longElt n k := Units.ext rfl

theorem longElt_last (j : Fin (m + 1)) :
    (longElt (m + 1) k : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = if j = 0 then 1 else 0 := by
  simp [longElt]

end Matrices

section Small

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_small {U : Set k} (hU : U ∈ 𝓝 (0 : k)) (a : k) : ∃ t : k, t ≠ 0 ∧ t ∈ U ∧ a * t ∈ U := by
  let := GroundTheory.LocalField.nontriviallyNormedField k
  have hU' : U ∩ (fun t => a * t) ⁻¹' U ∈ 𝓝 (0 : k) :=
    inter_mem hU ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU'
  obtain ⟨t, ht0, htε⟩ := NormedField.exists_norm_lt k hε
  have ht : t ∈ U ∩ (fun t => a * t) ⁻¹' U := hball (by simpa using htε)
  exact ⟨t, norm_pos_iff.1 ht0, ht.1, ht.2⟩

end Small

end DiscreteGroups.sglob.LConv

end

end
