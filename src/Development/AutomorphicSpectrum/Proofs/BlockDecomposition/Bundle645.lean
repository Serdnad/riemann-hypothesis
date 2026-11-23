module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Formalism.SatakeDualWeyl.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.CompanionTheory.NegDS

variable {n : ℕ} {ε ε' : Fin n → Bool}

theorem sign_eq_iff (he : ∀ a, ε' a = !ε a) (a b : Fin n) : ε' a = ε' b ↔ ε a = ε b := by
  rw [he a, he b]
  cases ε a <;> cases ε b <;> simp

theorem Jm_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.Jm ε' = -Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_neg]
  congr 1
  funext a
  rw [he a]
  cases ε a <;> simp

theorem UJset_flip (he : ∀ a, ε' a = !ε a) : Formalism.MainNotions.S.UJset ε' = Formalism.MainNotions.S.UJset ε := by
  ext g
  show Formalism.REAL.inUJ ε' g ↔ Formalism.REAL.inUJ ε g
  unfold Formalism.REAL.inUJ
  rw [Jm_flip he, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem Kset_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.Kset ε' = Formalism.REAL.Kset ε := by
  ext g
  show g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε' = Formalism.REAL.Jm ε' * g ↔
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g
  rw [Jm_flip he, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem rhoC_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.rhoC ε' = Formalism.REAL.rhoC ε := by
  funext a
  simp only [Formalism.REAL.rhoC, sign_eq_iff he]

theorem rhoN_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.rhoN ε' = Formalism.REAL.rhoN ε := by
  funext a
  simp only [Formalism.REAL.rhoN, ne_eq, sign_eq_iff he]

theorem lowK_flip (he : ∀ a, ε' a = !ε a) (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.lowK ε' lam = Formalism.QuantumDeterminants.lowK ε lam := by
  unfold Formalism.QuantumDeterminants.lowK
  rw [rhoC_flip he, rhoN_flip he]

theorem vNormSq_flip (he : ∀ a, ε' a = !ε a) (μ : Fin n → ℝ) : Formalism.MainNotions.S.vNormSq ε' μ = Formalism.MainNotions.S.vNormSq ε μ := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [rhoC_flip he]

theorem cdom_flip (he : ∀ a, ε' a = !ε a) (μ Λ : Fin n → ℝ) : Formalism.MainNotions.S.CDom ε' μ Λ ↔ Formalism.MainNotions.S.CDom ε μ Λ := by
  simp only [Formalism.MainNotions.S.CDom, sign_eq_iff he]

section Rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kstable_flip (he : ∀ a, ε' a = !ε a) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKStableOn ε' σ S ↔ Formalism.MainNotions.S.IsKStableOn ε σ S := by
  simp only [Formalism.MainNotions.S.IsKStableOn, Kset_flip he]

theorem ktype_flip (he : ∀ a, ε' a = !ε a) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKTypeOf ε' σ Λ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ Λ S := by
  simp only [Formalism.MainNotions.S.IsKTypeOf, kstable_flip he, Kset_flip he, cdom_flip he]

end Rep

def flipU (he : ∀ a, ε' a = !ε a) : Formalism.REAL.UJ ε' ≃* Formalism.REAL.UJ ε where
  toFun g := ⟨g.1, (Set.ext_iff.1 (UJset_flip he) _).1 g.2⟩
  invFun g := ⟨g.1, (Set.ext_iff.1 (UJset_flip he) _).2 g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem flipU_cont (he : ∀ a, ε' a = !ε a) : Continuous (flipU he) := by
  exact continuous_induced_rng.2 continuous_subtype_val

theorem flipU_symm_cont (he : ∀ a, ε' a = !ε a) : Continuous (flipU he).symm := by
  exact continuous_induced_rng.2 continuous_subtype_val

theorem memLp_flip (he : ∀ a, ε' a = !ε a) {F : Formalism.REAL.UJ ε → ℂ} (hF : MemLp F 2 (Formalism.REAL.muG ε)) :
    MemLp (F ∘ flipU he) 2 (Formalism.REAL.muG ε') := by
  have hc := flipU_cont he
  have hcs := flipU_symm_cont he
  let eH : Formalism.REAL.UJ ε' ≃ₜ Formalism.REAL.UJ ε := ⟨(flipU he).toEquiv, hc, hcs⟩
  have hme : MeasurableEmbedding (flipU he) := eH.measurableEmbedding
  haveI : (Measure.map (flipU he) (Formalism.REAL.muG ε')).IsHaarMeasure :=
    (flipU he).isHaarMeasure_map (Formalism.REAL.muG ε') hc hcs
  have hmap : Measure.map (flipU he) (Formalism.REAL.muG ε') =
      MeasureTheory.Measure.haarScalarFactor (Measure.map (flipU he) (Formalism.REAL.muG ε')) (Formalism.REAL.muG ε) •
        Formalism.REAL.muG ε :=
    MeasureTheory.Measure.isMulLeftInvariant_eq_smul _ _
  rw [← hme.memLp_map_measure_iff, hmap, ENNReal.smul_def]
  exact hF.smul_measure ENNReal.coe_ne_top

theorem sqInt_flip {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (he : ∀ a, ε' a = !ε a) (h : Formalism.MainNotions.S.IsSqIntOn ε σ) : Formalism.MainNotions.S.IsSqIntOn ε' σ := by
  intro v w
  have e : Formalism.MainNotions.S.coefOn (ε := ε') σ v w = Formalism.MainNotions.S.coefOn (ε := ε) σ v w ∘ flipU he := by
    funext g
    rfl
  rw [e]
  exact memLp_flip he (h v w)

theorem isDS_flip : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS (fun a => !ε a) lam σ := by
  intro n H _ _ ε lam σ h
  have he : ∀ a, (fun a => !ε a) a = !ε a := fun _ => rfl
  unfold Formalism.MainNotions.S.IsDS at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, ?_, ?_, sqInt_flip he h5, ?_, ?_⟩
  · rw [UJset_flip he]
    exact h3
  · rw [UJset_flip he]
    exact h4
  · obtain ⟨S, hS⟩ := h6
    exact ⟨S, by rw [lowK_flip he, ktype_flip he]; exact hS⟩
  · intro μ S hS
    rw [lowK_flip he, vNormSq_flip he, vNormSq_flip he]
    exact h7 μ S ((ktype_flip he μ S).1 hS)

end GlobalTheory.CompanionTheory.NegDS

end
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin

theorem exists_larger_of_valuationSubring {k : Type} [Field k] (O : ValuationSubring k) (a b : k) :
    ∃ c : k, (c = a ∨ c = b) ∧ (∃ u ∈ O, a = c * u) ∧ (∃ u ∈ O, b = c * u) := by
  by_cases ha : a = 0
  · exact ⟨b, Or.inr rfl, ⟨0, O.zero_mem, by simp [ha]⟩, ⟨1, O.one_mem, by simp⟩⟩
  by_cases hb : b = 0
  · exact ⟨a, Or.inl rfl, ⟨1, O.one_mem, by simp⟩, ⟨0, O.zero_mem, by simp [hb]⟩⟩
  rcases O.mem_or_inv_mem (a / b) with h | h
  · exact ⟨b, Or.inr rfl, ⟨a / b, h, by field_simp⟩, ⟨1, O.one_mem, by simp⟩⟩
  · refine ⟨a, Or.inl rfl, ⟨1, O.one_mem, by simp⟩, ⟨(a / b)⁻¹, h, ?_⟩⟩
    field_simp

theorem fg_eq_prod_principal {k R : Type} [Field k] [CommRing R] (O : ValuationSubring k)
    (φ : R ≃+* k × k) (𝔬 : Subring R)
    (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) (I : Submodule 𝔬 R) (hI : I.FG) :
    ∃ α β : k, ∀ r, r ∈ I ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y) := by
  induction I, hI using Submodule.fg_induction with
  | singleton r₀ =>
    refine ⟨(φ r₀).1, (φ r₀).2, fun r => ?_⟩
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, rfl⟩
      have ht := (h𝔬 t).1 t.2
      have hs : φ (t • r₀) = φ (t : R) * φ r₀ := by
        rw [Subring.smul_def, smul_eq_mul, map_mul]
      refine ⟨⟨(φ (t : R)).1, ht.1, ?_⟩, ⟨(φ (t : R)).2, ht.2, ?_⟩⟩
      · rw [hs, Prod.fst_mul, mul_comm]
      · rw [hs, Prod.snd_mul, mul_comm]
    · rintro ⟨⟨x, hx, h1⟩, ⟨y, hy, h2⟩⟩
      have hmem : φ.symm (x, y) ∈ 𝔬 := by
        rw [h𝔬]
        simpa using ⟨hx, hy⟩
      refine ⟨⟨φ.symm (x, y), hmem⟩, ?_⟩
      apply φ.injective
      rw [Subring.smul_def, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
      ext
      · simp [h1, mul_comm]
      · simp [h2, mul_comm]
  | sup I₁ I₂ _ _ ih₁ ih₂ =>
    obtain ⟨α₁, β₁, h₁⟩ := ih₁
    obtain ⟨α₂, β₂, h₂⟩ := ih₂
    obtain ⟨α, hα, ⟨u₁, hu₁, e₁⟩, ⟨u₂, hu₂, e₂⟩⟩ := exists_larger_of_valuationSubring O α₁ α₂
    obtain ⟨β, hβ, ⟨v₁, hv₁, f₁⟩, ⟨v₂, hv₂, f₂⟩⟩ := exists_larger_of_valuationSubring O β₁ β₂
    refine ⟨α, β, fun r => ?_⟩
    constructor
    · intro hr
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨⟨x₁, hx₁, p₁⟩, ⟨y₁, hy₁, q₁⟩⟩ := (h₁ a).1 ha
      obtain ⟨⟨x₂, hx₂, p₂⟩, ⟨y₂, hy₂, q₂⟩⟩ := (h₂ b).1 hb
      refine ⟨⟨u₁ * x₁ + u₂ * x₂, O.add_mem _ _ (O.mul_mem _ _ hu₁ hx₁) (O.mul_mem _ _ hu₂ hx₂), ?_⟩,
        ⟨v₁ * y₁ + v₂ * y₂, O.add_mem _ _ (O.mul_mem _ _ hv₁ hy₁) (O.mul_mem _ _ hv₂ hy₂), ?_⟩⟩
      · rw [map_add (f := _), Prod.fst_add, p₁, p₂, e₁, e₂]
        ring
      · rw [map_add (f := _), Prod.snd_add, q₁, q₂, f₁, f₂]
        ring
    · rintro ⟨⟨x, hx, p⟩, ⟨y, hy, q⟩⟩
      have hsplit : r = φ.symm ((φ r).1, 0) + φ.symm (0, (φ r).2) := by
        apply φ.injective
        rw [map_add (f := _), RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        ext <;> simp
      rw [hsplit]
      refine Submodule.add_mem _ ?_ ?_
      · rcases hα with rfl | rfl
        · refine Submodule.mem_sup_left ((h₁ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨x, hx, p⟩, ⟨0, O.zero_mem, by simp⟩⟩
        · refine Submodule.mem_sup_right ((h₂ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨x, hx, p⟩, ⟨0, O.zero_mem, by simp⟩⟩
      · rcases hβ with rfl | rfl
        · refine Submodule.mem_sup_left ((h₁ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨0, O.zero_mem, by simp⟩, ⟨y, hy, q⟩⟩
        · refine Submodule.mem_sup_right ((h₂ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨0, O.zero_mem, by simp⟩, ⟨y, hy, q⟩⟩

end GlobalTheory.CompanionTheory.KFin
end
