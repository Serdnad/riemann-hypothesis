module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurGA

@[expose] public section

section

open MeasureTheory
open scoped NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def HaarUniqueSF : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ₀ μ : Measure (Mt k r)), IsClosedSubgroup U → Formalism.FourierDecayAlt.B.IsHaarOn U μ₀ →
    Formalism.MainNotions.S.IsHaarOn U μ → ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • μ₀

theorem haarUniqueSF' : HaarUniqueSF := by
  intro k r U μ₀ μ hU h₀ hμ
  have : Fact (IsClosedSubgroup U) := ⟨hU⟩
  obtain ⟨hσ, hne, hconc, hleft⟩ := hμ
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨h₀.finite_compact⟩
  have hcμ : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hconc
  have hcν : μ₀ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := h₀.conc
  have := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ
  have := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ₀
  have := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ hcμ hleft
  have := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ₀ hcν h₀.left
  have hμS : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0 := fun h0 => hne (by
    rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hcμ, h0, Measure.map_zero])
  have hνS : μ₀.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0 := fun h0 => h₀.ne_zero (by
    rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ hcν, h0, Measure.map_zero])
  obtain ⟨c, hc0, hc⟩ := HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hμS hνS
  refine ⟨c, hc0, ?_⟩
  rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hcμ, hc, Measure.map_smul,
    HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ hcν]
  exact (HaarSigmaFiniteUniqueness.mEmb (U := U)).measurable.aemeasurable

theorem haarUniqueSF (_h : UnitaryGroupStructuralFacts) : HaarUniqueSF := haarUniqueSF'

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 RepsA

theorem stReps (h : UnitaryGroupStructuralFacts) : StReps := by
  obtain ⟨hB2, -, hRC, hBCF, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClG, -, hClW, -⟩ := hB2
  intro k r Wp _ _ _ D X hD _ γ hγ c d hc hd
  have hk := D.k_pos
  obtain ⟨hγu, hγz⟩ := hγ
  have hT : 0 < Tz k r D.z := D.T_pos

  have hdet : IsUnit γ.det := by
    have h1 := congrArg Matrix.det hγu
    rw [det_mul, det_mul, det_conjTranspose] at h1
    have hHb : (Hb k).det = -1 := by
      unfold Hb; rw [det_diagonal, Finset.prod_ite_eq' Finset.univ (Fin.last k) (fun _ => (-1 : ℂ))]
      simp
    rw [hHb] at h1
    rw [isUnit_iff_ne_zero]; intro h0; rw [h0] at h1; simp at h1
  have hγi : γ⁻¹ * γ = 1 := nonsing_inv_mul γ hdet
  have hγi' : γ * γ⁻¹ = 1 := mul_nonsing_inv γ hdet
  have hHbi : (γ⁻¹)ᴴ * Hb k * γ⁻¹ = Hb k := by
    calc (γ⁻¹)ᴴ * Hb k * γ⁻¹ = (γ⁻¹)ᴴ * (γᴴ * Hb k * γ) * γ⁻¹ := by rw [hγu]
      _ = (γ * γ⁻¹)ᴴ * Hb k * (γ * γ⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hb k := by rw [hγi']; simp
  set μ := mud k d with hμ
  set M := γ * μ * γ⁻¹ with hM
  have hμu : μᴴ * Hb k * μ = Hb k := mud_unitary hk d hd

  have h1 : Mᴴ * Hb k * M = Hb k := by
    rw [show Mᴴ * Hb k * M = (γ⁻¹)ᴴ * (μᴴ * (γᴴ * Hb k * γ) * μ) * γ⁻¹ by
      simp only [hM, conjTranspose_mul, Matrix.mul_assoc]]
    rw [hγu, hμu, hHbi]

  set s : ℝ := Real.sqrt (Tz k r D.z) with hs
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 hT).ne'
  have hzE : D.z = wbE k r ((s : ℂ) • (γ *ᵥ Pi.single (Fin.last k) 1)) := by
    rw [wbE_smul, ← embWb_mulVec, ← bvec_wI, hγz, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0,
      Complex.ofReal_one, one_smul]
  have hMγ : M * γ = γ * μ := by rw [hM, Matrix.mul_assoc, hγi, Matrix.mul_one]
  have h2 : herm (Hpk k r) (embWb k r M *ᵥ D.z) D.z = -((Tz k r D.z : ℝ) : ℂ) * d := by
    conv_lhs => rw [hzE]
    rw [embWb_mulVec, herm_wbE, mulVec_smul, mulVec_mulVec, hMγ, ← mulVec_mulVec, herm_smul, herm_mulVec, hγu,
      herm_mud_last hk d, Complex.conj_ofReal, ← Complex.ofReal_mul, hs, Real.mul_self_sqrt hT.le]
    ring

  have hB1 : bigCell k r c 1 ∈ GV k r := bigCell_one_unitary c hc
  have hEM : embWb k r M ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨M, h1, rfl⟩
  have hg0 : g0 k r γ c d = bigCell k r c 1 * embWb k r M := (hBCF k r c M).1
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rw [hg0]; exact (hClG k r).mul_mem _ hB1 _ hEM.1
  · set Γ := embWb k r γ with hΓdef
    set Γi := embWb k r γ⁻¹ with hΓidef
    have hΓΓi : Γ * Γi = 1 := by rw [hΓdef, hΓidef, ← embWb_mul, hγi', embWb_one]
    have hΓiΓ : Γi * Γ = 1 := by rw [hΓdef, hΓidef, ← embWb_mul, hγi, embWb_one]
    have hΓinv : Γ⁻¹ = Γi := inv_eq_right_inv hΓΓi
    have hΓW : Γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγu, rfl⟩
    have hΓiW : Γi ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ⁻¹, hHbi, rfl⟩
    have hconjM : ∀ N, embWb k r (γ * N * γ⁻¹) = Γ * embWb k r N * Γi := by
      intro N; rw [embWb_mul, embWb_mul]
    have e1 : Γi * g0 k r γ c d * Γ = bigCell k r c μ := by
      rw [hg0, hM, hconjM, (hBCF k r c μ).1]
      rw [show Γi * (bigCell k r c 1 * (Γ * embWb k r μ * Γi)) * Γ =
          (Γi * bigCell k r c 1) * Γ * embWb k r μ * (Γi * Γ) by simp only [Matrix.mul_assoc]]
      rw [(hUWb k r).2.2 c Γi hΓiW, Matrix.mul_assoc (bigCell k r c 1) Γi Γ, hΓiΓ, Matrix.mul_one, Matrix.mul_one]
    have e2 : gbar k r γ (g0 k r γ c d) =
        bigCell k r (star c) 1 * embWb k r (γ * μ.map (starRingEnd ℂ) * γ⁻¹) := by
      unfold gbar
      rw [hΓinv, e1, bigCell_map_conj, (hBCF k r (star c) _).1, hconjM, ← Matrix.mul_assoc Γ,
        (hUWb k r).2.2 (star c) Γ hΓW]
      simp only [Matrix.mul_assoc]
    have hB1' : bigCell k r (star c) 1 * bigCell k r c 1 = 1 := bigCell_star_mul c hc
    have hμc : μ.map (starRingEnd ℂ) * μ = 1 := mud_conj_mul hk d hd
    have hE : embWb k r (γ * μ.map (starRingEnd ℂ) * γ⁻¹) * embWb k r M = 1 := by
      rw [← embWb_mul, hM, show γ * μ.map (starRingEnd ℂ) * γ⁻¹ * (γ * μ * γ⁻¹) =
          γ * (μ.map (starRingEnd ℂ) * μ) * γ⁻¹ by
            simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc γ⁻¹ γ, hγi, Matrix.one_mul],
        hμc, Matrix.mul_one, hγi', embWb_one]
    have hg0' : g0 k r γ c d = embWb k r M * bigCell k r c 1 := (hBCF k r c M).2
    unfold th
    rw [e2, Matrix.mul_inv_rev, inv_eq_right_inv hE, inv_eq_right_inv hB1', hg0']
  · have hz' : D.z' = D.z := hD.z_eq
    have hcond : Tz k r D.z * Tz k r D.z' <
        Complex.normSq (herm (Hpk k r) (embWb k r M *ᵥ D.z') D.z) := by
      rw [hz', h2, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal]
      have h1d : 1 < Complex.normSq d := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg d]
      have hTT : 0 < Tz k r D.z * Tz k r D.z := mul_pos hT hT
      nlinarith
    obtain ⟨h, hh, h', hh', hm⟩ :=
      hRC k r D.z D.z' D.μsec hk D.z_mem D.z'_mem D.T_pos D.T'_pos D.sec (embWb k r M) hEM hcond
    rw [hz', h2] at hm
    rw [hz'] at hh'
    have hu := (hClW k r D.z).unit h hh
    have hu' := (hClW k r D.z).unit h' hh'
    refine ⟨h⁻¹, (hClW k r D.z).inv_mem h hh, h'⁻¹, (hClW k r D.z).inv_mem h' hh', ?_⟩
    rw [nonsing_inv_nonsing_inv h hu]
    show bigCell k r c (D.μsec (-((Tz k r D.z : ℝ) : ℂ) * d)) = h * g0 k r γ c d * h'⁻¹
    have hE : embWb k r (D.μsec (-((Tz k r D.z : ℝ) : ℂ) * d)) = h * embWb k r M * h'⁻¹ := by
      rw [hm]; simp only [← Matrix.mul_assoc]
      rw [mul_nonsing_inv h hu, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv h' hu', Matrix.mul_one]
    have hcm := (hUWb k r).2.2 c h ((hUWb k r).2.1 D.z hh)
    rw [(hBCF k r c _).1, hE, hg0]
    simp only [← Matrix.mul_assoc]
    rw [← hcm]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem stSchurG : StSchurG := by
  intro k r Wp _ _ _ D X _ hX
  letI := X.hN
  letI := X.hI
  letI := X.hC

  haveI : Nontrivial X.Hs := ⟨⟨X.w, 0, fun h => by
    have hw := X.w_norm
    rw [h, norm_zero] at hw
    exact zero_ne_one hw⟩⟩
  obtain ⟨d, hd, h⟩ := schur_GV D.haarG X.rep X.irr (fun v w => hX v w)
  exact ⟨d, hd, fun v w v' w' => h v w v' w'⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def StCut0 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), ∀ g ∈ GV k r, ∀ v ∈ DDinf D X, X.σ g v ∈ DDinf D X

def StCut1p : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (A : ℝ) (m : ℕ) (f : Mat k r → ℂ) (X₀ : Wp →L[ℂ] Wp), InCC A m f → InCC A m (fun g => f g • X₀)

def StCut1 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → ∀ d : ℝ, IsFdegG D X d →
    ∀ (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp), (∀ g ∈ GV k r, f g = mc X x y g) →
    ∀ p : SS k r, D.inSS p →
      Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) p =
        hsInner ((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)) X₀ *
          (mc X x a₂ (Matrix.of p.2.2 * Matrix.of p.2.1) *
            star (mc X y b₂ (Matrix.of p.1.2 * Matrix.of p.1.1))) / (d : ℂ)

def StCut2 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → ∀ d : ℝ, IsFdegG D X d →
    ∀ (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp), (∀ g ∈ GV k r, f g = mc X x y g) →
    Integrable (beInt D X x a₂) (D.μW.prod D.μN) → Integrable (beInt D X y b₂) (D.μW.prod D.μN) →
      Integrable (Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀)) D.μSS ∧
      ∫ p, xiTau D (1, 1) p * Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) p ∂D.μSS =
        hsInner ((ContinuousLinearMap.adjoint (beOp D X y b₂)).comp (beOp D X x a₂)) X₀ / (d : ℂ)

def StCut4 : Prop :=
  StSchurW →
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp), IsDiag D → ∀ (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (P₁ Q P₂ Q₂ : Wp →L[ℂ] Wp),
    (∀ h ∈ UWset k r D.z, (ContinuousLinearMap.adjoint P₁).comp ((D.π h).comp Q) =
      (ContinuousLinearMap.adjoint P₂).comp ((D.π (th k r γ h)).comp Q₂)) →
    ((∀ x y x' y' : Wp, ∫ h : Mt k r, ⟪y, D.π (th k r γ (Matrix.of h)) x⟫_ℂ *
        star ⟪y', D.π (Matrix.of h) x'⟫_ℂ ∂D.μW = 0) →
      ∀ x y ξ η : Wp, ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ = 0) ∧
    (∀ C₀ : Wp ≃ₗᵢ⋆[ℂ] Wp,
      (∀ h ∈ UWset k r D.z, ∀ x y : Wp, ⟪y, D.π (th k r γ h) x⟫_ℂ = ⟪C₀ x, D.π h (C₀ y)⟫_ℂ) →
      ∀ x y ξ η : Wp, ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ = ⟪η, C₀ (P₂ y)⟫_ℂ * ⟪C₀ (Q₂ x), ξ⟫_ℂ)

def StCut3 : Prop :=
  StInvGroup →
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ x y x' y' : X.Hs,
      ∫ g : Mt k r, ⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪y', X.σ (Matrix.of g) x'⟫_ℂ ∂D.μG = 0) →
    ∀ (a₁ b₁ a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp) (p : SS k r), D.inSS p →
      Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) p = 0

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
