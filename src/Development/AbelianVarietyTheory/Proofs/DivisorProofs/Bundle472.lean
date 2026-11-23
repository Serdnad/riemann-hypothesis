module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle432
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Formalism.DoubleCosetMeasures.Statement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def entryForm (c : k) (i0 : Fin n) (j : Fin d) : Matrix (Fin n) (Fin d) k →ₗ[k] k where
  toFun Y := c * Y i0 j
  map_add' Y Y' := by simp [mul_add]
  map_smul' a Y := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mu_tr_eq_smul (ψ0 : AddChar k ℂ)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd (k := k) n d)
    (l : Matrix (Fin n) (Fin d) k →ₗ[k] k)
    (hl : ∀ Y : Matrix (Fin n) (Fin d) k, (∀ i j, Y i j ∈ 𝒪[k]) → ψ0 (l Y) = 1)
    (C : Matrix (Fin n) (Fin d) k) :
    Mu l (Tr C φ0) = ψ0 (l (-C)) • Tr C φ0 := by
  obtain ⟨hT, hTι⟩ := hTr C φ0 hφ0
  obtain ⟨hM, hMι⟩ := hMu l _ hT
  refine hι hM ((GlobalTheory.WeilM.SB _).smul_mem _ hT) ?_
  rw [map_smul, hMι, hTι, hι0]
  funext Y
  simp only [Pi.smul_apply, smul_eq_mul, intInd]
  by_cases h : ∀ i j, (Y + C) i j ∈ 𝒪[k]
  · have e : ψ0 (l Y) = ψ0 (l (-C)) := by
      calc ψ0 (l Y) = ψ0 (l (Y + C) + l (-C)) := by rw [← map_add (f := _)]; congr 2; abel
        _ = ψ0 (l (-C)) := by rw [AddChar.map_add_eq_mul, hl _ h, one_mul]
    rw [e]
  · rw [Set.indicator_of_notMem (show Y + C ∉ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} from h)]
    simp

theorem inner_eq_mul_inner (ψ0 : AddChar k ℂ)
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (l : Matrix (Fin n) (Fin d) k →ₗ[k] k) (f f' : (Fin n × Fin d → k) → ℂ)
    (hf : f ∈ GlobalTheory.WeilM.SB _) (hf' : f' ∈ GlobalTheory.WeilM.SB _) (a b : ℂ) (ha : Mu l f = a • f) (hb : Mu l f' = b • f') :
    ∫ y, f y * (starRingEnd ℂ) (f' y) ∂μ = a * (starRingEnd ℂ) b * ∫ y, f y * (starRingEnd ℂ) (f' y) ∂μ := by
  rw [← integral_const_mul, ← hMuI μ hμ l f hf f' hf', ha, hb]
  congr 1; funext y
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

end GlobalTheory.HeisUnit

namespace GlobalTheory.HeisUnit

theorem cosetRep_sub_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T T' : Fin d → SplitFlip.Res (k := k) 1) (j : Fin d) :
    (cosetRep ϖ i0 T' - cosetRep ϖ i0 T) i0 j =
      (ϖ : k)⁻¹ * (((Quotient.out (T j) : 𝒪[k]) : k) - ((Quotient.out (T' j) : 𝒪[k]) : k)) := by
  simp [cosetRep]; ring

theorem not_mem_int_of_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (hϖ : SplitFlip.IsUnif ϖ) (t t' : SplitFlip.Res (k := k) 1) (h : t ≠ t') :
    (ϖ : k)⁻¹ * (((Quotient.out t : 𝒪[k]) : k) - ((Quotient.out t' : 𝒪[k]) : k)) ∉ 𝒪[k] := by
  intro ha
  apply h
  rw [← Ideal.Quotient.mk_out t, ← Ideal.Quotient.mk_out t', Ideal.Quotient.eq]
  have hs : Quotient.out t - Quotient.out t' ∈ Ideal.span {(⟨ϖ, hϖ.mem⟩ : 𝒪[k])} := by
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, ha⟩, Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub]
    field_simp
  convert hs using 1
  exact (pow_one _).trans hϖ.maximalIdeal_eq

theorem orth_of_charsep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ)
    (hcs : (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd (k := k) n d)
    (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1) (hTT : T ≠ T')
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫ y, Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) ∂μ = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hTT
  set C := cosetRep ϖ i0 T
  set C' := cosetRep ϖ i0 T'
  have hna := not_mem_int_of_ne ϖ hϖ (T j) (T' j) hj
  rw [← cosetRep_sub_apply ϖ i0 T T' j] at hna
  obtain ⟨c, hc1, hc2⟩ := hcs.2 _ hna
  have hl : ∀ Y : Matrix (Fin n) (Fin d) k, (∀ i j, Y i j ∈ 𝒪[k]) → ψ0 (entryForm c i0 j Y) = 1 :=
    fun Y hY => hc1 _ (hY i0 j)
  have e1 := mu_tr_eq_smul ψ0 ι hι Tr hTr Mu hMu φ0 hφ0 hι0 _ hl C
  have e2 := mu_tr_eq_smul ψ0 ι hι Tr hTr Mu hMu φ0 hφ0 hι0 _ hl C'
  have hI := inner_eq_mul_inner ψ0 Mu hMuI μ hμ (entryForm c i0 j) _ _ (hTr C φ0 hφ0).1 (hTr C' φ0 hφ0).1 _ _ e1 e2
  have hA : ψ0 (entryForm c i0 j (-C)) * (starRingEnd ℂ) (ψ0 (entryForm c i0 j (-C'))) ≠ 1 := by
    rw [← Complex.inv_eq_conj (hcs.1 _), ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, ← map_neg, ← map_add (f := _),
      neg_neg, neg_add_eq_sub]
    exact hc2
  set I := ∫ y, Tr C φ0 y * (starRingEnd ℂ) (Tr C' φ0 y) ∂μ
  have h0 : (1 - ψ0 (entryForm c i0 j (-C)) * (starRingEnd ℂ) (ψ0 (entryForm c i0 j (-C')))) * I = 0 := by
    linear_combination hI
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hA))

end GlobalTheory.HeisUnit

namespace GlobalTheory.HeisUnit

theorem tr_cosetRep_orth {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ) (hψc : Continuous ψ0) (hψ1 : ψ0 ≠ 1)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd (k := k) n d)
    (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1) (hTT : T ≠ T')
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫ y, Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) ∂μ = 0 :=
  orth_of_charsep ψ0 (GlobalTheory.CharSep.unitary_and_separates ψ0 hψc hψ1) ι hι Tr hTr Mu hMu hMuI φ0 hφ0 hι0 ϖ hϖ i0 T T'
    hTT μ hμ

end GlobalTheory.HeisUnit
end
end

section

open MeasureTheory Matrix Topology

namespace GlobalTheory.RankFibre

theorem X0_mul_X0_transpose (k : Type) [Field k] (a b : ℕ) :
    GlobalTheory.SplitFlip.X0 (k := k) (finSumFinEquiv (m := a) (n := b)) *
      (GlobalTheory.SplitFlip.X0 (k := k) (finSumFinEquiv (m := a) (n := b)))ᵀ = 1 := by
  ext i j
  rw [GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply]
  simp [GlobalTheory.SplitFlip.X0, Matrix.one_apply, eq_comm]

theorem isUnit_of_rank_mul_X0 {k : Type} [Field k] {a b : ℕ} (A : Matrix (Fin a) (Fin a) k)
    (h : (A * GlobalTheory.SplitFlip.X0 (k := k) (finSumFinEquiv (m := a) (n := b))).rank = a) : IsUnit A := by
  have h1 : A.rank = Fintype.card (Fin a) := by
    refine le_antisymm (by simpa using A.rank_le_width) ?_
    simpa [h] using Matrix.rank_mul_le_left A (GlobalTheory.SplitFlip.X0 (k := k) (finSumFinEquiv (m := a) (n := b)))
  have hli : LinearIndependent k A.row := by
    rw [rank_eq_finrank_span_row] at h1
    rw [linearIndependent_iff_card_eq_finrank_span, eq_comm]; exact h1
  exact Matrix.linearIndependent_row_iff_isUnit.1 hli

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL in
theorem integrable_fibre_integrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ),
    GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB (k := k) a (a + b),
    MeasureTheory.Integrable (fun g : GL (Fin a) k =>
      Φ (g.val * GlobalTheory.SplitFlip.X0 (k := k) finSumFinEquiv) *
        (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2))
      (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := by
  intro k _ _ _ _ _ _ a b ν hν Φ hΦ
  obtain ⟨⟨hl, hK⟩, hrk⟩ := hΦ
  set X0 := GlobalTheory.SplitFlip.X0 (k := k) (finSumFinEquiv (m := a) (n := b)) with hX0
  have hc1 : IsLocallyConstant fun g : GL (Fin a) k => Φ (g.val * X0) :=
    hl.comp_continuous (Units.continuous_val.matrix_mul continuous_const)
  have hc2 := GlobalTheory.GodementJacquet.isLocallyConstant_char_det (k := k) (n := Fin a) hν
  have hc3 : IsLocallyConstant fun g : GL (Fin a) k =>
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) :=
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp
      fun x => ((x : ℝ) : ℂ) ^ (((a + b : ℕ) : ℂ) / 2)
  have hcont := ((hc1.mul hc2).mul hc3).continuous

  set D : Set (Matrix (Fin a) (Fin a) k) := {A | Φ (A * X0) ≠ 0} with hD
  have hDc : IsClosed D := by
    exact (hl.isOpen_fiber 0).isClosed_compl.preimage
      (show Continuous fun A : Matrix (Fin a) (Fin a) k => A * X0 from continuous_id.matrix_mul continuous_const)
  have hDsub : D ⊆ (fun M : Matrix (Fin a) (Fin (a + b)) k => M * X0ᵀ) '' tsupport Φ := by
    intro A hA
    refine ⟨A * X0, subset_tsupport _ hA, ?_⟩
    show A * X0 * X0ᵀ = A
    rw [Matrix.mul_assoc, hX0, X0_mul_X0_transpose, Matrix.mul_one]
  have hDcpt : IsCompact D :=
    (hK.image (show Continuous fun M : Matrix (Fin a) (Fin (a + b)) k => M * X0ᵀ from
      continuous_id.matrix_mul continuous_const)).of_isClosed_subset hDc hDsub
  have hDr : D ⊆ Set.range fun g : GL (Fin a) k => g.val := by
    intro A hA
    have hr : (A * X0).rank = a := by
      by_contra hne
      exact hA (hrk _ hne)
    exact ⟨(isUnit_of_rank_mul_X0 A hr).unit, rfl⟩
  have hS : IsCompact ((fun g : GL (Fin a) k => g.val) ⁻¹' D) :=
    GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.isCompact_preimage' hDcpt hDr
  have hcs : HasCompactSupport fun g : GL (Fin a) k => Φ (g.val * X0) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) := by
    refine HasCompactSupport.intro hS fun g hg => ?_
    have : Φ (g.val * X0) = 0 := not_not.1 hg
    simp [this]
  exact hcont.integrable_of_hasCompactSupport hcs

end GlobalTheory.RankFibre
end

section

open MeasureTheory Matrix Topology


attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL in
theorem _root_.GlobalTheory.T.integrable_full_rank_fibre :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ),
      GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB (k := k) a (a + b),
      MeasureTheory.Integrable (fun g : GL (Fin a) k =>
        Φ (g.val * GlobalTheory.SplitFlip.X0 (k := k) finSumFinEquiv) *
          (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2))
        (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := by
  intro k _ _ _ _ _ _ a b ν hν Φ hΦ
  obtain ⟨⟨hLocal, hCompact⟩, hRank⟩ := hΦ
  let σ := finSumFinEquiv (m := a) (n := b)
  let X₀ := GlobalTheory.SplitFlip.X0 (k := k) σ
  have hLocalΦ : IsLocallyConstant fun g : GL (Fin a) k => Φ (g.val * X₀) :=
    hLocal.comp_continuous (Units.continuous_val.matrix_mul continuous_const)
  have hLocalν := GlobalTheory.GodementJacquet.isLocallyConstant_char_det (k := k) (n := Fin a) hν
  have hLocalPow : IsLocallyConstant fun g : GL (Fin a) k =>
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) :=
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp
      fun x => ((x : ℝ) : ℂ) ^ (((a + b : ℕ) : ℂ) / 2)
  have hContinuous := ((hLocalΦ.mul hLocalν).mul hLocalPow).continuous

  let D : Set (Matrix (Fin a) (Fin a) k) := {A | Φ (A * X₀) ≠ 0}
  have hClosed : IsClosed D :=
    (hLocal.isOpen_fiber 0).isClosed_compl.preimage
      (show Continuous fun A : Matrix (Fin a) (Fin a) k => A * X₀ from
        continuous_id.matrix_mul continuous_const)
  have hSubset : D ⊆ (fun M : Matrix (Fin a) (Fin (a + b)) k => M * X₀ᵀ) '' tsupport Φ := by
    intro A hA
    refine ⟨A * X₀, subset_tsupport _ hA, ?_⟩
    have hTranspose : X₀ * X₀ᵀ = 1 := by
      ext i j
      change (GlobalTheory.SplitFlip.X0 (k := k) σ * X₀ᵀ) i j = _
      rw [GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply]
      simp [X₀, GlobalTheory.SplitFlip.X0, Matrix.one_apply, eq_comm]
    show A * X₀ * X₀ᵀ = A
    rw [Matrix.mul_assoc, hTranspose, Matrix.mul_one]
  have hCompactD : IsCompact D :=
    (hCompact.image (show Continuous fun M : Matrix (Fin a) (Fin (a + b)) k => M * X₀ᵀ from
      continuous_id.matrix_mul continuous_const)).of_isClosed_subset hClosed hSubset
  have hRange : D ⊆ Set.range fun g : GL (Fin a) k => g.val := by
    intro A hA
    have hFullRank : (A * X₀).rank = a := by
      by_contra hne
      exact hA (hRank _ hne)
    have hRankA : A.rank = Fintype.card (Fin a) := by
      refine le_antisymm (by simpa using A.rank_le_width) ?_
      simpa [hFullRank] using Matrix.rank_mul_le_left A X₀
    have hIndependent : LinearIndependent k A.row := by
      rw [rank_eq_finrank_span_row] at hRankA
      rw [linearIndependent_iff_card_eq_finrank_span]
      exact hRankA.symm
    exact ⟨(Matrix.linearIndependent_row_iff_isUnit.1 hIndependent).unit, rfl⟩
  have hPreimage : IsCompact ((fun g : GL (Fin a) k => g.val) ⁻¹' D) :=
    GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.isCompact_preimage' hCompactD hRange
  have hSupport : HasCompactSupport fun g : GL (Fin a) k =>
      Φ (g.val * X₀) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) := by
    refine HasCompactSupport.intro hPreimage fun g hg => ?_
    have hZero : Φ (g.val * X₀) = 0 := not_not.1 hg
    simp [hZero]
  exact hContinuous.integrable_of_hasCompactSupport hSupport
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indScal_lift_law (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    (fun x => f x ⊗ₜ[ℂ] (1:ℂ)) ∈ indSpace (parab k (blocks a b))
      ((twist ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) (deltaHalf k (Two (Fin a) (Fin b)))).comp
        (leviProj k (blocks a b))) := by
  intro p x
  have h := hf.2 p x
  apply (TensorProduct.lid ℂ ℂ).injective
  simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, MonoidHom.coe_coe] at h ⊢
  rw [h]
  simp [parChar, detRep, ofChar_apply]
  ring

def indScalLift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
  ⟨⟨fun x => f x ⊗ₜ[ℂ] (1:ℂ), indScal_lift_law ν β a b hf⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((show IsOpen {g : GL (Fin (a + b)) k | rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f} from hf.1).mem_nhds (by simp)) fun g hg => by
      have hg' : rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f := hg
      apply Subtype.ext
      funext x
      show f (x * g) ⊗ₜ[ℂ] (1:ℂ) = f x ⊗ₜ[ℂ] (1:ℂ)
      rw [show f (x * g) = f x from congrFun hg' x])⟩

theorem indScal_lift_apply (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b)
    (x : GL (Fin (a + b)) k) : TensorProduct.lid ℂ ℂ ((indScalLift ν β a b hf).1.1 x) = f x := by
  simp [indScalLift]

def indScalVal (ν β : kˣ →* ℂˣ) (a b : ℕ) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] (GL (Fin (a + b)) k → ℂ) where
  toFun F x := TensorProduct.lid ℂ ℂ (F.1.1 x)
  map_add' F G := by
    funext x
    show TensorProduct.lid ℂ ℂ (F.1.1 x + G.1.1 x) = _
    rw [map_add (f := _)]
    rfl
  map_smul' c F := by
    funext x
    show TensorProduct.lid ℂ ℂ (c • F.1.1 x) = _
    rw [map_smul]
    rfl

theorem indScal_scal_lift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    indScalVal ν β a b (indScalLift ν β a b hf) = f :=
  funext (indScal_lift_apply ν β a b hf)

theorem indScal_irreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M := by
  intro H k _ _ _ _ a b ν β hνs hνu hβs hβu M hM hinv
  have hs : IsSmoothChar (ν * β) := hνs.mul hβs
  have hu : IsUnitaryChar (ν * β) := fun g => by simp [hνu g, hβu g]
  have h₁ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp a hs hu
  have h₂ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp b hβs hβu
  have hirr := H k a b ℂ ℂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β) h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
  let S : Subrepresentation (prod₂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β)) :=
    ⟨M.comap (indScalVal ν β a b), fun g F hF => hinv _ hF g⟩
  have hS : S.toSubmodule = M.comap (indScalVal ν β a b) := rfl
  have hmem : ∀ f (hf : f ∈ indScal ν β a b), f ∈ M ↔ indScalLift ν β a b hf ∈ S.toSubmodule := fun f hf => by
    rw [hS, Submodule.mem_comap, indScal_scal_lift]
  rcases hirr.eq_bot_or_eq_top S with h | h
  · left
    refine (Submodule.eq_bot_iff M).2 fun f hf => ?_
    have h' := (hmem f (hM hf)).1 hf
    rw [h] at h'
    have h0 : indScalLift ν β a b (hM hf) = 0 := (Submodule.mem_bot ℂ).1 h'
    rw [← indScal_scal_lift ν β a b (hM hf), h0, map_zero]
  · right
    intro f hf
    refine (hmem f hf).2 ?_
    rw [h]
    exact Submodule.mem_top

end GlobalTheory.RankFibre
end
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem GlobalTheory.FullRankCoinv.fullRk_support_finite_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (S : Set (Matrix (Fin n) (Fin d) k)), IsOpen S →
    (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ E : GL (Fin n) k, E.val * Y ∈ S) →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ s : Finset (GL (Fin n) k), ∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S := by
  intro k _ _ _ _ n d S hS hcov Ψ hΨ
  obtain ⟨⟨hlc, hcs⟩, hz⟩ := hΨ
  have hcl : IsClosed (Function.support Ψ) := by
    have h := (hlc.isOpen_fiber 0).isClosed_compl
    convert h using 1
    ext Y; simp [Function.mem_support]
  have hK : IsCompact (Function.support Ψ) :=
    IsCompact.of_isClosed_subset hcs hcl (subset_tsupport Ψ)
  have hU : ∀ E : GL (Fin n) k, IsOpen ((fun Y : Matrix (Fin n) (Fin d) k => E.val * Y) ⁻¹' S) := fun E =>
    hS.preimage (Continuous.matrix_mul continuous_const continuous_id)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun E : GL (Fin n) k => (fun Y : Matrix (Fin n) (Fin d) k => E.val * Y) ⁻¹' S) hU
    (by
      intro Y hY
      have hr : Y.rank = n := by
        by_contra h
        exact hY (hz Y h)
      obtain ⟨E, hE⟩ := hcov Y hr
      exact Set.mem_iUnion.2 ⟨E, hE⟩)
  refine ⟨t, fun Y hY => ?_⟩
  have := ht hY
  simp only [Set.mem_iUnion, Set.mem_preimage] at this
  obtain ⟨E, hEt, hE⟩ := this
  exact ⟨E, hEt, hE⟩
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv

theorem exists_eq_normal_form_mul_of_rank_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) (hnd : n ≤ d)
    (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) :
    ∃ h : GL (Fin d) k, Y = GlobalTheory.FullRankCoinv.Y0 k n d * h.val := by
  let σ : Fin n ⊕ Fin (d - n) ≃ Fin d :=
    (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσ : ∀ i : Fin n, ((σ (Sum.inl i) : Fin d) : ℕ) = d - n + i := fun i => by
    simp [σ]
  have hX : X0 k σ = GlobalTheory.FullRankCoinv.Y0 k n d := by
    ext i j
    simp only [X0, GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply]
    congr 1
    apply propext
    rw [← hσ i, eq_comm]
    exact Fin.val_inj.symm
  have hc : Y.rank = Fintype.card (Fin n) := by simpa using hY
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ Y).1 hc
  exact ⟨invT h, by rw [hh, hX]⟩

end GlobalTheory.FullRankCoinv
end
