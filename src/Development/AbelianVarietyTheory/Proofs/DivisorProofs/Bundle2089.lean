module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle121
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle005
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle024
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle009

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

theorem latCorr_blockLat : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [DecidableEq D] [DecidableEq D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ}, IsUnif ϖ → IsUnif ϖ₂ → ∀ (e : ℕ) (P : Finset D) (P₂ : Finset D₂), (∀ c, c ∈ P₂ ↔ cD c ∈ P) → LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := by
  intro k k' _ _ _ _ _ _ _ _ j D D₂ _ _ hj cD ϖ ϖ₂ hϖ hϖ₂ e P P₂ hP x
  have hu : valuation k' (j (ϖ : k)) = valuation k' (ϖ₂ : k') := by
    have h1 := isUnif_map hj hϖ
    exact h1.trans hϖ₂.symm
  have hb : ∀ c : D₂, valuation k' ((blockUnits ϖ₂ e P₂ c : k'ˣ) : k') =
      valuation k' (j (blockUnits ϖ e P (cD c) : kˣ)) := by
    intro c
    by_cases hc : c ∈ P₂
    · have hc' : cD c ∈ P := (hP c).1 hc
      simp only [blockUnits, if_pos hc, if_pos hc', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
        map_pow, hu]
    · have hc' : cD c ∉ P := fun h => hc ((hP c).2 h)
      simp [blockUnits, hc, hc']
  show (∀ c, valuation k' (j (x (cD c))) ≤ valuation k' ((blockUnits ϖ₂ e P₂ c : k'ˣ) : k')) ↔
    ∀ d, valuation k (x d) ≤ valuation k ((blockUnits ϖ e P d : kˣ) : k)
  simp only [hb, val_le_iff hj]
  exact ⟨fun h d => by simpa using h (cD.symm d), fun h c => h (cD c)⟩

end GlobalTheory.PureMatch.Transport
end
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

section
variable {k k' : Type} [Field k] [Field k'] {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem gdet_glTrEquiv_ffun (j : k ≃+* k') (e : D₂ ≃ D) (g : GL D k) :
    gdet (glTrEquiv j e g) = Units.map (j : k →* k') (gdet g) := by
  apply Units.ext
  show (glTrEquiv j e g).val.det = j g.val.det
  rw [glTrEquiv_val, show trM j e e g.val = (g.val.map j).submatrix e e from rfl, det_submatrix_equiv_self]
  exact ((j : k →+* k').map_det g.val).symm

theorem invT_glTrEquiv_ffun (j : k ≃+* k') (e : D₂ ≃ D) (g : GL D k) :
    (invT (glTrEquiv j e g)).val = trM j e e (invT g).val := by
  have h1 : (invT (glTrEquiv j e g)).val = ((glTrEquiv j e g)⁻¹).valᵀ := rfl
  have h2 : (invT g).val = (g⁻¹).valᵀ := rfl
  rw [h1, h2, ← map_inv, glTrEquiv_val]
  rfl

end

attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace in
theorem fFun_trM : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂] [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k'] (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D) (μ₂ : Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D), (∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) → ∀ (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ), (∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) → ∀ (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k), fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z := by
  intro k k' _ _ _ _ _ _ _ _ j A A' D A₂ A₂' D₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj rA rA' cD μ₂ hμ₂ σ₂ σ hσ ν₂ ν hν Ψ Z
  letI : BorelSpace (GL A' k) := _root_.GlobalTheory.SplitFlip.borel_GL
  letI : BorelSpace (GL A₂' k') := _root_.GlobalTheory.SplitFlip.borel_GL
  have hμ : (pullMeas hj rA' μ₂).IsHaarMeasure :=
    @isHaar_pullMeas A' A₂' _ _ _ _ k k' _ _ _ _ _ _ _ _ j _ _ _ _ hj rA' μ₂ hμ₂
  have hcard : Fintype.card D₂ = Fintype.card D := Fintype.card_congr cD
  have hX : ∀ M : Matrix D D k, trM j rA cD (X0 k σ * M) = X0 k' σ₂ * trM j cD cD M := fun M => by
    ext r c
    rw [trM_apply, frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply, trM_apply, hσ]; rfl
  have hY : ∀ M : Matrix D D k, trM j rA' cD (Y0 k σ * M) = Y0 k' σ₂ * trM j cD cD M := fun M => by
    ext r c
    rw [trM_apply, frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply, trM_apply, hσ]; rfl
  have hS : ∀ Y : Matrix A' D k, smallF μ₂ ν₂ Ψ (trM j rA' cD Y) =
      smallF (pullMeas hj rA' μ₂) ν (fun Y => Ψ (trM j rA' cD Y)) Y := fun Y => by
    conv_lhs => rw [← map_pullMeas hj rA' μ₂]
    unfold smallF
    have := integral_map_equiv (μ := pullMeas hj rA' μ₂) (glTr hj rA').toHomeomorph.toMeasurableEquiv
      (fun g => Ψ (g.val * trM j rA' cD Y) * (ν₂ (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D₂ : ℂ) / 2))
    refine Eq.trans this ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show Ψ ((glTrEquiv j rA' g).val * trM j rA' cD Y) * ν₂ (gdet (glTrEquiv j rA' g)) *
      apow (gdet (glTrEquiv j rA' g)) _ = _
    rw [gdet_glTrEquiv_ffun, apow_map hj, ← hν, glTrEquiv_val, ← trM_mul, hcard]
  by_cases h : ∃ h : GL D k, Z = X0 k σ * (invT h).val
  · obtain ⟨h, rfl⟩ := h
    rw [hX, ← invT_glTrEquiv_ffun]
    erw [_root_.GlobalTheory.SplitFlip.splitTheta_fFun_frameFirstBlock_mul,
      @_root_.GlobalTheory.SplitFlip.splitTheta_fFun_frameFirstBlock_mul
        k _ _ _ _ A A' D _ _ _ _ _ _ _ _ (pullMeas hj rA' μ₂) hμ σ ν
        (fun Y => Ψ (trM j rA' cD Y)) h]
    rw [gdet_glTrEquiv_ffun, apow_map hj, ← hν, glTrEquiv_val, ← hY, hS, hcard]
  · have h' : ¬ ∃ h₂ : GL D₂ k', trM j rA cD Z = X0 k' σ₂ * (invT h₂).val := by
      rintro ⟨h₂, H⟩
      obtain ⟨g, rfl⟩ := (glTrEquiv j cD).surjective h₂
      rw [invT_glTrEquiv_ffun, ← hX] at H
      exact h ⟨g, trM_injective j rA cD H⟩
    unfold _root_.GlobalTheory.SplitFlip.fFun
    rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.PureMatch.Transport
end
end

section

noncomputable section

open NumberField

namespace GlobalTheory.VacRead

theorem int_of_mem_bInv (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {γ : D.host.E} (hγ : γ ∈ cE D D.host.ccK) {c : 𝓞 D.host.K} (hcc : c ∈ cc) {y : D.host.E} (hy : y ∈ bInv D cc r) :
    GlobalTheory.InertSign.IntE D (D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * y /
      (Ideal.absNorm D.host.ccK : D.host.E)) := by
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  have hN : (Ideal.absNorm cc : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hc
  have hcE : ((c : D.host.K) : D.host.E) ∈ cE D cc := Submodule.subset_span ⟨c, hcc, rfl⟩
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, hα, γ₂, hγ₂, rfl⟩ := hy
    obtain ⟨o₁, h₁⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).1 γ hγ γ₂ hγ₂
    obtain ⟨o₂, h₂⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).1 α hα _ hcE
    refine ⟨o₁ * o₂, ?_⟩
    have e : D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * (r * D.host.conj α * γ₂ / (Ideal.absNorm cc : D.host.E)) /
        (Ideal.absNorm D.host.ccK : D.host.E) =
        (D.host.conj γ * γ₂ / (Ideal.absNorm D.host.ccK : D.host.E)) *
          (D.host.conj α * ((c : D.host.K) : D.host.E) / (Ideal.absNorm cc : D.host.E)) := by
      field_simp
    rw [e, h₁, h₂, mul_div_cancel_left₀ _ hN0, mul_div_cancel_left₀ _ hN]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add (f := _), hu, hv]; ring⟩
  | smul o x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨o * u, ?_⟩
    rw [map_mul, hu, Algebra.smul_def]
    ring

theorem mul_mem_Iid (D : Formalism.BasicNotions.D7) {ε α : D.host.E} (hε : ε ∈ cE D D.host.ccK)
    (hα : α ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) : ε * α ∈ GlobalTheory.InertSign.Iid D D.host.ccK := by
  induction hε using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c₀, hc₀, rfl⟩ := hx
    exact Submodule.subset_span ⟨c₀, hc₀, α, hα, rfl⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ o hx

theorem smul_mem_homL (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {γ : D.host.E} (hγ : γ ∈ cE D D.host.ccK) {c : 𝓞 D.host.K} (hcc : c ∈ cc)
    {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)) :
    (D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ / (Ideal.absNorm D.host.ccK : D.host.E)) • A ∈
      Formalism.MainNotions.TaylorLogMetric.homL D (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hA' := GlobalTheory.ThetaLatImage.mem_homL.1 hA
  have hint : ∀ i j, GlobalTheory.InertSign.IntE D (A i j) := by
    intro i j
    have h1 : Pi.single j (1 : D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D a := by
      rw [GlobalTheory.ThetaLatImage.mem_stdL]
      intro k
      refine ⟨if k = j then 1 else 0, ?_⟩
      by_cases h : k = j
      · subst h; simp
      · simp [h]
    have h2 := GlobalTheory.ThetaLatImage.mem_stdL.1 (hA' _ h1) i
    have hcol : A.mulVec (Pi.single j 1) i = A i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rwa [hcol] at h2
  rw [GlobalTheory.ThetaLatImage.mem_homL]
  intro x hx
  rw [GlobalTheory.ThetaLatImage.mem_stdL]
  intro i
  have hy : A.mulVec x i ∈ bInv D cc r := by
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨o, ho⟩ := hint i j
    rw [← ho, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o (mem_lsB.1 hx j)
  have := int_of_mem_bInv D cc r hc hr hγ hcc hy
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  convert this using 1
  ring

theorem gen_mem_RL (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {c : 𝓞 D.host.K} (hcc : c ∈ cc) {α : D.host.E} (hα : α ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)) :
    (r⁻¹ * (((c : D.host.K) : D.host.E) * α)) • A ∈
      GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  set X := r⁻¹ * (((c : D.host.K) : D.host.E) * α) with hX
  have key : ∀ t ∈ Submodule.span (𝓞 D.host.E) {t | ∃ γ ∈ cE D D.host.ccK, ∃ ε ∈ cE D D.host.ccK,
      t = D.host.conj γ * ε},
      (t * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A ∈
        GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨γ, hγ, ε, hε, rfl⟩ := ht
      have e : (D.host.conj γ * ε * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A =
          (ε * α) • ((D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ /
            (Ideal.absNorm D.host.ccK : D.host.E)) • A) := by
        rw [smul_smul, hX]
        congr 1
        ring
      rw [e]
      exact Submodule.subset_span ⟨ε * α, mul_mem_Iid D hε hα, _, smul_mem_homL D cc r a d hc hr hγ hcc hA, rfl⟩
    | zero => rw [zero_mul, zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_mul, add_smul]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx => rw [smul_mul_assoc, smul_assoc]; exact Submodule.smul_mem _ o hx
  have h := key _ (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).2
  rwa [mul_inv_cancel_left₀ hN0] at h

theorem rl_div_scale : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ), cc ≠ ⊥ →
    GlobalTheory.NormExact.IsScale D cc r → ∀ z ∈ GlobalTheory.InertSign.RL D cc (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d),
      r⁻¹ • z ∈ GlobalTheory.InertSign.RL D D.host.ccK (GlobalTheory.VacRead.lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  intro D cc r a d hc hs z hz
  have hr : r ≠ 0 := GlobalTheory.NormExact.IsScale.ne_zero hc hs
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    rw [smul_smul]
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨c, hcc, α, hα, rfl⟩ := ht
      exact gen_mem_RL D cc r a d hc hr hcc hα hA
    | zero => rw [mul_zero, zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add, add_smul]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx => rw [mul_smul_comm, smul_assoc]; exact Submodule.smul_mem _ o hx
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

end GlobalTheory.VacRead
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.TorsionAnyChar

noncomputable section

namespace GlobalTheory.PeriodsAnyChar

end GlobalTheory.PeriodsAnyChar

open GlobalTheory.PeriodsAnyChar

namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

end GlobalTheory.UT.CoefVal

namespace GlobalTheory.UT.CoefUnit
open GlobalTheory.UT.CoefBasic

end GlobalTheory.UT.CoefUnit

namespace GlobalTheory.UT.SmallPoint
open CoefBasic

end GlobalTheory.UT.SmallPoint

namespace GlobalTheory.UT.SmallZero
open CoefBasic SmallPoint

end GlobalTheory.UT.SmallZero

namespace GlobalTheory.UT.EvalZero
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

end GlobalTheory.UT.EvalZero

namespace GlobalTheory.UT.MixedConv
open GlobalTheory.FieldBaseChange

section Core
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]

end Core

end GlobalTheory.UT.MixedConv

namespace GlobalTheory.UT

theorem _root_.GlobalTheory.PeriodsAnyChar.weilQkIs_iff_weilIs : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ) := by
  intro hL R _ _ I _ D A G _ _ _ U F _ _ _ k hk p p' x x' hx hx' ζ
  have hG := hL.1.globalFns
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  obtain ⟨ρ, hρ, hcomm, -⟩ := thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_commIsOf hG A.isAb A.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, Units.ext (by simp [unitOn])⟩
  let E : SecM A.A A.L (k : ℤ) (TFK (R := R) F) → Fam D.toPre F k := fun v => e (SecM.toSec A.A v)
  have hE : ∀ s, ∃ v, E v = s := fun s => ⟨SecM.ofSec A.A (e.symm s), e.apply_symm_apply s⟩
  have a : ∀ v, PhiRel D.toPre F k p w (E v) (E (ρ θ v)) := fun v =>
    h _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have a' : ∀ v, PhiRel D.toPre F k p' w' (E v) (E (ρ θ' v)) := fun v =>
    h' _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have b : ∀ v t, PhiRel D.toPre F k p w (E v) t → t = E (ρ θ v) := fun v t H =>
    phi_unique p w ((phiRel_iff hG p w hw _ _).1 H) ((phiRel_iff hG p w hw _ _).1 (a v))
  have b' : ∀ v t, PhiRel D.toPre F k p' w' (E v) t → t = E (ρ θ' v) := fun v t H =>
    phi_unique p' w' ((phiRel_iff hG p' w' hw' _ _).1 H) ((phiRel_iff hG p' w' hw' _ _).1 (a' v))
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' (z : F) (fun s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ => by
    obtain ⟨v, rfl⟩ := hE s
    obtain rfl := b' _ _ h₁
    obtain rfl := b _ _ h₂
    obtain rfl := b _ _ h₃
    obtain rfl := b' _ _ h₄
    rw [hcomm θ θ' _ hc v]
    exact e.map_smul (z : F) (SecM.toSec A.A (ρ θ' (ρ θ v)))) (by
    obtain ⟨B, hB, -⟩ := BoxSpan.exists_basis hL.1.secBaseChange A k hk F (jFK (R := R) F)
    have : Nontrivial Γ((TFK (R := R) F).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    have hne := hB.ne_zero ⟨0, pow_pos hk _⟩
    refine ⟨_, _, _, a (B ⟨0, pow_pos hk _⟩), a' _, fun h0 => hne ?_⟩
    have h1 : SecM.toSec A.A (ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩))) = _ := e.map_eq_zero_iff.1 h0
    have h2 : ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩)) = 0 := congrArg (SecM.ofSec A.A) h1
    exact (ρ θ).map_eq_zero_iff.1 ((ρ θ').map_eq_zero_iff.1 h2)) hk (ζ : F)
  have hz := GlobalLift.weilIs_of_commIsOf hG A.isAb A.isLB hc
  rw [key]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective (CommutatorPairing.weilIs_unique hG A.isAb A.isLB H hz))

end GlobalTheory.UT

namespace GlobalTheory.TorsionIso

theorem _root_.GlobalTheory.PeriodsAnyChar.torsion_map : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), (∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f p) ∧ ((k : F) ≠ 0 → ∀ x, x ^ k = 1 → ∃ p, f p = x) ∧ (∀ p p', f p = f p' ↔ QkPt.Equiv D.toPre F p p') ∧ (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧ ∀ p p' (z : Fˣ), WeilQkIs D.toPre F k p p' z ↔ WeilIs A.A A.L k (f p) (f p') (unitOn z) := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k hk
  have hqk := indAtTransl_any hL R I hI D A G hG U F k hk
  have hcomp := indAtComp_any hL R I hI D A G hG U F k hk
  have huniq := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hinj := GlobalTheory.TorsionMapInj.qkToAk_injective hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hex : ∀ p : QkPt D.toPre F k, ∃ x, QkToAkU U.toUnifPre F k p x := fun p => by
    obtain ⟨x, hx⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
    exact ⟨x, (hqk p x).1 (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩
  choose f hf using hex
  have hwd : ∀ p p', QkPt.Equiv D.toPre F p p' → f p = f p' := fun p p' h =>
    huniq p' _ _ ((hqk _ _).1 ((hcomp p p' p' _ (𝟙 _) ((hqk _ _).2 (hf p))).2.1 h)) (hf p')
  have hpow : ∀ p, f p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U.ext
    exact (hf p w hw).1
  refine ⟨f, fun p x => ⟨fun h => huniq p _ _ h (hf p), fun h => h ▸ hf p⟩, ?_,
    fun p p' => ⟨fun h => hinj p p' (f p) (hf p) (h ▸ hf p'), hwd p p'⟩, ?_,
    fun p p' z => GlobalTheory.PeriodsAnyChar.weilQkIs_iff_weilIs hL R I hI D A G hG U F k hk p p' _ _ (hf p) (hf p') z⟩
  · intro hkF x hx
    obtain ⟨p, hp⟩ := exists_qkToAkU R I hI D A G hG U F k hkF x hx
    exact ⟨p, huniq p _ _ (hf p) hp⟩
  · intro p p' p'' h
    have := (hcomp p p' p'' _ _ ((hqk _ _).2 (hf p))).1 ((hqk _ _).2 (hf p')) h
    rw [translT_comp] at this
    exact huniq p'' _ _ (hf p'') ((hqk _ _).1 this)

end GlobalTheory.TorsionIso

namespace GlobalTheory.LevelCompat
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem _root_.GlobalTheory.PeriodsAnyChar.qkToAkU_level : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n → N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, (q.y = n • p.y → q.g = p.g → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F N q x)) ∧ (p.y = q.y → GtPtF.IsNsmul n q.g p.g → QkToAkU U.toUnifPre F N q x → QkToAkU U.toUnifPre F k p (x ^ n)) := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k n N hk hn hN
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hn
  obtain ⟨f, hf, -⟩ := GlobalTheory.PeriodsAnyChar.torsion_map hL R I hI D A G hG U F k hk
  obtain ⟨f', hf', -, -, hadd, -⟩ := GlobalTheory.PeriodsAnyChar.torsion_map hL R I hI D A G hG U F N hN1
  have key : ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → f p = f' q := by
    intro p q hy hg
    obtain ⟨x₀, h₀⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
    have a := (indAtTransl_any hL R I hI D A G hG U F k hk p x₀).1
      (h₀ 1 k le_rfl (Nat.mul_one k).symm p (one_nsmul _).symm rfl)
    have b := (indAtTransl_any hL R I hI D A G hG U F N hN1 q x₀).1 (h₀ n N hn hN q hy hg)
    exact ((hf p x₀).1 a).symm.trans ((hf' q x₀).1 b)
  intro p q x
  refine ⟨fun hy hg => by rw [hf, hf', key p q hy hg], fun hy hg hx => ?_⟩
  have hx' : x = f' q := (hf' q x).1 hx
  have hp : ∀ j : ℕ, f' (qkNsmul D.tau_bimult (j + 1) q) = x ^ (j + 1) := by
    intro j
    induction j with
    | zero => rw [Nat.zero_add, qkNsmul_one, pow_one, hx']
    | succ j ih => rw [hadd _ _ _ (qkAdd_qkNsmul D.tau_bimult (j + 1) q), ih, ← hx', ← pow_succ]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [hf, ← hp j]
  exact (key p _ (by rw [hy]; rfl) ((isNsmul_iff_eq _ _ _).1 hg).symm).symm

end GlobalTheory.LevelCompat

namespace GlobalTheory.UT.EndTors
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic
attribute [local instance] gtGroup

end GlobalTheory.UT.EndTors

namespace GlobalTheory.UT.EndBaseChange
open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

end GlobalTheory.UT.EndBaseChange

end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := by
  first | exact @GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar | exact GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar | (intros; apply GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar <;> assumption)
end
