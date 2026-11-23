module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle051
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024

@[expose] public section

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.IndDual

attribute [local instance 2000] _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace

section Real

open GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace k] [BorelSpace k]

theorem integral_KO_mul_right_real (μ : Measure (GL n k)) [μ.IsHaarMeasure] {f : GL n k → ℝ}
    (hf : Continuous f) (hlaw : ∀ (p : parab k e) x, f (p * x) = modulus k m (leviProj k e p) * f x)
    (g : GL n k) :
    ∫ x in (KO k n : Set (GL n k)), f (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), f x ∂μ := by
  have h1 : IntegrableOn (fun x => f (x * g)) (KO k n : Set (GL n k)) μ :=
    (hf.comp (continuous_mul_const g)).continuousOn.integrableOn_compact isCompact_KO
  have h2 : IntegrableOn f (KO k n : Set (GL n k)) μ := hf.continuousOn.integrableOn_compact isCompact_KO
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2,
    UnitInd.lintegral_KO_mul_right e μ (φ := fun x => ENNReal.ofReal (f x)) hf.measurable.ennreal_ofReal
      (fun p x => by rw [hlaw, ENNReal.ofReal_mul (modulus_pos k _).le]) g,
    UnitInd.lintegral_KO_mul_right e μ (φ := fun x => ENNReal.ofReal (-f x)) hf.neg.measurable.ennreal_ofReal
      (fun p x => by rw [hlaw, ← mul_neg, ENNReal.ofReal_mul (modulus_pos k _).le]) g]

theorem integral_integralGL_mul_right_complex_productSigma (μ : Measure (GL n k)) [μ.IsHaarMeasure] {F : GL n k → ℂ}
    (hF : Continuous F) (hlaw : ∀ (p : parab k e) x, F (p * x) = (modulus k m (leviProj k e p) : ℂ) * F x)
    (g : GL n k) :
    ∫ x in (KO k n : Set (GL n k)), F (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), F x ∂μ := by
  have h1 : IntegrableOn (fun x => F (x * g)) (KO k n : Set (GL n k)) μ :=
    (hF.comp (continuous_mul_const g)).continuousOn.integrableOn_compact isCompact_KO
  have h2 : IntegrableOn F (KO k n : Set (GL n k)) μ := hF.continuousOn.integrableOn_compact isCompact_KO
  have hre := integral_KO_mul_right_real e μ (Complex.continuous_re.comp hF)
    (fun p x => by simp [hlaw]) g
  have him := integral_KO_mul_right_real e μ (Complex.continuous_im.comp hF)
    (fun p x => by simp [hlaw]) g
  refine Complex.ext ?_ ?_
  · exact ((integral_re h1).symm.trans hre).trans (integral_re h2)
  · exact ((integral_im h1).symm.trans him).trans (integral_im h2)

end Real

theorem integral_KO_mul_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure] (F : GL n k → ℂ), Continuous F → (∀ (p : parab k e) (g : GL n k), F (p * g) = (modulus k m (leviProj k e p) : ℂ) * F g) → ∀ g : GL n k, ∫ x in (KO k n : Set (GL n k)), F (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), F x ∂μ := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e M hM μ _ F hF hlaw g
  borelize k
  obtain rfl : M = Units.instMeasurableSpace :=
    hM.measurable_eq.trans (SplitFlip.borel_GL (k := k) (n := n)).measurable_eq.symm
  exact integral_integralGL_mul_right_complex_productSigma e μ hF hlaw g

end GlobalTheory.SmGL.IndDual
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.TwistVertex

section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem toBlocks₁₁_eq_one {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) : u.val.toBlocks₁₁ = 1 := by
  ext i j
  have := RootEx.Model.mem_N_iff.1 hu (.inl i) (.inl j) le_rfl
  simpa [toBlocks₁₁, Matrix.one_apply] using this

theorem val_embX (g : GL n k) : (embX c g).val = fromBlocks g.val 0 0 1 := rfl

end Plain

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section General
variable {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem embX_mem_KO {g : GL n k} (hg : g ∈ KO k n) : embX c g ∈ KO k (n ⊕ Fin c) := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hg
  refine mem_KO.2 ⟨?_, ?_⟩
  · rw [val_embX]; exact intM_fromBlocks.2 ⟨h1, intM_zero, intM_zero, intM_one⟩
  · rw [← map_inv, val_embX]; exact intM_fromBlocks.2 ⟨h2, intM_zero, intM_zero, intM_one⟩

theorem mem_KO_of_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) {g : GL n k}
    (h : u * embX c g ∈ KO k (n ⊕ Fin c)) : g ∈ KO k n := by
  obtain ⟨h1, h2⟩ := mem_KO.1 h
  have e1 : (u * embX c g).val.toBlocks₁₁ = g.val := by
    rw [Units.val_mul, mul_toBlocks₁₁, toBlocks₁₁_eq_one hu, val_embX]; simp
  have e2 : ((u * embX c g)⁻¹).val.toBlocks₁₁ = (g⁻¹).val := by
    rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, mul_toBlocks₁₁, toBlocks₁₁_eq_one (inv_mem hu), val_embX]; simp
  exact mem_KO.2 ⟨e1 ▸ fun i j => h1 _ _, e2 ▸ fun i j => h2 _ _⟩

theorem simpleSum_mem {u : GL (n ⊕ Fin c) k} (hu : u ∈ KO k (n ⊕ Fin c)) : simpleSum u ∈ 𝒪[k] := by
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  split_ifs
  · exact intM_of_mem_KO hu _ _
  · exact zero_mem _

end General

section Empty
variable {r e n : Type*} [Fintype r] [DecidableEq r] [Fintype e] [DecidableEq e] [IsEmpty e]
  [Fintype n] [DecidableEq n] {c : ℕ} {δ : kˣ →* ℂˣ} {hδ : IsTame δ}

theorem mem_level_iff (o : r ⊕ e ≃ n ⊕ Fin c) (x : GL (n ⊕ Fin c) k) :
    x ∈ ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).J ↔ x ∈ KO k (n ⊕ Fin c) := by
  have e0 : ∀ y : GL (n ⊕ Fin c) k, ((plainFrame (k := k) o).conj.symm y).val = y.val.submatrix o o := by
    intro y
    have : (plainFrame (k := k) o).conj.symm y = (reGL o).symm y := by
      rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply]; simp [plainFrame]
    rw [this, reGL_symm_val]
  rw [Level.mem_map, mem_parahoric, mem_KO, mem_KO, ← map_inv, e0, e0]
  refine ⟨fun ⟨⟨h1, h2⟩, _⟩ => ⟨fun i j => ?_, fun i j => ?_⟩,
    fun ⟨h1, h2⟩ => ⟨⟨fun i j => h1 _ _, fun i j => h2 _ _⟩, fun i => isEmptyElim i⟩⟩
  · simpa using h1 (o.symm i) (o.symm j)
  · have := h2 (o.symm i) (o.symm j)
    rwa [submatrix_apply, o.apply_symm_apply, o.apply_symm_apply] at this

theorem level_lam (o : r ⊕ e ≃ n ⊕ Fin c)
    (x : ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).J) :
    ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).lam x = 1 := by
  rw [Level.map_lam, parahoric_lam _ 1 (by ext i; exact isEmptyElim i), map_one, map_one]

end Empty

theorem firstVertex_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (s : ℕ) (t : Type) [Fintype t] [DecidableEq t] (κ : Type) [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (H : 0 + c = s + 1), (prX (Cgrp ((twistChain s t κ δ hδ η).lev 0 c H).J 1) : Set (GL (XIx κ t 0) k)) = KO k (XIx κ t 0) ∧ (∀ γ ∈ KO k (XIx κ t 0), ∃ hm : embX c γ ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨_, hm⟩ : ℂ) = 1) ∧ ∀ u ∈ N k (XIx κ t 0) c 1, ∀ hm : u ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u) := by
  intro k _ _ _ _ ψ hψ s t _ _ κ _ _ δ hδ η c H
  have hJ : ∀ x, x ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J ↔ x ∈ KO k (XIx κ t 0 ⊕ Fin c) :=
    fun x => mem_level_iff (hδ := hδ) (stdOrd κ t 0 c H) x
  have hl : ∀ x, ((twistChain s t κ δ hδ η).lev 0 c H).lam x = 1 :=
    fun x => level_lam (hδ := hδ) (stdOrd κ t 0 c H) x
  refine ⟨?_, fun γ hγ => ⟨(hJ _).2 (embX_mem_KO hγ), by rw [hl]; rfl⟩, fun u _ hm => ?_⟩
  · ext g
    simp only [SetLike.mem_coe, mem_prX, mem_Cgrp, hJ, inv_one, one_mul, mul_one]
    refine ⟨fun ⟨u, hu, _, h⟩ => mem_KO_of_mul_embX hu h, fun hg => ⟨1, one_mem _, ?_, ?_⟩⟩
    · rw [one_mul]; exact (le_sup_left : (embX c).range ≤ R k _ c 1) ⟨g, rfl⟩
    · rw [one_mul]; exact embX_mem_KO hg
  · rw [hl, hψ.eq_one (show _ ∈ cball (1 : kˣ) from simpleSum_mem ((hJ u).1 hm))]; rfl

end GlobalTheory.TwistVertex
end
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.BoxCosets

theorem finite_cosets (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (c₁ c₂ : kˣ) :
    {yb : (n → k) ⧸ box n c₂ | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb}.Finite := by
  have e : ∀ c : kˣ, (box n c : Set (n → k)) = Set.pi Set.univ (fun _ => cball c) := by
    intro c
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    rfl
  have hc : IsCompact (box n c₁ : Set (n → k)) := by
    rw [e]; exact isCompact_univ_pi fun _ => isCompact_cball c₁
  have ho : IsOpen (box n c₂ : Set (n → k)) := by
    rw [e]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball c₂
  obtain ⟨t, -, ht⟩ := hc.elim_nhds_subcover
    (fun x => (fun y => y - x) ⁻¹' (box n c₂ : Set (n → k))) (by
      intro x _
      refine (ho.preimage (continuous_id.sub continuous_const)).mem_nhds ?_
      simp)
  refine (t.finite_toSet.image (fun x => (Submodule.Quotient.mk x : (n → k) ⧸ box n c₂))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hx, hxy⟩ := this
  exact ⟨x, hx, ((Submodule.Quotient.eq _).2 hxy).symm⟩

end GlobalTheory.BoxCosets
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.StepData

open MeasureTheory ValuativeRel Matrix in
private theorem sigmaCompactSpace_of_isNonarchimedeanLocalField' (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨a, ha0, ha1⟩ := Valuation.RankOne.nontrivial (valuation k)
  obtain ⟨b, hb0, hb1⟩ : ∃ b : k, valuation k b ≠ 0 ∧ valuation k b < 1 := by
    rcases lt_or_gt_of_ne ha1 with h | h
    · exact ⟨a, ha0, h⟩
    · refine ⟨a⁻¹, by simpa using ha0, ?_⟩
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ h
  have hb : b ≠ 0 := by
    intro h
    simp [h] at hb0
  refine ⟨⟨fun m : ℕ => (fun x => (b ^ m)⁻¹ * x) '' (𝒪[k] : Set k),
    fun m => (_root_.GlobalTheory.SplitWeil.isCompact_int k).image (continuous_const.mul continuous_id), ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  set S := (IsRankLeOne.nonempty (R := k)).some
  have hf := S.strictMono
  obtain ⟨m, hm⟩ : ∃ m : ℕ, S.emb (valuation k b) ^ m * S.emb (valuation k x) ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, by simp⟩
    have hpos : 0 < S.emb (valuation k x) := by
      rw [← map_zero S.emb]
      exact hf (zero_lt_iff.2 (by simpa using hx))
    have hlt : S.emb (valuation k b) < 1 := by
      rw [← map_one S.emb]
      exact hf hb1
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hlt
    refine ⟨m, ?_⟩
    calc _ ≤ (S.emb (valuation k x))⁻¹ * S.emb (valuation k x) := by gcongr
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨m, b ^ m * x, ?_, by field_simp⟩
  rw [SetLike.mem_coe, Valuation.mem_integer_iff, ← hf.le_iff_le, map_one, map_mul, map_mul,
    map_pow, map_pow]
  exact hm


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.StepData.mul_mem_of_hat_cosetInd_ne_zero : ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ψ : AddChar k Circle) (_ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : kˣ) (ε : k)
    (yb : (n → k) ⧸ _root_.GlobalTheory.StepData.box n c) (η : n → k),
    _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb) η ≠ 0 →
    ∀ i, ε * η i * (c : k) ∈ 𝒪[k] := by
  intro k _ _ _ _ _ _ ψ hψ ν _ n _ _ c ε yb η hne i
  haveI := sigmaCompactSpace_of_isNonarchimedeanLocalField' k
  by_contra hx
  obtain ⟨t, ht, hψt⟩ : ∃ t ∈ 𝒪[k], ψ (t * (ε * η i * c)) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hx (_root_.GlobalTheory.RootEx.Unram.mem_of_psi hψ h)
  have hvmem : Pi.single i ((c : k) * t) ∈ _root_.GlobalTheory.StepData.box n c := by
    show ∀ j, valuation k (Pi.single (M := fun _ => k) i ((c : k) * t) j) ≤ valuation k (c : k)
    intro j
    rcases eq_or_ne j i with rfl | hj
    · simp only [Pi.single_eq_same, map_mul]
      exact mul_le_of_le_one_right' ht
    · simp [Pi.single_eq_of_ne hj]
  apply hne
  unfold _root_.GlobalTheory.StepData.hat
  set g : (n → k) → ℂ := fun y => _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y *
    (ψ (ε * η ⬝ᵥ y) : ℂ) with hg
  have hshift : ∀ y, g (y + Pi.single i ((c : k) * t)) = (ψ (t * (ε * η i * c)) : ℂ) * g y := by
    intro y
    have hind : _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb
        (y + Pi.single i ((c : k) * t)) =
          _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y := by
      unfold _root_.GlobalTheory.StepData.cosetInd
      simp only [Set.indicator]
      have hq : Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n c)
          (y + Pi.single i ((c : k) * t)) = Submodule.Quotient.mk y := by
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hvmem, add_zero]
      have hv0 := (Submodule.Quotient.mk_eq_zero _).2 hvmem
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact absurd (hq.symm.trans h₁) h₂
      · exact absurd (hq.trans h₂) h₁
      · rfl
    simp only [hg, hind, dotProduct_add, dotProduct_single, mul_add, AddChar.map_add_eq_mul,
      Circle.coe_mul]
    have hr : ε * (η i * ((c : k) * t)) = t * (ε * η i * c) := by ring
    rw [hr]
    ring
  have h1 := integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) g
    (Pi.single i ((c : k) * t))
  simp only [hshift, integral_const_mul] at h1
  have hne1 : (ψ (t * (ε * η i * c)) : ℂ) ≠ 1 := by
    intro h
    exact hψt (Circle.ext_iff.mpr (by simpa using h))
  have hzero : ((ψ (t * (ε * η i * c)) : ℂ) - 1) * (∫ y, g y ∂Measure.pi fun _ => ν) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 hzero).resolve_left (sub_ne_zero.2 hne1)

end GlobalTheory.StepData
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.FlatSourceStable

theorem om_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ≠ 0) : om μ g h Φ ≠ 0 := by
  intro h0
  apply hΦ
  have h1 := om_mul μ g⁻¹ g h⁻¹ h Φ
  rw [inv_mul_cancel, inv_mul_cancel, om_one, h0] at h1
  rw [h1]
  funext x
  simp [om]

theorem flat_ne_zero_of_mem_R : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ) (g : GL (n' ⊕ Fin (c + 1 + 1)) k) (h : GL (n ⊕ Fin (c + 1)) k), flat ψ ν μ Φ g h ≠ 0 → ∀ r ∈ R k n' (c + 1 + 1) 1, flat ψ ν μ Φ (r * g) h ≠ 0 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ψ ν _ μ Φ g h h0 r hr
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hr
  unfold flat at h0 ⊢
  have e : om μ (embX (c + 1 + 1) x * u * g) h Φ =
      om μ (embX (c + 1 + 1) x) 1 (om μ u 1 (om μ g h Φ)) := by
    rw [← om_mul, ← om_mul, one_mul, one_mul]
  rw [e, (GlobalTheory.RootEx.opE_om_embX k n n' (c + 1) 1 le_rfl (by omega) ψ ν μ _).2 x,
    GlobalTheory.RootExSource.opE_om_source k n n' (c + 1) 1 le_rfl (by omega) ψ ν μ _ u hu]
  refine smul_ne_zero ?_ (om_ne_zero μ _ _ (smul_ne_zero (Circle.coe_ne_zero _) h0))
  exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (nabs_pos k _) _).ne'

end GlobalTheory.FlatSourceStable
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder

noncomputable section

namespace GlobalTheory.Twist.EuclidCoord

open GlobalTheory.RealWeil.UnitaryOsc


open scoped MatrixOrder in
theorem exists_coord : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H s : Matrix ι ι ℂ), Hᴴ = H → s * s = 1 → (H * s).PosDef → ∃ (E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ)) (J : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι), (∀ x, J (J x) = -x) ∧ (∀ x, E (J x) = I • s *ᵥ E x) ∧ ∀ x y, (star (E y) ⬝ᵥ H *ᵥ E x).im = omJ J x y := by
  intro ι _ _ H s hH hs hpos
  have hP0 : (0 : Matrix ι ι ℂ) ≤ H * s := hpos.posSemidef.nonneg
  set R : Matrix ι ι ℂ := CFC.sqrt (H * s)
  have hR0 : (0 : Matrix ι ι ℂ) ≤ R := CFC.sqrt_nonneg _
  have hRh : Rᴴ = R := hR0.posSemidef.isHermitian.eq
  have hRR : R * R = H * s := CFC.sqrt_mul_sqrt_self _ hP0
  have hdet : R.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hRR
    rw [det_mul, h0, zero_mul] at e
    exact (hpos.det_pos.ne') (by rw [← e])
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det R).2 hdet.isUnit
  set s₀ : Matrix ι ι ℂ := u.1 * s * (u⁻¹).1 with hs₀
  have hs₀2 : s₀ * s₀ = 1 := by
    simp only [hs₀, mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc s, hs, one_mul, Units.mul_inv]

  have hRRs : u.1ᴴ * u.1 * s = H := by
    rw [hu, hRh, hRR, mul_assoc, hs, mul_one]
  have hform : (u⁻¹).1ᴴ * H * (u⁻¹).1 = s₀ := by
    rw [← hRRs]
    calc _ = (u.1 * (u⁻¹).1)ᴴ * (u.1 * s * (u⁻¹).1) := by simp only [mul_assoc, conjTranspose_mul]
      _ = s₀ := by simp [hs₀]
  have hs₀h : s₀ᴴ = s₀ := by
    rw [← hform, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, mul_assoc]
  let E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) :=
    (crd ι).trans (ContinuousLinearEquiv.equivOfInverse (mvL (u⁻¹).1) (mvL u.1)
      (fun v => by
        change u.1 *ᵥ (u⁻¹).1 *ᵥ v = v
        rw [mulVec_mulVec, Units.mul_inv, one_mulVec])
      (fun v => by
        change (u⁻¹).1 *ᵥ u.1 *ᵥ v = v
        rw [mulVec_mulVec, Units.inv_mul, one_mulVec]))
  have hE : ∀ x, E x = (u⁻¹).1 *ᵥ crd ι x := fun _ => rfl
  refine ⟨E, cplx s₀ hs₀h hs₀2, cplx_cplx s₀ hs₀h hs₀2, fun x => ?_, fun x y => ?_⟩
  · rw [hE, hE, crd_cplx, mulVec_smul, mulVec_mulVec, mulVec_mulVec]
    congr 2
    rw [hs₀, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
  · rw [omJ_cplx, hE, hE, form_mulVec, hform]

end GlobalTheory.Twist.EuclidCoord

end
end

section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable def hermFormImPullback {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm (h y) (h w)).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by
      rw [show h (c • a) = (c : ℂ) • h a by rw [← map_smul]; rfl]
      simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      rw [show h (c • a) = (c : ℂ) • h a by rw [← map_smul]; rfl]
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul])

theorem hermForm_eq_of_im_eq_on_spanning_lattice :
    ∀ {g : ℕ} {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ)), Submodule.span ℝ (Set.range P) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (h h' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h (P a)) (h (P b))).im = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' (P a)) (h' (P b))).im) → ∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y) := by
  intro g L _ P hsp Hm h h' hab
  have hB : hermFormImPullback Hm h = hermFormImPullback Hm h' := by
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨a, rfl⟩
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨b, rfl⟩
    exact hab a b
  have him : ∀ x y, (hermForm Hm (h x) (h y)).im = (hermForm Hm (h' x) (h' y)).im := by
    intro x y
    exact LinearMap.congr_fun₂ hB x y
  intro x y
  have hI : ∀ (k : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (hermForm Hm (k (Complex.I • x)) (k y)).im = (hermForm Hm (k x) (k y)).re := by
    intro k
    simp [hermForm, map_smul, smul_dotProduct]
  apply Complex.ext
  · rw [← hI h, ← hI h']
    exact him _ _
  · exact him x y

end GlobalTheory
end
