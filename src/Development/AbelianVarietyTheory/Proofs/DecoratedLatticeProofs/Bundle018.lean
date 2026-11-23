module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslationInvariantSchwartzBruhatMapFactorsInte
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle017
public import Formalism.LocalRingCardinality.Bundle001
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle016
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

@[expose] public section

section

open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)

noncomputable section
namespace GlobalTheory.GluedOrbit
open GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration (interX)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}

theorem eq_gluedS_of_mem (q : Unif k) {M : Submodule 𝒪[k] (n ⊕ Fin 1 → k)}
    (hq : ∀ x ∈ M, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) {m : n ⊕ Fin 1 → k} (hm : m ∈ M)
    (hm1 : m (Sum.inr 0) = q.inv) : M = gluedS q 1 (interX M) (m ∘ Sum.inl) := by
  have hqi : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  ext y
  rw [GlobalTheory.LevelUnfold.mem_gluedS]
  constructor
  · intro hy
    refine ⟨⟨_, hq y hy⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    · have e : inX k n 1 (y ∘ Sum.inl - (⟨_, hq y hy⟩ : 𝒪[k]) • (m ∘ Sum.inl)) =
          y - (⟨_, hq y hy⟩ : 𝒪[k]) • m := by
        ext (j | j)
        · rfl
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = y (Sum.inr 0) - (q.1 : k) * y (Sum.inr 0) * m (Sum.inr 0)
          rw [hm1, mul_right_comm, hqi, one_mul, sub_self]
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem hy (M.smul_mem _ hm)
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      change y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))
      rw [← mul_assoc, mul_comm q.inv, hqi, one_mul]
  · rintro ⟨s, hs, h⟩
    have e : y = inX k n 1 (y ∘ Sum.inl - s • (m ∘ Sum.inl)) + s • m := by
      ext (j | j)
      · change y (Sum.inl j) = (y (Sum.inl j) - (s : k) * m (Sum.inl j)) + (s : k) * m (Sum.inl j)
        ring
      · have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        change y (Sum.inr 0) = 0 + (s : k) * m (Sum.inr 0)
        rw [(h 0).1 rfl, hm1, zero_add, mul_comm]
    rw [e]
    exact add_mem hs (M.smul_mem _ hm)

theorem gluedS_zero_eq_lastPair_lat [Fintype n] (q : Unif k) (L : Submodule 𝒪[k] (n → k))
    [L.IsFullLattice k] :
    gluedS q 1 L 0 = (lastPair q L).lat := by
  change _ = (glue (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last q L)).lat
  rw [glue_lat]
  refine le_antisymm (GlobalTheory.LevelUnfold.gluedS_le_iff.2 ⟨fun y hy => ?_, ?_, fun i hi => absurd hi (by omega)⟩)
    (sup_le (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_))
  · refine Submodule.mem_sup_left (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa [inX] using hy, ?_⟩)
    simp [inX]
  · rw [map_zero, add_zero]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · obtain ⟨h1, h2⟩ := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy
    refine GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨⟨(q.1 : k) * y (Sum.inr 0), mul_mem q.1.2 h2⟩, by simpa using h1,
      fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))
    rw [← mul_assoc, mul_comm q.inv, GlobalTheory.LevelUnfold.mul_inv_q, one_mul]
  · have := GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := 1) L (0 : n → k)
    rwa [map_zero, add_zero] at this

theorem smul_gluedS_cases : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (h : GL (n ⊕ Fin 1) k),
    (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ h • gluedS q 1 P.ker P.vec →
    (∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) →
    (∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsFullLattice k), h • gluedS q 1 P.ker P.vec = lastKer Λ ∨
      h • gluedS q 1 P.ker P.vec = (lastPair q Λ).lat) ∨
    ∃ g : GL n k, h • gluedS q 1 P.ker P.vec = embX 1 g • gluedS q 1 P.ker P.vec := by
  intro k _ _ _ _ n _ _ q P h hz hq
  have hML : (h • gluedS q 1 P.ker P.vec).IsFullLattice k := inferInstance
  generalize h • gluedS q 1 P.ker P.vec = M at hz hq hML ⊢
  have : (interX M).IsFullLattice k := by
    refine { toIsLattice := Submodule.IsLattice.of_fg k ?_, span_eq_top := ?_ }
    · exact Submodule.fg_of_fg_map_injective (inX k n 1)
        (fun x y e => funext fun i => congrFun e (Sum.inl i))
        (hML.fg.of_le (Submodule.map_comap_le _ _))
    · refine eq_top_iff.2 fun x _ => ?_
      have hx : inX k n 1 x ∈ Submodule.span k (M : Set (n ⊕ Fin 1 → k)) :=
        hML.span_eq_top ▸ Submodule.mem_top
      obtain ⟨y, hy, d, hd⟩ := (IsLocalization.mem_span_iff (M := nonZeroDivisors 𝒪[k])).1 hx
      have hdx : (d : 𝒪[k]) • x ∈ interX M := by
        change inX k n 1 ((d : 𝒪[k]) • x) ∈ M
        rw [map_smul, hd, ← IsScalarTower.algebraMap_smul k (d : 𝒪[k]), smul_smul,
          IsLocalization.mk'_spec', map_one, one_smul]
        simpa only [Submodule.span_eq] using hy
      have h := (Submodule.span k (interX M : Set (n → k))).smul_mem
        (IsLocalization.mk' k 1 d) (Submodule.subset_span hdx)
      rwa [← IsScalarTower.algebraMap_smul k (d : 𝒪[k]), smul_smul,
        IsLocalization.mk'_spec, map_one, one_smul] at h
  have hqi : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  by_cases hO : ∀ x ∈ M, x (Sum.inr 0) ∈ 𝒪[k]
  · refine Or.inl ⟨interX M, inferInstance, Or.inl ?_⟩
    ext y
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    constructor
    · intro hy
      refine ⟨?_, hO y hy⟩
      have e : inX k n 1 (y ∘ Sum.inl) = y - (⟨_, hO y hy⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · simp [inX]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = y (Sum.inr 0) - y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          simp
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem hy (M.smul_mem _ hz)
    · rintro ⟨h1, h2⟩
      have e : y = inX k n 1 (y ∘ Sum.inl) + (⟨_, h2⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · simp [inX]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change y (Sum.inr 0) = 0 + y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          simp
      rw [e]
      exact add_mem h1 (M.smul_mem _ hz)
  · push Not at hO
    obtain ⟨m₀, hm₀, hm₀'⟩ := hO
    have ht : IsUnit (⟨_, hq m₀ hm₀⟩ : 𝒪[k]) := by
      by_contra ht
      obtain ⟨s, hs⟩ := q.mem_max_iff.1 ((IsLocalRing.mem_maximalIdeal _).2 ht)
      apply hm₀'
      have h' : (q.1 : k) * m₀ (Sum.inr 0) = (q.1 : k) * s := congrArg Subtype.val hs
      rw [mul_left_cancel₀ q.ne_zero h']
      exact s.2
    obtain ⟨u, hu⟩ := ht
    have hu' : ((u : 𝒪[k]) : k) = (q.1 : k) * m₀ (Sum.inr 0) := congrArg Subtype.val hu
    have hinv : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * ((u : 𝒪[k]) : k) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      exact this
    set m : n ⊕ Fin 1 → k := ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • m₀
    have hm : m ∈ M := M.smul_mem _ hm₀
    have hm1 : m (Sum.inr 0) = q.inv := by
      change ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * m₀ (Sum.inr 0) = (q.1 : k)⁻¹
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← hinv, hu']
      ring
    have hMeq := eq_gluedS_of_mem q hq hm hm1
    have hqf : q.1 • (m ∘ Sum.inl) ∈ interX M := by
      have e : inX k n 1 (q.1 • (m ∘ Sum.inl)) = q.1 • m - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · change (q.1 : k) * m (Sum.inl j) = (q.1 : k) * m (Sum.inl j) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inl j)
          simp
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = (q.1 : k) * m (Sum.inr 0) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          rw [hm1, hqi]
          simp
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem (M.smul_mem _ hm) hz
    by_cases hf : m ∘ Sum.inl ∈ interX M
    · refine Or.inl ⟨interX M, inferInstance, Or.inr ?_⟩
      calc M = gluedS q 1 (interX M) (m ∘ Sum.inl) := hMeq
        _ = gluedS q 1 (interX M) 0 := GlobalTheory.LevelUnfold.gluedS_congr (by simpa using hf)
        _ = (lastPair q (interX M)).lat := gluedS_zero_eq_lastPair_lat q _
    · refine Or.inr ?_
      have hG : IsGlue (interX M) (m ∘ Sum.inl) := (isGlue_iff q).2 ⟨inferInstance, hf, hqf⟩
      obtain ⟨g, hg1, hg2⟩ := (GlobalTheory.LevelUnfold.oneOrbit (k := k) (n := n) (c := 1) (q := q)).1 P.ker (interX M)
        P.vec (m ∘ Sum.inl) (Pair.isGlue P.hasVal_vec) hG
      refine ⟨g, ?_⟩
      rw [GlobalTheory.LevelUnfold.embX_smul_gluedS, hg1, GlobalTheory.LevelUnfold.gluedS_congr hg2]
      exact hMeq

end GlobalTheory.GluedOrbit
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory

theorem lam_purerow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P → ∀ (i₀ : Fin l) (g : P.J), (∀ a b, a ≠ Sum.inr i₀ → (g : GL (Fin κ ⊕ Fin l) k).val a b = (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) a b) → (∀ i : Fin l, i.val = i₀.val + 1 → (g : GL (Fin κ ⊕ Fin l) k).val (Sum.inr i₀) (Sum.inr i) = 0) → P.lam g = 1 := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP i₀ g h1 h2
  have hs : simpleSum (g : GL (Fin κ ⊕ Fin l) k) = 0 := by
    unfold simpleSum
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · by_cases hi : i = i₀
      · subst hi; exact h2 j hij
      · have hne : i ≠ j := by
          intro e; subst e; omega
        rw [h1 _ _ (by simpa using hi)]
        simp [hne]
    · rfl
  have hu : superSum Fin.val (g : GL (Fin κ ⊕ Fin l) k).val.toBlocks₁₁ = 0 := by
    unfold superSum
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hab
    · have hne : a ≠ b := by
        intro e; subst e; omega
      rw [Matrix.toBlocks₁₁]
      simp only [Matrix.of_apply]
      rw [h1 _ _ (by simp)]
      simp [hne]
    · rfl
  apply Units.ext
  rw [hP.2 g, hs, hu]
  simp

end GlobalTheory
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.symmetricPositionLevel_character_eq_one_single_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P → ∀ (i₀ : Fin l) (g : P.J), (∀ a b, a ≠ Sum.inr i₀ → (g : GL (Fin κ ⊕ Fin l) k).val a b = (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) a b) → (∀ i : Fin l, i.val = i₀.val + 1 → (g : GL (Fin κ ⊕ Fin l) k).val (Sum.inr i₀) (Sum.inr i) = 0) → P.lam g = 1 := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP i₀ g h1 h2
  have hs : simpleSum (g : GL (Fin κ ⊕ Fin l) k) = 0 := by
    unfold simpleSum
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · by_cases hi : i = i₀
      · subst hi; exact h2 j hij
      · have hne : i ≠ j := by
          intro e; subst e; omega
        rw [h1 _ _ (by simpa using hi)]
        simp [hne]
    · rfl
  have hu : superSum Fin.val (g : GL (Fin κ ⊕ Fin l) k).val.toBlocks₁₁ = 0 := by
    unfold superSum
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hab
    · have hne : a ≠ b := by
        intro e; subst e; omega
      rw [Matrix.toBlocks₁₁]
      simp only [Matrix.of_apply]
      rw [h1 _ _ (by simp)]
      simp [hne]
    · rfl
  apply Units.ext
  rw [hP.2 g, hs, hu]
  simp

end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

theorem _root_.GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (fun x => ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∈ SB (I₀ → k) := by
  first | exact @GlobalTheory.SliceIntegral.integral_slice_mem_SB | exact GlobalTheory.SliceIntegral.integral_slice_mem_SB | (intros; apply GlobalTheory.SliceIntegral.integral_slice_mem_SB <;> assumption)
end

section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.translationInvariant_schwartzBruhat_map_factors_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (X₀ : Type) [TopologicalSpace X₀] [T2Space X₀] [LocallyCompactSpace X₀] [TotallyDisconnectedSpace X₀] (m₁ m₂ : Type) [Fintype m₁] [Fintype m₂] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × ((m₁ → k) × (m₂ → k))) →ₗ[ℂ] M), (∀ (a : (m₁ → k) × (m₂ → k)) (G G' : SB (X₀ × ((m₁ → k) × (m₂ → k)))), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G) → ∃ l₀ : SB X₀ →ₗ[ℂ] M, ∀ G, ∃ Ψ : SB X₀, (∀ x, Ψ.1 x = ∫ a₁, ∫ a₂, G.1 (x, (a₁, a₂)) ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν)) ∧ L G = l₀ Ψ := by
  first | exact @GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors | exact GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors | (intros; apply GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.rootExchangeRowUnipotent_latticeFrame_conj_apply : ∀ (k : Type) [Field k] (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (ϖ : kˣ) (j c l : ℕ) (h : j + c = l) (p : ℕ) (hp : p < c) (u : XIx κ t j → k) (a b : Ix (κ ⊕ Fin l) t j), ((typeFrame ϖ (stdOrd κ t j c h)).conj.symm (rowE c (p + 1) u)).val a b = (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b + if a = Sum.inl (Sum.inr ⟨p, by omega⟩) then Sum.elim (fun y => ((ϖ : k) ^ (p + 1))⁻¹ * u y) (fun _ => 0) (stdOrd κ t j c h b) else 0 := by
  first | exact @GlobalTheory.typeFrame_conj_symm_rowE_apply | exact GlobalTheory.typeFrame_conj_symm_rowE_apply | (intros; apply GlobalTheory.typeFrame_conj_symm_rowE_apply <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.parahoricChain_last_two_steps_root_of_unity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → ∀ g : GL (XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : XIx κ t (s + 1) → k) x, (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  exact @GlobalTheory.LevelLaw.last_steps_law
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.Core.Int.ProdPrimePow

theorem vAdd_eq_count {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : x ≠ 0) :
    vAdd v x = FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
  have key : ∀ r : 𝓞 K, r ≠ 0 → v.valuation K (algebraMap (𝓞 K) K r) = WithZero.exp
      (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r))) := by
    intro r hr
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v (by simpa using hr)]
    have := v.valuation_of_algebraMap (K := K) r
    rw [HeightOneSpectrum.intValuation_if_neg _ hr] at this
    exact this
  have hv : v.valuation K x =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by rintro rfl; simp at hx
    have hb1 : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
    have ha1 : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha0
    rw [map_div₀, key a ha0, key b hb0, div_eq_mul_inv (algebraMap (𝓞 K) K a),
      ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha1)
        (FractionalIdeal.spanSingleton_ne_zero_iff.2 (inv_ne_zero hb1)),
      ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, ← WithZero.exp_sub]
    congr 1; ring
  unfold vAdd
  rw [hv, WithZero.log_exp, neg_neg]

theorem vAdd_ge_of_mem_prod_zpow :
    ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [DecidableEq ι]
      (e : ι ≃ HeightOneSpectrum (𝓞 K)) (S : Finset ι) (n : ι → ℤ) (a : K),
      a ∈ (∏ w ∈ S, ((e w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(n w))) →
      ∀ w : ι, a = 0 ∨ (if w ∈ S then -(n w) else 0) ≤ vAdd (e w) a := by
  intro K _ _ ι _ e S n a ha w
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  right
  have hne : ∀ i ∈ S, ((e i).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n i)) ≠ 0 := fun i _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (e i).ne_bot)
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≤
      ∏ i ∈ S, ((e i).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n i)) :=
    (FractionalIdeal.spanSingleton_le_iff_mem).2 ha
  have hmono := FractionalIdeal.count_mono K (e w)
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0) hle
  rw [FractionalIdeal.count_prod K (e w) S _ hne] at hmono
  have hterm : ∀ i ∈ S, FractionalIdeal.count K (e w)
      (((e i).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n i))) = if w = i then -(n i) else 0 := by
    intro i _
    by_cases hwi : w = i
    · subst hwi
      rw [if_pos rfl, FractionalIdeal.count_zpow_self]
    · rw [if_neg hwi, FractionalIdeal.count_zpow,
        FractionalIdeal.count_maximal_coprime K (e w) (fun h => hwi (e.injective h).symm), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq] at hmono
  rw [vAdd_eq_count (e w) ha0]
  exact hmono

end GlobalTheory.Core.Int.ProdPrimePow
end
end

section

open IsDedekindDomain NumberField

theorem _root_.GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  first | exact @GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | exact GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | (intros; apply GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers <;> assumption)
end
