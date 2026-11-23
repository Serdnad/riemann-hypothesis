module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle059
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle063
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle056
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle064
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.CosetQuotInt

attribute [local instance 2000] _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace


open MeasureTheory ValuativeRel Matrix Topology in
theorem _root_.GlobalTheory.CosetQuotInt.isQuotInt_cosetFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J)
    (h : GL (n ⊕ Fin c) k)
    (m : Measure (GL n k)) (v : ℝ) (hv : v ≠ 0)
    (hvol : ∀ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1, ∀ g₀ : GL n k, ∫ g,
      (∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
      (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
        (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
          (u₀ * _root_.GlobalTheory.RootEx.embX c g₀))
          ∂(_root_.GlobalTheory.RootEx.volN ν n c 1)) ∂m
          = ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ * v : ℝ) : ℂ))
    (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ)
    (hf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCosetFn J h f) :
    _root_.GlobalTheory.RootEx.IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by
  classical
  haveI : BorelSpace (GL (n ⊕ Fin c) k) :=
    (_root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν).1
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) :=
    (_root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν).2.2.1
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO at hJ
  obtain ⟨hJo, hJc⟩ := hJ
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCosetFn at hf
  obtain ⟨hleft, hright, hsupp⟩ := hf
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hv
  have hembP : ∀ g : GL n k,
      _root_.GlobalTheory.RootEx.embX c g ∈ _root_.GlobalTheory.RootEx.R k n c 1 := by
    intro g
    unfold _root_.GlobalTheory.RootEx.R
    exact Subgroup.mem_sup_left ⟨g, rfl⟩
  have hNP : ∀ u ∈ _root_.GlobalTheory.RootEx.N k n c 1,
      u ∈ _root_.GlobalTheory.RootEx.R k n c 1 := by
    intro u hu
    unfold _root_.GlobalTheory.RootEx.R
    exact Subgroup.mem_sup_right hu
  obtain ⟨F, hFdef⟩ : ∃ F : GL (n ⊕ Fin c) k → ℂ,
      ∀ x, F x = if h⁻¹ * x ∈ J then f h / (v : ℂ) else 0 := ⟨_, fun _ => rfl⟩
  unfold _root_.GlobalTheory.RootEx.IsQuotInt
  refine ⟨F, ?_, fun x => ?_, ?_⟩
  · have hSB := _root_.GlobalTheory.QuotInt.sb_of_quot J hJo hJc
      {(h : GL (n ⊕ Fin c) k ⧸ J)}
      (fun q => if q = (h : GL (n ⊕ Fin c) k ⧸ J) then f h / (v : ℂ) else 0)
      (fun q hq => by
        simp only [Finset.mem_singleton] at hq
        simp [hq])
    have hFq : F = fun y : GL (n ⊕ Fin c) k => (fun q : GL (n ⊕ Fin c) k ⧸ J =>
        if q = (h : GL (n ⊕ Fin c) k ⧸ J) then f h / (v : ℂ) else 0) (y : GL (n ⊕ Fin c) k ⧸ J) := by
      funext y
      rw [hFdef]
      dsimp only
      by_cases hy : h⁻¹ * y ∈ J
      · rw [if_pos hy, if_pos (QuotientGroup.eq.2 hy).symm]
      · rw [if_neg hy, if_neg (fun (he : (y : GL (n ⊕ Fin c) k ⧸ J) = h) =>
          hy (QuotientGroup.eq.1 he.symm))]
    rw [hFq]
    exact hSB
  · by_cases hx : DoubleCoset.mk (_root_.GlobalTheory.RootEx.R k n c 1) J h =
        DoubleCoset.mk (_root_.GlobalTheory.RootEx.R k n c 1) J x
    · obtain ⟨p, hp, j, hj, rfl⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hx
      obtain ⟨x₀, u', hu', rfl⟩ := _root_.GlobalTheory.RootEx.VolN.exists_of_mem_R hp
      obtain ⟨u₀, hu₀, hpeq⟩ : ∃ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1,
          _root_.GlobalTheory.RootEx.embX c x₀ * u' = u₀ * _root_.GlobalTheory.RootEx.embX c x₀ :=
        ⟨_, _root_.GlobalTheory.RootEx.Radical.conj_mem x₀ hu', by group⟩
      rw [hpeq, hright _ j hj, hleft u₀ hu₀ x₀ h]
      have hpt : ∀ (g : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c 1),
          F (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) =
          f h / (v : ℂ) * (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator
            (fun _ => (1 : ℂ)) (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) := by
        intro g u
        have hyP : _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀) ∈ _root_.GlobalTheory.RootEx.R k n c 1 :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (hembP g) (hNP _ u.2))
            (Subgroup.mul_mem _ (hNP _ hu₀) (hembP x₀))
        have hiff : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) ∈ J ↔
            h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h ∈ J := by
          have heq : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) =
              h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h * j := by group
          rw [heq, J.mul_mem_cancel_right hj]
        rw [hFdef]
        by_cases hin : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h ∈ J
        · rw [if_pos (hiff.2 hin), Set.indicator_of_mem
            (show _ ∈ _root_.GlobalTheory.StepData.Cgrp J h from
              _root_.GlobalTheory.StepData.mem_Cgrp.2 ⟨hyP, hin⟩), mul_one]
        · rw [if_neg (fun h' => hin (hiff.1 h')), Set.indicator_of_notMem
            (show _ ∉ _root_.GlobalTheory.StepData.Cgrp J h from
              fun h' => hin (_root_.GlobalTheory.StepData.mem_Cgrp.1 h').2), mul_zero]
      simp_rw [hpt, integral_const_mul]
      rw [hvol u₀ hu₀ x₀]
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR
      rw [Complex.ofReal_mul, div_mul_eq_mul_div, eq_div_iff hv']
      ring
    · have hfx : f x = 0 := hsupp x (fun he => hx he.symm)
      rw [hfx]
      have hpt : ∀ (g : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c 1),
          F (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * x) = 0 := by
        intro g u
        rw [hFdef, if_neg]
        intro hmem
        apply hx
        refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(_root_.GlobalTheory.RootEx.embX c g *
          (u : GL (n ⊕ Fin c) k))⁻¹, Subgroup.inv_mem _ (Subgroup.mul_mem _ (hembP g)
            (hNP _ u.2)), h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * x),
          hmem, by group⟩
      simp_rw [hpt, integral_zero]
  · have hFind : F = ((fun y => h⁻¹ * y) ⁻¹' (J : Set (GL (n ⊕ Fin c) k))).indicator
        (fun _ => f h / (v : ℂ)) := by
      funext y
      rw [hFdef]
      by_cases hy : h⁻¹ * y ∈ J
      · rw [if_pos hy, Set.indicator_of_mem (show y ∈ (fun y => h⁻¹ * y) ⁻¹' (J : Set _) from hy)]
      · rw [if_neg hy,
          Set.indicator_of_notMem (show y ∉ (fun y => h⁻¹ * y) ⁻¹' (J : Set _) from hy)]
    rw [hFind, integral_indicator_const _
      (hJo.measurableSet.preimage (measurable_const_mul h⁻¹)), measureReal_def,
      measure_preimage_mul, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.CosetQuotInt
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.SymShape

theorem block_mul_embX {F : Type} [Field F] {κ l p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p)
    (γ : GL (Fin κ) F) : (u * embX l γ).val.toBlocks₁₁ = γ.val := by
  rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val, ← Matrix.fromBlocks_toBlocks u.val,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu]
  simp

theorem simpleSum_embX {F : Type} [Field F] {κ l : ℕ} (γ : GL (Fin κ) F) : simpleSum (embX l γ) = 0 := by
  apply GlobalTheory.RootEx.Radical.simpleSum_eq_zero
  intro i j
  rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.fromBlocks_apply₂₂]

theorem sym_shape :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ)
      (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l)),
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P →
        (∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J →
          ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
        (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb →
          IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J,
          (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
        ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J,
          (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u) := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP
  refine ⟨?_, ?_, ?_⟩
  · intro u hu γ hm
    obtain ⟨u', hu', γ', hγ', g₀, hg₀, hr₀⟩ := (hP.1 _).1 hm
    have key : ∀ {F : Type} [Field F] (f : 𝒪[k] →+* F) (x : GL (Fin κ ⊕ Fin l) F) (y : GL (Fin κ) F),
        Matrix.GeneralLinearGroup.map f g₀ = x → x.val.toBlocks₁₁ = y.val →
          (g₀.val.toBlocks₁₁).map f = y.val := by
      intro F _ f x y h1 h2
      rw [← h2, ← h1]
      rfl
    have hBk := key (algebraMap 𝒪[k] k) _ γ hg₀ (block_mul_embX hu γ)
    have hBr := key (IsLocalRing.residue 𝒪[k]) _ γ' hr₀ (block_mul_embX hu' γ')
    have hdet : IsUnit (g₀.val.toBlocks₁₁).det := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      change ((g₀.val.toBlocks₁₁).map (IsLocalRing.residue 𝒪[k])).det ≠ 0
      rw [hBr]
      exact (Matrix.isUnits_det_units γ').ne_zero
    refine ⟨γ', ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_, ?_⟩, hγ'⟩
    · exact Units.ext (by rw [← hBk]; rfl)
    · exact Units.ext (by rw [← hBr]; rfl)
  · intro γ gb hred hgb
    obtain ⟨γ₀, h1, h2⟩ := hred
    let g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k] :=
      ⟨Matrix.fromBlocks γ₀.val 0 0 1, Matrix.fromBlocks (γ₀⁻¹).val 0 0 1,
        by rw [Matrix.fromBlocks_multiply]; simp, by rw [Matrix.fromBlocks_multiply]; simp⟩
    have hemb : ∀ {F : Type} [Field F] (f : 𝒪[k] →+* F),
        Matrix.GeneralLinearGroup.map f g₀ = embX l (Matrix.GeneralLinearGroup.map f γ₀) := by
      intro F _ f
      refine Units.ext ?_
      rw [GlobalTheory.RootEx.Radical.embX_val]
      change (Matrix.fromBlocks γ₀.val 0 0 1).map f = _
      rw [Matrix.fromBlocks_map]
      simp
    have hm : embX l γ ∈ P.J := (hP.1 _).2 ⟨1, one_mem _, gb, hgb, g₀, by rw [hemb, h1], by rw [hemb, h2, one_mul]⟩
    refine ⟨hm, ?_⟩
    have hblk : (embX l γ).val.toBlocks₁₁ = γ.val := by
      rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.toBlocks_fromBlocks₁₁]
    rw [hP.2 ⟨_, hm⟩]
    simp only [simpleSum_embX, hblk, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  · intro u hu hm
    rw [hP.2 ⟨u, hm⟩]
    simp only [GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu, GlobalTheory.GenericShape.superSum_one, mul_zero,
      AddChar.map_zero_eq_one, Circle.coe_one, mul_one]

end GlobalTheory.SymShape
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.symmetricPositionLevel_shape_on_parabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ)
      (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l)),
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P →
        (∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J →
          ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
        (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb →
          IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J,
          (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
        ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J,
          (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u) := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP
  have block_mul_embX {F : Type} [Field F] {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F}
      (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
      (u * embX l γ).val.toBlocks₁₁ = γ.val := by
    rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val, ← Matrix.fromBlocks_toBlocks u.val,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁,
      GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu]
    simp
  have simpleSum_embX (γ : GL (Fin κ) k) : simpleSum (embX l γ) = 0 := by
    apply GlobalTheory.RootEx.Radical.simpleSum_eq_zero
    intro i j
    rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.fromBlocks_apply₂₂]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu γ hm
    obtain ⟨u', hu', γ', hγ', g₀, hg₀, hr₀⟩ := (hP.1 _).1 hm
    have map_corner {F : Type} [Field F] (f : 𝒪[k] →+* F)
        (x : GL (Fin κ ⊕ Fin l) F) (y : GL (Fin κ) F)
        (hx : Matrix.GeneralLinearGroup.map f g₀ = x) (hy : x.val.toBlocks₁₁ = y.val) :
        (g₀.val.toBlocks₁₁).map f = y.val := by
      rw [← hy, ← hx]
      rfl
    have hBk := map_corner (algebraMap 𝒪[k] k) _ γ hg₀ (block_mul_embX hu γ)
    have hBr := map_corner (IsLocalRing.residue 𝒪[k]) _ γ' hr₀ (block_mul_embX hu' γ')
    have hdet : IsUnit (g₀.val.toBlocks₁₁).det := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      change ((g₀.val.toBlocks₁₁).map (IsLocalRing.residue 𝒪[k])).det ≠ 0
      rw [hBr]
      exact (Matrix.isUnits_det_units γ').ne_zero
    refine ⟨γ', ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_, ?_⟩, hγ'⟩
    · exact Units.ext (by rw [← hBk]; rfl)
    · exact Units.ext (by rw [← hBr]; rfl)
  · intro γ gb hred hgb
    obtain ⟨γ₀, h₁, h₂⟩ := hred
    let g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k] :=
      ⟨Matrix.fromBlocks γ₀.val 0 0 1, Matrix.fromBlocks (γ₀⁻¹).val 0 0 1,
        by rw [Matrix.fromBlocks_multiply]; simp, by rw [Matrix.fromBlocks_multiply]; simp⟩
    have hemb {F : Type} [Field F] (f : 𝒪[k] →+* F) :
        Matrix.GeneralLinearGroup.map f g₀ = embX l (Matrix.GeneralLinearGroup.map f γ₀) := by
      refine Units.ext ?_
      rw [GlobalTheory.RootEx.Radical.embX_val]
      change (Matrix.fromBlocks γ₀.val 0 0 1).map f = _
      rw [Matrix.fromBlocks_map]
      simp
    have hm : embX l γ ∈ P.J :=
      (hP.1 _).2 ⟨1, one_mem _, gb, hgb, g₀, by rw [hemb, h₁], by rw [hemb, h₂, one_mul]⟩
    refine ⟨hm, ?_⟩
    have hblk : (embX l γ).val.toBlocks₁₁ = γ.val := by
      rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.toBlocks_fromBlocks₁₁]
    rw [hP.2 ⟨_, hm⟩]
    simp only [simpleSum_embX, hblk, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  · intro u hu hm
    rw [hP.2 ⟨u, hm⟩]
    simp only [GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu, GlobalTheory.GenericShape.superSum_one,
      mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.haar_compactOpen_ratio_eq_zpow_of_topNilpotent : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ), q.Prime → (∀ u : G, ∀ U ∈ 𝓝 (1 : G), ∃ m : ℕ, u ^ (q ^ m) ∈ U) → ∀ H₁ H₂ : Subgroup G, IsCO H₁ → IsCO H₂ → ∃ z : ℤ, (μ H₁).toReal / (μ H₂).toReal = (q : ℝ) ^ z := by
  first | exact @GlobalTheory.VolPow.vol_div_eq_zpow | exact GlobalTheory.VolPow.vol_div_eq_zpow | (intros; apply GlobalTheory.VolPow.vol_div_eq_zpow <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.integral_indicator_Cgrp_translate_eq_deltaR_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c → ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (h : GL (n ⊕ Fin c) k), IsCO (prX (Cgrp J h)) → ∀ (m : Measure (GL n k)) [m.IsHaarMeasure], ∀ u₀ ∈ N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : N k n c 1, (Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * embX c g₀)) ∂(volN ν n c 1)) ∂m = ((deltaR c g₀ * ((volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1))).toReal * (m (prX (Cgrp J h))).toReal) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.StepAvg.integral_translate_indicator | exact GlobalTheory.StepAvg.integral_translate_indicator | (intros; apply GlobalTheory.StepAvg.integral_translate_indicator <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.exists_adapted_exponent_schwartzBruhat_lastColumn : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  first | exact @GlobalTheory.AdaptedExp.exists_adapted_exponent | exact GlobalTheory.AdaptedExp.exists_adapted_exponent | (intros; apply GlobalTheory.AdaptedExp.exists_adapted_exponent <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.exists_genericLevelOfFrame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ κ l : ℕ, ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsGenericLevel ψ ϖ P := by
  first | exact @GlobalTheory.GenericLevel.exists_isGenericLevel | exact GlobalTheory.GenericLevel.exists_isGenericLevel | (intros; apply GlobalTheory.GenericLevel.exists_isGenericLevel <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.exists_parabolicDoubleCosetFunction_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), (∀ g ∈ prX (Cgrp J h), deltaR c g = 1) → ∃ f, IsCosetFn J h f ∧ f h = 1 := by
  first | exact @GlobalTheory.CosetFn.exists_isCosetFn | exact GlobalTheory.CosetFn.exists_isCosetFn | (intros; apply GlobalTheory.CosetFn.exists_isCosetFn <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.firstVertex_iteratedLevelChain_in_frame :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (s : ℕ) (t : Type) [Fintype t] [DecidableEq t]
      (κ : ℕ) (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin (s + 1))),
    ((∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ γ : GL (Fin κ) k,
        u * embX (s + 1) γ ∈ P.J → ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
      (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb → IsUpperUnip Fin.val gb.val →
        ∃ hm : embX (s + 1) γ ∈ P.J,
          (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
      ∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ hm : u ∈ P.J,
        (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) →
    ∀ (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (c : ℕ) (H : 0 + c = s + 1),
      (prX (Cgrp ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J 1) :
        Set (GL (XIx (Fin κ) t 0) k)) = colGroup (k := k) κ t ∧
      (∀ γ ∈ colGroup (k := k) κ t,
        ∃ hm : embX c γ ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J,
          (((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨_, hm⟩ : ℂ) =
            colChar ψ ϖ γ) ∧
      ∀ u ∈ N k (XIx (Fin κ) t 0) c 1,
        ∀ hm : u ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J,
          (((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨u, hm⟩ : ℂ) =
            ψ (simpleSum u) := by
  first | exact @GlobalTheory.FirstVertexFrame.firstVertex_typeChain | exact GlobalTheory.FirstVertexFrame.firstVertex_typeChain | (intros; apply GlobalTheory.FirstVertexFrame.firstVertex_typeChain <;> assumption)
end

section

open MeasureTheory GlobalTheory.FunObj

theorem _root_.GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (ϖ : kˣ) (e : ℕ) (keep : Bool) (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ), (∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) → ∀ X Y, flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y = ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  first | exact @GlobalTheory.FunObj.flatTensor_moved_sum | exact GlobalTheory.FunObj.flatTensor_moved_sum | (intros; apply GlobalTheory.FunObj.flatTensor_moved_sum <;> assumption)
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder

theorem _root_.GlobalTheory.T.exists_euclideanCoords_hermitian_cartanInvolution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H s : Matrix ι ι ℂ), Hᴴ = H → s * s = 1 → (H * s).PosDef → ∃ (E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ)) (J : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι), (∀ x, J (J x) = -x) ∧ (∀ x, E (J x) = I • s *ᵥ E x) ∧ ∀ x y, (star (E y) ⬝ᵥ H *ᵥ E x).im = omJ J x y := by
  first | exact @GlobalTheory.Twist.EuclidCoord.exists_coord | exact GlobalTheory.Twist.EuclidCoord.exists_coord | (intros; apply GlobalTheory.Twist.EuclidCoord.exists_coord <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.additive_family_function_determined_constituents : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] [∀ i, IsTopologicalGroup (Γ i)] (Φ : (∀ i, GlobalTheory.SmGL.SmRep (Γ i)) → ℕ∞), (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α), Subsingleton (A i).V → Φ A = 0) → (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → Φ (Function.update A i B) = Φ (Function.update A i B₁) + Φ (Function.update A i B₂)) → ∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)), (∀ i, GlobalTheory.SmGL.HasFiniteLength (A i).ρ) → ∀ T : Finset (∀ i, GlobalTheory.SmGL.IrrCl (Γ i)), (∀ t ∉ T, ∃ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ = 0) → Φ A = ∑ t ∈ T, (∏ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ) * Φ (fun i => GlobalTheory.SmGL.SmRep.ofIrr (t i).rep) := by
  first | exact @GlobalTheory.SmGL.additive_family_expand | exact GlobalTheory.SmGL.additive_family_expand | (intros; apply GlobalTheory.SmGL.additive_family_expand <;> assumption)
end
