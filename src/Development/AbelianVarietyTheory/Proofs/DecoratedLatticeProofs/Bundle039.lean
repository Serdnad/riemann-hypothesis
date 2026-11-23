module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceOrder
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicationSeriesUnitCoeffNormLe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsKernelSubspaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsSubspacesContaining
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeightLatticeIndexIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle068
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open GlobalTheory.LowerHecke.MaxReps in

theorem _root_.GlobalTheory.T.exists_finset_reps_maximalIdealMatrix_mod_mul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ),
      valuation k (ϖ : k) = uniformizer k →
      ∀ (s : Finset D) (g : GL D k),
        (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D,
          g = κ * GlobalTheory.GLDoubling.torusElt (k := k) (n := D) ϖ (indic s) * κ') →
        ∃ N : Finset (Matrix D A k), (∀ ν ∈ N, ∀ i a, valuation k (ν i a) < 1) ∧
          ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) →
            ∃! ν', ν' ∈ N ∧ ∃ μ : Matrix D A k,
              (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s g hg
  classical
  have existsRightInverse :
      ∃ Q : Matrix D D k, GlobalTheory.StepData.IntM Q ∧
        g.1 * Q = (ϖ : k) • (1 : Matrix D D k) := by
    obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
    have hϖ1 : (ϖ : k) ∈ 𝒪[k] := (hϖ ▸ uniformizer_lt_one).le
    have inverseIntegral (u : GL D k) (hu : u ∈ KO k D) :
        GlobalTheory.StepData.IntM u⁻¹.1 := by
      obtain ⟨v, rfl⟩ := hu
      rw [← map_inv]
      exact fun i j => (v⁻¹.1 i j).2
    have mulIntegral (X Y : Matrix D D k) (hX : GlobalTheory.StepData.IntM X)
        (hY : GlobalTheory.StepData.IntM Y) : GlobalTheory.StepData.IntM (X * Y) :=
      fun i j => sum_mem fun l _ => mul_mem (hX i l) (hY l j)
    let t := GlobalTheory.GLDoubling.torusElt (k := k) (n := D) ϖ (indic s)
    have ht : t.1 = diagonal fun i => (ϖ : k) ^ indic s i := by
      exact GlobalTheory.GLDoubling.val_torusElt ϖ (indic s)
    let D0 : Matrix D D k := diagonal fun i => (ϖ : k) ^ (1 - indic s i)
    have hD0 : t.1 * D0 = (ϖ : k) • (1 : Matrix D D k) := by
      rw [ht, diagonal_mul_diagonal, smul_one_eq_diagonal]
      congr 1
      funext i
      rw [← zpow_add₀ ϖ.ne_zero]
      simp
    refine ⟨(κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1, ?_, ?_⟩
    · refine mulIntegral _ _ (mulIntegral _ _ (inverseIntegral κ' hκ') ?_) (inverseIntegral κ hκ)
      intro i j
      simp only [D0, diagonal_apply]
      split_ifs
      · by_cases hi : i ∈ s <;> simp [indic, hi, hϖ1]
      · exact zero_mem _
    · have e1 : κ'.1 * (κ'⁻¹ : GL D k).1 = 1 := Units.mul_inv κ'
      have e2 : κ.1 * (κ⁻¹ : GL D k).1 = 1 := Units.mul_inv κ
      simp only [Units.val_mul]
      calc κ.1 * t.1 * κ'.1 * ((κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1)
          = κ.1 * (t.1 * (κ'.1 * (κ'⁻¹ : GL D k).1) * D0) * (κ⁻¹ : GL D k).1 := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [e1, Matrix.mul_one, hD0, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, e2]
  obtain ⟨Q, hQ, hgQ⟩ := existsRightInverse
  let M : AddSubgroup (Matrix D A k) := maxLat k A D
  let H := (mulLat (A := A) g.1).addSubgroupOf M
  have scaleMem {x : k} (hx : valuation k x < 1) : (ϖ : k)⁻¹ * x ∈ 𝒪[k] := by
    change valuation k _ ≤ 1
    have h0 : valuation k (ϖ : k) ≠ 0 := by simp
    rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one, hϖ, le_uniformizer_iff]
    exact hx
  let redMap : M →+ (D → A → 𝓀[k]) :=
    { toFun := fun ν i a =>
        IsLocalRing.residue 𝒪[k] ⟨(ϖ : k)⁻¹ * (ν : Matrix D A k) i a, scaleMem (ν.2 i a)⟩
      map_zero' := by
        funext i a
        simp only [AddSubgroup.coe_zero, Matrix.zero_apply, mul_zero, Pi.zero_apply]
        exact map_zero _
      map_add' := by
        intro ν ν'
        funext i a
        simp only [Pi.add_apply]
        rw [← map_add (f := _)]
        congr 1
        ext
        simp [mul_add] }
  have hK : redMap.ker ≤ H := by
    intro ν hν
    rw [AddMonoidHom.mem_ker] at hν
    rw [AddSubgroup.mem_addSubgroupOf]
    have hμ : ∀ i a, valuation k ((ϖ : k)⁻¹ * (ν : Matrix D A k) i a) < 1 := fun i a => by
      have := congrFun (congrFun hν i) a
      simp only [redMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at this
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one] at this
      exact this
    refine ⟨Q * ((ϖ : k)⁻¹ • (ν : Matrix D A k)), ?_, ?_⟩
    · intro i a
      rw [Matrix.mul_apply]
      refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
      rw [map_mul]
      calc
        _ ≤ 1 * valuation k (((ϖ : k)⁻¹ • (ν : Matrix D A k)) l a) :=
          mul_le_mul_of_nonneg_right (hQ i l) zero_le
        _ < 1 := by simpa using hμ l a
    · rw [← Matrix.mul_assoc, hgQ, Matrix.smul_mul, Matrix.one_mul, smul_smul,
        mul_inv_cancel₀ ϖ.ne_zero, one_smul]
  have : Finite (M ⧸ redMap.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).symm.toEquiv
  have : redMap.ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have : H.FiniteIndex := AddSubgroup.finiteIndex_of_le hK
  have : Finite (M ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  let _ := Fintype.ofFinite (M ⧸ H)
  refine ⟨Finset.univ.image fun q : M ⧸ H => ((Quotient.out q : M) : Matrix D A k), ?_, ?_⟩
  · intro ν hν
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hν
    exact (Quotient.out q).2
  · intro ν hν
    have key : ∀ q : M ⧸ H, q = (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) ↔
        ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ((Quotient.out q : M) : Matrix D A k) = g.1 * μ := by
      intro q
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine exists_congr fun μ => and_congr_right fun _ => ?_
      show -((Quotient.out q : M) : Matrix D A k) + ν = g.1 * μ ↔ _
      rw [neg_add_eq_sub]
    refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) : M) : Matrix D A k),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).1 rfl⟩, ?_⟩
    rintro y ⟨hy, hyμ⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [(key q).2 hyμ]
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.cartan_decomposition_dominance_local_field :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
      ∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k,
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        g = κ * GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ
          (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') →
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ μ * g =
          κ * GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ ν * κ') →
      ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
            (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i) := by
  intro k _ _ _ _ N ϖ hϖ μ ν hμ _ n hn g hg hmain
  let ε := indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)
  let T := GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ
  change ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), g = κ * T ε * κ' at hg
  change ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), T μ * g = κ * T ν * κ' at hmain
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
  obtain ⟨κ₁, hκ₁, κ₂, hκ₂, hdecomp⟩ := hmain
  have hϖ₀ : 0 < valuation k (ϖ : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  have hϖ₁ : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hT (e : Fin N → ℤ) : (T e).1 = diagonal (fun i => (ϖ : k) ^ e i) :=
    GlobalTheory.GLDoubling.val_torusElt ..
  have hsum : ∑ i, ν i = ∑ i, μ i + ∑ i, ε i := by
    have hdet (e : Fin N → ℤ) : valuation k (T e).1.det = valuation k (ϖ : k) ^ ∑ i, e i := by
      rw [hT, det_diagonal, GlobalTheory.CartanDom.val_torus_prod]
    have h := congrArg (fun x : GL (Fin N) k => valuation k x.1.det) hdecomp
    simp only [Units.val_mul, det_mul, map_mul] at h
    rw [hdet, hdet, GlobalTheory.CartanDom.KO_det hκ, GlobalTheory.CartanDom.KO_det hκ',
      GlobalTheory.CartanDom.KO_det hκ₁, GlobalTheory.CartanDom.KO_det hκ₂] at h
    simp only [hdet, mul_one, one_mul] at h
    rw [← zpow_add₀ hϖ₀.ne'] at h
    exact le_antisymm ((zpow_le_zpow_iff_right_of_lt_one₀ hϖ₀ hϖ₁).1 h.le)
      ((zpow_le_zpow_iff_right_of_lt_one₀ hϖ₀ hϖ₁).1 h.ge)
  have hε : Antitone ε := GlobalTheory.CartanDom.indic_antitone N n
  have hcard : ∑ i, ε i = n := GlobalTheory.CartanDom.sum_indic N n hn
  refine ⟨hsum.trans (congrArg ((∑ i, μ i) + ·) hcard), fun j => ?_⟩
  let tail := Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j)
  have htail : (∑ i ∈ tail, μ i) + (∑ i ∈ tail, ε i) ≤ ∑ i ∈ tail, ν i := by
    by_cases hj : j < N
    swap
    · have hempty : tail = ∅ := by
        ext i
        simp [tail]
        omega
      simp [hempty]
    let I := {i : Fin N // ¬ (i : ℕ) < j}
    have hA (f h : I → Fin N) :
        valuation k (((T ε).1 * κ'.1).submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1 := by
      rw [hT]
      exact GlobalTheory.CartanDom.tail_diag ϖ hϖ ε hε j hj κ'.1 1
        (fun f h => GlobalTheory.CartanDom.val_det_le_one _
          (fun a b => GlobalTheory.CartanDom.KO_int hκ' (f a) (h b))) f h
    have hB (f h : I → Fin N) :
        valuation k ((κ * T ε * κ').1.submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1 := by
      rw [Units.val_mul, Units.val_mul, mul_assoc]
      exact GlobalTheory.CartanDom.minor_int_mul _ _ _ (GlobalTheory.CartanDom.KO_int hκ) hA f h
    have hC (f h : I → Fin N) :
        valuation k ((T μ * (κ * T ε * κ')).1.submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, μ i) *
            (valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1) := by
      rw [Units.val_mul (T μ), hT]
      exact GlobalTheory.CartanDom.tail_diag ϖ hϖ μ hμ j hj _ _ hB f h
    have hνdecomp : T ν = κ₁⁻¹ * (T μ * (κ * T ε * κ')) * κ₂⁻¹ := by
      rw [hdecomp]
      group
    have hD (f h : I → Fin N) :
        valuation k ((T ν).1.submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, μ i) *
            (valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1) := by
      rw [hνdecomp, Units.val_mul, Units.val_mul]
      exact GlobalTheory.CartanDom.minor_mul_int _ _ _ (GlobalTheory.CartanDom.KO_int (inv_mem hκ₂))
        (GlobalTheory.CartanDom.minor_int_mul _ _ _ (GlobalTheory.CartanDom.KO_int (inv_mem hκ₁)) hC) f h
    have h := hD Subtype.val Subtype.val
    rw [hT, submatrix_diagonal _ _ Subtype.val_injective, det_diagonal] at h
    simp only [Function.comp_apply] at h
    rw [GlobalTheory.CartanDom.val_torus_prod, mul_one, ← zpow_add₀ hϖ₀.ne'] at h
    have hle := (zpow_le_zpow_iff_right_of_lt_one₀ hϖ₀ hϖ₁).1 h
    rwa [← Finset.sum_subtype tail (fun i => by simp [tail]) ν] at hle
  have hνsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) ν
  have hμsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) μ
  have hεsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) ε
  change ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), (μ i + ε i)
  rw [Finset.sum_add_distrib]
  dsimp only [tail] at htail
  linarith
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open GlobalTheory.ZonalInduct (pot pot_lt pot_nonneg pos_iff_lt psum nonneg_of_dom) in

theorem _root_.GlobalTheory.T.cartan_decomposition_dominance_order :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (ϖ : kˣ) (c : ℕ → ℂ), c N ≠ 0 →
    (∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧
      ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        x = κ * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * κ') →
    (∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k,
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        g = κ * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ
          (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') →
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ μ * g =
          κ * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * κ') →
      ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
            (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i)) →
    (∀ g : GL (Fin N) k, ∃ R, IsRepsK g R) →
    ∀ h : GL (Fin N) k → ℂ,
      (∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m) →
      (∀ (s : Finset (Fin N)) R,
        IsRepsK (GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (indic s)) R →
          ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m) →
      h 1 = 0 → ∀ m, h m = 0 := by
  intro k _ _ _ _ N ϖ c hc hcart hdom hex h hK hT h1 m
  let torus := GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ
  have torus_add (a b : Fin N → ℤ) : torus (a + b) = torus a * torus b := by
    apply Units.ext
    simp only [torus, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt, diagonal_mul_diagonal]
    congr 1; funext i; simp [zpow_add₀ (Units.ne_zero ϖ)]
  have torus_zero : torus (fun _ => 0) = 1 := by
    apply Units.ext
    rw [GlobalTheory.GLDoubling.val_torusElt]; simp
  have torus_one_comm (g : GL (Fin N) k) :
      g * torus (fun _ => 1) = torus (fun _ => 1) * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt]
    ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have vanish_of_shift (j : ℕ) (m : GL (Fin N) k)
      (hm : h (m * torus (fun _ => (j : ℤ))) = 0) : h m = 0 := by
    induction j generalizing m with
    | zero => simpa [torus_zero] using hm
    | succ j ih =>
      apply ih
      have hz : indic (Finset.univ : Finset (Fin N)) = fun _ => 1 := funext fun i => by simp [indic]
      obtain ⟨R, hR⟩ := hex (torus (indic Finset.univ))
      set z := torus (fun _ => 1) with hzdef
      set m' := m * torus (fun _ => (j : ℤ))
      have hsplit : torus (fun _ => ((j + 1 : ℕ) : ℤ)) = torus (fun _ => (j : ℤ)) * z := by
        rw [hzdef, ← torus_add]; congr 1
      have hm' : h (m' * z) = 0 := by rw [← hm, hsplit, mul_assoc]
      have key := hT Finset.univ R hR m'
      have hterm : ∀ g ∈ R, h (m' * g) = 0 := by
        intro g hg
        obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hR.1 g hg
        rw [hz] at *
        have e : m' * (κ * z * κ') = (m' * z) * (κ * κ') := by
          rw [torus_one_comm]
          simp only [mul_assoc]
        rw [e, (hK _ (mul_mem hκ hκ') _).2, hm']
      rw [Finset.sum_eq_zero hterm, Finset.card_univ, Fintype.card_fin] at key
      exact (mul_eq_zero.1 key.symm).resolve_left hc
  have vanish_dominant :
      ∀ n : ℕ, ∀ e : Fin N → ℤ, Antitone e → (∀ i, 0 ≤ e i) → pot e ≤ n → h (torus e) = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih e ha he hpot
    have IH : ∀ ν : Fin N → ℤ, Antitone ν → (∀ i, 0 ≤ ν i) → pot ν < pot e →
        h (torus ν) = 0 := by
      intro ν hν hν0 hlt
      have h0 := pot_nonneg hν0
      exact ih (pot ν).toNat (by omega) ν hν hν0 (by omega)
    by_cases hzero : ∀ i, e i = 0
    · have : e = fun _ => 0 := funext hzero
      rw [this, torus_zero, h1]
    push Not at hzero
    obtain ⟨i₀, hi₀⟩ := hzero
    have hi₀pos : 0 < e i₀ := lt_of_le_of_ne (he i₀) (Ne.symm hi₀)
    obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = (Finset.univ.filter fun j => 0 < e j).card := ⟨_, rfl⟩
    have key : ∀ i, 0 < e i ↔ (i : ℕ) < n₀ := fun i => hn₀ ▸ pos_iff_lt ha i
    have hn₀N : n₀ ≤ N := by rw [hn₀]; exact (Finset.card_le_univ _).trans (by simp)
    obtain ⟨s, hs⟩ : ∃ s : Finset (Fin N), s = Finset.univ.filter fun i : Fin N => (i : ℕ) < n₀ := ⟨_, rfl⟩
    have hind : ∀ i, indic s i = if 0 < e i then 1 else 0 := by
      intro i; simp only [indic, hs, Finset.mem_filter, Finset.mem_univ, true_and, ← key]
    have hscard : s.card = n₀ := by
      rw [hn₀]; congr 1; rw [hs]; ext i; simp [key]
    set μ : Fin N → ℤ := fun i => e i - indic s i with hμdef
    have hμe : ∀ i, μ i + indic s i = e i := fun i => by simp [hμdef]
    have hμa : Antitone μ := by
      intro i j hij
      have := ha hij; have hi := he i; have hj := he j
      simp only [hμdef, hind]
      split_ifs <;> omega
    have hμ0 : ∀ i, 0 ≤ μ i := by
      intro i; have := he i; simp only [hμdef, hind]; split_ifs <;> omega
    have hμlt : pot μ < pot e := by
      apply pot_lt
      · intro j; unfold psum
        exact Finset.sum_le_sum fun i _ => by simp only [hμdef, hind]; split_ifs <;> omega
      · intro hh; have := congrFun hh i₀; simp only [hμdef, hind, ite_eq_left hi₀pos] at this; omega
    have hμv := IH μ hμa hμ0 hμlt
    have hTe : torus e = torus μ * torus (indic s) := by
      rw [← torus_add]; congr 1; funext i; exact (hμe i).symm
    have hsumind : ∑ i, indic s i = (n₀ : ℤ) := by
      rw [← hscard]; simp [indic]
    obtain ⟨R, hR⟩ := hex (torus (indic s))
    have hsum := hT s R hR (torus μ)
    rw [hμv, mul_zero] at hsum
    have hterm : ∀ g ∈ R, h (torus μ * g) = 0 ∨
        h (torus μ * g) = h (torus e) := by
      intro g hg
      obtain ⟨ν, hν, κ1, hκ1, κ2, hκ2, hx⟩ := hcart (torus μ * g)
      have hval : h (torus μ * g) = h (torus ν) := by
        rw [hx, mul_assoc, (hK κ1 hκ1 _).1, (hK κ2 hκ2 _).2]
      obtain ⟨κ, hκ, κ', hκ', hgeq⟩ := hR.1 g hg
      have hd := hdom μ ν hμa hν n₀ hn₀N g ⟨κ, hκ, κ', hκ', by rw [← hs]; exact hgeq⟩ ⟨κ1, hκ1, κ2, hκ2, hx⟩
      simp only [← hs] at hd
      obtain ⟨hd1, hd2⟩ := hd
      have hle : ∀ j, psum ν j ≤ psum e j := by
        intro j; have := hd2 j; simp only [hμe] at this; exact this
      have hsumeq : ∑ i, ν i = ∑ i, e i := by
        rw [hd1, ← hsumind, ← Finset.sum_add_distrib]; simp only [hμe]
      have hν0 := nonneg_of_dom hν he hle hsumeq
      by_cases hνe : ν = e
      · right; rw [hval, hνe]
      · left; rw [hval]; exact IH ν hν hν0 (pot_lt hle hνe)
    obtain ⟨g₁, ⟨hg₁R, hg₁K⟩, -⟩ := hR.2 1 (one_mem _)
    have hg₁ : h (torus μ * g₁) = h (torus e) := by
      have e1 : torus μ * g₁ =
          torus e * (g₁⁻¹ * (1 * torus (indic s)))⁻¹ := by
        rw [hTe]; group
      rw [e1, (hK _ (inv_mem hg₁K) _).2]
    by_contra hx
    have hite : ∀ g ∈ R, h (torus μ * g) =
        if h (torus μ * g) = h (torus e) then h (torus e) else 0 := by
      intro g hg
      rcases hterm g hg with h0 | h0
      · rw [h0, ite_eq_right (Ne.symm hx)]
      · rw [ite_eq_left h0]; exact h0
    rw [Finset.sum_congr rfl hite, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul] at hsum
    have hcard : (R.filter fun g => h (torus μ * g) = h (torus e)).card ≠ 0 :=
      Finset.card_ne_zero.2 ⟨g₁, Finset.mem_filter.2 ⟨hg₁R, hg₁⟩⟩
    rcases mul_eq_zero.1 hsum with hc0 | hc0
    · exact hcard (by exact_mod_cast hc0)
    · exact hx hc0
  obtain ⟨ν, hν, κ, hκ, κ', hκ', rfl⟩ := hcart m
  rw [mul_assoc, (hK κ hκ _).1, (hK κ' hκ' _).2]
  change h (torus ν) = 0
  let j := (∑ i, |ν i|).toNat
  apply vanish_of_shift j
  rw [← torus_add]
  refine vanish_dominant (pot (ν + fun _ => (j : ℤ))).toNat (ν + fun _ => (j : ℤ))
    ?_ ?_ (Int.self_le_toNat _)
  · intro a b hab; simp only [Pi.add_apply]; linarith [hν hab]
  · intro i; simp only [Pi.add_apply]
    have h1' : |ν i| ≤ ∑ i, |ν i| :=
      Finset.single_le_sum (f := fun i => |ν i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (ν i)
    have h3 := Int.self_le_toNat (∑ i, |ν i|)
    omega
end

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.multiplication_series_unit_coeff_norm_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (A v : K⟦X⟧) (e e' : K) (M : ℕ) (Dp Np : Polynomial K), CoefLe 1 A → constantCoeff A = 1 → CoefLe 1 v → constantCoeff v = 0 → ‖e‖ ≤ 1 → ‖e'‖ ≤ 1 → Np.Monic → Np.natDegree = M + 1 → (∀ i, ‖Np.coeff i‖ ≤ 1) → Dp.natDegree ≤ M → ‖Dp.eval e'‖ = 1 → (A.subst v - C e * v ^ 2) * (∑ i ∈ Finset.range (M + 1), C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i))) * X ^ 2 = v ^ 2 * ∑ i ∈ Finset.range (M + 2), C (Np.coeff i) * A ^ i * X ^ (2 * (M + 1 - i)) → ∃ n, n ≤ M + 1 ∧ ‖coeff n v‖ = 1 := by
  first | exact @GlobalTheory.Honda.htform_unit_coeff_le | exact GlobalTheory.Honda.htform_unit_coeff_le | (intros; apply GlobalTheory.Honda.htform_unit_coeff_le <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.sum_integralIndicator_cosets_kernel_subspaces : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) RK, IsRepsK (torusElt k D ϖ (-indic s)) RK → ∀ y : Matrix D' D k, ((¬ ∀ i j, y i j ∈ 𝒪[k]) → ∑ g ∈ RK, intInd (y * g.1) = 0) ∧ ∀ y₀ : Matrix D' D 𝒪[k], y = y₀.map (algebraMap 𝒪[k] k) → ∑ g ∈ RK, intInd (y * g.1) = (Nat.card {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = s.card} : ℂ) := by
  first | exact @GlobalTheory.ParHecke.CosetSub.sum_intInd_cosets | exact GlobalTheory.ParHecke.CosetSub.sum_intInd_cosets | (intros; apply GlobalTheory.ParHecke.CosetSub.sum_intInd_cosets <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.sum_integralIndicator_cosets_subspaces_containing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') RK, IsRepsK (GlobalTheory.GLDoubling.torusElt k D' ϖ (indic s)) RK → ∀ y : Matrix D' D k, ((¬ ∀ i j, y i j ∈ 𝒪[k]) → ∑ g ∈ RK, GlobalTheory.ParHecke.intInd ((g⁻¹).1 * y) = 0) ∧ ∀ y₀ : Matrix D' D 𝒪[k], y = y₀.map (algebraMap 𝒪[k] k) → ∑ g ∈ RK, GlobalTheory.ParHecke.intInd ((g⁻¹).1 * y) = (Nat.card {U : Submodule 𝓀[k] (D' → 𝓀[k]) // LinearMap.range (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ≤ U ∧ Module.finrank 𝓀[k] U + s.card = Fintype.card D'} : ℂ) := by
  first | exact @GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up | exact GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up | (intros; apply GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open GlobalTheory.HeckeLatIndex in

theorem _root_.GlobalTheory.T.unramifiedHeight_lattice_index_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ (m g : GL D k) (s : Finset D), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → ∀ (L Lm large₂ : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ Lm ↔ m.1.mulVec v ∈ L) → (∀ v, v ∈ large₂ ↔ (g⁻¹).1.mulVec v ∈ L) → (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g) = (resCard k : ℝ) ^ s.card * H m := by
  apply _root_.GlobalTheory.HeckeLatIndex.index_identity <;> assumption
end

section


theorem _root_.GlobalTheory.T.relIndex_eq_prod_relIndex_of_surjective_pi : ∀ {G : Type} [Group G] {r : ℕ} {H : Fin r → Type} [∀ i, Group (H i)] (φ : G →* ((i : Fin r) → H i)) (U U' : Subgroup G) (K J : (i : Fin r) → Subgroup (H i)), (∀ i, J i ≤ K i) → (∀ g ∈ U, ∀ i, φ g i ∈ K i) → (∀ x : (i : Fin r) → H i, (∀ i, x i ∈ K i) → ∃ g ∈ U, φ g = x) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i) → U'.relIndex U = ∏ i, (J i).relIndex (K i) := by
  first | exact @GlobalTheory.relIndex_preimage_pi_eq_prod | exact GlobalTheory.relIndex_preimage_pi_eq_prod | (intros; apply GlobalTheory.relIndex_preimage_pi_eq_prod <;> assumption)
end
