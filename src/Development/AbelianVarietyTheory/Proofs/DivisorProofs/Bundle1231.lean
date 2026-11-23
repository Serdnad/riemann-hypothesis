module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.PowersCompact

theorem ball_isCompact_isOpen {E : Type} [Field E] [NumberField E] (w : Pl E) (m : ℤ) :
    IsCompact {x : w.adicCompletion E | Valued.v x ≤ WithZero.exp m} ∧
      IsOpen {x : w.adicCompletion E | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    exact WithZero.exp_ne_zero hc.symm
  have hO : IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    Valued.isOpen_valuationSubring _
  have hC : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  have e : {x : w.adicCompletion E | Valued.v x ≤ WithZero.exp m} =
      (Homeomorph.mulLeft₀ c⁻¹ (inv_ne_zero hc0)) ⁻¹' (w.adicCompletionIntegers E) := by
    ext x
    change _ ↔ Valued.v (c⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hc, inv_mul_le_iff₀ WithZero.exp_pos, mul_one]
    exact Iff.rfl
  rw [e]
  exact ⟨(Homeomorph.isCompact_preimage _).2 hC, (Homeomorph.isOpen_preimage _).2 hO⟩

theorem exists_le_exp {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    ∃ m : ℤ, Valued.v x ≤ WithZero.exp m := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), (WithZero.exp_log hx).ge⟩

theorem isCompact_closure_zpowers_iff {E : Type} [Field E] [NumberField E] [IsCMField E]
    (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (hH : IsClosed (H : Set (GLw n w))) (s : H) :
    IsCompact (closure (Subgroup.zpowers s : Set H)) ↔ ∃ m : ℤ, ∀ k : ℤ, ∀ i j,
      Valued.v ((((s ^ k : H) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
        WithZero.exp m := by
  let B : ℤ → Set (w.adicCompletion E) := fun m => {x | Valued.v x ≤ WithZero.exp m}
  constructor
  · intro hK
    have key : ∀ p : Fin n × Fin n, ∃ m : ℤ, ∀ u ∈ closure (Subgroup.zpowers s : Set H),
        Valued.v (((u : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) p.1 p.2) ≤
          WithZero.exp m := by
      intro p
      have hc : Continuous fun u : H =>
          (((u : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) p.1 p.2) :=
        (Units.continuous_val.comp continuous_subtype_val).matrix_elem p.1 p.2
      obtain ⟨m, hm⟩ := (hK.image hc).elim_directed_cover B
        (fun m => (ball_isCompact_isOpen w m).2)
        (by
          intro x _
          obtain ⟨m, hm⟩ := exists_le_exp w x
          exact Set.mem_iUnion.2 ⟨m, hm⟩)
        (by
          intro a b
          refine ⟨max a b, ?_, ?_⟩ <;> intro x hx <;>
            exact le_trans hx (WithZero.exp_le_exp.2 (by omega)))
      exact ⟨m, fun u hu => hm ⟨u, hu, rfl⟩⟩
    choose m hm using key
    obtain ⟨M, hM⟩ := (Set.finite_range m).bddAbove
    refine ⟨M, fun k i j => ?_⟩
    have h1 := hm (i, j) (s ^ k) (subset_closure (Subgroup.zpow_mem_zpowers s k))
    exact le_trans h1 (WithZero.exp_le_exp.2 (hM ⟨(i, j), rfl⟩))
  · rintro ⟨m, hm⟩
    let Bm : Set (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := {A | ∀ i j, A i j ∈ B m}
    have hBm : IsCompact Bm := by
      have : Bm = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => B m)) := by
        ext A
        exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => (ball_isCompact_isOpen w m).1
    let f : H → Matrix (Fin n) (Fin n) (w.adicCompletion E) ×
        (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ :=
      Units.embedProduct _ ∘ Subtype.val
    have hf : Topology.IsClosedEmbedding f :=
      Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
    let K := Bm ×ˢ (MulOpposite.op '' Bm)
    have hKc : IsCompact K := hBm.prod (hBm.image MulOpposite.continuous_op)
    have hC : IsCompact (f ⁻¹' K) := hf.isCompact_preimage hKc
    have hsub : (Subgroup.zpowers s : Set H) ⊆ f ⁻¹' K := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      refine ⟨fun i j => hm k i j, ⟨(((s ^ k : H) : GLw n w)⁻¹ : GLw n w), fun i j => ?_, rfl⟩⟩
      have h2 := hm (-k) i j
      rw [_root_.zpow_neg] at h2
      change Valued.v (_ : w.adicCompletion E) ≤ WithZero.exp m
      simpa using h2
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)

end GlobalTheory.PowersCompact
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Topology ValuativeRel

namespace GlobalTheory.CjInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E}

theorem valuation_equiv :
    (valuation (w.adicCompletion E)).IsEquiv (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv _ _

theorem lt_one_iff (x : w.adicCompletion E) : valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  simp only [← not_le]
  exact not_congr valuation_equiv.one_le_iff_one_le

theorem tendsto_pow_zero {x : w.adicCompletion E} (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [← lt_one_iff] at h
  rw [(IsValuativeTopology.hasBasis_nhds_zero' (w.adicCompletion E)).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero (w.adicCompletion E)) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  show valuation _ (x ^ m) < γ
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : w.adicCompletion E | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion E) := by
  have := (IsValuativeTopology.hasBasis_nhds_zero' (w.adicCompletion E)).mem_iff.2 ⟨1, one_ne_zero, fun _ hy => hy⟩
  simpa only [lt_one_iff] using this

theorem lt_one_of_map (s : w.adicCompletion E →+* w.adicCompletion E) (hs : Continuous s) {x : w.adicCompletion E}
    (h : Valued.v x < 1) : Valued.v (s x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s x ^ n) atTop (𝓝 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ Valued.v (s x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem valued_map_eq (s : w.adicCompletion E →+* w.adicCompletion E) (hs : Continuous s) (hss : ∀ x, s (s x) = x)
    (x : w.adicCompletion E) : Valued.v (s x) = Valued.v x := by

  have hle : ∀ y : w.adicCompletion E, Valued.v y ≤ 1 → Valued.v (s y) ≤ 1 := by
    intro y hy
    by_contra hc
    push_neg at hc
    have hy0 : s y ≠ 0 := by
      intro h0; rw [h0, map_zero] at hc; exact absurd hc (not_lt.2 zero_le')
    have h1 : Valued.v (s y)⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
    have h2 := lt_one_of_map s hs h1
    rw [map_inv₀, hss, map_inv₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v y := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]
      intro h; apply hy0; rw [h, map_zero]
    exact absurd hy (not_le.2 ((inv_lt_one₀ h0).1 h2))

  have hord : ∀ a b : w.adicCompletion E, b ≠ 0 → Valued.v a ≤ Valued.v b → Valued.v (s a) ≤ Valued.v (s b) := by
    intro a b hb hab
    have hb' : s b ≠ 0 := (map_ne_zero s).2 hb
    have h1 : Valued.v (a / b) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le'
    have h2 := hle _ h1
    rw [map_div₀, map_div₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (s b) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact hb'
    exact (div_le_one₀ h0).1 h2

  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  set p : w.adicCompletion E := algebraMap E (w.adicCompletion E) π with hp
  have hvp : Valued.v p = WithZero.exp (-1) := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w π
    rw [hπ] at this
    exact this
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hvp; exact WithZero.exp_ne_zero hvp.symm
  have hsp0 : s p ≠ 0 := (map_ne_zero s).2 hp0
  have hvsp : Valued.v (s p) = Valued.v p := by
    apply le_antisymm
    · rw [hvp]; apply le_exp_neg_one; apply lt_one_of_map s hs; rw [hvp]
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    · have := hord (s p) p hp0 (by
        rw [hvp]; apply le_exp_neg_one; apply lt_one_of_map s hs; rw [hvp]
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
      rwa [hss] at this
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  set k := WithZero.log (Valued.v x) with hk
  set u := x * p ^ k with hu
  have hvpk : Valued.v p ^ k ≠ 0 := zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 hp0)
  have hvu : Valued.v u = 1 := by
    rw [hu, map_mul, map_zpow₀, hvp, ← WithZero.exp_log hvx, ← hk, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hvu; exact zero_ne_one hvu
  have hsu1 : Valued.v (s u) ≤ 1 := hle u hvu.le
  have hsu2 : Valued.v (s u⁻¹) ≤ 1 := hle u⁻¹ (by rw [map_inv₀, hvu, inv_one])
  have hsu : Valued.v (s u) = 1 := by
    apply le_antisymm hsu1
    rw [map_inv₀, map_inv₀] at hsu2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (s u) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact (map_ne_zero s).2 hu0
    exact (inv_le_one₀ h0).1 hsu2
  rw [hu, map_mul, map_zpow₀, map_mul, map_zpow₀, hvsp] at hsu
  rw [hu, map_mul, map_zpow₀] at hvu
  exact mul_right_cancel₀ hvpk (hsu.trans hvu.symm)

end GlobalTheory.CjInv

namespace GlobalTheory.BCT

theorem cj_involutive_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x, cj w (cj w x) = x) ∧ ∀ x, Valued.v (cj w x) = Valued.v x := by
  intro E _ _ _ w
  have key : (∀ x, cj w (cj w x) = x) ∧ Continuous (cj w) := by
    unfold cj
    split_ifs with h
    · obtain ⟨hc, hE⟩ := h.choose_spec
      refine ⟨fun x => ?_, hc⟩
      have hd := HeightOneSpectrum.denseRange_algebraMap E w
      have := hd.equalizer (hc.comp hc) continuous_id (funext fun y => by
        simp only [Function.comp_apply, id_eq, hE, IsCMField.complexConj_apply_apply])
      exact congrFun this x
    · exact ⟨fun x => rfl, continuous_id⟩
  exact ⟨key.1, GlobalTheory.CjInv.valued_map_eq (cj w) key.2 key.1⟩

end GlobalTheory.BCT
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CharpolyBound

theorem continuous_coeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  refine (MvPolynomial.continuous_eval _).comp ?_
  exact continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1)

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_vle (w : Pl E) (m : ℤ) : IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound {X : Type} [TopologicalSpace X] (w : Pl E) {f : X → w.adicCompletion E} (hf : Continuous f)
    {C : Set X} (hC : IsCompact C) : ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ C, Valued.v (f x) ≤ B := by
  have hcov : C ⊆ ⋃ m : ℤ, f ⁻¹' {y | Valued.v y ≤ WithZero.exp m} := by
    intro x _
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
    rcases eq_or_ne (Valued.v (f x)) 0 with h | h
    · exact ⟨0, by rw [h]; exact zero_le'⟩
    · exact ⟨WithZero.log (Valued.v (f x)), (WithZero.exp_log h).ge⟩
  have hmono : Monotone fun m : ℤ => f ⁻¹' {y | Valued.v y ≤ WithZero.exp m} := by
    intro a b hab x hx
    exact le_trans hx (WithZero.exp_le_exp.2 hab)
  obtain ⟨m, hm⟩ := hC.elim_directed_cover _ (fun m => (isOpen_vle w m).preimage hf) hcov hmono.directed_le
  exact ⟨WithZero.exp m, fun x hx => hm hx⟩

end GlobalTheory.CharpolyBound

open GlobalTheory.CharpolyBound in
theorem GlobalTheory.CharpolyBound.bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (C : Set (GLw n w)), IsCompact C → ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ B) ∧ Valued.v ((g.val.charpoly.coeff 0)⁻¹) ≤ B := by
  intro E _ _ _ n w C hC
  have hval : Continuous fun g : GLw n w => g.val := Units.continuous_val
  have hinv : Continuous fun g : GLw n w => ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    Units.continuous_coe_inv
  have hk : ∀ k : ℕ, ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, Valued.v (g.val.charpoly.coeff k) ≤ B :=
    fun k => exists_bound w ((continuous_coeff n k).comp hval) hC
  choose Bk hBk using hk
  obtain ⟨Bi, hBi⟩ := exists_bound w (hinv.matrix_det) hC
  refine ⟨(Finset.range (n + 1)).sup Bk ⊔ Bi, fun g hg => ⟨fun k => ?_, ?_⟩⟩
  · by_cases hkn : k ≤ n
    · exact le_sup_of_le_left ((hBk k g hg).trans (Finset.le_sup (f := Bk) (Finset.mem_range.2 (by omega))))
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; omega), map_zero]
      exact zero_le'
  · have h0 : g.val.charpoly.coeff 0 = (-1) ^ n * g.val.det := by
      rw [det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    have hdet : g.val.det * ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det = 1 := by
      rw [← det_mul, Units.mul_inv, det_one]
    have hc : (g.val.charpoly.coeff 0)⁻¹ =
        (-1) ^ n * ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det := by
      rw [h0, mul_inv, inv_eq_of_mul_eq_one_right hdet, ← inv_pow, inv_neg_one]
    rw [hc, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    exact le_sup_of_le_right (hBi g hg)
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.KapSignFull

theorem ordL_cj_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E)
    (hcj : ∀ x, Valued.v (cj w x) = Valued.v x) (x : w.adicCompletion E) (hx : x ≠ 0) :
    ordL (cj w x * x) = 2 * ordL x := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  have e : Valued.v (cj w x * x) = Valued.v x * Valued.v x := by rw [map_mul, hcj]
  have h1 : Valued.v (cj w x * x) ≠ 0 := by rw [e]; exact mul_ne_zero h0 h0
  unfold ordL
  rw [dite_eq_right h1, dite_eq_right h0]
  have : WithZero.unzero h1 = WithZero.unzero h0 * WithZero.unzero h0 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, e]
  rw [this, toAdd_mul]; ring

theorem kapSign_charpoly_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) → ∀ γ : GLw n w, kapSign n w γ.val.charpoly γ = 1 := by
  intro E _ _ _ n w hcj γ
  unfold kapSign
  split_ifs with hs
  · rfl
  · simp only []
    set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val γ.val.charpoly)) with hV
    have htop : V₁ = ⊤ := by rw [hV, Matrix.aeval_self_charpoly]; simp
    set b := Module.finBasis (w.adicCompletion E) V₁
    have hm : Module.finrank (w.adicCompletion E) V₁ = n := by
      rw [htop, finrank_top]; simp
    let e : Fin (Module.finrank (w.adicCompletion E) V₁) ≃ Fin n := finCongr hm
    let M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := fun k j => (b (e.symm j)).1 k
    have hG : (Matrix.of fun i j => ∑ k, cj w ((b i).1 k) * (b j).1 k) =
        ((M.map (cj w))ᵀ * M).submatrix e e := by
      refine Matrix.ext fun i j => ?_
      rw [Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => rfl
    have hM : M.det ≠ 0 := by
      have hli : LinearIndependent (w.adicCompletion E) M.col := by
        have h1 : LinearIndependent (w.adicCompletion E) (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) :=
          b.linearIndependent.map' V₁.subtype (Submodule.ker_subtype V₁)
        have h2 := h1.comp e.symm e.symm.injective
        have hc : M.col = (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) ∘ e.symm := by funext j; rfl
        rw [hc]; exact h2
      exact (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli) |>.ne_zero
    rw [hG, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose, show (M.map (cj w)).det = cj w M.det by rw [RingHom.map_det]; rfl,
      ordL_cj_mul w hcj _ hM]
    exact Even.neg_one_zpow ⟨ordL M.det, by ring⟩

end GlobalTheory.BCT.KapSignFull
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

def cPl (w : Pl E) : Pl E := conjSrc (IsCMField.complexConj E).toRingEquiv w

def orb (w : Pl E) : Finset (Pl E) := {w, cPl E w}

def idem (T : Finset (Pl E)) : FiniteAdeleRing (𝓞 E) E :=
  ⟨fun w => if w ∈ T then 1 else 0, by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with w hw
    rw [if_neg (by simpa using hw)]
    exact zero_mem _⟩

theorem idem_mul_self (T : Finset (Pl E)) : idem E T * idem E T = idem E T := by
  refine Subtype.ext (funext fun w => ?_)
  show (if w ∈ T then (1 : w.adicCompletion E) else 0) * (if w ∈ T then 1 else 0) = if w ∈ T then 1 else 0
  split_ifs <;> simp

def prjM (T : Finset (Pl E)) :
    Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) →* Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) where
  toFun M := idem E T • M + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
  map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
  map_mul' M N := by
    have h1 : idem E T * (1 - idem E T) = 0 := by rw [mul_sub, mul_one, idem_mul_self, sub_self]
    have h2 : (1 - idem E T) * idem E T = 0 := by rw [sub_mul, one_mul, idem_mul_self, sub_self]
    have h3 : (1 - idem E T) * (1 - idem E T) = 1 - idem E T := by rw [sub_mul, one_mul, h1, sub_zero]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
      idem_mul_self, h1, h2, h3, zero_smul, add_zero, zero_add]

def prjG (T : Finset (Pl E)) : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) →* GL (Fin n) (FiniteAdeleRing (𝓞 E) E) :=
  Units.map (prjM E n T)

def Kglob : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :=
  ⨅ w : Pl E, (GlobalTheory.LFun.KGL w (n := n)).comap (GeneralLinearGroup.map (pLoc E w))

instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 E) E) :=
  T2Space.of_injective_continuous (f := fun x : FiniteAdeleRing (𝓞 E) E => (x : ∀ v : Pl E, v.adicCompletion E))
    Subtype.val_injective RestrictedProduct.continuous_coe

end GlobalTheory.EulerTw
end
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.localSign_full_charpoly_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) → ∀ γ : GLw n w, kapSign n w γ.val.charpoly γ = 1 := by
  first | exact @GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one | exact GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one | (intros; apply GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

theorem _root_.GlobalTheory.T.isCompact_closure_zpowers_iff_bounded_entries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)), IsClosed (H : Set (GLw n w)) → ∀ s : H, IsCompact (closure (Subgroup.zpowers s : Set H)) ↔ ∃ m : ℤ, ∀ k : ℤ, ∀ i j, Valued.v ((((s ^ k : H) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp m := by
  first | exact @GlobalTheory.PowersCompact.isCompact_closure_zpowers_iff | exact GlobalTheory.PowersCompact.isCompact_closure_zpowers_iff | (intros; apply GlobalTheory.PowersCompact.isCompact_closure_zpowers_iff <;> assumption)

end
end
