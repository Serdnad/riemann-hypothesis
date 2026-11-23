module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle070
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Mathlib.Analysis.CStarAlgebra.Classes
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.DatumEigen

variable {k : Type} [Field k] [ValuativeRel k]

theorem val_det_sub_lt {m : Type} [Fintype m] [DecidableEq m] {M N : Matrix m m k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hN : ∀ i j, N i j ∈ 𝒪[k]) (h : ∀ i j, valuation k (M i j - N i j) < 1) :
    valuation k (M.det - N.det) < 1 := by
  have key : ∀ x : 𝒪[k], IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  let M' : Matrix m m 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  let N' : Matrix m m 𝒪[k] := fun i j => ⟨N i j, hN i j⟩
  have eM : M = (algebraMap 𝒪[k] k).mapMatrix M' := rfl
  have eN : N = (algebraMap 𝒪[k] k).mapMatrix N' := rfl
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M' = (IsLocalRing.residue 𝒪[k]).mapMatrix N' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, key]
    exact h i j
  rw [eM, eN, ← RingHom.map_det, ← RingHom.map_det, ← map_sub, ← key, map_sub, RingHom.map_det,
    RingHom.map_det, hres, sub_self]

theorem val_mul_lt {a b : k} (ha : valuation k a ≤ 1) (hb : valuation k b < 1) : valuation k (a * b) < 1 := by
  rw [map_mul]
  exact (mul_le_of_le_one_left' ha).trans_lt hb

theorem det_int {m : Type} [Fintype m] [DecidableEq m] {M : Matrix m m k} (hM : ∀ i j, M i j ∈ 𝒪[k]) :
    M.det ∈ 𝒪[k] := by
  let M' : Matrix m m 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  have eM : M = (algebraMap 𝒪[k] k).mapMatrix M' := rfl
  rw [eM, ← RingHom.map_det]
  exact (M'.det).2

theorem eq_one_of_mul {a b : ValueGroupWithZero k} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  by_contra hlt
  replace hlt := not_le.1 hlt
  have : a * b < 1 := (mul_le_of_le_one_right' hb).trans_lt hlt
  exact this.ne h

theorem tame_eq {ξ : kˣ →* ℂˣ} (hξ : IsTame ξ) {a b : kˣ} (hb : valuation k (b : k) = 1)
    (h : valuation k ((a : k) - b) < 1) : ξ a = ξ b := by
  have hb0 : (b : k) ≠ 0 := b.ne_zero
  have h1 : ξ (a * b⁻¹) = 1 := by
    apply hξ
    have e : ((a * b⁻¹ : kˣ) : k) - 1 = ((a : k) - b) * (b : k)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [e, map_mul, map_inv₀, hb, inv_one, mul_one]
    exact h
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Blocks

variable {A D E : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem int_of_mem {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) (i l : A ⊕ D) : j.val i l ∈ 𝒪[k] :=
  ((GlobalTheory.SplitFlip.mem_KO_iff j).1 (mem_parahoric.1 hj).1).1 i l

theorem det_cong {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) :
    valuation k (j.val.det - j.val.toBlocks₁₁.det * j.val.toBlocks₂₂.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  rw [← det_fromBlocks_zero₂₁ j.val.toBlocks₁₁ j.val.toBlocks₁₂ j.val.toBlocks₂₂]
  refine val_det_sub_lt hJ ?_ ?_
  · rintro (i | i) (l | l) <;> simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₂, hJ]
  · rintro (i | i) (l | l) <;> simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₂, hl]

theorem val_det_blocks {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) :
    valuation k j.val.toBlocks₁₁.det = 1 ∧ valuation k j.val.toBlocks₂₂.det = 1 := by
  have hJ := int_of_mem hj
  have h1 : valuation k j.val.det = 1 := by
    have := nabs_det_of_mem_KO (mem_parahoric.1 hj).1
    rwa [nabs_eq_one_iff] at this
  have h2 := Valuation.map_eq_of_sub_lt _ (show valuation k (j.val.toBlocks₁₁.det * j.val.toBlocks₂₂.det
      - j.val.det) < valuation k j.val.det by
    rw [h1, ← Valuation.map_neg, neg_sub]; exact det_cong hj)
  rw [h1, map_mul] at h2
  have i11 : valuation k j.val.toBlocks₁₁.det ≤ 1 := det_int fun i l => hJ _ _
  have i22 : valuation k j.val.toBlocks₂₂.det ≤ 1 := det_int fun i l => hJ _ _
  exact ⟨eq_one_of_mul i11 i22 h2, eq_one_of_mul i22 i11 (by rw [mul_comm]; exact h2)⟩


omit [Fintype E] [DecidableEq E] in
theorem inSupp_mul {x : Matrix (A ⊕ E) (A ⊕ D) k} (hx : InSupp x) {j : GL (A ⊕ D) k}
    (hj : j ∈ parahoric k A D) : InSupp (x * j.val) ∧
      valuation k ((x * j.val).toBlocks₁₁.det - x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  obtain ⟨hxi, hxd, hxl⟩ := hx
  have hprod : ∀ i l, (x * j.val) i l ∈ 𝒪[k] := fun i l => by
    rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hxi i m) (hJ m l)
  have hcong : valuation k ((x * j.val).toBlocks₁₁.det - x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hxi _ _) (hJ _ _)
    · simp only [toBlocks₁₁, of_apply, Matrix.mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => val_mul_lt (hxi _ _) (hl _ _)
  have hd1 : valuation k (x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hxd, one_mul, (val_det_blocks hj).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact val_mul_lt (hJ _ _) (hxl _ _)
    · exact val_mul_lt (hxi _ _) (hl _ _)

end Blocks

theorem om_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ₀ : kˣ →* ℂˣ), IsTame ξ → IsUnram μ₀ →
    ∀ j ∈ parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    om (μ₀ * ξ) j (1 : GL (A ⊕ E) k) (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ) = fun x => (ξ d : ℂ) * datum ξ x := by
  intro k _ _ _ _ A D E _ _ _ _ _ _ ξ μ₀ hξ hμ j hj d hd
  funext x
  have hK := (mem_parahoric.1 hj).1
  have hdetv : valuation k (GeneralLinearGroup.det j : k) = 1 := (nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hK)
  have hμj : μ₀ (GeneralLinearGroup.det j) = 1 := hμ _ hdetv
  simp only [om, nabs_det_of_mem_KO hK, MonoidHom.mul_apply, hμj, one_mul, map_one, mul_one, inv_one,
    Units.val_one, Real.one_rpow, Complex.ofReal_one]
  rw [show nabs k 1 = 1 by simp [nabs], Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.one_mul]
  unfold datum
  obtain ⟨h11, h22⟩ := val_det_blocks hj
  by_cases hx : InSupp x
  · obtain ⟨hs, hc⟩ := inSupp_mul hx hj
    have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
    set u : kˣ := Units.mk0 _ n11 with hu
    have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
    have t1 : ξ (GeneralLinearGroup.det j) = ξ (u * d) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
      rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
      exact det_cong hj
    have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (Units.mk0 _ hx.det_ne * u) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, Units.val_mk0, hx.2.1, one_mul]; exact h11) ?_
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
      exact hc
    rw [dite_eq_left hs, dite_eq_left hx, t1, t2, map_mul, map_mul]
    simp only [Units.val_mul, _root_.mul_inv_rev, Units.val_inv_eq_inv_val]
    have a1 : (ξ u : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · have hs : ¬ InSupp (x * j.val) := fun hs => by
      have := (inSupp_mul hs (inv_mem hj)).1
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
      exact hx this
    rw [dite_eq_right hs, dite_eq_right hx, mul_zero, mul_zero]

end GlobalTheory.DatumEigen
end
end

section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ParahoricOpenCompact

theorem KOne_le_parahoric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] :
    KOne k (A ⊕ D) ≤ parahoric k A D := by
  intro g hg
  refine mem_parahoric.2 ⟨StepData.KOne_le_KO hg, fun i j => ?_⟩
  have h := StepData.mem_KOne.1 hg
  have h' : valuation k ((g.val - 1) (.inr i) (.inl j)) < 1 := h _ _
  simpa using h'

theorem isOpen_isCompact_parahoric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) ∧ IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  intro k _ _ _ _ A D _ _ _ _
  have ho : IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) :=
    Subgroup.isOpen_mono (KOne_le_parahoric k A D) StepData.isOpen_KOne
  exact ⟨ho, SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho)
    fun _ hg => (mem_parahoric.1 hg).1⟩

end GlobalTheory.ParahoricOpenCompact
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling
  GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ParahoricLowerBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_val (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem lower_block_det (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (j : GL (A ⊕ D) k) (hj : j ∈ parahoric k A D) :
    ∃ a b : 𝒪[k], (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det = algebraMap 𝒪[k] k a ∧
      ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det = algebraMap 𝒪[k] k b ∧
      IsLocalRing.residue 𝒪[k] (a * b) = 1 := by
  obtain ⟨⟨h, rfl⟩, hlow⟩ := mem_parahoric.1 hj
  set f := IsLocalRing.residue 𝒪[k]
  set Hb := f.mapMatrix h.val
  set Gb := f.mapMatrix (h⁻¹).val
  have hz : Hb.toBlocks₂₁ = 0 := by
    ext i j'
    exact (residue_eq_zero_iff_val _).2 (hlow i j')
  have hHG : Hb * Gb = 1 := by
    simp only [Hb, Gb, ← map_mul, Units.mul_inv, map_one]
  have h22 : Hb.toBlocks₂₂ * Gb.toBlocks₂₂ = 1 := by
    have := congrArg Matrix.toBlocks₂₂ hHG
    rw [← fromBlocks_toBlocks Hb, ← fromBlocks_toBlocks Gb, fromBlocks_multiply, hz] at this
    have e : (1 : Matrix (A ⊕ D) (A ⊕ D) 𝓀[k]).toBlocks₂₂ = 1 := by
      ext a b; simp [toBlocks₂₂, Matrix.one_apply]
    simpa [e] using this
  refine ⟨h.val.toBlocks₂₂.det, (h⁻¹).val.toBlocks₂₂.det, ?_, ?_, ?_⟩
  · rw [RingHom.map_det]; rfl
  · rw [RingHom.map_det, ← map_inv]; rfl
  · rw [map_mul, RingHom.map_det, RingHom.map_det, ← det_mul]
    exact (congrArg det h22).trans det_one

end GlobalTheory.ParahoricLowerBlock

namespace GlobalTheory.ParahoricLowerBlock

theorem lower_block_tame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ →
  ∀ j ∈ parahoric k A D, (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det ≠ 0 ∧
    ∀ d d' : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      (d' : k) = ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det → (ξ d : ℂ) * ξ d' = 1 := by
  intro k _ _ _ _ A D _ _ _ _ ξ hξ j hj
  obtain ⟨a, b, ha, hb, hab⟩ := lower_block_det A D j hj
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul, map_zero] at hab
    exact zero_ne_one hab
  refine ⟨?_, fun d d' hd hd' => ?_⟩
  · rw [ha]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective 𝒪[k] k)).2 ha0
  · have hv : valuation k (((d * d' : kˣ) : k) - 1) < 1 := by
      have e : ((d * d' : kˣ) : k) - 1 = algebraMap 𝒪[k] k (a * b - 1) := by
        rw [Units.val_mul, hd, hd', ha, hb, map_sub, map_mul, map_one]
      rw [e, ← residue_eq_zero_iff_val, map_sub, hab, map_one, sub_self]
    have := hξ (d * d') hv
    rw [map_mul] at this
    have := congrArg Units.val this
    simpa using this

end GlobalTheory.ParahoricLowerBlock
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.SuppFirstBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem toBlocks₁₁_mul_diag {A D E : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (z : Matrix (A ⊕ E) (A ⊕ D) k) (x : GL A k) (y : GL D k) :
    (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₁ = z.toBlocks₁₁ * x.val := by
  have he : (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k) =
      fromBlocks x.val 0 0 y.val := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [emb₂, leviEmb, leviTwo, two, Matrix.blockDiagonal']
  rw [he]
  conv_lhs => rw [← fromBlocks_toBlocks z]
  simp [fromBlocks_multiply]

theorem exists_GL_of_int {A : Type} [Fintype A] [DecidableEq A] (M : Matrix A A k)
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hd : valuation k M.det = 1) :
    ∃ g : GL A 𝒪[k], (GeneralLinearGroup.map (n := A) (algebraMap 𝒪[k] k) g : Matrix A A k) = M := by
  let N : Matrix A A 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  have hN : (algebraMap 𝒪[k] k).mapMatrix N = M := rfl
  have hu : IsUnit N.det := by
    rw [(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one, RingHom.map_det, hN]
    exact hd
  refine ⟨((Matrix.isUnit_iff_isUnit_det N).2 hu).unit, ?_⟩
  exact hN

end GlobalTheory.SuppFirstBlock

open GlobalTheory.SuppFirstBlock in
theorem GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (z : Matrix (A ⊕ E) (A ⊕ D) k) (x : GL A k) (y : GL D k),
    InSupp z → InSupp (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)) → x ∈ KO k A := by
  intro k _ _ _ _ A D E _ _ _ _ _ _ z x y hz hw
  have hb := toBlocks₁₁_mul_diag z x y
  obtain ⟨g, hg⟩ := exists_GL_of_int z.toBlocks₁₁ (fun i j => hz.1 _ _) hz.2.1
  obtain ⟨h, hh⟩ := exists_GL_of_int (z.toBlocks₁₁ * x.val)
    (fun i j => by rw [← hb]; exact hw.1 _ _) (by rw [← hb]; exact hw.2.1)
  have key : GeneralLinearGroup.map (n := A) (algebraMap 𝒪[k] k) g * x =
      GeneralLinearGroup.map (n := A) (algebraMap 𝒪[k] k) h := by
    ext1
    rw [Units.val_mul, hg, hh]
  refine ⟨g⁻¹ * h, ?_⟩
  rw [map_mul, map_inv, ← key, inv_mul_cancel_left]
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.ZetaConvergence

attribute [local instance 2000] _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nabs_le {K : Set k} (hK : IsCompact K) : ∃ B : ℝ, ∀ x : kˣ, (x : k) ∈ K → nabs k x ≤ B := by
  obtain ⟨y, hy⟩ := hK.elim_directed_cover (fun y : kˣ => GlobalTheory.SplitWeil.cball y)
    (fun y => GlobalTheory.SplitWeil.isOpen_cball y)
    (fun x _ => by
      by_cases hx : x = 0
      · exact Set.mem_iUnion.2 ⟨1, by simp [hx, GlobalTheory.SplitWeil.cball]⟩
      · exact Set.mem_iUnion.2 ⟨Units.mk0 x hx, by simp [GlobalTheory.SplitWeil.cball]⟩)
    (fun a b => by
      rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
      · exact ⟨b, fun z hz => le_trans (show valuation k z ≤ _ from hz) h, subset_rfl⟩
      · exact ⟨a, subset_rfl, fun z hz => le_trans (show valuation k z ≤ _ from hz) h⟩)
  exact ⟨nabs k y, fun x hx => nabs_le_of_valuation_le (hy hx)⟩

theorem integrable_zetaIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : GL n k → ℂ) (α : ℝ), Continuous c → (∀ N : ℕ, ∃ C : ℝ, ∀ g : GL n k, (∀ i j, Deep (-(N : ℤ)) (g.val i j)) → ‖c g‖ ≤ C * nabs k (GeneralLinearGroup.det g) ^ (-α)) → ∀ Φ ∈ SB (Matrix n n k), ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (zetaIntegrand Φ c s) (volGL ν n) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c α hc hb Φ hΦ
  obtain ⟨N, -, hN, -⟩ := GlobalTheory.SBUniform.exists_bound_period k n Φ hΦ
  obtain ⟨C, hC⟩ := hb N
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨B, hB⟩ := exists_nabs_le (IsCompact.image hK (f := fun x : Matrix n n k => x.det)
    continuous_id.matrix_det)
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : BorelSpace (GL n k) := SplitFlip.borel_GL
  have : SecondCountableTopology (GL n k) := SplitFlip.secondCountable_GL
  have hE := GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) n
  have hd := continuous_density_volGL (k := k) (n := n)
  have hn : IsLocallyConstant fun g : GL n k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hI : Integrable (fun g : GL n k => Φ g.val) ((volM ν n n).comap fun g : GL n k => g.val) := by
    have h1 : Integrable Φ (volM ν n n) := hl.continuous.integrable_of_hasCompactSupport hK
    refine hE.integrable_map_iff.1 ?_
    rw [hE.map_comap]
    exact h1.restrict
  refine ⟨α + Fintype.card n - ((Fintype.card n : ℝ) - 1) / 2, fun s hs => ?_⟩
  set t : ℂ := s + ((Fintype.card n : ℂ) - 1) / 2 with ht
  have htr : t.re = s.re + ((Fintype.card n : ℝ) - 1) / 2 := by
    have : ((Fintype.card n : ℂ) - 1) / 2 = ((((Fintype.card n : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [ht, this, Complex.add_re, Complex.ofReal_re]
  have he : 0 ≤ -(Fintype.card n : ℝ) + -α + t.re := by linarith
  have hz : Continuous (zetaIntegrand Φ c s) :=
    ((hl.continuous.comp Units.continuous_val).mul hc).mul (hn.comp fun r : ℝ => (r : ℂ) ^ t).continuous
  unfold volGL
  rw [integrable_withDensity_iff_integrable_smul' hd.measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hI.norm.mul_const (|C| * B ^ (-(Fintype.card n : ℝ) + -α + t.re))).mono'
    (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hz.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos' k (GeneralLinearGroup.det g)
  by_cases h0 : Φ g.val = 0
  · simp [zetaIntegrand, h0]
  have h1 : nabs k (GeneralLinearGroup.det g) ≤ B := hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩
  have h2 := (hC g (hN _ h0)).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hp.le _))
  rw [norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), zetaIntegrand, norm_mul, norm_mul,
    val_absPow, Complex.norm_cpow_eq_rpow_re_of_pos hp, ← ht, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
  set a := nabs k (GeneralLinearGroup.det g)
  calc _ ≤ a ^ (-(Fintype.card n : ℝ)) * (‖Φ g.val‖ * (|C| * a ^ (-α)) * a ^ t.re) := by gcongr
    _ = ‖Φ g.val‖ * (|C| * a ^ (-(Fintype.card n : ℝ) + -α + t.re)) := by
      rw [Real.rpow_add hp, Real.rpow_add hp]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.ZetaConvergence
end

section

noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.InertZeta

theorem elementaryDivisors_exist_discretely_valued : Smith := by
  intro L _ _ ϖ n hϖ g hg
  have hv0 : Valued.v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.exp_ne_zero
  have hϖ0 : ϖ ≠ 0 := fun h => hv0 (by rw [h, map_zero])
  have hnt : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, hv0, by rw [hϖ]; decide⟩
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hA : IsDiscreteValuationRing A := Valuation.valuationSubring_isDiscreteValuationRing _
  have : IsPrincipalIdealRing (intL L) := inferInstanceAs (IsPrincipalIdealRing A)
  let G : GL (Fin n) L := Matrix.nonsingInvUnit g (isUnit_iff_ne_zero.2 hg)
  obtain ⟨c, hc0, hcg, -⟩ := P.glint_exists_denom (n := Fin n) A G
  obtain ⟨d, -, k₁, h₁, k₂, h₂, e⟩ := P.cartan_decomp_gen (intL L) Valued.v (fun _ => Iff.rfl) ϖ hϖ0
    (fun x hx => by
      have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      refine ⟨-WithZero.log (Valued.v x), ?_⟩
      rw [hϖ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hx']) G c hc0 hcg
  refine ⟨d, k₁, (k₁⁻¹ : GL (Fin n) L), k₂, (k₂⁻¹ : GL (Fin n) L), P.cartan_entries_of_mem _ _ h₁,
    P.cartan_entries_of_mem _ _ (inv_mem h₁), P.cartan_entries_of_mem _ _ h₂,
    P.cartan_entries_of_mem _ _ (inv_mem h₂), k₁.inv_mul, k₂.mul_inv, ?_⟩
  exact e

end GlobalTheory.InertZeta

end
end
