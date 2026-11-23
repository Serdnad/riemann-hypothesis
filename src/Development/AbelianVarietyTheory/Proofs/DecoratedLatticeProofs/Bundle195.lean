module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle192
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceReductionsConjOfNestedFrameStabilisers
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle175
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle176
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.CayleyOrd

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_mul' {α β γ : Type} [Fintype β] {x : Matrix α β L} {y : Matrix β γ L}
    (hx : x ∈ intMat L α β) (hy : y ∈ intMat L β γ) : x * y ∈ intMat L α γ := fun i j =>
  Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hx i k) (hy k j)

theorem intMat_one' {α : Type} [DecidableEq α] : (1 : Matrix α α L) ∈ intMat L α α := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem det_mem' {n : ℕ} {x : Matrix (Fin n) (Fin n) L} (hx : x ∈ intMat L (Fin n) (Fin n)) :
    x.det ∈ Formalism.UG.intL L := by
  have : x = (Formalism.UG.intL L).subtype.mapMatrix (Matrix.of fun i j => (⟨x i j, hx i j⟩ : Formalism.UG.intL L)) := by
    ext i j; rfl
  rw [this, ← RingHom.map_det]; exact SetLike.coe_mem _

theorem v_det_eq_one {n : ℕ} {x y : Matrix (Fin n) (Fin n) L} (hx : x ∈ intMat L (Fin n) (Fin n))
    (hy : y ∈ intMat L (Fin n) (Fin n)) (h : x * y = 1) : Valued.v x.det = 1 := by
  have h1 : Valued.v x.det * Valued.v y.det = 1 := by rw [← map_mul, ← Matrix.det_mul, h, Matrix.det_one, map_one]
  have ha : Valued.v x.det ≤ 1 := GlobalTheory.SphTheta.mem_intL.1 (det_mem' hx)
  have hb : Valued.v y.det ≤ 1 := GlobalTheory.SphTheta.mem_intL.1 (det_mem' hy)
  refine le_antisymm ha ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
    _ ≤ Valued.v x.det * 1 := by gcongr
    _ = _ := mul_one _

theorem ku_int {σ : L →+* L} {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) : k.1.1 ∈ intMat L (Fin n) (Fin n) := by
  obtain ⟨m, hm⟩ := (Subgroup.mem_subgroupOf.1 hk).2
  intro i j
  rw [← hm]; exact (m.1 i j).2

theorem zpow_int {ϖ : L} (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (m : ℤ) (hm : 0 ≤ m) : ϖ ^ m ∈ Formalism.UG.intL L := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [zpow_natCast]
  refine Subring.pow_mem _ (GlobalTheory.SphTheta.mem_intL.2 ?_) k
  rw [hv]; exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)

theorem v_zpow {ϖ : L} (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (m : ℤ) : Valued.v (ϖ ^ m) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, hv, ← WithZero.coe_zpow, ← ofAdd_zsmul]; congr 2; simp

end GlobalTheory.ChainOnto.CayleyOrd

namespace GlobalTheory.ChainOnto


open GlobalTheory.ChainOnto.CayleyOrd in
theorem ordL_det_one_add_of_inv_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (g t : GU σ n) (d : Fin n → ℤ), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, g⁻¹ = k₁ * t * k₂ → (1 + g.1.1).det ≠ 0 → (1 + g.1.1)⁻¹ ∈ intMat L (Fin n) (Fin n) → ordL (1 + g.1.1).det = -∑ i, max (d i) 0 := by
  intro L _ _ _ ϖ σ q hU n g t d ht k₁ hk₁ k₂ hk₂ hg hdet hc
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hU.2.2.2.1
  have hϖ : ϖ ≠ 0 := by intro h; rw [h, map_zero] at hv; exact WithZero.zero_ne_coe hv
  have hK1 := ku_int hk₁
  have hK1i := ku_int (inv_mem hk₁)
  have hK2 := ku_int hk₂
  have hK2i := ku_int (inv_mem hk₂)
  have e1 : k₁.1.1 * (k₁⁻¹).1.1 = 1 := by
    rw [show k₁.1.1 * (k₁⁻¹).1.1 = (k₁ * k₁⁻¹).1.1 from rfl, mul_inv_cancel]; rfl
  have e1' : (k₁⁻¹).1.1 * k₁.1.1 = 1 := by
    rw [show (k₁⁻¹).1.1 * k₁.1.1 = (k₁⁻¹ * k₁).1.1 from rfl, inv_mul_cancel]; rfl
  have e2 : k₂.1.1 * (k₂⁻¹).1.1 = 1 := by
    rw [show k₂.1.1 * (k₂⁻¹).1.1 = (k₂ * k₂⁻¹).1.1 from rfl, mul_inv_cancel]; rfl
  have eg : g.1.1 * (g⁻¹).1.1 = 1 := by
    rw [show g.1.1 * (g⁻¹).1.1 = (g * g⁻¹).1.1 from rfl, mul_inv_cancel]; rfl
  have hgi : (g⁻¹).1.1 = k₁.1.1 * t.1.1 * k₂.1.1 := by rw [hg]; rfl
  set Ti : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => ϖ ^ (-d i) with hTi
  have eT : t.1.1 * Ti = 1 := by
    rw [ht, hTi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hG : g.1.1 = (k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1 := by
    have X : (k₁.1.1 * t.1.1 * k₂.1.1) * ((k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂.1.1, e2, Matrix.one_mul, ← Matrix.mul_assoc t.1.1, eT, Matrix.one_mul, e1]
    calc g.1.1 = g.1.1 * ((k₁.1.1 * t.1.1 * k₂.1.1) * ((k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1)) := by rw [X, Matrix.mul_one]
      _ = (g.1.1 * (g⁻¹).1.1) * ((k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1) := by rw [hgi]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [eg, Matrix.one_mul]
  have hu : IsUnit (1 + g.1.1).det := Ne.isUnit hdet
  have hCG : (1 + g.1.1)⁻¹ * (1 + g.1.1) = 1 := Matrix.nonsing_inv_mul _ hu
  have hGC : (1 + g.1.1) * (1 + g.1.1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hCG' : (1 + g.1.1)⁻¹ * g.1.1 = 1 - (1 + g.1.1)⁻¹ := by
    rw [Matrix.mul_add, Matrix.mul_one] at hCG; exact eq_sub_of_add_eq' hCG
  set D : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => ϖ ^ max (d i) 0 with hD
  set Di : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => ϖ ^ (-max (d i) 0) with hDi
  have eD : D * Di = 1 := by
    rw [hD, hDi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hyZ : (D * k₂.1.1 * (1 + g.1.1)) * ((1 + g.1.1)⁻¹ * (k₂⁻¹).1.1 * Di) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 + g.1.1), hGC, Matrix.one_mul, ← Matrix.mul_assoc k₂.1.1, e2, Matrix.one_mul, eD]
  have hDint : D ∈ intMat L (Fin n) (Fin n) := fun i j => by
    rw [hD, Matrix.diagonal_apply]; split_ifs
    · exact zpow_int hv _ (le_max_right _ _)
    · exact Subring.zero_mem _
  have hy : D * k₂.1.1 * (1 + g.1.1) ∈ intMat L (Fin n) (Fin n) := by
    have : D * k₂.1.1 * (1 + g.1.1) = D * k₂.1.1 + (D * Ti) * (k₁⁻¹).1.1 := by
      rw [Matrix.mul_add, Matrix.mul_one, hG]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂.1.1, e2, Matrix.one_mul]
    rw [this]
    refine add_mem (intMat_mul' hDint hK2) (intMat_mul' ?_ hK1i)
    intro i j
    rw [hD, hTi, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]; split_ifs
    · rw [← zpow_add₀ hϖ]; exact zpow_int hv _ (by omega)
    · exact Subring.zero_mem _
  have hCK : (1 + g.1.1)⁻¹ * (k₂⁻¹).1.1 * Ti = (1 - (1 + g.1.1)⁻¹) * k₁.1.1 := by
    rw [← hCG', hG]; simp only [Matrix.mul_assoc]; rw [e1', Matrix.mul_one]
  have hZ : (1 + g.1.1)⁻¹ * (k₂⁻¹).1.1 * Di ∈ intMat L (Fin n) (Fin n) := by
    intro i j
    rw [hDi, Matrix.mul_diagonal]
    rcases le_or_gt (d j) 0 with h | h
    · rw [max_eq_right h, neg_zero, zpow_zero, mul_one]; exact intMat_mul' hc hK2i i j
    · rw [max_eq_left h.le]
      have := congrFun (congrFun hCK i) j
      rw [hTi, Matrix.mul_diagonal] at this
      rw [this]
      exact intMat_mul' (sub_mem intMat_one' hc) hK1 i j
  have vy := v_det_eq_one hy hZ hyZ
  have vK := v_det_eq_one hK2 hK2i e2
  rw [Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, vK, mul_one, hD, Matrix.det_diagonal, map_prod] at vy
  simp only [v_zpow hv] at vy
  have hP : ∀ s : Finset (Fin n), ∏ i ∈ s, (((Multiplicative.ofAdd (-max (d i) 0) : Multiplicative ℤ)) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-∑ i ∈ s, max (d i) 0) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← WithZero.coe_mul, ← ofAdd_add, neg_add]
  rw [hP] at vy
  have vX : Valued.v (1 + g.1.1).det = ((Multiplicative.ofAdd (∑ i, max (d i) 0) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [eq_inv_of_mul_eq_one_right vy, ← WithZero.coe_inv, ← ofAdd_neg, neg_neg]
  have h0 : Valued.v (1 + g.1.1).det ≠ 0 := by rw [vX]; exact WithZero.coe_ne_zero
  unfold ordL
  rw [dite_eq_right h0]
  have hu : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (∑ i, max (d i) 0) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    (WithZero.coe_unzero h0).trans vX
  rw [WithZero.coe_injective hu, toAdd_ofAdd]

end GlobalTheory.ChainOnto
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto


open Classical in
theorem heisInv_forms_proportional : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ l e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, l (ρ u m) = l m) → (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, e (ρ u m) = e m) → ∀ m, e m * l s = l m * e s := by
  intro L _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s h l e hl he m
  have hH := h.isHeis

  have key : ∀ (f : M →ₗ[ℂ] ℂ), (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, f (ρ u m) = f m) →
      ∀ x : Matrix (Fin n') (Fin n) L, f (ρ x s) = if x ∈ intMat L (Fin n') (Fin n) then f s else 0 := by
    intro f hf x
    split_ifs with hx
    · rw [h.fixes x hx]
    · have : ∃ i j, x i j ∉ Formalism.UG.intL L := by
        by_contra hc
        push_neg at hc
        exact hx hc
      obtain ⟨i, j, hij⟩ := this
      obtain ⟨u, hu, hne⟩ := GlobalTheory.SphTheta.exists_pairing_single_ne h.1.unr h.v_two h.1.delta.1 h.1.psi_ne x hij
      have hu' : Matrix.single i.rev j.rev u ∈ intMat L (Fin n') (Fin n) := by
        intro i' j'
        rw [Matrix.single_apply]
        split_ifs
        exacts [hu, zero_mem _]
      have hc := hH.comm (Matrix.single i.rev j.rev u) x s
      rw [h.fixes _ hu'] at hc
      have h1 := hf _ hu' (ρ x s)
      rw [hc, map_smul, smul_eq_mul, hH.swap] at h1
      have hz : (GlobalTheory.SphTheta.pairing σ δ ψ x (Matrix.single i.rev j.rev u))⁻¹ ≠ 1 := by
        intro h'; exact hne (inv_eq_one.1 h')
      have : ((GlobalTheory.SphTheta.pairing σ δ ψ x (Matrix.single i.rev j.rev u))⁻¹ - 1) * f (ρ x s) = 0 := by
        rw [sub_mul, one_mul, h1, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hz)
  have hall : (l s) • e = (e s) • l := by
    refine LinearMap.ext_on_range h.2.2.2 fun x => ?_
    simp only [LinearMap.smul_apply, smul_eq_mul, key e he x, key l hl x]
    split_ifs <;> ring
  have := LinearMap.congr_fun hall m
  simp only [LinearMap.smul_apply, smul_eq_mul] at this
  rw [mul_comm, this, mul_comm]

end GlobalTheory.ChainOnto

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LFun (heckeVec)

namespace GlobalTheory.ChainOnto


open Formalism.UG GlobalTheory.Hk3 GlobalTheory.SphTheta in
theorem heckeVec_howe : GlobalTheory.Hk3.HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ h' ∈ Hecke ℂ (KU σ n'), ∃ h ∈ Hecke ℂ (KU σ n), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s := by
  intro hH L _ _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS h' hh'
  have hU := hS.1.unr
  obtain ⟨-, hw2⟩ := hH L ϖ σ q δ n n' (antiG L n) (antiG L n') ψ M ρ ω hS.1 s hS.2.1 hS.2.2.1 hS.2.2.2
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hK' := P.isCommensurated_integral_unitary_of_unramified hU n'
  have f1 : ∀ k ∈ KU σ n, ω (k, 1) s = s := fun k hk => hS.1.fix k 1 (mem_KU_iff.1 hk) (one_mem _) s hS.2.2.1
  have f2 : ∀ k ∈ KU σ n', ω (1, k) s = s := fun k hk => hS.1.fix 1 k (one_mem _) (mem_KU_iff.1 hk) s hS.2.2.1
  set w := heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s with hw
  have w1 : ∀ k ∈ KU σ n, ω (k, 1) w = w := fun k hk => by
    rw [hw, GlobalTheory.LFun.map_heckeVec hK' hh' (ρ' := ω.comp (MonoidHom.inr _ _)) (ω (k, 1)) (fun g y => by
      show (ω (k, 1) * ω (1, g)) y = (ω (1, g) * ω (k, 1)) y
      rw [← map_mul, ← map_mul]
      simp), f1 k hk]
  have w2 : ∀ k ∈ KU σ n', ω (1, k) w = w := fun k hk => by
    have hs : s ∈ GlobalTheory.PRep.fixed (ω.comp (MonoidHom.inr _ _)) (KU σ n') := GlobalTheory.LGrp.mem_fixed.2 f2
    let e : GU σ n' ⧸ KU σ n' ≃ GU σ n' ⧸ KU σ n' := MulAction.toPerm k
    conv_rhs => rw [hw, GlobalTheory.LFun.heckeVec_eq_of_section hh'.1 hs (fun c => k * (e.symm c).out) (fun c => by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      exact e.apply_symm_apply c), ← finsum_comp_equiv e]
    rw [hw]
    refine ((ω (1, k)).toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK' hh' _ s)).trans (finsum_congr fun c => ?_)
    have := hh'.1 ⟨k, hk⟩ 1 c.out
    simp only [OneMemClass.coe_one, mul_one] at this
    simp only [Equiv.symm_apply_apply, this, map_mul, LinearMap.toAddMonoidHom_coe, map_smul]
    rfl
  obtain ⟨h, hh, e⟩ := GlobalTheory.T.exists_hecke_translate_of_mem_span_fixed_translates _ (KU σ n) hK M (ω.comp (MonoidHom.inl _ _)) s w f1 w1
    (hw2 w fun g hg => w2 g (mem_KU_iff.2 hg))
  exact ⟨h, hh, e⟩

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlaceReductions_conj_of_nestedFrameStabilisers : ∀ (D : D7) (V : HSp D) (β₁ β₂ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), Formalism.IndefR.Lev.IsBaseFrame V β₁ Λ N → ∀ (e : Formalism.L2.Theta.AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → (∀ κ ∈ GfC V, Formalism.IndefR.Lev.finE V κ ∈ Formalism.L2.DIV.St β₁ → Formalism.IndefR.Lev.finE V κ ∈ Formalism.L2.DIV.St β₂) → ∃ m : GL (Fin V.rank) (Formalism.L2.DIV.kP PP), ∀ y, y ∈ Formalism.L2.DIV.St β₁ → y ∈ Formalism.L2.DIV.St β₂ → Formalism.L2.DIV.redFn β₂ PP y = m * Formalism.L2.DIV.redFn β₁ PP y * m⁻¹ := by
  first | exact @GlobalTheory.NestedStab.redFn_conj_of_stab_le | exact GlobalTheory.NestedStab.redFn_conj_of_stab_le | (intros; apply GlobalTheory.NestedStab.redFn_conj_of_stab_le <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.OrthIsom

open scoped TensorProduct

theorem mul_inv_mem_UJ {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J : Matrix (Fin n) (Fin n) R)
    (β β' : GL (Fin n) R) (h : Formalism.UG.cT σ β'.1 * J * β'.1 = Formalism.UG.cT σ β.1 * J * β.1) :
    β' * β⁻¹ ∈ Formalism.UG.UJ σ J := by
  change Formalism.UG.cT σ (β' * β⁻¹).1 * J * (β' * β⁻¹).1 = J
  calc Formalism.UG.cT σ (β' * β⁻¹).1 * J * (β' * β⁻¹).1
      = Formalism.UG.cT σ (β⁻¹).1 * (Formalism.UG.cT σ β'.1 * J * β'.1) * (β⁻¹).1 := by
        rw [Units.val_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ (β.1 * (β⁻¹).1) * J * (β.1 * (β⁻¹).1) := by
        rw [h, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_iff_of_frames {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β β' : GL (Fin n) R)
    (H H' : Set (Fin n → R)) (h : ∀ y, y ∈ H ↔ ∀ i, ((β⁻¹).val *ᵥ y) i ∈ S)
    (h' : ∀ y, y ∈ H' ↔ ∀ i, ((β'⁻¹).val *ᵥ y) i ∈ S) (y : Fin n → R) :
    y ∈ H ↔ (β' * β⁻¹).val *ᵥ y ∈ H' := by
  rw [h, h', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} (R : Type) [CommRing R] [Algebra F R]

theorem swap_symm_mem_HR (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (E ⊗[F] R)) (hg : g ∈ Formalism.UG.UPts σ J R) :
    Formalism.UG.bc (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom g ∈ HR R σ J := by
  have h := Formalism.UG.Final.BCMem _ _ (Fin n) (Formalism.UG.sigR σ R) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ)
    (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom
    (RingHom.ext fun x => ?_) (J.map (Formalism.UG.inclE R)) g hg
  · exact h
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a x => rfl

theorem swap_mulVec (g : GL (Fin n) (E ⊗[F] R)) (z : Fin n → R ⊗[F] E) :
    (fun i => Algebra.TensorProduct.comm F R E
      (((Formalism.UG.bc (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom g).val *ᵥ z) i)) =
      g.val *ᵥ fun i => Algebra.TensorProduct.comm F R E (z i) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact (Algebra.TensorProduct.comm F R E).apply_symm_apply (g.val i j)

end Alg

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_latHat_iff_swap (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → Af F ⊗[F] E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (Af F) E (z i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  refine ⟨GlobalTheory.PrincInLevel.swap_mem_hatL Λ z, fun h => ?_⟩
  have h1 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h
  simp only [AlgEquiv.symm_apply_apply] at h1
  exact h1

theorem exists_of_swap (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (g : GL (Fin n) (E ⊗[F] Af F)) (hg : g ∈ Formalism.UG.UPts σ J (Af F))
    (h : ∀ y, y ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ g.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ') :
    ∃ b ∈ HR (Af F) σ J, ∀ w : Fin n → Af F ⊗[F] E,
      w ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) ↔ b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ' : Set (Fin n → E)) := by
  refine ⟨_, swap_symm_mem_HR (Af F) σ J g hg, fun w => ?_⟩
  rw [mem_latHat_iff_swap, mem_latHat_iff_swap, swap_mulVec]
  exact h _

end Swap

theorem exists_unitary_latHat : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)),
    IsSelfDualC A L → IsSelfDualC A L' →
    ∃ b ∈ HR (Af D.host.F) D.sp.cm.sig A.gram, ∀ w : Fin A.rank → TensorProduct D.host.F (Af D.host.F) D.host.E,
      w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L : Set (Fin A.rank → D.host.E)) ↔
        b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L' : Set (Fin A.rank → D.host.E)) := by
  intro D A L L' hL hL'
  obtain ⟨β, e, hβ⟩ := GlobalTheory.AdIsom.exists_orth hL
  obtain ⟨β', e', hβ'⟩ := GlobalTheory.AdIsom.exists_orth hL'
  refine exists_of_swap D.sp.cm.sig A.gram L L' (β' * β⁻¹) (mul_inv_mem_UJ _ _ β β' (hβ'.trans hβ.symm)) ?_
  rw [e, e']
  exact mem_iff_of_frames (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) β β' _ _ (GlobalTheory.AdIsom.mem_hat_lat β) (GlobalTheory.AdIsom.mem_hat_lat β')

end GlobalTheory.Core.Rk.OrthIsom
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.theta_functions_dense_continuous_theta_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ u, ‖q u - g u‖ ≤ ε := by
  first | exact @GlobalTheory.HeisSmoothing.exists_theta_near | exact GlobalTheory.HeisSmoothing.exists_theta_near | (intros; apply GlobalTheory.HeisSmoothing.exists_theta_near <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_all_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ q : WO S T → ℂ, Continuous q → (∀ γ w, q (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * q w) → (∀ f, IsThetaFunO ψ S T f → ∫ w in 𝓕, q w * star (f w) ∂μ = 0) → q = 0 := by
  first | exact @GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta | exact GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta | (intros; apply GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta <;> assumption)
end
