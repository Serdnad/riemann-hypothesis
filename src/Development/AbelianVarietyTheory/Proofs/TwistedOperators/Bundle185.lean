module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle168
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.LowBlocks

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_congr_v {x y : L} (h : Valued.v x = Valued.v y) : Formalism.UG.ordL x = Formalism.UG.ordL y := by
  unfold Formalism.UG.ordL
  by_cases hx : Valued.v x = 0
  · have hy : Valued.v y = 0 := h ▸ hx
    rw [dite_eq_left hx, dite_eq_left hy]
  · have hy : Valued.v y ≠ 0 := h ▸ hx
    rw [dite_eq_right hx, dite_eq_right hy]
    congr 2
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_unzero, h]

theorem ordL_one_eq : Formalism.UG.ordL (1 : L) = 0 :=
  Formalism.UG.P.fIwasawa_ordL_unit 1 1 (by simp) (by simp) (by simp)

theorem ordL_of_mul_eq_one {x y : L} (h : x * y = 1) : Formalism.UG.ordL y = - Formalism.UG.ordL x := by
  have hx : x ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hy : y ≠ 0 := right_ne_zero_of_mul_eq_one h
  have := Formalism.UG.P.fIwasawa_ordL_mul x y hx hy
  rw [h, ordL_one_eq] at this
  omega

variable {σ : L →+* L} {n : ℕ}

theorem ordL_rev_diag (hv : ∀ x, Valued.v (σ x) = Valued.v x) {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    Formalism.UG.ordL (b.1.1 i.rev i.rev) = - Formalism.UG.ordL (b.1.1 i i) := by
  rw [ordL_of_mul_eq_one (Formalism.UG.P.fSatake_unit_diag hb i), ordL_congr_v (hv _)]

theorem diag_ne_zero {b : GU σ n} (hb : IsBorelU b) (i : Fin n) : b.1.1 i i ≠ 0 := fun h0 => by
  have := Formalism.UG.P.fSatake_unit_diag hb i
  rw [show (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 0 from h0, map_zero, zero_mul] at this
  exact zero_ne_one this

theorem lowBlock_tri {M : Matrix (Fin n) (Fin n) L} (hM : ∀ i j : Fin n, j < i → M i j = 0) :
    (lowBlock M).BlockTriangular id := fun i j hij => by
  apply hM
  rw [Fin.lt_def] at hij ⊢
  simp only [hi, id] at *
  omega

theorem hi_eq_rev_lo (r : Fin (n / 2)) : hi n r = (lo n r.rev).rev := by
  ext; simp only [hi, lo, Fin.val_rev]; omega

end GlobalTheory.SphTheta.LowBlocks


open GlobalTheory.SphTheta.LowBlocks in
theorem GlobalTheory.SphTheta.lowBlocks_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (hn : n ≤ n'), (∀ g : GU σ n, IsBorelU g → ∃ U : GL (Fin (n / 2)) L, U.1 = lowBlock g.1.1 ∧ U.1.BlockTriangular id ∧ ∀ r, ordL (U.1 r r) = -ordL (g.1.1 (lo n r.rev) (lo n r.rev))) ∧ ∀ h : GU σ n', IsBorelU h → ∃ V : GL (Fin (n / 2)) L, V.1.BlockTriangular id ∧ (∀ r : Fin (n / 2), ordL (V.1 r.rev r.rev) = ordL (h.1.1 (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩) (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩))) ∧ ∀ t : Matrix (Fin (n / 2)) (Fin (n / 2)) L, lowBlock (h⁻¹).1.1 * (Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0) = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then (V.1 * t) ⟨r.1, e⟩ c else 0 := by
  intro L _ _ ϖ σ q hU n n' hn
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  refine ⟨fun g hg => ?_, fun h hh => ?_⟩
  · have htri : (lowBlock g.1.1).BlockTriangular id := lowBlock_tri hg
    have hdet : (lowBlock g.1.1).det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]
      intro r _
      exact diag_ne_zero hg _
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, htri, fun r => ?_⟩
    show Formalism.UG.ordL (g.1.1 (hi n r) (hi n r)) = _
    rw [hi_eq_rev_lo, ordL_rev_diag hv hg]
  · have hle : n / 2 ≤ n' / 2 := Nat.div_le_div_right hn
    have hb' : IsBorelU h⁻¹ := Formalism.UG.P.fSatake_borel_inv hh
    set W := lowBlock (h⁻¹).1.1 with hW
    have hWt : W.BlockTriangular id := lowBlock_tri hb'
    set V0 : Matrix (Fin (n / 2)) (Fin (n / 2)) L := W.submatrix (Fin.castLE hle) (Fin.castLE hle) with hV0
    have htri : V0.BlockTriangular id := fun i j hij => hWt (by rw [Fin.lt_def] at hij ⊢; exact hij)
    have hdet : V0.det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]
      intro r _
      exact diag_ne_zero hb' _
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, htri, fun r => ?_, fun t => ?_⟩
    · show Formalism.UG.ordL ((h⁻¹).1.1 (hi n' (Fin.castLE hle r.rev)) (hi n' (Fin.castLE hle r.rev))) = _
      have e : hi n' (Fin.castLE hle r.rev) = (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩).rev := by
        ext; simp only [hi, lo, Fin.val_rev, Fin.coe_castLE]; omega
      rw [e]
      have a := ordL_of_mul_eq_one (Formalism.UG.P.fSatake_borel_diag_inv hh (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩).rev)
      have b := ordL_rev_diag hv hh (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩)
      change Formalism.UG.ordL (h.1.1 _ _) = - Formalism.UG.ordL ((h⁻¹).1.1 _ _) at a
      linarith
    · ext r c
      simp only [Matrix.mul_apply, Matrix.of_apply]
      split_ifs with hr
      · have hr' : (Fin.castLE hle ⟨r.1, hr⟩ : Fin (n' / 2)) = r := Fin.ext rfl
        let emb : Fin (n / 2) ↪ Fin (n' / 2) := ⟨Fin.castLE hle, Fin.castLE_injective hle⟩
        rw [← Finset.sum_subset (s₁ := Finset.univ.map emb) (Finset.subset_univ _), Finset.sum_map]
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hk : ((emb k : Fin (n' / 2)) : ℕ) < n / 2 := k.2
          rw [dite_eq_left hk]
          show W r (Fin.castLE hle k) * t ⟨k.1, hk⟩ c = W (Fin.castLE hle ⟨r.1, hr⟩) (Fin.castLE hle k) * t k c
          rw [hr']
        · intro k _ hk
          have : ¬ (k : ℕ) < n / 2 := fun e => hk (Finset.mem_map.2 ⟨⟨k.1, e⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          rw [dite_eq_right this, mul_zero]
      · refine Finset.sum_eq_zero fun k _ => ?_
        split_ifs with hk
        · rw [hWt (show k < r by rw [Fin.lt_def]; omega), zero_mul]
        · rw [mul_zero]
end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CayleyTorus

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_one_add_inv_unif {ϖ : L}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (1 + ϖ⁻¹) = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h1 : Valued.v (ϖ⁻¹) = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_inv₀, hv]; rfl
  rw [Valuation.map_add_eq_of_lt_right, h1]
  rw [h1, map_one]; exact WithZero.coe_lt_coe.2 (by decide)

theorem v_one_add_unif {ϖ : L}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (1 + ϖ) = 1 := by
  rw [Valuation.map_add_eq_of_lt_left, map_one]
  rw [hv, map_one]; exact WithZero.coe_lt_coe.2 (by decide)

theorem inv_diagonal_field {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → L) (hf : ∀ i, f i ≠ 0) :
    (Matrix.diagonal f)⁻¹ = Matrix.diagonal (fun i => (f i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i; exact inv_mul_cancel₀ (hf i)

theorem cayley_torus_inv : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → ∀ (n' : ℕ) (k : Fin (n' / 2)) (t : GU σ n'), t.1.1 = tMat ϖ n' (n' / 2) (Pi.single k 1) → (1 + (t⁻¹).1.1).det ≠ 0 ∧ (1 + (t⁻¹).1.1)⁻¹ ∈ intMat L (Fin n') (Fin n') ∧ ordL (1 + (t⁻¹).1.1).det = -1 := by
  intro L _ _ ϖ σ q hU h2 n' k t ht
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    hU.2.2.2.1
  have hϖ : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact WithZero.zero_ne_coe hv
  set d : Fin n' → L := fun i => if h : i.val < n' / 2 then ϖ ^ ((Pi.single k (1 : ℤ) : Fin (n' / 2) → ℤ) ⟨i.val, h⟩)
    else if h' : n' - n' / 2 ≤ i.val ∧ n' - 1 - i.val < n' / 2 then
      ϖ ^ (-((Pi.single k (1 : ℤ) : Fin (n' / 2) → ℤ) ⟨n' - 1 - i.val, h'.2⟩)) else 1 with hd
  have htd : t.1.1 = Matrix.diagonal d := ht
  have hdne : ∀ i, d i ≠ 0 := by
    intro i; simp only [hd]; split_ifs <;> simp [zpow_ne_zero, hϖ]
  have hinv : (t⁻¹).1.1 = Matrix.diagonal (fun i => (d i)⁻¹) := by
    rw [show (t⁻¹).1.1 = (t.1.1)⁻¹ by simp [Matrix.coe_units_inv], htd, inv_diagonal_field d hdne]
  have hone : 1 + (t⁻¹).1.1 = Matrix.diagonal (fun i => 1 + (d i)⁻¹) := by
    rw [hinv, ← Matrix.diagonal_one, Matrix.diagonal_add]
  have hk : k.val < n' := by omega
  have hval : ∀ i, Valued.v (1 + (d i)⁻¹) =
      if i = ⟨k.val, hk⟩ then ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) else 1 := by
    intro i
    by_cases hi : i.val < n' / 2
    · by_cases hik : (⟨i.val, hi⟩ : Fin (n' / 2)) = k
      · have : d i = ϖ := by simp only [hd, dif_pos hi, hik, Pi.single_eq_same, zpow_one]
        rw [this, v_one_add_inv_unif hv, if_pos (show i = ⟨k.val, hk⟩ from Fin.ext (by have e := congrArg Fin.val hik; simpa using e))]
      · have : d i = 1 := by simp only [hd, dif_pos hi, Pi.single_eq_of_ne hik, zpow_zero]
        rw [this, inv_one, one_add_one_eq_two, h2, if_neg]
        intro e; apply hik; ext; simp [e]
    · rw [if_neg (fun e => hi (by rw [e]; exact k.2))]
      by_cases h' : n' - n' / 2 ≤ i.val ∧ n' - 1 - i.val < n' / 2
      · by_cases hik : (⟨n' - 1 - i.val, h'.2⟩ : Fin (n' / 2)) = k
        · have : d i = ϖ⁻¹ := by simp only [hd, dif_neg hi, dif_pos h', hik, Pi.single_eq_same, _root_.zpow_neg, zpow_one]
          rw [this, inv_inv, v_one_add_unif hv]
        · have : d i = 1 := by simp only [hd, dif_neg hi, dif_pos h', Pi.single_eq_of_ne hik, neg_zero, zpow_zero]
          rw [this, inv_one, one_add_one_eq_two, h2]
      · have : d i = 1 := by simp only [hd, dif_neg hi, dif_neg h']
        rw [this, inv_one, one_add_one_eq_two, h2]
  have hfne : ∀ i, 1 + (d i)⁻¹ ≠ 0 := by
    intro i e
    have := hval i
    rw [e, map_zero] at this
    split_ifs at this with h
    · exact WithZero.zero_ne_coe this
    · exact zero_ne_one this
  have hdet : Valued.v (1 + (t⁻¹).1.1).det =
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [hone, Matrix.det_diagonal, map_prod]
    simp_rw [hval]
    rw [Finset.prod_ite_eq']; simp
  refine ⟨?_, ?_, ?_⟩
  · intro e; rw [e, map_zero] at hdet; exact WithZero.zero_ne_coe hdet
  · rw [hone, inv_diagonal_field _ hfne]
    intro i j
    rw [mem_intL, Matrix.diagonal_apply]
    split_ifs with hij
    · rw [map_inv₀, hval i]
      split_ifs
      · rw [← WithZero.coe_inv]; exact WithZero.coe_le_coe.2 (by decide)
      · simp
    · simp
  · have hne : Valued.v (1 + (t⁻¹).1.1).det ≠ 0 := by rw [hdet]; exact WithZero.coe_ne_zero
    have hu : WithZero.unzero hne = Multiplicative.ofAdd (1 : ℤ) :=
      WithZero.coe_inj.mp ((WithZero.coe_unzero hne).trans hdet)
    rw [ordL, dif_neg hne, hu]; rfl

end GlobalTheory.CayleyTorus
end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SatBorel

theorem heckeVec_satU_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ), ∀ h ∈ Hecke ℂ (KU σ n), ∃ (ι : Type) (_ : Fintype ι) (b : ι → GU σ n), (∀ i, IsBorelU (b i)) ∧ (∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (s : M), (∀ k ∈ KU σ n, π k s = s) → heckeVec π (KU σ n) h s = ∑ i, h (b i) • π (b i) s) ∧ ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = ∑ i, h (b i) * ∏ k : Fin (n / 2), ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((b i).1.1 (lo n k) (lo n k)) := by
  intro L _ _ _ ϖ σ q hU n h hh
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hfin := P.finite_support_cosets hK hh.2
  have hI : ∀ c : GU σ n ⧸ KU σ n, ∃ b : GU σ n, IsBorelU b ∧ (b : GU σ n ⧸ KU σ n) = c := by
    intro c
    obtain ⟨b, k, hb, hk, e⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 c.out
    refine ⟨b, hb, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' c, e]
    exact QuotientGroup.eq.2 (by simpa using hk)
  choose s hsB hs using hI
  have hhs : ∀ c, h (s c) = h c.out := by
    intro c
    have hk : (c.out)⁻¹ * s c ∈ KU σ n := QuotientGroup.eq.1 (c.out_eq'.trans (hs c).symm)
    have e : s c = 1 * c.out * ((c.out)⁻¹ * s c) := by group
    rw [e]
    exact hh.1 1 ⟨_, hk⟩ c.out
  have c1 : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (x : M),
      (∀ k ∈ KU σ n, π k x = x) →
      heckeVec π (KU σ n) h x = ∑ i : hfin.toFinset, h (s i.1) • π (s i.1) x := by
    intro M _ _ π x hx
    rw [GlobalTheory.LFun.heckeVec_eq_of_section hh.1 (GlobalTheory.LGrp.mem_fixed.2 hx) s hs,
      finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_, ← Finset.sum_coe_sort]
    intro c hc
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq, ← hhs]
    intro h0
    exact hc (by simp [h0])
  refine ⟨hfin.toFinset, inferInstance, fun i => s i.1, fun i => hsB _, c1, fun α => ?_⟩
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega)
    (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have e := congrFun (Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _
    (fun i => (α i).ne_zero) h hh φ hφ) 1
  have hfix : ∀ k ∈ KU σ n, GlobalTheory.PRep.rightReg ℂ (GU σ n) ℂ k φ = φ := by
    intro k hk
    funext g
    change φ (g * k) = φ g
    simpa [GlobalTheory.LFun.chiDeltaU_one] using hφ 1 g k GlobalTheory.LFun.isBorelU_one hk
  rw [← GlobalTheory.LFun.heckeVec_rightReg hK hh, c1 _ _ φ hfix] at e
  have hχ : ∀ i : hfin.toFinset, φ (s i.1) = ∏ k : Fin (n / 2),
      ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((s i.1).1.1 (lo n k) (lo n k)) := by
    intro i
    have := hφ (s i.1) 1 1 (hsB _) (one_mem _)
    simp only [mul_one, h1] at this
    rw [this]
    unfold chiDeltaU
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [dite_eq_left (by omega), mul_zpow, ← _root_.zpow_mul]
    have hl : lo n k = ⟨k.1, by omega⟩ := rfl
    rw [hl]
    congr 2
    ring
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h1, mul_one] at e
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hχ i]
  exact congrArg (h (s i.1) * ·) (congrArg φ (one_mul _))

end GlobalTheory.SatBorel
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ),
    w ∈ M.sm τ ↔ SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w := by
  first | exact @GlobalTheory.SmVecModel.mem_sm_iff | exact GlobalTheory.SmVecModel.mem_sm_iff | (intros; apply GlobalTheory.SmVecModel.mem_sm_iff <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv.TwoBlockDet

def lowEquiv {n r : ℕ} (hr : r ≤ n) : Fin r ≃ {a : Fin n // a.val < r} where
  toFun i := ⟨Fin.castLE hr i, i.2⟩
  invFun a := ⟨a.1.val, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_eq_mul {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) κ) (h : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g := by
  apply Units.ext
  rw [Units.val_mul, diag_block_det_val 1 h, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    upper_block_val_submatrix hr h, Matrix.twoBlockTriangular_det (g : Matrix (Fin n) (Fin n) κ) (fun a : Fin n => a.val < r)
      (fun i hi j hj => h (by simp [blk2, hi, hj]))]
  congr 1
  · rw [← Matrix.det_submatrix_equiv_self (lowEquiv hr)]
    rfl
  · rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight
      (show ∀ a : Fin n, blk2 r a = 1 ↔ ¬ a.val < r from fun a => by unfold blk2; split_ifs with h <;> simp [h]))]
    rfl

theorem blockPartitionOf_eq_twoBlock (r t : ℕ) : (blkOf r t : Fin (r + t) → ℕ) = blk2 r := by
  funext a
  unfold blkOf blk2
  split_ifs with h
  · rfl
  · have := a.2
    rw [Nat.div_eq_of_lt (by omega)]

theorem firstDiagBlock_full_rank_eq_self {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have h : g ∈ blockTri (blk2 n) := fun i j hij => by simp [blk2] at hij
  apply Units.ext
  rw [upper_block_val_submatrix hr h]
  rfl

theorem det_blocks : ∀ (κ : Type) [CommRing κ] (n r t : ℕ) (hr : r ≤ n) (g : GL (Fin n) κ), (g ∈ blockTri (blk2 r) → Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g) ∧ (n = r + t → g ∈ blockTri (blkOf r t) → dBlk (blkOf r t) 1 g = dBlk (blk2 r) 1 g) ∧ (n = r → Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) = Matrix.GeneralLinearGroup.det g) := by
  intro κ _ n r t hr g
  refine ⟨det_eq_mul hr g, fun e _ => ?_, fun e => ?_⟩
  · subst e
    rw [blockPartitionOf_eq_twoBlock]
  · subst e
    rw [firstDiagBlock_full_rank_eq_self]

end GlobalTheory.VecInv.TwoBlockDet
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameMatrix_movedHom_integral_reductions : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP : Pl D.host.E, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  first | exact @GlobalTheory.FrameRed.frMapO_actO_int_red | exact GlobalTheory.FrameRed.frMapO_actO_int_red | (intros; apply GlobalTheory.FrameRed.frMapO_actO_int_red <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem collect_factors {ι : Type} (s : Finset ι) (A B p q : ι → ℂˣ) (u v : ℂ)
    (h : (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹)) * u =
      ((∏ i ∈ s, A i : ℂˣ) : ℂ) * ((∏ i ∈ s, B i : ℂˣ) : ℂ)⁻¹ * v) :
    u = ((∏ i ∈ s, (A i * (B i)⁻¹ * (p i * (q i)⁻¹)) : ℂˣ) : ℂ) * v := by

  have hne : (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _))
  have hu : u = (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹))⁻¹ *
      (((∏ i ∈ s, A i : ℂˣ) : ℂ) * ((∏ i ∈ s, B i : ℂˣ) : ℂ)⁻¹ * v) := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hu]
  push_cast [Units.coe_prod]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv, inv_inv]
  ring

theorem omegaG_blockTri_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, G PP ∈ blockTri (blkOf r t) ∧ H PP ∈ blockTri (blkOf r t) ∧ upperLeftBlock ha (G PP) = upperLeftBlock hb (H PP)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP))) * (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))⁻¹ * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹)) : ℂˣ) : ℂ) * omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) y := by
  intro D a b r t k ha hb hak hbk Pg Q χ ξ G H hGH y

  have hlaw := GlobalTheory.T.typePlaces_localDatum_blockTriangular_law D a b r t k ha hb hak hbk Pg Q χ ξ G H y
    (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val)
    (fun PP hP => (hGH PP hP).1) (fun PP hP => (hGH PP hP).2.1) (fun PP hP => (hGH PP hP).2.2)
    (fun _ _ => rfl)
  exact collect_factors Pg
    (fun PP => ∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP)))
    (fun PP => ∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))
    (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)))
    (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP))) _ _ hlaw

end GlobalTheory.StepLaw
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_thetaLift_goodProjector_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.tw_thF → R.ex_thF → R.ex_thG := by
  first | exact @GlobalTheory.Twist.exists_thG_models | exact GlobalTheory.Twist.exists_thG_models | (intros; apply GlobalTheory.Twist.exists_thG_models <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_const_sqNorm_two_haar_fundamentalDomains : ∀ (D : D7) (V' W : HSp D) (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (μ'' : Measure (WO V' W)) (𝓕'' : Set (WO V' W)), IsCovolOne (ratL W V') μ'' 𝓕'' → ∃ c : ENNReal, ∀ g : WO V' W → ℂ, Continuous g → (∀ γ ∈ ratL W V', ∀ w, ‖g (γ + w)‖ = ‖g w‖) → ∫⁻ x in 𝓕', ‖g x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x in 𝓕'', ‖g x‖ₑ ^ 2 ∂μ'' := by
  first | exact @GlobalTheory.Twist.NormRed.sq_norm_two_haar | exact GlobalTheory.Twist.NormRed.sq_norm_two_haar | (intros; apply GlobalTheory.Twist.NormRed.sq_norm_two_haar <;> assumption)
end
