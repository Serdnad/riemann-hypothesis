module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per



private theorem mem_FilD_zero (l : ℕ) [Fact l.Prime] (x : Per.BdR l) :
    x ∈ Per.FilD l 0 ↔ ∃ y : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) y = x :=
  ⟨fun h => let ⟨z, _, e⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l (n := 0) h; ⟨z, e⟩,
    fun ⟨y, e⟩ => e ▸ GlobalTheory.RingIface.alg_mem_FilD_zero l y⟩

theorem _root_.UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective :
    ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (K : FinExt l), (∀ x : Pl.R.BdR, x ∈ (Pl.PD K).Fil 0 ↔ ∃ y : Per.BdRp l, x = GlobalTheory.BKGal.JumpDR.cD Td y) ∧ Function.Injective (GlobalTheory.BKGal.JumpDR.cD Td) := by
  intro l _ Pl AI Td K
  refine ⟨fun x => ?_, fun y z h => ?_⟩
  · rw [Td.fil, mem_FilD_zero]
    refine exists_congr fun y => ?_
    change _ ↔ x = Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y)
    rw [RingEquiv.eq_symm_apply, eq_comm]
  · exact (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1 (Td.eD.symm.injective h)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per



theorem _root_.UpperTheory.KN.crisComparison_ainf_eq_deRhamComparison :
    ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (w : Ainf l), GlobalTheory.BKGal.JumpDR.cB Td (acrisToBcris l (ainfToAcris l w)) = GlobalTheory.BKGal.JumpDR.cD Td (ainfToBdRp l w) := by
  intro l _ Pl AI Td w
  refine Td.eD.injective ?_
  have h := GlobalTheory.CrisIncl.incl_aB l _ Td.incl w
  refine Eq.trans h ?_
  exact (Td.eD.apply_symm_apply _).symm
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private theorem hat_mulVec' {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
    {ι : Type} [Fintype ι] {Y : Matrix ι ι K⟦X⟧} (hY : ∀ i j, Y i j ∈ RpiE O K l e) {m : ι → K⟦X⟧}
    (hm : ∀ j, m j ∈ RpiE O K l e) (i : ι) :
    hat O l e ((Y *ᵥ m) i) = ∑ j, hat O l e (Y i j) * hat O l e (m j) := by
  have : (Y *ᵥ m) i = ((∑ j, ⟨Y i j, hY i j⟩ * ⟨m j, hm j⟩ : RpiE O K l e) : K⟦X⟧) := by
    simp [Matrix.mulVec, dotProduct]

  rw [this, hat_coe, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hat_of_mem l e (hY i j), hat_of_mem l e (hm j)]

theorem _root_.UpperTheory.KN.phiMod_coefficients_eq_sum_of_inverse_matrix :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat O K l e),
    (∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) →
    ∀ j, (fun τ => c τ j) = ∑ k, s k * fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P n s m c h j
  funext τ
  apply algebraMap_AhatE_injective l e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h τ j, Finset.sum_apply, map_sum]
  simp only [GlobalTheory.BKGal.JumpDR.hsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc (i : ι) : (coordL P (invL l (S O K e)) (m k) i τ : K⟦X⟧) ∈ Rpi O K l e :=
    invL_S_le_Rpi l e (coordL P (invL l (S O K e)) (m k) i τ).2
  have hm (i : ι) : (m k).1 τ i ∈ RpiE O K l e := by
    have := congrFun (mx_mulVec_coordL P (invL l (S O K e)) (m k) τ) i
    rw [← this]
    exact Subalgebra.sum_mem _ fun i' _ =>
      mul_mem (invE_A_le_RpiE l e (P.mx_mem τ i i')) (le_away _ _ (hc i'))
  have h1 : (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧) = (P.mxInv τ *ᵥ (m k).1 τ) j := rfl
  rw [Pi.mul_apply, map_mul, GlobalTheory.GalStep.hatR_of_mem (hc j), ← hat_coe_Rpi]
  change _ = _ * hat O l e (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧)
  rw [h1, hat_mulVec' (fun i i' => invE_A_le_RpiE l e (P.mxInv_mem τ i i')) hm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm]
  rfl
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal



theorem _root_.UpperTheory.KN.phiMod_deRham_image_coord_expansion :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (hx : ∀ τ i j, E K l e ^ α * P.mx τ i j ∈ A O K) (σ : P.MMl),
    GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • σ.1) = ∑ j, ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) σ j τ : K⟦X⟧)) •
      fun i => toOD l O (ϖ.iTot t K (fun τ => ⟨E K l e ^ α * P.mx τ i j, hx τ i j⟩)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α hx σ
  funext i
  simp only [GlobalTheory.GalStep.YD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [← PiSys.iD_ofA, ← map_mul]

  rw [← map_sum]
  congr 1
  funext τ
  have hw' : ∀ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) ∈ Rpi O K l e := fun k =>
    invL_S_le_Rpi l e (coordL P (invL l (S O K e)) σ k τ).2
  have hb' : ∀ k, E K l e ^ α * P.mx τ i k ∈ Rpi O K l e := fun k => A_le_Rpi l e (hx τ i k)
  have hs : E K l e ^ α * σ.1 τ i =
      ∑ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) * (E K l e ^ α * P.mx τ i k) := by
    rw [← mx_mulVec_coordL P (invL l (S O K e)) σ τ]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hm : (∑ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) * (E K l e ^ α * P.mx τ i k)) ∈ Rpi O K l e :=
    Subalgebra.sum_mem _ fun k _ => mul_mem (hw' k) (hb' k)
  have hA : ∀ k, ofA O K l e ⟨E K l e ^ α * P.mx τ i k, hx τ i k⟩ = toHat O K l e ⟨_, hb' k⟩ := fun k =>
    (toHat_eq_ofAl l e rfl).symm
  rw [hs, GlobalTheory.GalStep.hatR_of_mem (O := O) hm, Finset.sum_apply]
  simp only [Pi.mul_apply, GlobalTheory.GalStep.hatR_of_mem (O := O) (hw' _), hA, ← map_mul]

  rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl
end
