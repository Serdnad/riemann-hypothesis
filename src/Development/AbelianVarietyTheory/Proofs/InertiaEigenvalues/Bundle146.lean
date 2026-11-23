module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle124
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle102
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle118
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle126
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle129
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle131
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.charpoly_companionMatrix_etaleGenerator_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p → (companion p).charpoly.Separable := by
  first | exact @GlobalTheory.JR.LinDesc.charpoly_companion_separable | exact GlobalTheory.JR.LinDesc.charpoly_companion_separable | (intros; apply GlobalTheory.JR.LinDesc.charpoly_companion_separable <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_etaleHermitianPair_isGen_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F), (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  first | exact @GlobalTheory.JR.exists_et_isGen_companion | exact GlobalTheory.JR.exists_et_isGen_companion | (intros; apply GlobalTheory.JR.exists_et_isGen_companion <;> assumption)
end

section

open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK.XiTriv
theorem frobA : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ f ∈ invE l e (A O K), frob K l f ∈ R O K l k := GlobalTheory.T.frobenius_mem_rigidFunctions_of_mem_invertEisenstein
theorem limR : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧), (∀ n, s n ∈ R O K l k) → (∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n) → Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0) → f ∈ R O K l k := GlobalTheory.T.mem_rigidFunctionsClosedDisc_of_adic_limit
theorem growth : ∀ (C r : ℝ) (l : ℕ), 0 ≤ C → 0 ≤ r → r < 1 → 2 ≤ l → Tendsto (fun n : ℕ => C ^ n * r ^ (l ^ n)) atTop (𝓝 0) := GlobalTheory.T.tendsto_const_pow_mul_pow_pow_zero'
theorem decay : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j) → ∃ M β : ℝ, 0 ≤ β ∧ ∀ n τ i j, Z n τ i j ∈ R O K l k ∧ normR l k (Z (n + 1) τ i j - Z n τ i j) ≤ M * β ^ n * rad l k ^ (l ^ n) := GlobalTheory.T.frobenius_recursion_differences_decay_gaussNorm

theorem convB : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧) (Y : ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ n τ i j, (X : K⟦X⟧) ^ (n + 1) ∣ Y τ i j - Z n τ i j) → ∀ τ i j, Y τ i j ∈ R O K l k := by
  intro O K _ _ _ _ _ l a _ _ ι _ _ k hk B c Z Y hB h0 hs hY τ i j
  have h1 : ∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j := fun τ i j => by
    have a1 := hY 0 τ i j
    have a2 := (pow_dvd_pow (X : K⟦X⟧) (by omega : 1 ≤ 2)).trans (hY 1 τ i j)
    rw [pow_one] at a1 a2
    have := dvd_sub a1 a2
    rwa [sub_sub_sub_cancel_left] at this
  obtain ⟨M, β, hβ, hD⟩ := decay O K l a ι k hk B c Z hB h0 hs h1
  have hr0 : 0 ≤ rad l k := rad_nonneg l k
  have hr1 : rad l k < 1 := rad_lt_one l hk
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  refine limR O K l k (Y τ i j) (fun n => Z n τ i j) (fun n => (hD n τ i j).1) (fun n => hY n τ i j) ?_
  have hg := (growth β (rad l k) l hβ hr0 hr1 hl2).const_mul M
  rw [mul_zero] at hg
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hg
  · have hm := sub_mem (hD (n + 1) τ i j).1 (hD n τ i j).1
    exact (mul_nonneg (norm_nonneg _) (pow_nonneg hr0 0)).trans (le_normR hm 0)
  · rw [← mul_assoc]; exact (hD n τ i j).2
end GlobalTheory.BK.XiTriv

noncomputable section

namespace GlobalTheory.BK.XiTriv

open PowerSeries Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]

theorem frob_map_mul (M N : Matrix ι ι K⟦X⟧) :
    (M * N).map (frob K l) = M.map (frob K l) * N.map (frob K l) :=
  Matrix.map_mul (f := (frob K l).toRingHom)

theorem frob_map_one : (1 : Matrix ι ι K⟦X⟧).map (frob K l) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem dvd_mul_mul_apply {c : K⟦X⟧} (M D N : Matrix ι ι K⟦X⟧) (h : ∀ i j, c ∣ D i j) (i j : ι) :
    c ∣ (M * D * N) i j := by
  rw [Matrix.mul_apply]
  refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_right ?_ _
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun m _ => (h m k).mul_left _

namespace Seq

variable (P : PhiMod O K l e a ι)

def Ws (n : ℕ) : ZMod a → Matrix ι ι K⟦X⟧ :=
  (fun W τ => (P.mx0 τ).map C * (W (τ - 1)).map (frob K l) * P.mxInv τ)^[n] fun _ => 1

theorem Ws_zero (τ : ZMod a) : Ws P 0 τ = 1 := rfl

theorem Ws_succ (n : ℕ) (τ : ZMod a) : Ws P (n + 1) τ =
    (P.mx0 τ).map C * (Ws P n (τ - 1)).map (frob K l) * P.mxInv τ := by
  rw [Ws, Function.iterate_succ_apply']
  rfl

theorem Ws_mul (n : ℕ) (τ : ZMod a) : Ws P n τ * P.xiSeq n τ = 1 := by
  induction n generalizing τ with
  | zero => rw [Ws_zero, PhiMod.xiSeq_zero, Matrix.one_mul]
  | succ n ih =>
    have h1 := P.mxInv_mul_mx τ
    have h3 : (P.mx0 τ).map C * ((P.mxInv τ).map constantCoeff).map C = 1 := by
      rw [← Matrix.map_mul, P.matrix_mul_inv_const_eq_one τ, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [PhiMod.xiSeq_succ, Ws_succ]
    calc _ = (P.mx0 τ).map C * (Ws P n (τ - 1)).map (frob K l) * (P.mxInv τ * P.mx τ) *
          (P.xiSeq n (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C := by
          simp only [Matrix.mul_assoc]
      _ = (P.mx0 τ).map C * ((Ws P n (τ - 1) * P.xiSeq n (τ - 1)).map (frob K l)) *
          ((P.mxInv τ).map constantCoeff).map C := by
          rw [h1, frob_map_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [ih, frob_map_one, Matrix.mul_one, h3]

theorem xiMat_mul_inv (τ : ZMod a) : P.xiMat τ * (P.xiMat τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)

theorem inv_sub_dvd (n : ℕ) (τ : ZMod a) (i j : ι) :
    (X : K⟦X⟧) ^ (n + 2) ∣ ((P.xiMat τ)⁻¹ - Ws P (n + 1) τ) i j := by
  have h : (P.xiMat τ)⁻¹ - Ws P (n + 1) τ =
      Ws P (n + 1) τ * (P.xiSeq (n + 1) τ - P.xiMat τ) * (P.xiMat τ)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Ws_mul, Matrix.one_mul, Matrix.mul_assoc,
      xiMat_mul_inv, Matrix.mul_one]
  rw [h]
  refine dvd_mul_mul_apply _ _ _ (fun i j => ?_) i j
  rw [Matrix.sub_apply, ← neg_sub]
  exact (dvd_neg).2 (P.xiMat_sub_dvd (n + 1) τ i j)

end Seq

variable [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]

theorem mulVec_mem {B : Subalgebra O K⟦X⟧} {M : Matrix ι ι K⟦X⟧} (hM : ∀ i j, M i j ∈ B)
    {v : ι → K⟦X⟧} (hv : v ∈ vecs ι B) : M *ᵥ v ∈ vecs ι B := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subalgebra.sum_mem _ fun j _ => mul_mem (hM i j) (hv j)

theorem Y_mem (P : PhiMod O K l e a ι) {k : ℝ} (hk : 1 / ((e : ℝ) * l) < k) (τ : ZMod a) (i j : ι) :
    (P.mxInv τ * P.xiMat τ) i j ∈ R O K l k := by
  have hk0 : 0 < k := by
    have h1 := NeZero.pos e
    have h2 := (Fact.out : l.Prime).pos
    exact lt_trans (by positivity) hk
  refine convB O K l a ι k hk0 (fun τ => (P.mx (τ - 1)).map (frob K l))
    (fun τ => (P.mxInv τ).map constantCoeff) (fun n τ => P.mxInv τ * P.xiSeq (n + 1) τ)
    (fun τ => P.mxInv τ * P.xiMat τ) (fun τ i j => frobA O K l e k hk _ (P.mx_mem _ i j))
    (fun τ => ?_) (fun n τ => ?_) (fun n τ i j => ?_) τ i j
  · rw [PhiMod.xiSeq_succ, PhiMod.xiSeq_zero, frob_map_one, Matrix.mul_one, ← Matrix.mul_assoc,
      PhiMod.mxInv_mul_mx, Matrix.one_mul]
  · rw [PhiMod.xiSeq_succ P (n + 1), ← frob_map_mul, ← Matrix.mul_assoc (P.mx (τ - 1)),
      PhiMod.mx_mul_mxInv, Matrix.one_mul, ← Matrix.mul_assoc (P.mxInv τ), ← Matrix.mul_assoc (P.mxInv τ),
      PhiMod.mxInv_mul_mx, Matrix.one_mul]
  · have h : P.mxInv τ * P.xiMat τ - P.mxInv τ * P.xiSeq (n + 1) τ =
        P.mxInv τ * (P.xiMat τ - P.xiSeq (n + 1) τ) * 1 := by
      rw [Matrix.mul_one, Matrix.mul_sub]
    rw [← Matrix.sub_apply, h]
    exact dvd_mul_mul_apply _ _ _ (fun i j => (pow_dvd_pow _ (by omega)).trans
      (P.xiMat_sub_dvd (n + 1) τ i j)) i j

theorem Yi_mem (P : PhiMod O K l e a ι) {k : ℝ} (hk : 1 / ((e : ℝ) * l) < k) (τ : ZMod a) (i j : ι) :
    ((P.xiMat τ)⁻¹ * P.mx τ) i j ∈ R O K l k := by
  have hk0 : 0 < k := by
    have h1 := NeZero.pos e
    have h2 := (Fact.out : l.Prime).pos
    exact lt_trans (by positivity) hk
  have key := convB O K l a ι k hk0 (fun τ => ((P.mxInv (τ - 1)).map (frob K l))ᵀ)
    (fun τ => (P.mx0 τ)ᵀ) (fun n τ => (Seq.Ws P (n + 1) τ * P.mx τ)ᵀ)
    (fun τ => ((P.xiMat τ)⁻¹ * P.mx τ)ᵀ) (fun τ i j => frobA O K l e k hk _ (P.mxInv_mem _ j i))
    (fun τ => ?_) (fun n τ => ?_) (fun n τ i j => ?_) τ j i
  · simpa using key
  · show (Seq.Ws P (0 + 1) τ * P.mx τ)ᵀ = ((P.mx0 τ)ᵀ).map C
    rw [Seq.Ws_succ, Seq.Ws_zero, frob_map_one, Matrix.mul_one, Matrix.mul_assoc,
      PhiMod.mxInv_mul_mx, Matrix.mul_one, Matrix.transpose_map]
  · show (Seq.Ws P (n + 2) τ * P.mx τ)ᵀ = ((P.mxInv (τ - 1)).map (frob K l))ᵀ *
        ((Seq.Ws P (n + 1) (τ - 1) * P.mx (τ - 1))ᵀ).map (frob K l) * ((P.mx0 τ)ᵀ).map C
    rw [Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul,
      ← Matrix.transpose_mul]
    congr 1
    rw [Seq.Ws_succ P (n + 1), Matrix.mul_assoc _ (P.mxInv τ), PhiMod.mxInv_mul_mx, Matrix.mul_one,
      ← frob_map_mul,
      Matrix.mul_assoc (Seq.Ws P (n + 1) (τ - 1)), PhiMod.mx_mul_mxInv, Matrix.mul_one]
  · rw [Matrix.transpose_apply, Matrix.transpose_apply, ← Matrix.sub_apply, ← Matrix.sub_mul,
      ← Matrix.one_mul ((P.xiMat τ)⁻¹ - Seq.Ws P (n + 1) τ)]
    exact dvd_mul_mul_apply _ _ _ (fun i j => (pow_dvd_pow _ (by omega)).trans
      (Seq.inv_sub_dvd P n τ i j)) j i

end GlobalTheory.BK.XiTriv

end

open PowerSeries GlobalTheory.BK in
theorem GlobalTheory.BK.xiExt_mem_Lk_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ w : Vec K a ι, P.xiExt w ∈ P.Lk k ↔ w ∈ P.Mext (R O K l k) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P k hk w
  have hprod (τ : ZMod a) : ((P.xiMat τ)⁻¹ * P.mx τ) * (P.mxInv τ * P.xiMat τ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P.mx τ), PhiMod.mx_mul_mxInv, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ)]
  constructor
  · intro h
    refine mem_tot.2 fun τ => ?_
    have h1 := P.mem_extc_iff.1 (mem_tot.1 h τ)
    rw [PhiMod.xiExt_apply, Matrix.mulVec_mulVec] at h1
    have h2 := XiTriv.mulVec_mem (XiTriv.Yi_mem P hk τ) h1
    rwa [Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec] at h2
  · intro h
    refine mem_tot.2 fun τ => P.mem_extc_iff.2 ?_
    rw [PhiMod.xiExt_apply, Matrix.mulVec_mulVec]
    exact XiTriv.mulVec_mem (XiTriv.Y_mem P hk τ) (mem_tot.1 h τ)
end

section

noncomputable section
namespace GlobalTheory.PhiGam.Range
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem finite_map_trans {k U : Type} [Field k] [AddCommGroup U] [Module k U] {P Q S : Submodule k U}
    (hSQ : S ≤ Q) (h1 : FiniteDimensional k (P.map Q.mkQ)) (h2 : FiniteDimensional k (Q.map S.mkQ)) :
    FiniteDimensional k (P.map S.mkQ) := by
  refine Module.Finite.iff_fg.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor hSQ) ?_ ?_)
  · rw [← Submodule.map_comp, Submodule.factor_comp_mk]
    exact Module.Finite.iff_fg.mp h1
  · have hle : P.map S.mkQ ⊓ LinearMap.ker (Submodule.factor hSQ) ≤ Q.map S.mkQ := by
      rintro _ ⟨⟨p, -, rfl⟩, hp⟩
      exact ⟨p, (Submodule.Quotient.mk_eq_zero Q).mp hp, rfl⟩
    exact Module.Finite.iff_fg.mp (Submodule.finiteDimensional_of_le hle)

theorem finite_quot_of_map {k U : Type} [Field k] [AddCommGroup U] [Module k U] {P S : Submodule k U}
    (h : FiniteDimensional k (P.map S.mkQ)) : FiniteDimensional k (↥P ⧸ S.submoduleOf P) := by
  have hker : LinearMap.ker (S.mkQ ∘ₗ P.subtype) = S.submoduleOf P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  have hr : LinearMap.range (S.mkQ ∘ₗ P.subtype) = P.map S.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  haveI : FiniteDimensional k (LinearMap.range (S.mkQ ∘ₗ P.subtype)) := by rw [hr]; exact h
  rw [← hker]
  exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm

theorem gmult_self {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P : Submodule k U) (x : k) : gmult T P P x = 0 := by
  unfold gmult
  set P' := P ⊓ ⨆ m : ℕ, P.comap ((T - algebraMap k (Module.End k U) x) ^ m)
  have h : P.submoduleOf P' = ⊤ := eq_top_iff.mpr fun y _ => y.2.1
  haveI : Subsingleton (↥P' ⧸ P.submoduleOf P') := Submodule.Quotient.subsingleton_iff.mpr h
  exact Module.finrank_zero_of_subsingleton

theorem finite_sh {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
    [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    {N : Submodule k⟦X⟧ V} (hN : IsLat N) (a : ℤ) (m : ℕ) :
    FiniteDimensional k (((sh a N).restrictScalars k).map ((sh (a + m) N).restrictScalars k).mkQ) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero, Submodule.mkQ_map_self]
    infer_instance
  | succ m ih =>
    have h := Window.finite_quot (hN.shift (a + m)).1
    rw [sh_sh_eq, add_comm (1 : ℤ)] at h
    rw [Nat.cast_succ, ← add_assoc]
    exact finite_map_trans (fun y hy => Window.sh_succ_le _ _ hy) ih h

theorem qmult_sh_range : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ) (x : k), qmult g (sh a N) (sh (a + m) N) x = ∑ j ∈ Finset.range m, sen g N (x + (a + j : ℤ)) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC a m x
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero, Finset.sum_range_zero]
    exact gmult_self _ _ _
  | succ m ih =>
    have hf := finite_quot_of_map (finite_sh hN a (m + 1))
    rw [Finset.sum_range_succ, ← ih, ← GlobalTheory.T.senMultiplicity_shift_lattice_variablePow R g hg N hN hC (a + m) x, sen, sh_sh_eq,
      add_comm (1 : ℤ)]
    rw [Nat.cast_succ, ← add_assoc] at hf ⊢
    exact GlobalTheory.T.genEigenMultiplicityQuotient_additive_chain (nab g) _ _ _ (fun y hy => Window.sh_succ_le _ _ hy)
      (fun y hy => Window.sh_add_le a m N hy) (fun y hy => Window.nab_mem_sh R hg hC _ hy)
      (fun y hy => Window.nab_mem_sh R hg hC _ hy) (fun y hy => Window.nab_mem_sh R hg hC _ hy) hf x

end GlobalTheory.PhiGam.Range
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hermitianBlock_hasInvariants_of_lift_match : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E), ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) → HasInv X (inv Z) := by
  first | exact @GlobalTheory.JR.Step.hasInv_of_lift | exact GlobalTheory.JR.Step.hasInv_of_lift | (intros; apply GlobalTheory.JR.Step.hasInv_of_lift <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hermitianBlock_hasInvariants_of_liftWithLastBasis : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E), ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 → HasInv X (inv Z) → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) := by
  first | exact @GlobalTheory.JR.Step.MatchNotIm.hasInv_liftH | exact GlobalTheory.JR.Step.MatchNotIm.hasInv_liftH | (intros; apply GlobalTheory.JR.Step.MatchNotIm.hasInv_liftH <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem intMap_isIntegral_of_unr : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧
      @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := by
  intro K K' d φ hU
  obtain ⟨φO, hφO⟩ := exists_intMap_of_unr hU
  refine ⟨φO, hφO, ?_⟩
  letI : Algebra K.O K'.O := φO.toAlgebra
  obtain ⟨u, hu⟩ := exists_int_basis_of_unr K K' d φ hU
  have hspan : Submodule.span K.O (Set.range u) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨a, ha⟩ := hu y
    have hy : y = ∑ i, a i • u i := by
      apply IsFractionRing.injective K'.O K'.E

      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      change φ (algebraMap K.O K.E (a i)) * _ = algebraMap K'.O K'.E (φO (a i)) * _
      rw [hφO]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Module.Finite K.O K'.O := ⟨Submodule.fg_def.2 ⟨_, Set.finite_range u, hspan⟩⟩
  exact Algebra.IsIntegral.of_finite K.O K'.O

end GlobalTheory.UnitLemma.Unr
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O, algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr | exact GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr | (intros; apply GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.stableLatticePair_projection_smul_units : ∀ (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (M : stLat O E ((g₁, g₂) : A₁ × A₂)), latProj O E g₁ g₂ (t • M) = t • latProj O E g₁ g₂ M := by
  first | exact @GlobalTheory.UnitLemma.latProj_smul | exact GlobalTheory.UnitLemma.latProj_smul | (intros; apply GlobalTheory.UnitLemma.latProj_smul <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A) (L : stLat O E g), MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  first | exact @GlobalTheory.UnitLemma.stabilizer_le_intUnits | exact GlobalTheory.UnitLemma.stabilizer_le_intUnits | (intros; apply GlobalTheory.UnitLemma.stabilizer_le_intUnits <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂), MulAction.stabilizer A₁ˣ y.1 ≤ intUnits O A₁ → MulAction.stabilizer A₂ˣ y.2 ≤ intUnits O A₂ → MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧ (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) = (MulAction.stabilizer A₁ˣ y.1).relIndex (intUnits O A₁) * (MulAction.stabilizer A₂ˣ y.2).relIndex (intUnits O A₂) := by
  first | exact @GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex | exact GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex | (intros; apply GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A), countGL O E g = ∑ᶠ o : MulAction.orbitRel.Quotient Aˣ (stLat O E g), ((MulAction.stabilizer Aˣ (Quotient.out o)).relIndex (intUnits O A) : ℚ) := by
  first | exact @GlobalTheory.UnitLemma.countGL_eq_sum_orbits | exact GlobalTheory.UnitLemma.countGL_eq_sum_orbits | (intros; apply GlobalTheory.UnitLemma.countGL_eq_sum_orbits <;> assumption)
end
