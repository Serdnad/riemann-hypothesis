module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle035
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle007
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle022
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle006
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RankOneTensors
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MonoidAlgebra MeasureTheory

namespace Formalism.L2.SG.Pf.AllRowsEtAlg

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA
  Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsES Formalism.L2.SG.Pf.unitaryCongruence

variable {D : D7} {X : HidaSetting D} (hS : Function.Surjective (rhoX X))
include hS

def Ehat : MonoidAlgebra ℂ (G0g D.nd) := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (hat hS X.B.e))

theorem Ehat_coeff (γ : G0g D.nd) : (Ehat hS).coeff γ = hat hS X.B.e γ := by
  simp [Ehat, MonoidAlgebra.coeff_ofCoeff]

theorem Ehat_idem : Ehat hS * Ehat hS = Ehat hS := by
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin]
  simp only [Ehat_coeff hS]
  exact hat_e_idem hS γ

theorem hat_inv {f : X.B.I.Gf → ℂ} (hf : BiInv X f) (hsa : ∀ x, f x⁻¹ = star (f x)) (γ : G0g D.nd) :
    hat hS f γ⁻¹ = star (hat hS f γ) := by
  have h1 : f ((sec hS γ⁻¹ : KSub X.B.I) : X.B.I.Gf) = f (((sec hS γ)⁻¹ : KSub X.B.I) : X.B.I.Gf) := by
    rw [val_hat hS hf, val_hat hS hf, rho_sec, map_inv, rho_sec]
  have hcoe : (((sec hS γ)⁻¹ : KSub X.B.I) : X.B.I.Gf) = ((sec hS γ : KSub X.B.I) : X.B.I.Gf)⁻¹ := rfl
  unfold hat
  rw [h1, hcoe, hsa, star_mul', Complex.star_def, Complex.conj_ofReal]

theorem Ehat_selfadj : conjA (Ehat hS) = Ehat hS := by
  apply MonoidAlgebra.ext
  ext γ
  rw [conjA_coeff, Ehat_coeff hS, Ehat_coeff hS, hat_inv hS (biInv_e X) X.B.e_adm.2.2.1 γ, star_star]

theorem hat_eT' (S : Set (Tup2 D)) (γ : G0g D.nd) : hat hS (eT X S) γ = (Ehat hS * ES S).coeff γ := by
  rw [hat_eT hS S γ, coeff_mul_fin]
  simp only [Ehat_coeff hS]

theorem prod_idem (S : Set (Tup2 D)) : (Ehat hS * ES S) * (Ehat hS * ES S) = Ehat hS * ES S := by
  rw [mul_assoc, ES_central S (Ehat hS * ES S), mul_assoc, ← mul_assoc (Ehat hS) (Ehat hS), Ehat_idem hS,
    ES_idem]

theorem prod_selfadj (S : Set (Tup2 D)) : conjA (Ehat hS * ES S) = Ehat hS * ES S := by
  rw [conjA_mul, ES_selfadj, Ehat_selfadj hS, ES_central]

theorem eT_idem (S : Set (Tup2 D)) : X.B.I.convF X.B.μf (eT X S) (eT X S) = eT X S := by
  apply hat_inj hS (biInv_conv hS (biInv_eT X S) (biInv_eT X S)) (biInv_eT X S)
  intro γ
  rw [conv_hat hS (biInv_eT X S) (biInv_eT X S) γ]
  simp only [hat_eT' hS S]
  rw [← coeff_mul_fin, prod_idem hS S]

theorem eT_inv (S : Set (Tup2 D)) (x : X.B.I.Gf) : eT X S x⁻¹ = star (eT X S x) := by
  by_cases hx : x ∈ X.B.I.Kset
  · have key : eT X S x = hat hS (eT X S) (rhoX X ⟨x, hx⟩) / (V X : ℂ) := val_hat hS (biInv_eT X S) ⟨x, hx⟩
    have k1 : eT X S x⁻¹ = hat hS (eT X S) (rhoX X ⟨x, hx⟩)⁻¹ / (V X : ℂ) := by
      have := val_hat hS (biInv_eT X S) (⟨x, hx⟩ : KSub X.B.I)⁻¹
      rwa [map_inv] at this
    have hc : ∀ γ, (Ehat hS * ES S).coeff γ⁻¹ = star ((Ehat hS * ES S).coeff γ) := by
      intro γ
      conv_lhs => rw [← prod_selfadj hS S]
      rw [conjA_coeff, inv_inv]
    rw [k1, key, hat_eT' hS S, hat_eT' hS S, hc, star_div₀, Complex.star_def, Complex.conj_ofReal]
  · have hx' : x⁻¹ ∉ X.B.I.Kset := fun h => hx (by simpa using K_inv X.B.I h)
    rw [eT_of_not_mem X S hx, eT_of_not_mem X S hx', star_zero]

section Pos

open scoped ComplexOrder


omit hS in
theorem posType_of (I : AutInst) (μ : Measure I.Gf) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {f : I.Gf → ℂ} (hc : Continuous f) {C : Set I.Gf} (hC : IsCompact C) (hCo : IsOpen C)
    (hsupp : ∀ x, f x ≠ 0 → x ∈ C) (hconv : I.convF μ f f = f) (hsa : ∀ x, f x⁻¹ = star (f x)) :
    I.IsPosType f := by
  intro m x c
  have hsub : ∀ i j, f ((x i)⁻¹ * x j) = ∫ z, star (f (z⁻¹ * x i)) * f (z⁻¹ * x j) ∂μ := by
    intro i j
    conv_lhs => rw [← hconv]
    have := integral_mul_left_eq_self (μ := μ) (fun y => f y * f (y⁻¹ * ((x i)⁻¹ * x j))) (x i)⁻¹
    show ∫ y, f y * f (y⁻¹ * ((x i)⁻¹ * x j)) ∂μ = _
    rw [← this]
    congr 1
    funext z
    rw [← hsa (z⁻¹ * x i)]
    congr 1 <;> congr 1 <;> group
  have hint : ∀ i j, Integrable (fun z => star (f (z⁻¹ * x i)) * f (z⁻¹ * x j)) μ := by
    intro i j
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hc.comp (continuous_inv.mul continuous_const)).star).mul
        (hc.comp (continuous_inv.mul continuous_const))
    · refine HasCompactSupport.intro
        (IsCompact.image (f := fun y : I.Gf => x j * y⁻¹) hC (continuous_const.mul continuous_inv)) ?_
      intro z hz
      have h0 : f (z⁻¹ * x j) = 0 := by
        by_contra h
        apply hz
        exact ⟨z⁻¹ * x j, hsupp _ h, by group⟩
      rw [h0, mul_zero]
  have hF : ∀ z, ((Complex.normSq (∑ j, c j * f (z⁻¹ * x j)) : ℝ) : ℂ) =
      ∑ i, ∑ j, star (c i) * c j * (star (f (z⁻¹ * x i)) * f (z⁻¹ * x j)) := by
    intro z
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
    ring
  have key : ∫ z, ((Complex.normSq (∑ j, c j * f (z⁻¹ * x j)) : ℝ) : ℂ) ∂μ =
      ∑ i, ∑ j, star (c i) * c j * f ((x i)⁻¹ * x j) := by
    simp_rw [hF]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hint i j).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hsub]
  rw [← key, integral_complex_ofReal]
  exact Complex.zero_le_real.2 (integral_nonneg fun z => Complex.normSq_nonneg _)

end Pos

theorem eT_pos (S : Set (Tup2 D)) : X.B.I.IsPosType (eT X S) := by
  exact posType_of X.B.I X.B.μf (isLocallyConstant_eT X S).continuous (PI.WAU.Cpt.isCompact_Kset X.B.I)
    (PI.WAU.kset_open X.B.I) (fun x hx => by_contra fun h => hx (eT_of_not_mem X S h)) (eT_idem hS S)
    (eT_inv hS S)

theorem etAlg_of (S : Set (Tup2 D)) : EtAlg X S :=
  ⟨eT_idem hS S, eT_inv hS S, eT_pos hS S⟩

end Formalism.L2.SG.Pf.AllRowsEtAlg
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

theorem gv_eq : GX X u u' D.host.rdE (gamW X u u' w) v =
    Gv (Tw u) (Tw u') (Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v)) := rfl

theorem sub_one_mulVec (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (x : Fin X.B.I.n → ℂ) :
    (M - 1) *ᵥ x = M *ᵥ x - x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

theorem frame_diff {m : ℕ} {N : ℕ} (V : Fin (m + 1) → Fin N → ℂ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (a' : Fin (m + 1)) : ∑ a'', A a'' a' • V a'' - V a' = ∑ a'', (A - 1) a'' a' • V a'' := by
  simp [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.one_apply]

section Main

variable (hw : OkPt X u u' w)

include hw in
theorem hgap_w : 1 - ((Tw u : ℝ) : ℂ) * (Tw u' : ℝ) *
    ((Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v))⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) *
      starRingEnd ℂ ((Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v))⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS))) ≠ 0 := by
  set Z := Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) with hZd
  have hG : 0 < Gv (Tw u) (Tw u') Z := by
    rw [← gv_eq X u u' w v]
    exact hw.2 v
  have hdet : IsUnit Z.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hD : Dl Z (D.R.rS + 1) = Z.det := by
      unfold Formalism.L2.SG.RealObj.Dl
      rw [dite_eq_left le_rfl]
      congr 1
    have hnn : (0 : ℝ) ≤ (Tw u : ℝ) * (Tw u' : ℝ) * ‖Dl Z D.R.rS‖ ^ 2 :=
      mul_nonneg (mul_nonneg (Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u).le
        (Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u').le) (sq_nonneg _)
    unfold Gv at hG
    rw [hD, h0, norm_zero, zero_pow two_ne_zero, zero_sub] at hG
    linarith
  exact gap_of_G Z hdet _ _ hG

include hw in
theorem yM_unit (c : FreeE w → ℂ) :
    (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
      Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) = Formalism.REAL.Jm (X.B.I.ε v) :=
  by
  have hC : IsUB (blkW w) (Cw w c) := by
      refine ⟨fun i => by simp [Cw], fun i j h => ?_⟩
      simp only [Cw, Matrix.of_apply] at h
      split_ifs at h with h1 h2
      · exact ⟨le_of_eq h1, by rw [h1]⟩
      · exact ⟨le_of_lt h2.1, h2.2⟩
      · exact absurd rfl h
  exact Yc_unitary (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Tw u : ℝ) (Tw u' : ℝ) (piW w) (blkW w) (fun a b => gram_frm (X := X) v u D.host.rdE a b)
    (fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
    (fun a => piW_invol (w := w) a)
    (fun a => piW_blk (w := w) a) (fun a b h hab => piW_anti (w := w) a b h hab)
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (hgap_w X u u' w v hw) hC

include hw in
theorem yM_F (c : FreeE w → ℂ) (a : Fin (D.R.rS + 1)) :
    Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Fw X u v a =
      ∑ a', Am (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) a' a • Fw X u v a' :=
  Yc_F (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Tw u : ℝ) (Tw u' : ℝ) (piW w) (fun a b => gram_frm (X := X) v u D.host.rdE a b)
    (fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
    (fun a => piW_invol (w := w) a)
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (hgap_w X u u' w v hw) a

include hw in
theorem yM_G (c : FreeE w → ℂ) (b : Fin (D.R.rS + 1)) :
    Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Gw X u u' w v b =
      ∑ b', Cw w c b' b • Gw X u u' w v b' :=
  Yc_G (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Tw u : ℝ) (Tw u' : ℝ) (piW w) (fun a b => gram_frm (X := X) v u D.host.rdE a b)
    (fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
    (fun a => piW_invol (w := w) a)
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (hgap_w X u u' w v hw) b

include hw in
theorem yM_isUB_A (c : FreeE w → ℂ) : IsUB (blkW w) (Am (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c)) := by
  unfold Am
  exact isUB_A (piW w) (fun a => piW_invol (w := w) a) (fun a => piW_blk (w := w) a)
    (fun a b h hab => piW_anti (w := w) a b h hab) (Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v))
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (isUB_Cw w c)

theorem lt_last_set : {a : Fin (D.R.rS + 1) | a ≠ Fin.last D.R.rS} = {a | a.1 < D.R.rS} := by
  ext a
  simp only [Set.mem_setOf_eq]
  rw [← Fin.lt_last_iff_ne_last]
  exact Iff.rfl

theorem e_eq (b : Fin D.R.rS) : rv X.B.I v (X.eR b) =
    ((D.host.rdE : ℂ) ^ (D.R.rS - b.1)) • frm X u D.host.rdE v b.castSucc := by
  have hr : (D.host.rdE : ℂ) ≠ 0 := by exact_mod_cast (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D).ne'
  simp only [frm, famSc, fam, Fin.coe_castSucc, Fin.snoc_castSucc, smul_smul]
  rw [mul_inv_cancel₀ (pow_ne_zero _ hr), one_smul]

include hw in
theorem inN_u (c : FreeE w → ℂ) :
    InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))
      (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c)) := by
  have hr : (D.host.rdE : ℂ) ≠ 0 := by exact_mod_cast (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D).ne'
  have hF : ∀ b : Fin D.R.rS, Fw X u v b.castSucc =
      ((D.host.rdE : ℂ) ^ (D.R.rS - b.1))⁻¹ • rv X.B.I v (X.eR b) := by
    intro b
    show frm X u D.host.rdE v b.castSucc = _
    rw [e_eq X u v b, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hr), one_smul]
  have hspan : ∀ k, k ≤ D.R.rS → Submodule.span ℂ (Fw X u v '' {a | a.1 < k}) ≤
      spanLt (fun a => rv X.B.I v (X.eR a)) k := by
    intro k hk
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a.1 < k := ha
    obtain ⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc := ⟨⟨a.1, by omega⟩, Fin.ext rfl⟩
    rw [hF b]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ha', rfl⟩)
  have hA := yM_isUB_A X u u' w v hw c
  have hcol : ∀ a' : Fin (D.R.rS + 1),
      Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Fw X u v a' - Fw X u v a' ∈
        spanLt (fun a => rv X.B.I v (X.eR a)) a'.1 := by
    intro a'
    rw [yM_F X u u' w v hw c a', frame_diff]
    exact hspan a'.1 (Nat.lt_succ_iff.mp a'.2) (comb_mem X u v hA a')
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · show (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) - 1) *ᵥ rv X.B.I v (X.eR a) ∈ _
    have he : rv X.B.I v (X.eR a) = ((D.host.rdE : ℂ) ^ (D.R.rS - a.1)) • Fw X u v a.castSucc := by
      rw [hF a, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hr), one_smul]
    rw [sub_one_mulVec X, he, Matrix.mulVec_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ (hcol a.castSucc)
  · have hz : Fw X u v (Fin.last D.R.rS) = rv X.B.I v (X.zR u) := by
      simp [Fw, frm, famSc, fam]
    rw [sub_one_mulVec X, ← hz]
    exact hcol (Fin.last D.R.rS)
  · have hx : ∀ a, a ≠ Fin.last D.R.rS → hJ (X.B.I.ε v) (Fw X u v a) y = 0 := by
      intro a ha
      obtain ⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc :=
        ⟨⟨a.1, Fin.val_lt_last ha⟩, Fin.ext rfl⟩
      rw [hF b, hJs_l, hy b, mul_zero]
    have hp := Yc_perpF (ε := X.B.I.ε v) (F := Fw X u v) (G := Gw X u u' w v) (T := (Tw u : ℝ))
      (T' := (Tw u' : ℝ)) (π := piW w) (blk := blkW w)
      (hFF := fun a b => gram_frm (X := X) v u D.host.rdE a b)
      (hGG := fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
      (hπ := fun a => piW_invol (w := w) a) (hblk := fun a => piW_blk (w := w) a)
      (hanti := fun a b h hab => piW_anti (w := w) a b h hab)
      (hZ := fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b)
      (hgap := hgap_w X u u' w v hw) (hC := isUB_Cw w c) y hx
    rw [lt_last_set] at hp
    rw [sub_one_mulVec X]
    exact hspan D.R.rS le_rfl hp

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.OOCoreHilbertSchmidt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsNormSq_eq_hilbertSchmidt_sq {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) :
    Formalism.MainNotions.S.hsNormSq A = Formalism.L2.SG.RealObj.hs2 A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
    | exact inner_self_eq_norm_sq _
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
    | (rw [inner_self_eq_norm_sq_to_K]; simp [sq])

variable {D : D7} {X : HidaSetting D} (u u' : D.what₂.Word)

theorem hsNormSq_OOP_quot (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl) (w : Point D.host.E (D.R.rS + 1))
    (hw : ∃ γ, IsPtRep X u u' w γ) (hG : ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) :
    Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν w) =
      ∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) := by
  obtain ⟨hon, hsp⟩ := Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by simp [B]
  have hF := hQ w hw hG
  rw [hsNormSq_eq_hilbertSchmidt_sq]
  simp only [hsNormSq_eq_hilbertSchmidt_sq]
  unfold Formalism.L2.SG.Pf.OOCore.OOP hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hF, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

def GXPos : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ γ, IsPtRep X u u' w γ) → ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v

variable (Y : Formalism.L2.SG.Full.Full X) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

section GX

variable {D : D7} {X : HidaSetting D}

theorem frm_sc (u : D.what₂.Word) (sc : ℝ) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    frm X u sc v a = (((sc ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • frm X u 1 v a := by
  unfold frm famSc
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Complex.ofReal_inv, Complex.ofReal_pow]

theorem zx_rd (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (a b : Fin (D.R.rS + 1)) :
    ZX X u u' D.host.rdE γ v a b = ((rhoF D a * rhoF D b : ℝ) : ℂ) * ZX X u u' 1 γ v a b := by
  have hρ : ∀ c : Fin (D.R.rS + 1), rhoF D c = (D.host.rdE ^ (D.R.rS - (c : ℕ)))⁻¹ := by
    intro c
    have hc := c.isLt
    unfold rhoF
    have h1 := Real.rpow_intCast D.host.rdE (-((D.R.rS - (c : ℕ) : ℕ) : ℤ))
    rw [zpow_neg, zpow_natCast] at h1
    rw [← h1]
    congr 1
    push_cast [Nat.cast_sub (Nat.lt_succ_iff.mp hc)]
    ring
  rw [hρ a, hρ b]
  unfold ZX Formalism.L2.SG.RealObj.Zhat
  rw [frm_sc u D.host.rdE v a, frm_sc u' D.host.rdE v b, Matrix.mulVec_smul]
  unfold hJ
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  clear hρ
  push_cast
  ring

theorem gx_eq (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ γ, IsPtRep X u u' w γ)
    (τ : D.what₂.Tau) :
    GX X u u' D.host.rdE (gamW X u u' w) (vOf X τ) =
      Formalism.MainNotions.S.ThB.Gpt (Tw (D := D) u) (Tw (D := D) u') (Formalism.MainNotions.S.ThB.ptLoc D τ w) := by
  have hrep : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dite_eq_left hw]
    exact hw.choose_spec
  have hZ : ∀ a b, ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ) a b =
      (-1 : ℂ) ^ (D.R.rS - b.val) * ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w) a b := by
    intro a b
    have h1 := congrFun (congrFun (hrep (vOf X τ)) a) b
    unfold Formalism.L2.SG.RealObj.ZhatO Formalism.L2.SG.RealObj.ptC at h1
    simp only [Matrix.map_apply] at h1
    rw [X.φ_eq, X.ιE.apply_symm_apply, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h1
    have hs : ((-1 : ℂ) ^ (D.R.rS - b.val)) * (-1 : ℂ) ^ (D.R.rS - b.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [zx_rd, Formalism.L2.SG.Pf.RelPtR.ptMat_ptLoc τ w a b]
    have h2 : ZX X u u' 1 (gamW X u u' w) (vOf X τ) a b = (-1 : ℂ) ^ (D.R.rS - b.val) * embS D τ (ptMat w a b) := by
      rw [← h1, ← mul_assoc, hs, one_mul]
    rw [h2]
    ring
  have hD : ∀ l (hl : l ≤ D.R.rS + 1), Complex.normSq (Formalism.L2.SG.RealObj.Dl (ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ)) l) =
      Complex.normSq (leadMinor (ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w)) l hl) := by
    intro l hl
    unfold Formalism.L2.SG.RealObj.Dl leadMinor
    rw [dite_eq_left hl]
    have hM : (ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        (ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w)).submatrix (Fin.castLE hl) (Fin.castLE hl) *
          Matrix.diagonal (fun b : Fin l => (-1 : ℂ) ^ (D.R.rS - (Fin.castLE hl b).val)) := by
      ext i j
      simp [Matrix.mul_diagonal, hZ, mul_comm]
    rw [hM, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod]
    simp [Complex.normSq_neg]
  unfold GX Gv Formalism.MainNotions.S.ThB.Gpt
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hD (D.R.rS + 1) le_rfl, hD D.R.rS (Nat.le_succ _)]

theorem gxPos_holds (u u' : D.what₂.Word) : GXPos (X := X) u u' := by
  intro w hb hw v
  have hv : v = vOf X (X.pl v) := (X.pl.symm_apply_apply v).symm
  rw [hv, gx_eq u u' w hw (X.pl v)]
  exact hb.2 (X.pl v)

end GX

end Formalism.L2.SG.Pf.OOCoreHilbertSchmidt
end
end
