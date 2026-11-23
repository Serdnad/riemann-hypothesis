module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle003
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle004
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle005
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLt
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle002
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSx
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

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def DlSize {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps

theorem numsL_wtsL_fam {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) :
    ∃ Cn₀ : ℝ, ∀ Cn ≥ Cn₀, ∀ cL ≥ (3 : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ WtsL (Fm.D x i) (Fm.L x i) Cn :=
  flipTwoThree.nums_wts_of_tuSize Fm hT hDl

theorem factDGam_mono {D : D7} {C C' : ℝ} (h : FactDGam D C) (hC : C ≤ C') : FactDGam D C' := by
  intro u
  refine (h u).trans ?_
  have h1 : (0 : ℝ) ≤ Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by
    have : ((D.R.f : ℝ) * D.R.N D.R.m) = ((D.R.f * D.R.N D.R.m : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact Real.log_natCast_nonneg _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) h1
  have := mul_le_mul_of_nonneg_right hC h2
  simp only [mul_assoc] at this ⊢
  exact this

theorem slopes_family_of_column_values {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) (h5 : flipTwoThree.ConclusionF5 Fm)
    (h6 : flipTwoThree.ConclusionF6 Fm) (hCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) :
    LocalQuadraticParts.SlopesFamily Fm := by
  obtain ⟨Cn, hN⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨x1, hCV⟩ := hCV
  refine family_orderBound_of_fifth_sixth Fm Cn 3 h5 h6 (by norm_num) ⟨max x0 x1, fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hx
  have e1 : x ≥ x1 := le_trans (le_max_right _ _) hx
  exact ⟨by linarith [flipTwoThree.two_le_rdE (Fm.D x i).host], (hN x e0 i).1, (hN x e0 i).2, hCV x e1 i⟩

theorem family_levelPrime_summary_simple {eps : ℝ} (Fm : FamP eps) (C C1 : ℝ) (hC1 : 0 ≤ C1)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∀ u, product_first_zeroth_parts.Conclusion2 (Fm.D x i) u) ∧ (∀ u, product_first_zeroth_parts.Conclusion5 (Fm.D x i) u C) ∧
      LevelPrimeSizeBounds (Fm.D x i) (Fm.L x i) C1 ∧ ∀ u, product_first_zeroth_parts.HidaSetting (Fm.D x i) u) :
    LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨x0, hE⟩ := hE
  refine family_levelPrime_summary Fm C C1 hC1 ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hx
  have e1 : Fm.x1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hx)
  obtain ⟨a, b, c, d⟩ := hE x e0 i
  exact ⟨a, b, locSpan _, lenAtT _ _ (Fm.ex x e1 i).lat.atT, c, d⟩

end Formalism.MainNotions.J

end
end

section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

variable {D : D7} {L : SizeData₂ D}

theorem gammaDiscriminant_budget_of_sizes {Cn cL CG : ℝ} (hcL : 1 ≤ cL) (hCG : 0 ≤ CG) (hN : NumsL D L Cn cL) (hG : FactDGam D CG) :
    WeightDegreeSizes.StabiliserLogBound D L (4 * CG) := by
  unfold WeightDegreeSizes.StabiliserLogBound
  unfold FactDGam at hG
  intro u
  have hNu := hN u
  unfold flipTwoThree.Nums at hNu
  obtain ⟨hb0, -, -, -, -, hb', -, -, -, -, hNL, -, -, hx2, -, -⟩ := hNu
  have hfk : D.R.f ≤ D.R.k := by
    unfold Ranks.f
    exact D.R.f_le_k
  have hmf : D.R.m ≤ D.R.f := by
    unfold Ranks.f
    exact D.R.m_le_f
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hkN : D.R.k ≤ D.R.N D.R.m := by
    unfold Ranks.N
    omega
  have hfN : (D.R.f : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hfk.trans hkN
  have hf2 : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hm2.trans hmf
  have hm2r : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hN0 : (0 : ℝ) < D.R.N D.R.m := by linarith
  have hx1 := L.sc.one_lt_alt
  have hLr : 1 ≤ L.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hbb : L.sc.x * L.sc.b / L.sc.x = L.sc.b := by
    field_simp
  rw [hbb] at hb'
  have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hNL' : (D.R.N D.R.m : ℝ) * L.sc.L ≤ L.sc.b := by
    have : (D.R.N D.R.m : ℝ) * L.sc.L ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) := by
      apply mul_le_mul_of_nonneg_left _ hN0.le
      nlinarith
    linarith
  have hlogN : Real.log (D.R.N D.R.m : ℝ) ≤ L.sc.L := by
    have hNb : (D.R.N D.R.m : ℝ) ≤ Real.exp L.sc.L := by
      have : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * L.sc.L := le_mul_of_one_le_right hN0.le hLr
      have hb : L.sc.b = Real.exp L.sc.L := rfl
      linarith
    calc Real.log (D.R.N D.R.m : ℝ) ≤ Real.log (Real.exp L.sc.L) := Real.log_le_log hN0 hNb
      _ = L.sc.L := Real.log_exp _
  have hlogf : Real.log (D.R.f : ℝ) ≤ Real.log (D.R.N D.R.m : ℝ) := Real.log_le_log (by linarith) hfN
  have hlog : Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.sc.L := by
    rw [Real.log_mul (by linarith) hN0.ne']
    linarith
  have hB0 : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := rfl
  have hb0' : 0 < L.sc.b := Real.exp_pos _
  have key : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.B0 := by
    have h1 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤
        (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * (2 * L.sc.L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * L.sc.L) ≤ (D.R.f : ℝ) * L.sc.b :=
      mul_le_mul_of_nonneg_left hNL' (by positivity)
    have h3 : (D.R.f : ℝ) * L.sc.b * 1 ≤ (D.R.f : ℝ) * L.sc.b * ((D.R.m : ℝ) * L.sc.L) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    rw [hB0]
    nlinarith
  have hG' := hG u
  have := mul_le_mul_of_nonneg_left key hCG
  nlinarith

end Formalism.MainNotions.J

end
end

section

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.BasicNotions

theorem finrank_F_eq (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  exact D.host.der.finrank_F

theorem splitsF_g (D : D7) (i : Fin 2) : StandardLattice.SplitsF D (D.host.g i) := by
  have h := splits_sub D.host.F (D.host.g i) D.host.E (D.host.g_prime i) (D.nd.g_split i)
  rw [finrank_F_eq] at h
  exact h

theorem idxColTie_holds (D : D7) : IdxColTie D := idxColTie_of D (splitsF_g D)

theorem idxRowTie_holds (D : D7) : IdxRowTie D := idxRowTie_of D (splitsF_g D)

end Formalism.MainNotions.J

end
end

section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem servedModel_of_params (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (h3 : 3 ≤ L.sc.x ^ (L.sc.ez / 5)) :
    Formalism.MainNotions.WeightDegreeSizes.ServedHasModel X K := by
  unfold Formalism.MainNotions.WeightDegreeSizes.ServedHasModel
  intro u w hw hV
  refine Formalism.BasicNotions.gIdx_of_cand P K h3 u _ ?_ hw
  unfold VV at hV
  by_contra hc
  exact hV (if_neg (fun h => hc h.1))

end Formalism.MainNotions.J
end
end

section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}

theorem sizeData_at_level_primes_of_defs {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef) (hE : L.EDef X K c)
    (hTg : LevelPrimeNotTypePrime D) : LevelPrimeSizes D L := ETDef_of P hF hE hTg

end Formalism.MainNotions.J

end
end

section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem sgAtG_of {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) : Formalism.MainNotions.WeightDegreeSizes.SgAtG D L Xe C1 :=
  fun i w hwi u hw => sumFE_atG_le hF hE hC1 hC i w hwi u hw

theorem family_type_prime_loss {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {C1 : ℝ} (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ Fm.cX.err.g) :
    Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 :=
  ⟨0, fun x hx _ i => sgAtG_of (local_compatibility_family Fm x hx i).fdef (Fm.ex x hx i).err hC1 hC⟩

end Formalism.MainNotions.J

end
end
