module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.IsPhysSet
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle001

@[expose] public section

section

noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF.PhysicalTorus

variable {n : ℕ}

theorem prod_mode (ε : Fin n → Bool) {p : Fin n × Fin n → Prop} [Fintype (Subtype p)]
    (hp : ∀ x, p x ↔ ε x.1 = true ∧ ε x.2 = false) (f : Fin n × Fin n → ℂ) :
    ∏ x : Subtype p, f x.1 =
      ∏ i ∈ univ.filter (fun i => ε i = true), ∏ a ∈ univ.filter (fun a => ε a = false), f (i, a) := by
  rw [← Finset.prod_subtype ((univ.filter (fun i => ε i = true)) ×ˢ (univ.filter (fun a => ε a = false)))
    (fun x => by simp [hp, Finset.mem_product]) f, Finset.prod_product]

theorem physDet_diag (ε : Fin n → Bool) (s : Fin n → ℂ) :
    physDet ε (Matrix.diagonal s) = ∏ x : {x : Fin n × Fin n // IsPhys ε x}, (1 - s x.1.1 * star (s x.1.2)) := by
  delta physDet
  rw [← Matrix.det_diagonal]
  congr 1
  funext x y
  by_cases h : x = y
  · subst h; simp
  · have hxy : x.1.1 ≠ y.1.1 ∨ x.1.2 ≠ y.1.2 := by
      by_contra hc
      push Not at hc
      exact h (Subtype.ext (Prod.ext hc.1 hc.2))
    rcases hxy with h1 | h1 <;> simp [Matrix.diagonal_apply, h, h1]

theorem tor_ne (θ : Fin n → ℝ) (a : Fin n) : tor θ a ≠ 0 := Complex.exp_ne_zero _

theorem norm_tor (θ : Fin n → ℝ) (a : Fin n) : ‖tor θ a‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem star_tor (θ : Fin n → ℝ) (a : Fin n) : star (tor θ a) = (tor θ a)⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, norm_tor]
  simp

theorem one_sub_tor (θ : Fin n → ℝ) (i a : Fin n) :
    1 - tor θ i * star (tor θ a) = -1 * (tor θ i - tor θ a) * (tor θ a)⁻¹ := by
  rw [star_tor]
  have h := mul_inv_cancel₀ (tor_ne θ a)
  linear_combination -h

theorem factor_tor (θ : Fin n → ℝ) (i a : Fin n) :
    (1 - tor θ i * star (tor θ a)) * conj (1 - tor θ i * star (tor θ a)) = ((‖tor θ i - tor θ a‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, one_sub_tor, norm_mul, norm_mul, norm_inv, norm_tor]
  simp

end PhysicalTorus

open PhysicalTorus

theorem adjointDet_onCompactTorus (n : ℕ) (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    physDet ε (Matrix.diagonal (tor θ)) =
      (-1) ^ (pOf ε * qOf ε) *
        (∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (tor θ x.1.1 - tor θ x.1.2)) *
        ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) ∧
    physDet ε (Matrix.diagonal (tor θ)) * conj (physDet ε (Matrix.diagonal (tor θ))) =
      (GlobalTheory.PsCo.Pc1.dMode ε θ : ℂ) := by
  have hD : physDet ε (Matrix.diagonal (tor θ)) = ∏ i ∈ univ.filter (fun i => ε i = true),
      ∏ a ∈ univ.filter (fun a => ε a = false), (1 - tor θ i * star (tor θ a)) := by
    rw [physDet_diag]
    exact prod_mode ε (p := IsPhys ε) (fun _ => Iff.rfl) (fun y => 1 - tor θ y.1 * star (tor θ y.2))
  have hM : ∀ f : Fin n × Fin n → ℂ, ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, f x.1 = ∏ i ∈ univ.filter (fun i => ε i = true),
      ∏ a ∈ univ.filter (fun a => ε a = false), f (i, a) := fun f => prod_mode ε (fun _ => Iff.rfl) f
  refine ⟨?_, ?_⟩
  · have hV : ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (tor θ x.1.1 - tor θ x.1.2) = ∏ i ∈ univ.filter (fun i => ε i = true),
        ∏ a ∈ univ.filter (fun a => ε a = false), (tor θ i - tor θ a) := hM (fun y => tor θ y.1 - tor θ y.2)
    have hS : (-1 : ℂ) ^ (pOf ε * qOf ε) = ∏ i ∈ univ.filter (fun i => ε i = true),
        ∏ a ∈ univ.filter (fun a => ε a = false), (-1 : ℂ) := by
      delta pOf qOf
      rw [Finset.prod_const, Finset.prod_const, ← pow_mul, mul_comm]
    have hR : ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) = ∏ i ∈ univ.filter (fun i => ε i = true),
        ∏ a ∈ univ.filter (fun a => ε a = false), (tor θ a)⁻¹ := by
      rw [Finset.prod_comm]
      simp only [Finset.prod_const]
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl fun a _ => ?_
      delta pOf
      cases h : ε a <;> simp [zpow_neg, inv_pow]
    rw [hD, hV, hS, hR]
    simp only [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun a _ => one_sub_tor θ i a
  · rw [hD, map_prod]
    simp only [map_prod, ← Finset.prod_mul_distrib, factor_tor]
    delta GlobalTheory.PsCo.Pc1.dMode
    rw [Complex.ofReal_prod]
    exact (hM (fun y => ((‖tor θ y.1 - tor θ y.2‖ ^ 2 : ℝ) : ℂ))).symm

end GlobalTheory.PsCo.PcEF
end
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap Matrix
open Formalism.REAL (KG toMK)

namespace GlobalTheory.PsCo.PcEF.PhysicalMatrixDeterminant

variable {n : ℕ} {ε : Fin n → Bool}

def physM (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix {x : Fin n × Fin n // IsPhys ε x} {x : Fin n × Fin n // IsPhys ε x} ℂ :=
  fun x y => k x.1.1 y.1.1 * star (k x.1.2 y.1.2)

theorem physM_eq_adMat (k : Matrix (Fin n) (Fin n) ℂ) (x y : {x : Fin n × Fin n // IsPhys ε x}) :
    physM ε k x y = adMat ε k x.1 y.1 := by
  simp [physM, adMat, x.2, y.2]

theorem physM_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Kset ε) (hb : b ∈ Kset ε) :
    physM ε (a * b) = physM ε a * physM ε b := by
  ext x y
  rw [physM_eq_adMat, adMat_mul ha hb, Matrix.mul_apply, Matrix.mul_apply,
    ← Fintype.sum_subtype_add_sum_subtype (IsPhys ε)]
  have h0 : ∑ z : {z : Fin n × Fin n // ¬ IsPhys ε z}, adMat ε a x.1 z * adMat ε b z y.1 = 0 :=
    Finset.sum_eq_zero fun z _ => by simp [adMat, x.2, z.2]
  rw [h0, add_zero]
  simp only [physM_eq_adMat]

theorem physM_one : physM ε (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext x y
  rw [physM_eq_adMat, adMat_one]
  by_cases h : x = y
  · subst h; simp
  · have h' : x.1 ≠ y.1 := fun e => h (Subtype.ext e)
    simp [h, h']

theorem physDet_eq (k : Matrix (Fin n) (Fin n) ℂ) : physDet ε k = (1 - physM ε k).det := by
  unfold physDet
  congr 1

theorem physDet_conj (k k' : KG ε) : physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) := by
  have ha : toMK k'⁻¹ ∈ Kset ε := (k'⁻¹).2
  have hb : toMK k ∈ Kset ε := k.2
  have hc : toMK k' ∈ Kset ε := k'.2
  have hab : toMK k'⁻¹ * toMK k ∈ Kset ε := (k'⁻¹ * k).2
  have hac : physM ε (toMK k'⁻¹) * physM ε (toMK k') = 1 := by
    rw [← physM_mul ha hc, show toMK k'⁻¹ * toMK k' = toMK (k'⁻¹ * k') from rfl, inv_mul_cancel]
    exact physM_one
  rw [physDet_eq, physDet_eq, show toMK (k'⁻¹ * k * k') = toMK k'⁻¹ * toMK k * toMK k' from rfl,
    physM_mul hab hc, physM_mul ha hb]
  have e : 1 - physM ε (toMK k'⁻¹) * physM ε (toMK k) * physM ε (toMK k') =
      physM ε (toMK k'⁻¹) * (1 - physM ε (toMK k)) * physM ε (toMK k') := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hac]
  rw [e, det_mul, det_mul, mul_comm (det (physM ε (toMK k'⁻¹))), mul_assoc, ← det_mul, hac, det_one, mul_one]

theorem trK_conj {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (k k' : KG ε) :
    trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k) := by
  have hmul : ∀ a b : KG ε, (T (toMK (a * b)) : W →ₗ[ℂ] W) = (T (toMK a) : W →ₗ[ℂ] W) * (T (toMK b)) := by
    intro a b
    rw [show toMK (a * b) = toMK a * toMK b from rfl, hT.1.2 _ a.2 _ b.2]
    rfl
  have h1 : (T (toMK (1 : KG ε)) : W →ₗ[ℂ] W) = 1 := by
    rw [show toMK (1 : KG ε) = 1 from rfl, hT.1.1]
    rfl
  unfold trK
  rw [hmul, hmul, LinearMap.trace_mul_comm, ← mul_assoc, ← hmul k' k'⁻¹, mul_inv_cancel, h1, one_mul]

end GlobalTheory.PsCo.PcEF.PhysicalMatrixDeterminant

namespace GlobalTheory.PsCo.PcEF

theorem adjointDetTrace_classFunction (n : ℕ) (ε : Fin n → Bool) (k k' : KG ε) :
    physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) ∧
      ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
        (T : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)),
        Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
        trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k) := by
  refine ⟨PhysicalMatrixDeterminant.physDet_conj k k', ?_⟩
  intro W _ _ _ T hT
  exact PhysicalMatrixDeterminant.trK_conj T hT k k'

end GlobalTheory.PsCo.PcEF

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_interForm_dbl : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∃ T : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (Y.dim + 1) => Pic W.Z) ℤ, (∀ (σ : Equiv.Perm (Fin (Y.dim + 1))) (y : Fin (Y.dim + 1) → Pic W.Z), T (y ∘ σ) = T y) ∧ ∀ y : Fin (Y.dim + 1) → CartierDiv W.Z, T (fun i => toPic (y i)) = W.num y := by
  intro F _ Y W hW
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hv : DiffVanish (Y.dim + 1 + 1) (chiPic F (structureModule W.Z)) :=
    diffVanish_chiPic_of_isProjOver (algebraΓOfHom_algebraMap (W.p₁ ≫ Y.str)) (structureModule W.Z) W.proj
      (by rw [GlobalTheory.QCoh.suppDim_structureModule]; exact hW)
  refine ⟨hv.form, fun σ y => hv.form_comp_perm y σ, fun y => ?_⟩
  rw [hv.form_apply _ 0]
  show _ = interNum F (structureModule W.Z) fun i => toLB (y i)
  rw [interNum_eq_multiDiff F _ fun i => isLB_toLB (y i)]
  rfl

end GlobalTheory.FlagPush
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.exists_intersectionForm_picard_doubleSpace : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∃ T : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (Y.dim + 1) => Pic W.Z) ℤ, (∀ (σ : Equiv.Perm (Fin (Y.dim + 1))) (y : Fin (Y.dim + 1) → Pic W.Z), T (y ∘ σ) = T y) ∧ ∀ y : Fin (Y.dim + 1) → CartierDiv W.Z, T (fun i => toPic (y i)) = W.num y := by
  intro F _ Y W hW
  let := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hv : DiffVanish (Y.dim + 1 + 1) (chiPic F (structureModule W.Z)) :=
    diffVanish_chiPic_of_isProjOver (algebraΓOfHom_algebraMap (W.p₁ ≫ Y.str)) (structureModule W.Z) W.proj
      (by rw [GlobalTheory.QCoh.suppDim_structureModule]; exact hW)
  refine ⟨hv.form, fun σ y => hv.form_comp_perm y σ, fun y => ?_⟩
  rw [hv.form_apply _ 0]
  show _ = interNum F (structureModule W.Z) fun i => toLB (y i)
  rw [interNum_eq_multiDiff F _ fun i => isLB_toLB (y i)]
  rfl
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem isEffQDiv_add {X : Scheme.{0}} {Δ D : X → ℚ} (hΔ : IsEffQDiv Δ) (hD : IsEffQDiv D) :
    IsEffQDiv (Δ + D) := by
  refine ⟨(hΔ.finite.union hD.finite).subset (Function.support_add _ _), ?_, ?_⟩
  · intro z hz
    by_cases h : Δ z = 0
    · exact hD.coheight z fun h' => hz (by simp [h, h'])
    · exact hΔ.coheight z h
  · intro z
    exact add_nonneg (hΔ.nonneg z) (hD.nonneg z)

theorem isEffQDiv_add_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (Δ D : X → ℚ), IsEffQDiv Δ → IsQCart D → IsEffQDiv (Δ + D) := by
  intro X _ _ p hp Δ D hΔ hD
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨m, D₀, -, hD₀, rfl⟩ := hD
  exact isEffQDiv_add hΔ (isEffQDiv_qWeil hD₀ m)

end GlobalTheory.PairStep
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PairStep

theorem eff_divOfSec_of_sec {X : Scheme.{0}} [IsIntegral X] {L : LB X} (hL : L.IsLB) (s : L.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) : (divOfSec hL s hs).Eff := by
  refine CartierDiv.eff_iff.2 fun y g hg => ?_
  obtain ⟨i, hi⟩ := exists_chart hL y
  have h1 := (presents_divOfRatSec hL (isRatSec_ratOfSec s hs)).isEqn i y hi
  have hu := h1.iff_unitAt.1 hg
  have hr : RegAt y (ratOfSec s hs i : X.functionField) := by
    rw [val_ratOfSec (gen_mem hi)]
    exact regAt_fnOf hi (gen_mem hi) _
  have := hu.regAt.mul hr
  rwa [div_mul_cancel₀ _ (Units.ne_zero _)] at this

theorem qNum_divOfSec : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (hN : N.IsLB) (l m : ℕ) (s : (lbPow N l).Sec) (hs : genericPoint X ∈ nonzeroLocus s), 0 < m → (divOfSec (isLB_lbPow hN l) s hs).Eff ∧ QNum p N ((l : ℚ) / m) (qWeil (divOfSec (isLB_lbPow hN l) s hs) m) := by
  intro X _ _ p hp N hN l m s hs hm
  have hE := eff_divOfSec_of_sec (isLB_lbPow hN l) s hs
  refine ⟨hE, m, _, hm, hE, rfl, fun C hC => ?_⟩
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  letI := algebraΓOfHom p
  have hcls : toPic (divOfSec (isLB_lbPow hN l) s hs) = cls _ (isLB_lbPow hN l) :=
    (presents_divOfRatSec (isLB_lbPow hN l) (isRatSec_ratOfSec s hs)).toPic_eq
  rw [interNumRed_one_congr (isLB_toLB _) (isLB_lbPow hN l) hcls, hC.interNumRed_lbPow hH hN l]
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

end GlobalTheory.PairStep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem mult_nsmul_of_qadd {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X)
    (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    rw [zero_nsmul, (CartierDiv.isEqn_zero z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero]
    simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul_of_qadd {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem qNum_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ),
    IsProjOver p → ∀ (N : LB X) (a b : ℚ) (D B : X → ℚ), QNum p N a D → QNum p N b B →
      QNum p N (a + b) (D + B) := by
  intro X _ _ p hp N a b D B hD hB
  letI := algebraΓOfHom p
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨m, D₀, hm, hD₀, rfl, hDn⟩ := hD
  obtain ⟨m', B₀, hm', hB₀, rfl, hBn⟩ := hB
  refine ⟨m * m', m' • D₀ + m • B₀, Nat.mul_pos hm hm', (eff_nsmul_of_qadd hD₀ m').add
    (eff_nsmul_of_qadd hB₀ m), ?_, ?_⟩
  · funext z
    simp only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul_of_qadd]
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    push_cast
    field_simp
  · intro C hC
    let hLB (D : CartierDiv X) : (toLB D).IsLB := (presents_toLB D).isLB
    let f : CartierDiv X →+ Pic X := AddMonoidHom.mk' (fun D => cls _ (hLB D)) fun D E =>
      (cls_eq_iff _ (isLB_tens (hLB D) (hLB E))).2
        ((presents_toLB _).lbIso ((presents_toLB D).tens (presents_toLB E)))
    have e := hC.interNumRed_of_cls_eq_add (N := toLB (m' • D₀ + m • B₀))
      (A := lbPow (toLB D₀) m') (B := lbPow (toLB B₀) m) hH (hLB (m' • D₀ + m • B₀))
      (isLB_lbPow (hLB D₀) m') (isLB_lbPow (hLB B₀) m)
      (by
        rw [cls_lbPow (hLB D₀), cls_lbPow (hLB B₀)]
        change f (m' • D₀ + m • B₀) = m' • f D₀ + m • f B₀
        rw [map_add, map_nsmul, map_nsmul])
    rw [hC.interNumRed_lbPow hH (hLB D₀), hC.interNumRed_lbPow hH (hLB B₀)] at e
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    have hD' := hDn C hC
    have hB' := hBn C hC
    rw [e]
    push_cast
    rw [div_eq_iff h1] at hD'
    rw [div_eq_iff h2] at hB'
    rw [div_eq_iff (mul_ne_zero h1 h2), hD', hB']
    ring

end GlobalTheory.PairStep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.QCartCone

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem mult_zero' (z : X) : (0 : CartierDiv X).mult z = 0 := by
  have := CartierDiv.mult_add (0 : CartierDiv X) 0 z
  rw [add_zero] at this
  omega

theorem mult_nsmul' (D : CartierDiv X) (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero']; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul' {D : CartierDiv X} (h : D.Eff) (n : ℕ) : (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem isQCart_cone : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (D B : X → ℚ) (c : ℚ),
    IsQCart D → IsQCart B → 0 ≤ c → IsQCart (D + B) ∧ IsQCart (c • D) ∧ IsQCart (0 : X → ℚ) := by
  intro X _ _ D B c hD hB hc
  obtain ⟨m, D₀, hm, hD₀, rfl⟩ := hD
  obtain ⟨n, B₀, hn, hB₀, rfl⟩ := hB
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨m * n, n • D₀ + m • B₀, Nat.mul_pos hm hn, (eff_nsmul' hD₀ n).add (eff_nsmul' hB₀ m), ?_⟩,
    ⟨c.den * m, c.num.toNat • D₀, Nat.mul_pos c.den_pos hm, eff_nsmul' hD₀ _, ?_⟩,
    ⟨1, 0, one_pos, CartierDiv.eff_zero, ?_⟩⟩
  · funext z
    simp only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul']
    push_cast
    field_simp
  · funext z
    have hnum : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by
      have h1 : ((c.num.toNat : ℤ) : ℚ) = (c.num : ℚ) := by
        rw [Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)]
      exact_mod_cast h1
    have hden : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
    simp only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul']
    push_cast
    rw [hnum]
    conv_lhs => rw [← Rat.num_div_den c]
    field_simp
  · funext z
    simp [qWeil, mult_zero']

end GlobalTheory.QCartCone
end
end
