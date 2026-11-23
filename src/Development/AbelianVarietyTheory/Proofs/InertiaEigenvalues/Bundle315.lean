module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle078
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle286
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

@[expose] public section

section

noncomputable section

open scoped Formalism.Per
open Filter Topology

namespace GlobalTheory.PMon.Gauss

theorem iSup_monomial_logConvex (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1)
    {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (⨆ n, c n * (ρ₁ ^ t * ρ₂ ^ (1 - t)) ^ n) ≤
      (⨆ n, c n * ρ₁ ^ n) ^ t * (⨆ n, c n * ρ₂ ^ n) ^ (1 - t) := by
  have hb : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → BddAbove (Set.range fun n => c n * ρ ^ n) := fun ρ h0' h1' =>
    ⟨1, Set.forall_mem_range.2 fun n => mul_le_one₀ (h1 n) (pow_nonneg h0' n) (pow_le_one₀ h0' h1')⟩
  apply ciSup_le
  intro n
  have hc : c n = c n ^ t * c n ^ (1 - t) := by
    rw [← Real.rpow_add' (h0 n) (by norm_num), add_sub_cancel, Real.rpow_one]
  have e : c n * (ρ₁ ^ t * ρ₂ ^ (1 - t)) ^ n = (c n * ρ₁ ^ n) ^ t * (c n * ρ₂ ^ n) ^ (1 - t) := by
    rw [Real.mul_rpow (h0 n) (pow_nonneg hρ₁ n), Real.mul_rpow (h0 n) (pow_nonneg hρ₂ n), mul_pow,
      Real.rpow_pow_comm hρ₁, Real.rpow_pow_comm hρ₂]
    conv_lhs => rw [hc]
    ring
  rw [e]
  have ht1' : 0 ≤ 1 - t := by linarith
  exact mul_le_mul
    (Real.rpow_le_rpow (mul_nonneg (h0 n) (pow_nonneg hρ₁ n)) (le_ciSup (hb ρ₁ hρ₁ hρ₁1) n) ht0)
    (Real.rpow_le_rpow (mul_nonneg (h0 n) (pow_nonneg hρ₂ n)) (le_ciSup (hb ρ₂ hρ₂ hρ₂1) n) ht1')
    (Real.rpow_nonneg (mul_nonneg (h0 n) (pow_nonneg hρ₂ n)) _)
    (Real.rpow_nonneg ((mul_nonneg (h0 n) (pow_nonneg hρ₁ n)).trans (le_ciSup (hb ρ₁ hρ₁ hρ₁1) n)) _)

theorem gA_logConvex (l : ℕ) [Fact l.Prime] (a : Formalism.Per.Ainf l) {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gA l (ρ₁ ^ t * ρ₂ ^ (1 - t)) a ≤ gA l ρ₁ a ^ t * gA l ρ₂ a ^ (1 - t) :=
  iSup_monomial_logConvex _ (fun n => by positivity)
    (fun n => Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
    hρ₁ hρ₂ hρ₁1 hρ₂1 ht0 ht1

theorem rpow_mul_rpow_one_sub_self {a t : ℝ} (ha : 0 ≤ a) : a ^ t * a ^ (1 - t) = a := by
  rw [← Real.rpow_add' ha (by norm_num), add_sub_cancel, Real.rpow_one]

theorem gC_logConvex : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (ρ₁ ρ₂ t : ℝ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ ≤ ρ₂ →
    ρ₂ < 1 → 0 ≤ t → t ≤ 1 → gC l (ρ₁ ^ t * ρ₂ ^ (1 - t)) x ≤ gC l ρ₁ x ^ t * gC l ρ₂ x ^ (1 - t) := by
  intro l _ x ρ₁ ρ₂ t h1 h12 h2 ht0 ht1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ₁ : 0 < ρ₁ := (inv_pos.2 hl0).trans_le h1
  have hρ₂ : 0 < ρ₂ := hρ₁.trans_le h12
  have ht1' : 0 ≤ 1 - t := by linarith
  set ρ := ρ₁ ^ t * ρ₂ ^ (1 - t) with hρdef
  have hρlo : ρ₁ ≤ ρ := by
    calc ρ₁ = ρ₁ ^ t * ρ₁ ^ (1 - t) := (rpow_mul_rpow_one_sub_self hρ₁.le).symm
      _ ≤ ρ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ₁.le h12 ht1') (Real.rpow_nonneg hρ₁.le _)
  have hρhi : ρ ≤ ρ₂ := by
    calc ρ ≤ ρ₂ ^ t * ρ₂ ^ (1 - t) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hρ₁.le h12 ht0) (Real.rpow_nonneg hρ₂.le _)
      _ = ρ₂ := rpow_mul_rpow_one_sub_self hρ₂.le
  have hρ0 : 0 < ρ := hρ₁.trans_le hρlo
  have G : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → IsGauss l σ (gC l σ) := fun σ a b => isGauss_gC_of_le l σ a b
  have Gl : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ (l : Formalism.Per.Acris l) = σ := by
    intro σ a b
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, (G σ a b).2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l ((inv_pos.2 hl0).le.trans a)
  have g : IsGauss l ρ (gC l ρ) := G ρ (h1.trans hρlo) (hρhi.trans_lt h2)
  have g₁ : IsGauss l ρ₁ (gC l ρ₁) := G ρ₁ h1 (h12.trans_lt h2)
  have g₂ : IsGauss l ρ₂ (gC l ρ₂) := G ρ₂ (h1.trans h12) h2

  have P : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → ∀ (k : ℕ) (y : Formalism.Per.Acris l),
      gC l σ ((l : Formalism.Per.Acris l) ^ k * y) = σ ^ k * gC l σ y := by
    intro σ a b k y
    rw [GlobalTheory.GaussSlope.map_pow_mul _ (G σ a b).2.2.2.1, Gl σ a b]

  have hs : ∀ s : Formalism.Per.Acris0 l, gC l ρ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ≤
      gC l ρ₁ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ^ t *
        gC l ρ₂ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ^ (1 - t) := by
    intro s
    obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
    set y := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s
    have e : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → σ ^ k * gC l σ y = gA l σ a := by
      intro σ a' b
      rw [← P σ a' b, ha, (G σ a' b).2.2.2.2]
    have key := gA_logConvex l a hρ₁.le hρ₂.le (h12.trans h2.le) h2.le ht0 ht1
    rw [← e ρ (h1.trans hρlo) (hρhi.trans_lt h2), ← e ρ₁ h1 (h12.trans_lt h2), ← e ρ₂ (h1.trans h12) h2,
      Real.mul_rpow (pow_nonneg hρ₁.le _) (g₁.1 y).1, Real.mul_rpow (pow_nonneg hρ₂.le _) (g₂.1 y).1,
      ← Real.rpow_pow_comm hρ₁.le, ← Real.rpow_pow_comm hρ₂.le] at key
    have e2 : (ρ₁ ^ t) ^ k * gC l ρ₁ y ^ t * ((ρ₂ ^ (1 - t)) ^ k * gC l ρ₂ y ^ (1 - t)) =
        ρ ^ k * (gC l ρ₁ y ^ t * gC l ρ₂ y ^ (1 - t)) := by
      rw [hρdef, mul_pow]; ring
    rw [e2] at key
    exact le_of_mul_le_mul_left key (pow_pos hρ0 k)

  have F : ∀ r : ℕ, gC l ρ x ≤ max (max (gC l ρ₁ x) (ρ₁ ^ r) ^ t * max (gC l ρ₂ x) (ρ₂ ^ r) ^ (1 - t)) (ρ ^ r) := by
    intro r
    obtain ⟨s, z, hx⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
    set y := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s
    have hz : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ ((l : Formalism.Per.Acris l) ^ r * z) ≤ σ ^ r := by
      intro σ a b
      rw [P σ a b]
      exact mul_le_of_le_one_right (pow_nonneg ((inv_pos.2 hl0).le.trans a) _) ((G σ a b).1 z).2
    have hy : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ y ≤ max (gC l σ x) (σ ^ r) := by
      intro σ a b
      have : y = x + -((l : Formalism.Per.Acris l) ^ r * z) := by rw [hx]; ring
      rw [this]
      refine ((G σ a b).2.1 _ _).trans (max_le_max le_rfl ?_)
      rw [(G σ a b).2.2.1]
      exact hz σ a b
    conv_lhs => rw [hx]
    refine (g.2.1 _ _).trans (max_le_max ?_ (hz ρ (h1.trans hρlo) (hρhi.trans_lt h2)))
    refine (hs s).trans (mul_le_mul (Real.rpow_le_rpow (g₁.1 y).1 (hy ρ₁ h1 (h12.trans_lt h2)) ht0)
      (Real.rpow_le_rpow (g₂.1 y).1 (hy ρ₂ (h1.trans h12) h2) ht1') (Real.rpow_nonneg (g₂.1 y).1 _)
      (Real.rpow_nonneg ((g₁.1 x).1.trans (le_max_left _ _)) _))
  have T : Tendsto (fun r : ℕ => max (max (gC l ρ₁ x) (ρ₁ ^ r) ^ t * max (gC l ρ₂ x) (ρ₂ ^ r) ^ (1 - t)) (ρ ^ r))
      atTop (𝓝 (max (max (gC l ρ₁ x) 0 ^ t * max (gC l ρ₂ x) 0 ^ (1 - t)) 0)) := by
    have t1 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ₁.le (h12.trans_lt h2)
    have t2 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ₂.le h2
    have t0 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le (hρhi.trans_lt h2)
    exact ((((tendsto_const_nhds.max t1).rpow_const (Or.inr ht0)).mul
      ((tendsto_const_nhds.max t2).rpow_const (Or.inr ht1'))).max t0)
  have := ge_of_tendsto' T F
  rwa [max_eq_left (g₁.1 x).1, max_eq_left (g₂.1 x).1,
    max_eq_left (mul_nonneg (Real.rpow_nonneg (g₁.1 x).1 _) (Real.rpow_nonneg (g₂.1 x).1 _))] at this

end GlobalTheory.PMon.Gauss

end
end

section

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

theorem gA_teichmuller (ρ : ℝ) (y : Formalism.Per.Fl l) :
    gA l ρ (Formalism.Per.tm y) = ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have h : ∀ n : ℕ, ‖((((Formalism.Per.tm y : Formalism.Per.Ainf l).coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^
      ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n = if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0 := by
    intro n
    split_ifs with h
    · subst h
      simp
    · rw [WittVector.teichmuller_coeff_pos l y n (Nat.pos_of_ne_zero h), GlobalTheory.GaussSlope.untilt_zero]
      have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  unfold gA
  simp only [h]
  have hall : ∀ n : ℕ, (if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0) ≤
      ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := fun n => by split_ifs <;> simp
  exact le_antisymm (ciSup_le hall)
    (le_ciSup_of_le (f := fun n : ℕ => if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0)
      ⟨_, Set.forall_mem_range.2 hall⟩ 0 (by simp))

theorem isGauss_unit_eq_one {ρ : ℝ} (hρ : 0 < ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    {x : Formalism.Per.Acris l} (hx : IsUnit x) : N x = 1 := by
  obtain ⟨h01, -, -, hmul, halg⟩ := hN
  have hl : N (l : Formalism.Per.Acris l) = ρ := by
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, halg]
    exact GlobalTheory.GaussSlope.gauss_l l hρ.le
  have h1 : N 1 = 1 := by
    have := hmul (l : Formalism.Per.Acris l) 1
    rw [mul_one, hl] at this
    exact (mul_left_cancel₀ hρ.ne' (this.symm.trans (mul_one ρ).symm))
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h2 := hmul x y
  rw [hy, h1] at h2
  refine le_antisymm (h01 x).2 ?_
  rw [h2]
  exact mul_le_of_le_one_right (h01 x).1 (h01 y).2

theorem gC_basic_values : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ 1 = 1 ∧ gC l ρ (l : Formalism.Per.Acris l) = ρ ∧ (∀ c : ℤ_[l], c ≠ 0 → gC l ρ (zc l c) = ρ ^ c.valuation) ∧ (∀ y : Formalism.Per.Fl l, gC l ρ (tc l y) = ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖) ∧ ∀ a : Formalism.Per.Ainf l, IsUnit a → gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = 1 := by
  intro l _ ρ h0 h1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  have hN := isGauss_gC_of_le l ρ h0 h1
  have hl : gC l ρ (l : Formalism.Per.Acris l) = ρ := by
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, hN.2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l hρ.le
  refine ⟨isGauss_unit_eq_one hρ hN isUnit_one, hl, fun c hc => ?_, fun y => ?_,
    fun a ha => isGauss_unit_eq_one hρ hN (ha.map _)⟩
  · have e : zc l c = (l : Formalism.Per.Acris l) ^ c.valuation * zc l (PadicInt.unitCoeff hc : ℤ_[l]) := by
      conv_lhs => rw [PadicInt.unitCoeff_spec hc]
      rw [map_mul, map_pow, map_natCast, mul_comm]
    rw [e, GlobalTheory.GaussSlope.map_pow_mul _ hN.2.2.2.1, hl,
      isGauss_unit_eq_one hρ hN ((PadicInt.unitCoeff hc).isUnit.map (zc l)), mul_one]
  · rw [tc, hN.2.2.2.2, gA_teichmuller]

end GlobalTheory.PMon.Gauss

end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Classical

noncomputable section

namespace GlobalTheory.TwistPotCrys

section

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    Br.loc D.nbr i w hw (rTwO D.nd i r x) =
      twistM (Br.loc D.nbr i w hw (rO D.nd i r x)) (Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ := by
  refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
  show (D.nbr i w hw).toLL ((((chiU D.nd i 1)⁻¹ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g)) a b) = _
  rw [map_mul]
  rfl

theorem matRep_loc_rO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    matRep (Br.loc D.nbr i w hw (rO D.nd i r x)) = (D.nbr i w hw).rep ((r x).comp (decS D.nd w)) := rfl

theorem isTwistRep_loc (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    IsTwistRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) := by
  refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
  rw [loc_rTwO]
  change ((((Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) •
      Br.loc D.nbr i w hw (rO D.nd i r x) g).mulVec v = _
  exact Matrix.smul_mulVec _ _ _

theorem continuous_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i)
    (hc : Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) :
    Continuous fun g => rTwO D.nd i r x g := by
  have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
    (D.nd.chi_cont i 1).comp continuous_inv
  refine (h1.smul hc).congr fun g => ?_
  simp [rTwO, twistM, rO]

end



theorem twist_potCrys : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (K' : FinExt (D.nd.l i))
    (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ))
    (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ),
    Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0 →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))) {c} →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) ∧
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
        (Sig0.image (fun a => a * c⁻¹)) := by
  intro D hT i w hw r x K' h hN hF hS Sig0 c hcont hpot hit hχpot hχit
  have hcO : Continuous fun g => rO D.nd i r x g := hcont
  have hcT := continuous_rTwO D i r x hcont
  rw [← matRep_loc_rO] at hpot hit
  exact (hT (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS
      (GlobalTheory.PotDual.bundle _ _ (Br.loc D.nbr i w hw (rO D.nd i r x)) (GlobalTheory.PotDual.continuous_loc D i w hw _ hcO))
      (GlobalTheory.PotDual.bundle _ _ (Br.loc D.nbr i w hw (rTwO D.nd i r x)) (GlobalTheory.PotDual.continuous_loc D i w hw _ hcT))
      Sig0 (Sig0.image (fun a => a * c⁻¹)) hpot hit).1 _ c (isTwistRep_loc D i w hw r x) hχpot hχit
      (fun b => by
        rw [Finset.mem_image]
        exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩⟩)

end GlobalTheory.TwistPotCrys

end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.Quad

theorem length_torsionBy_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : O) :
    Module.length O (Submodule.torsionBy O (KOG O 1) a) ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  rcases eq_or_ne a 0 with rfl | ha
  · have e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O := Submodule.quotEquivOfEqBot _ (by simp)
    rw [e.length_eq]
    have : Module.length O O = ⊤ := by
      by_contra h
      have h2 := (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).2
      have : IsArtinianRing O := h2
      exact IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)
    rw [this]; exact le_top
  · have ha' : algebraMap O (FractionRing O) a ≠ 0 := by
      simpa using ha
    let x : KOG O 1 := Submodule.Quotient.mk fun _ => (algebraMap O (FractionRing O) a)⁻¹
    have hx : a • x = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨fun _ => 1, ?_⟩
      funext j
      simp [Algebra.smul_def, mul_inv_cancel₀ ha']
    let x' : Submodule.torsionBy O (KOG O 1) a := ⟨x, hx⟩
    let f : O →ₗ[O] Submodule.torsionBy O (KOG O 1) a := LinearMap.toSpanSingleton O _ x'
    have hf : Ideal.span {a} ≤ LinearMap.ker f := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Subtype.ext hx
    refine Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_
    rintro ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨b, hb⟩ := hy
      refine ⟨Submodule.Quotient.mk (b 0), Subtype.ext ?_⟩
      change b 0 • x = Submodule.Quotient.mk y
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      have h0 : algebraMap O (FractionRing O) (b 0) = algebraMap O (FractionRing O) a * y 0 := by
        simpa [Algebra.smul_def] using congrFun hb 0
      simp only [Pi.smul_apply, Algebra.smul_def, h0]
      field_simp

theorem eq_zero_of_tameGen {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {γ : G E Ω} (hγ : TameGenAt A γ) {M : Type} [AddCommGroup M] (f : G E Ω → M)
    (hf : IsLocallyConstant f) (hadd : ∀ a ∈ Ine (F := E) A, ∀ b ∈ Ine (F := E) A, f (a * b) = f a + f b)
    (hw : ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → f σ = 0) (h0 : f γ = 0)
    (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) : f σ = 0 := by
  have h1 : f 1 = 0 := by simpa using hadd 1 (one_mem _) 1 (one_mem _)
  let K : Subgroup (G E Ω) :=
    { carrier := {g | g ∈ Ine (F := E) A ∧ f g = 0}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨one_mem _, h1⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have := hadd a ha.1 a⁻¹ (inv_mem ha.1)
        rw [mul_inv_cancel, h1, ha.2, zero_add] at this
        exact this.symm⟩ }
  refine closure_minimal (t := {g | f g = 0}) ?_ (hf.isClosed_fiber 0) (hγ.2 hσ)
  intro g hg
  refine ((Subgroup.closure_le K).2 ?_ hg).2
  rintro g (rfl | hg)
  · exact ⟨hγ.1, h0⟩
  · exact ⟨GlobalTheory.TameCharUnique.mem_Ine_of_wild hg, hw g hg⟩

theorem psiChi_group {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}
    (hS : GoodCongruenceObjects D.nd r ρ π S) (c : Fin D.R.t) (g : GE D.nd) :
    S.ψχ c (fun x' => rO D.nd i r (S.p x') g) = ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g :=
    ⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩
  have a1 := h1 g (S.e.symm (0, fun _ => 1))
  have a2 := h2 _ hg (S.e.symm (0, fun _ => 1))
  simp only [hp] at a2
  have a3 := congrFun (congrArg Prod.snd (a2.symm.trans a1)) c
  simp only [LinearEquiv.apply_symm_apply, mul_one] at a3
  exact IsFractionRing.injective _ _ a3

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  intro D i r ρ π Xs S hr hS hπ v hv hq c
  have hl := D.nd.SQ_l i v hv
  have hchi : ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chiU D.nd i ((c : ℕ) + 1) γ = chiU D.nd i 1 γ :=
    fun γ hγ => (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v hl γ hγ).2 _ (by omega) c.2
  have hγ0 := D.nd.locNd_chebotarevPlace_mem i v
  have htor : ∀ f ∈ cocChi i r S Xs c, (D.nd.zeta i v - 1) • f (D.nd.gam0 i v) = 0 := by
    intro f hf
    have := Check.cocW_quad i r S Xs _ hq hf _ hγ0
    rw [Check.matKO_smul_one, psiChi_group hS, hchi _ hγ0] at this
    rw [sub_smul, one_smul, sub_eq_zero]
    exact this
  have hdet : ∀ f ∈ cocChi i r S Xs c, f (D.nd.gam0 i v) = 0 →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f σ = 0 := by
    intro f hf h0
    obtain ⟨hc, hz⟩ := (GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).2 c hf
    have : DiscreteTopology (KOG (D.nd.O i) 1) := ⟨rfl⟩
    have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 hc
    have hadd : ∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
        f (a * b) = f a + f b := by
      intro a ha b _
      have e : chiRatO D.nd i ((c : ℕ) + 1) a = (1 : D.nd.O i) • 1 := by
        change (((chiU D.nd i ((c : ℕ) + 1) a * (chiU D.nd i 1 a)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
          (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) = _
        rw [hchi a ha, mul_inv_cancel, Units.val_one]
      rw [hz, Check.WKG_eq_matKO, e, Check.matKO_smul_one, one_smul]
    exact eq_zero_of_tameGen (D.nd.restN_tameGenerator_generates i v hv) f hlc hadd (GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant D i v hl f hlc hadd) h0
  refine le_trans ?_ (length_torsionBy_le (D.nd.zeta i v - 1))
  refine Module.length_le_of_injective
    (LinearMap.restrict (LinearMap.proj (⟨D.nd.gam0 i v, hγ0⟩ : Ine (F := D.host.E) (D.nd.plOm.1 v))) ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact htor f hf
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, f, hf, rfl⟩ h0
    refine Subtype.ext (funext fun σ => ?_)
    exact hdet f hf (congrArg Subtype.val h0) σ.1 σ.2

end GlobalTheory.Cut.Quad
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem _root_.GlobalTheory.T.exists_padic_basis_galoisLattice_same_matrices : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ bV : Module.Basis (Fin d) ℚ_[l] T.V, ∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (bV.repr (T.ρ g (bV j)) i) := by
  first | exact @GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat | exact GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat | (intros; apply GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_letter_bijection {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) :
    ∃ τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K)),
      Function.Bijective τ ∧ (∀ i, (S.W H).emb (τ i) = S.emb i) ∧ ∀ i, τ (i - 1) = τ i - 1 := by
  obtain ⟨-, -, -, hSb, hSσ, -⟩ := S.hyp.1
  have hWb := (S.W H).emb_bij
  have hWσ := (S.W H).emb_σ
  have key : ∀ j, (S.W H).emb ((Equiv.ofBijective _ hWb).symm j) = j :=
    Equiv.ofBijective_apply_symm_apply _ hWb
  refine ⟨fun i => (Equiv.ofBijective _ hWb).symm (S.emb i),
    (Equiv.ofBijective _ hWb).symm.bijective.comp hSb, fun i => key _, fun i => hWb.1 ?_⟩
  calc (S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb (i - 1)))
      = S.emb (i - 1) := key _
    _ = (S.emb (i - 1 + 1)).comp (P.PD S.K).σ := (hSσ _).symm
    _ = ((S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb i))).comp (P.PD S.K).σ := by
        rw [sub_add_cancel, key]
    _ = (S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb i) - 1) := by
        rw [← hWσ ((Equiv.ofBijective _ hWb).symm (S.emb i) - 1), sub_add_cancel]

end GlobalTheory.RedFun
end
