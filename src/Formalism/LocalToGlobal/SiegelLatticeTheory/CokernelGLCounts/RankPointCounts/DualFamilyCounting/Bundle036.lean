module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle033
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExtensionIdentityOfMemCompl
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
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
import Mathlib.Tactic.Lemma
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Finset

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ltSigma (r : ℕ) : LsNc5.LtPair r ≃ Σ a : Fin r, Fin a.val where
  toFun p := ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
  invFun q := ⟨(⟨q.2.val, lt_trans q.2.isLt q.1.isLt⟩, q.1), q.2.isLt⟩
  left_inv p := by rcases p with ⟨⟨b, a⟩, h⟩; rfl
  right_inv q := by rcases q with ⟨a, b⟩; rfl

theorem sum_lt (r : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ p : LsNc5.LtPair r, g p.1.1.val p.1.2.val = ∑ a ∈ range r, ∑ b ∈ range a, g b a := by
  rw [Fintype.sum_equiv (ltSigma r) (fun p => g p.1.1.val p.1.2.val) (fun q => g q.2.val q.1.val) (fun _ => rfl),
    Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range a, g b a) r]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun b => g b a.val) a.val

theorem sum_id_real (a : ℕ) : ∑ b ∈ range a, (b : ℝ) = a * (a - 1) / 2 := by
  induction a with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem card_lt (r : ℕ) : (Fintype.card (LsNc5.LtPair r) : ℝ) = r * (r - 1) / 2 := by
  have h := sum_lt r (fun _ _ => 1)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Finset.card_univ] at h
  rw [h]
  exact sum_id_real r

theorem card_lt_nat (r : ℕ) : Fintype.card (LsNc5.LtPair r) = r * (r - 1) / 2 := by
  have h2 : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self r).two_dvd
  have : ((r * (r - 1) / 2 : ℕ) : ℝ) = r * (r - 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    rcases Nat.eq_zero_or_pos r with h0 | hp
    · rw [h0]; simp
    · rw [Nat.cast_mul, Nat.cast_sub hp]; push_cast; ring
  exact_mod_cast (card_lt r).trans this.symm

theorem sumX (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range a, ((1 : ℝ) - 2 * ((a : ℝ) - b)) =
    -((n - 1) * n * (2 * n - 1) / 6) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sum_id_real]
    push_cast; ring

theorem sumK (R : ℝ) (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range a, ((1 : ℝ) - 2 * (R - b) - 2 * (R - a)) =
    3 * ((n - 1) * n * (2 * n - 1) / 6) - 4 * R * (n * (n - 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : ∑ b ∈ range n, ((1 : ℝ) - 2 * (R - b) - 2 * (R - n)) =
        ∑ b ∈ range n, ((1 - 4 * R + 2 * (n : ℝ)) + 2 * (b : ℝ)) :=
      Finset.sum_congr rfl fun b _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, sum_id_real]
    push_cast; ring

theorem sumR (R K : ℝ) (n : ℕ) : ∑ b ∈ range n, ((K + 1) * (1 - 2 * (R - b))) = (K + 1) * (n - 2 * R * n + n * (n - 1)) := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sum_id_real]
  push_cast; ring

theorem sumD (R : ℝ) (n : ℕ) : ∑ a ∈ range n, ((1 / 2 : ℝ) - 2 * (R - a)) = n / 2 - 2 * R * n + n * (n - 1) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, sum_id_real]
  push_cast; ring

theorem prod_const_rpow {ι : Type*} (s : Finset ι) {c d : ℝ} (hd : 0 < d) (e : ι → ℝ) :
    ∏ x ∈ s, (c * d ^ e x) = c ^ s.card * d ^ (∑ x ∈ s, e x) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Real.rpow_sum_of_pos hd]

theorem half_succ (R : ℕ) : R * (R - 1) / 2 + R = R * (R + 1) / 2 := by
  rcases Nat.eq_zero_or_pos R with h0 | hp
  · subst h0; simp
  · obtain ⟨m, rfl⟩ : ∃ m, R = m + 1 := ⟨R - 1, by omega⟩
    rw [Nat.add_sub_cancel, show (m + 1) * (m + 1 + 1) = (m + 1) * m + (m + 1) * 2 by ring,
      Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]

theorem final_alg (t d : ℝ) (hd : 0 < d) (F R K : ℕ) (A B C E : ℝ)
    (h : A + B + C + E = LsNc5.covolumeExponent R K) :
    ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ A * ((t ^ F * (2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * d ^ B) *
        (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ C * d ^ E) =
      t ^ (R * F) * (2 : ℝ) ^ (-((F * (R * K + R * (R - 1) / 2) : ℕ) : ℝ)) * d ^ LsNc5.covolumeExponent R K /
        (2 : ℝ) ^ (F * (R * (R + 1) / 2)) := by
  have hd' : d ^ A * d ^ B * d ^ C * d ^ E = d ^ LsNc5.covolumeExponent R K := by
    rw [← h, Real.rpow_add hd, Real.rpow_add hd, Real.rpow_add hd]
  have h2 : ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * ((2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) =
      (2 : ℝ) ^ (-((F * (R * K + R * (R - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (F * (R * (R + 1) / 2)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, div_eq_mul_inv, ← inv_pow, ← inv_pow, ← pow_add,
      ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← half_succ]
    congr 1
    ring
  calc ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ A * ((t ^ F * (2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * d ^ B) *
        (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ C * d ^ E)
      = t ^ (R * F) * (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * ((2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R *
          ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2)) * (d ^ A * d ^ B * d ^ C * d ^ E) := by ring
    _ = _ := by rw [h2, hd']; ring

theorem cVal_prod {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    ∏ p, cVal X u p = LsNc5.covolN X u / LsNc5.twoU X := by
  have hd0 : 0 < |(NumberField.discr X.B.I.F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have hT : 0 < Tw (D := D) u := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos u
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [cVal]
  rw [prod_const_rpow _ hd0, prod_const_rpow _ hd0, prod_const_rpow _ hd0, ← Real.rpow_sum_of_pos hd0]
  have eX := sum_lt D.R.rS (fun b a => (1 : ℝ) - 2 * ((a : ℝ) - b))
  have eK := sum_lt D.R.rS (fun b a => (1 : ℝ) - 2 * ((D.R.rS : ℝ) - b) - 2 * ((D.R.rS : ℝ) - a))
  have eR : ∑ b : Fin D.R.rS, (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ)))) =
      ∑ b ∈ range D.R.rS, (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - b))) :=
    Fin.sum_univ_eq_sum_range (fun b => ((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - b))) D.R.rS
  have eD : ∑ a : Fin D.R.rS, ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - (a : ℕ))) =
      ∑ a ∈ range D.R.rS, ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - a)) :=
    Fin.sum_univ_eq_sum_range (fun a => (1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - a)) D.R.rS
  simp only [Finset.card_univ]
  rw [eX, eK, eR, eD, sumX, sumK, sumR, sumD, card_lt_nat, Fintype.card_fin]
  unfold LsNc5.covolN LsNc5.twoU
  exact final_alg _ _ hd0 _ _ _ _ _ _ _ (by unfold LsNc5.covolumeExponent; ring)

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

section General

variable (F : Type) [Field F] [NumberField F]

abbrev mDiff (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors

lemma differentIdeal_ne_zero' : differentIdeal ℤ (𝓞 F) ≠ 0 := by
  exact differentIdeal_ne_bot

variable {F}

lemma pow_mDiff_dvd (v : HeightOneSpectrum (𝓞 F)) :
    v.asIdeal ^ mDiff F v ∣ differentIdeal ℤ (𝓞 F) := by
  have hD : Associates.mk (differentIdeal ℤ (𝓞 F)) ≠ 0 := Associates.mk_ne_zero.mpr (differentIdeal_ne_zero' F)
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  rw [← Associates.mk_dvd_mk, Associates.mk_pow]
  exact (Associates.prime_pow_dvd_iff_le hD hirr).mpr le_rfl

lemma not_pow_succ_mDiff_dvd (v : HeightOneSpectrum (𝓞 F)) :
    ¬ v.asIdeal ^ (mDiff F v + 1) ∣ differentIdeal ℤ (𝓞 F) := by
  have hD : Associates.mk (differentIdeal ℤ (𝓞 F)) ≠ 0 := Associates.mk_ne_zero.mpr (differentIdeal_ne_zero' F)
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  intro h
  rw [← Associates.mk_dvd_mk, Associates.mk_pow] at h
  have := (Associates.prime_pow_dvd_iff_le hD hirr).mp h
  exact Nat.lt_irrefl _ (Nat.lt_of_succ_le this)

lemma intValuation_le_of_mem_different (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F}
    (hx : x ∈ differentIdeal ℤ (𝓞 F)) : v.intValuation x ≤ exp (-(mDiff F v : ℤ)) := by
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd]
  exact dvd_trans (pow_mDiff_dvd v) (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx))

lemma exists_mem_different_intValuation_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x ∈ differentIdeal ℤ (𝓞 F), v.intValuation x = exp (-(mDiff F v : ℤ)) := by
  have hnot := not_pow_succ_mDiff_dvd v
  rw [Ideal.dvd_iff_le, IsConcreteLE.not_le_iff_exists] at hnot
  obtain ⟨x, hxD, hxv⟩ := hnot
  refine ⟨x, hxD, le_antisymm (intValuation_le_of_mem_different v hxD) ?_⟩
  have h1 : ¬ v.intValuation x ≤ WithZero.exp (-((mDiff F v + 1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem]
    exact hxv
  have hx0 : v.intValuation x ≠ 0 := by
    intro h0
    apply h1
    rw [h0]
    exact zero_le
  rw [← WithZero.exp_log hx0] at h1 ⊢
  rw [WithZero.exp_le_exp] at h1 ⊢
  push_cast at h1
  omega

lemma valued_algebraMap_coe (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := by
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)

lemma valued_dV (v : HeightOneSpectrum (𝓞 F)) : Valued.v (dV v) = exp (-(mDiff F v : ℤ)) := by
  obtain ⟨x, hxD, hxv⟩ := exists_mem_different_intValuation_eq v
  have hex : ∃ d, IsDiffVal v d := by
    refine ⟨algebraMap F (Fv F v) (x : F), ?_, ?_, x, hxD, rfl⟩
    · intro h0
      have := valued_algebraMap_coe v x
      rw [h0, map_zero, hxv] at this
      exact WithZero.exp_ne_zero this.symm
    · intro y hy
      rw [valued_algebraMap_coe, valued_algebraMap_coe, hxv]
      exact intValuation_le_of_mem_different v hy
  have hd : IsDiffVal v (dV v) := by
    unfold dV
    rw [dite_eq_left hex]
    exact hex.choose_spec
  obtain ⟨-, hle, y, hyD, hyv⟩ := hd
  apply le_antisymm
  · rw [← hyv, valued_algebraMap_coe]
    exact intValuation_le_of_mem_different v hyD
  · have := hle x hxD
    rwa [valued_algebraMap_coe, hxv] at this

lemma absV_of_valued_eq (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) (n : ℤ) (h : Valued.v x = exp n) :
    absV v x = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n := by
  have hx : Valued.v x ≠ 0 := by
    rw [h]
    exact WithZero.exp_ne_zero
  unfold absV
  rw [dite_eq_right hx]
  congr 1
  have hu : WithZero.unzero hx = Multiplicative.ofAdd n := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [hu, toAdd_ofAdd]

lemma absV_dV (v : HeightOneSpectrum (𝓞 F)) :
    absV v (dV v) = ((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 F))) : ℕ) : ℝ)⁻¹ := by
  rw [absV_of_valued_eq v _ _ (valued_dV v), IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow,
    zpow_neg, zpow_natCast, Nat.cast_pow]


variable (F) in
theorem hasProd_absV_dV :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => absV v (dV v)) (|(discr F : ℝ)|⁻¹) := by
  have hD := differentIdeal_ne_zero' F
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      v.maxPowDividing (differentIdeal ℤ (𝓞 F))).Finite := Ideal.hasFiniteMulSupport hD
  have hfac : ∏ v ∈ hfin.toFinset, v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = differentIdeal ℤ (𝓞 F) := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hfin.mem_toFinset.mpr hv)]
    exact Ideal.finprod_heightOneSpectrum_factorization hD
  have hone : ∀ v ∉ hfin.toFinset, absV v (dV v) = 1 := by
    intro v hv
    rw [absV_dV]
    have h1 : v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = 1 := by
      by_contra hc
      exact hv (hfin.mem_toFinset.mpr hc)
    rw [h1, map_one]
    simp
  have hval : ∏ v ∈ hfin.toFinset, absV v (dV v) = |(discr F : ℝ)|⁻¹ := by
    rw [Finset.prod_congr rfl (fun v _ => absV_dV v), Finset.prod_inv_distrib, ← Nat.cast_prod, ← map_prod, hfac,
      NumberField.absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, Int.cast_abs]
  have key : HasProd (fun v : HeightOneSpectrum (𝓞 F) => absV v (dV v)) (∏ v ∈ hfin.toFinset, absV v (dV v)) :=
    hasProd_prod_of_ne_finset_one hone
  rw [hval] at key
  exact key

end General

section Loc

variable {D : D7} (X : HidaSetting D)

theorem diffProd_holds : DiffProd X := by
  exact hasProd_absV_dV _

end Loc

end Formalism.L2.SG.Pf.NcVal
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual {Y : Type} [AddCommGroup Y] [Module K Y] [Module (𝓞 K) Y] [IsScalarTower (𝓞 K) K Y]
    {B : Y →ₗ⋆[K] Y →ₗ[K] K} {L : Submodule (𝓞 K) Y} {x : Y} :
    x ∈ Formalism.HermitianLatticesTheory.dual B L ↔ ∀ y ∈ L, B y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}

theorem push_dualIn (L : Submodule (𝓞 K) ↥X) :
    push X (dualIn (formOn h X) ⊤ L) = dualIn h X (push X L) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, mem_dual.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact mem_dual.mp hx.2 y hy
  · rintro ⟨hvX, hv⟩
    refine ⟨⟨v, hvX⟩, ⟨by simp, mem_dual.mpr fun y hy => ?_⟩, rfl⟩
    exact mem_dual.mp hv _ (coe_mem_push.mpr hy)

variable {𝔭 : Ideal (𝓞 F)}

theorem map_incl_dual (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    (locF 𝔭 (dualIn (formOn h X) ⊤ L)).map (incl X) = locF 𝔭 (dualIn h X (push X L)) := by
  change push X _ = _
  rw [push_locF X hp, push_dualIn]

def dualEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L)) ≃ₗ[𝓞 K] ↥(locF 𝔭 (dualIn h X (push X L))) :=
  (Submodule.equivMapOfInjective (incl X) (incl_injective X) _).trans
    (LinearEquiv.ofEq _ _ (map_incl_dual hp L))

theorem dualEquiv_apply (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (x : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) :
    ((dualEquiv (h := h) hp L x : ↥(locF 𝔭 (dualIn h X (push X L)))) : V) = ((x : ↥X) : V) := rfl

theorem dualEquiv_symm_apply (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (y : ↥(locF 𝔭 (dualIn h X (push X L)))) :
    ((((dualEquiv (h := h) hp L).symm y : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) : ↥X) : V) = (y : V) := by
  have := dualEquiv_apply hp L ((dualEquiv (h := h) hp L).symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem map_dualEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    ((locF 𝔭 L).comap (locF 𝔭 (dualIn (formOn h X) ⊤ L)).subtype).map
        (dualEquiv (h := h) hp L : _ →ₗ[𝓞 K] _) =
      (locF 𝔭 (push X L)).comap (locF 𝔭 (dualIn h X (push X L))).subtype := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext y
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  rw [← coe_mem_push (X := X), push_locF X hp]
  exact Iff.of_eq (congrArg (fun v => v ∈ locF 𝔭 (push X L)) (dualEquiv_symm_apply (h := h) hp L y))

def discEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    DiscMod (formOn h X) ⊤ L 𝔭 ≃ₗ[𝓞 K] DiscMod h X (push X L) 𝔭 :=
  Submodule.Quotient.equiv _ _ (dualEquiv (h := h) hp L) (map_dualEquiv (h := h) hp L)

theorem discEquiv_mk (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (x : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) :
    discEquiv (h := h) hp L (Submodule.Quotient.mk x) = Submodule.Quotient.mk (dualEquiv (h := h) hp L x) := rfl

theorem discEquiv_symm_mk (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (y : ↥(locF 𝔭 (dualIn h X (push X L)))) :
    (discEquiv (h := h) hp L).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y) := rfl

def endEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    Module.End (𝓞 K) (DiscMod (formOn h X) ⊤ L 𝔭) ≃ Module.End (𝓞 K) (DiscMod h X (push X L) 𝔭) where
  toFun P := (discEquiv (h := h) hp L : _ →ₗ[𝓞 K] _) ∘ₗ P ∘ₗ ((discEquiv (h := h) hp L).symm : _ →ₗ[𝓞 K] _)
  invFun P := ((discEquiv (h := h) hp L).symm : _ →ₗ[𝓞 K] _) ∘ₗ P ∘ₗ (discEquiv (h := h) hp L : _ →ₗ[𝓞 K] _)
  left_inv P := by
    apply LinearMap.ext
    intro z
    simp
  right_inv P := by
    apply LinearMap.ext
    intro z
    simp

theorem discAut_push (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    discAut h X (push X L) 𝔭 = discAut (formOn h X) ⊤ L 𝔭 := by
  unfold discAut
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (endEquiv (h := h) hp L) ?_)
  intro P
  constructor
  · intro H x y x' y' hx hy
    have hx' : Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm x') =
        P (Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm x)) := by
      rw [← discEquiv_symm_mk, hx, ← discEquiv_symm_mk]
      change (discEquiv (h := h) hp L).symm ((discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm _))) = _
      rw [LinearEquiv.symm_apply_apply]
    have hy' : Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y') =
        P (Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y)) := by
      rw [← discEquiv_symm_mk, hy, ← discEquiv_symm_mk]
      change (discEquiv (h := h) hp L).symm ((discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm _))) = _
      rw [LinearEquiv.symm_apply_apply]
    have := H _ _ _ _ hx' hy'
    simpa only [formOn_apply, dualEquiv_symm_apply] using this
  · intro H x y x' y' hx hy
    have hx' : Submodule.Quotient.mk (dualEquiv (h := h) hp L x') =
        (endEquiv (h := h) hp L P) (Submodule.Quotient.mk (dualEquiv (h := h) hp L x)) := by
      change _ = (discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm (Submodule.Quotient.mk _)))
      rw [discEquiv_symm_mk, LinearEquiv.symm_apply_apply, ← hx, discEquiv_mk]
    have hy' : Submodule.Quotient.mk (dualEquiv (h := h) hp L y') =
        (endEquiv (h := h) hp L P) (Submodule.Quotient.mk (dualEquiv (h := h) hp L y)) := by
      change _ = (discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm (Submodule.Quotient.mk _)))
      rw [discEquiv_symm_mk, LinearEquiv.symm_apply_apply, ← hy, discEquiv_mk]
    have := H _ _ _ _ hx' hy'
    simpa only [formOn_apply, dualEquiv_apply] using this

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
end
end
