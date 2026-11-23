module

public import Formalism.TorsionNormIteration.InvIntegralOfClass
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
public import Mathlib.RingTheory.PowerSeries.Expand
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

@[expose] public section

section

noncomputable section

universe u v

namespace Formalism.LT.SolveP

open PowerSeries

theorem SolveExists_proof : Formalism.LT.SolveExists.{u, v} := by
  intro R _ ι _ f G hf0 hf1 hG0
  have hu : IsUnit (coeff 1 f) := by rw [hf1]; exact isUnit_one
  set g := f.substInvOfIsUnit hu with hg
  have hgS : HasSubst g := HasSubst.substInvOfIsUnit f hu
  have hGS : HasSubst G := HasSubst.of_constantCoeff_zero hG0
  refine ⟨g.subst G, ?_, ?_⟩
  · exact constantCoeff_subst_eq_zero hG0 g (constantCoeff_substInvOfIsUnit f hu)
  · rw [← subst_comp_subst_apply hgS hGS, subst_substInvOfIsUnit_right f hf0 hu, subst_X hGS]

end Formalism.LT.SolveP

theorem Formalism.LT.SolveExists_proof : Formalism.LT.SolveExists.{u, v} := Formalism.LT.SolveP.SolveExists_proof
end
end

section

noncomputable section

open PowerSeries

universe u v

namespace Formalism.LT

open Formalism.G

namespace InverseIntegralClassesKeyFacts

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_finsum_le {g : ℕ → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC

lemma norm_add_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a + b‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

lemma norm_sub_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a - b‖ ≤ C := by
  rw [sub_eq_add_neg]; exact norm_add_le_of ha (by simpa using hb)

lemma norm_sigma_le_one {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp1 : ‖(p : K)‖ ≤ 1)
    {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ 1 := (hσ a ha).trans hp1
  have h2 : ‖a ^ q‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have : σ a = (σ a - a ^ q) + a ^ q := by ring
  rw [this]; exact norm_add_le_of h1 h2

end InverseIntegralClassesKeyFacts

open InverseIntegralClassesKeyFacts

theorem FunEqSubst_of (h4 : Formalism.LT.IntegralSubst.{u, v}) (h5 : Formalism.LT.CoeffBound.{u})
    (h6 : Formalism.LT.PowCongr.{u, v}) (h7 : Formalism.LT.FrobCongr.{u, v}) : Formalism.G.FunEqSubst.{u, v} := by
  intro K _ _ _ p q hq σ hS f hf0 hfT ι α hα0 hαI
  obtain ⟨hp, ⟨h, hh, hqh⟩, hp1, hσ⟩ := id hS
  have hp1' : ‖(p : K)‖ ≤ 1 := hp1.le
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hppos : 0 < ‖(p : K)‖ := norm_pos_iff.mpr hpne

  set fs : PowerSeries K := PowerSeries.map σ f with hfs
  set g : PowerSeries K := f - (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) with hg
  set β : MvPowerSeries ι K := MvPowerSeries.expand q hq (MvPowerSeries.map σ α) with hβ
  have hαS : PowerSeries.HasSubst α := HasSubst.of_constantCoeff_zero hα0
  have hαq0 : MvPowerSeries.constantCoeff (α ^ q) = 0 := by
    rw [map_pow, hα0, zero_pow hq]
  have hαqS : PowerSeries.HasSubst (α ^ q) := HasSubst.of_constantCoeff_zero hαq0
  have hmα0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ α) = 0 := by
    simp [hα0]
  have hmαS : PowerSeries.HasSubst (MvPowerSeries.map σ α) := HasSubst.of_constantCoeff_zero hmα0
  have hβ0 : MvPowerSeries.constantCoeff β = 0 := by
    rw [hβ, MvPowerSeries.constantCoeff_expand, hmα0]
  have hβS : PowerSeries.HasSubst β := HasSubst.of_constantCoeff_zero hβ0
  have hXqS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries K) ^ q) :=
    HasSubst.of_constantCoeff_zero' (by simp [hq])

  have hdec : f.subst α - (p : K)⁻¹ • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α))
      = g.subst α + (p : K)⁻¹ • (fs.subst (α ^ q) - fs.subst β) := by
    have e1 : f = g + (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) := by
      rw [hg]; abel
    have e2 : PowerSeries.subst α (fs.subst ((PowerSeries.X : PowerSeries K) ^ q) : PowerSeries K) = fs.subst (α ^ q) := by
      rw [PowerSeries.subst_comp_subst_apply hXqS hαS, PowerSeries.subst_pow hαS,
        PowerSeries.subst_X hαS]
    have e3 : MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α)) = fs.subst β := by
      rw [PowerSeries.map_subst hαS, PowerSeries.expand_subst q hq hmαS]
    have e4 : f.subst α = g.subst α + (p : K)⁻¹ • fs.subst (α ^ q) := by
      conv_lhs => rw [e1]
      rw [PowerSeries.subst_add hαS, PowerSeries.subst_smul hαS, e2]
    rw [e3, e4, smul_sub]; abel

  have hXqI : IntegralPS ((PowerSeries.X : PowerSeries K) ^ q) := by
    intro n
    rw [PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  have hαqI : IntegralMv (α ^ q) := by
    have := h4 K ι _ α hXqI hα0 hαI
    rwa [PowerSeries.subst_pow hαS, PowerSeries.subst_X hαS] at this
  have hdiv : DivByMv (p : K) (α ^ q - β) := h7 K p q hq σ hS ι α hαI
  have hβI : IntegralMv β := by
    intro d
    have e : MvPowerSeries.coeff d β
        = MvPowerSeries.coeff d (α ^ q) - MvPowerSeries.coeff d (α ^ q - β) := by
      rw [map_sub]; ring
    rw [e]
    exact norm_sub_le_of (hαqI d) ((hdiv d).trans hp1')
  have hgI : IntegralMv (g.subst α) := h4 K ι g α hfT hα0 hαI

  have hbr : ∀ d, ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖ ≤ ‖(p : K)‖ := by
    intro d
    rw [map_sub, PowerSeries.coeff_subst hαqS, PowerSeries.coeff_subst hβS,
      ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hαqS fs d)
        (PowerSeries.coeff_subst_finite hβS fs d)]
    apply norm_finsum_le (norm_nonneg _)
    intro n
    rw [← smul_sub, ← map_sub, smul_eq_mul, norm_mul, hfs, PowerSeries.coeff_map]
    obtain ⟨k, hkdvd, hk⟩ := h5 K p q σ hS f hf0 hfT n
    obtain ⟨m, rfl⟩ := hkdvd
    have hn : q ^ k * m = p ^ (h * k) * m := by rw [hqh, ← pow_mul]
    have hdiv' : DivByMv ((p : K) ^ 1) (α ^ q - β) := by simpa using hdiv
    have hc0 := h6 K ι p hp (α ^ q) β hαqI hβI 1 le_rfl hdiv' (h * k) m d
    rw [← hn] at hc0
    have hs : ‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k ≤ 1 := by
      have h0 : ‖coeff (q ^ k * m) f * (p : K) ^ k‖ ≤ 1 := by rw [norm_mul, norm_pow]; exact hk
      have h' := norm_sigma_le_one hσ hp1' h0
      rwa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h'
    have hc : ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ := by
      refine hc0.trans ?_
      rw [norm_pow, pow_add, pow_one, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (norm_nonneg _) hp1' (Nat.le_mul_of_pos_left k hh)) (norm_nonneg _)
    calc ‖σ (coeff (q ^ k * m) f)‖ * ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖σ (coeff (q ^ k * m) f)‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖) :=
          mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ = (‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ := by ring
      _ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _

  unfold IsFunEqTypeMv
  rw [hdec]
  intro d
  rw [map_add (f := _), MvPowerSeries.coeff_smul]
  refine norm_add_le_of (hgI d) ?_
  rw [norm_mul, norm_inv]
  calc ‖(p : K)‖⁻¹ * ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖
      ≤ ‖(p : K)‖⁻¹ * ‖(p : K)‖ := mul_le_mul_of_nonneg_left (hbr d) (inv_nonneg.mpr (norm_nonneg _))
    _ = 1 := inv_mul_cancel₀ hppos.ne'

end Formalism.LT
end
end

section

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.Asm

open Formalism.G

section Integral

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem integralMv_add {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a + b) := by
  intro d
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) (hb d))

theorem integralMv_sub {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a - b) := by
  intro d
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) ?_)
  rw [norm_neg]
  exact hb d

theorem integralMv_X {ι : Type*} (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem funEqMv_add {ι : Type*} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K) {a b : MvPowerSeries ι K}
    (ha : IsFunEqTypeMv p q hq σ a) (hb : IsFunEqTypeMv p q hq σ b) :
    IsFunEqTypeMv p q hq σ (a + b) := by
  unfold IsFunEqTypeMv at *
  convert integralMv_add ha hb using 1
  simp only [map_add (f := _), smul_add]
  abel

theorem funEqMv_sub {ι : Type*} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K) {a b : MvPowerSeries ι K}
    (ha : IsFunEqTypeMv p q hq σ a) (hb : IsFunEqTypeMv p q hq σ b) :
    IsFunEqTypeMv p q hq σ (a - b) := by
  unfold IsFunEqTypeMv at *
  convert integralMv_sub ha hb using 1
  simp only [map_sub, smul_sub]
  abel

end Integral

theorem q_ne_zero {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : q ≠ 0 := by
  obtain ⟨hp, ⟨k, -, rfl⟩, -⟩ := h
  exact pow_ne_zero _ hp.ne_zero

theorem two_le_q {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : 2 ≤ q := by
  obtain ⟨hp, ⟨k, hk, rfl⟩, -⟩ := h
  exact hp.two_le.trans (Nat.le_self_pow (by omega) _)

theorem funEqInv (h2 : InvIntegralOfClass.{u, 0}) (h3 : FunEqLowCoeff.{u, 0})
    (hk : Formalism.G.FunEqSubst.{u, 0})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {p q : ℕ} {σ : K →+* K}
    (hS : FunctionalEquationSetting K p q σ) {ι : Type} [Finite ι] {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hfE : IsFunEqType p q σ f)
    (h : MvPowerSeries ι K) (hh0 : MvPowerSeries.constantCoeff h = 0)
    (hC : IsFunEqTypeMv p q (q_ne_zero hS) σ (f.subst h)) : IntegralMv h :=
  h2 K ι (IsFunEqTypeMv p q (q_ne_zero hS) σ) f hf0 hf1
    (fun _ _ ha hb => funEqMv_sub _ _ ha hb)
    (fun P hP0 hPI => hk K p q (q_ne_zero hS) σ hS f hf0 hfE ι P hP0 hPI)
    (fun D hD N hN hlow d hd => h3 K ι p q (q_ne_zero hS) σ (two_le_q hS) D hD N hN hlow d hd)
    h hh0 hC

theorem FunEqGroup_of' (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} := by
  intro K _ _ _ p q σ hS f hf0 hf1 hfE
  have hq := q_ne_zero hS
  have hG0 : MvPowerSeries.constantCoeff (atX f + atY f) = 0 := by
    rw [map_add (f := _), atX, atY, PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0,
      PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0, add_zero]
  have hGE : IsFunEqTypeMv p q hq σ (atX f + atY f) :=
    funEqMv_add hq σ (hk K p q hq σ hS f hf0 hfE (Fin 2) _ (by simp) (integralMv_X 0))
      (hk K p q hq σ hS f hf0 hfE (Fin 2) _ (by simp) (integralMv_X 1))
  obtain ⟨F, hF0, hF⟩ := h1 K (Fin 2) f (atX f + atY f) hf0 hf1 hG0
  refine ⟨F, hF0, funEqInv h2 h3 hk hS hf0 hf1 hfE F hF0 ?_, hF⟩
  rw [hF]
  exact hGE

theorem funEqType_unit {K : Type u} [NormedField K] {p q : ℕ} (hq : q ≠ 0) {σ : K →+* K}
    {g : PowerSeries K} (hg : IsFunEqType p q σ g) :
    IsFunEqTypeMv (ι := Unit) p q hq σ (g : MvPowerSeries Unit K) := by
  have hx : (PowerSeries.map σ g).subst ((PowerSeries.X : PowerSeries K) ^ q) =
      MvPowerSeries.expand q hq (MvPowerSeries.map σ g) := by
    rw [← PowerSeries.expand_apply q hq]
    rfl
  intro d
  have := hg (d ())
  rw [hx] at this
  have hd : d = Finsupp.single () (d ()) := by
    ext
    simp
  rw [hd]
  exact this

theorem FunEqHom_of' (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} := by
  intro K _ _ _ p q σ hS f g hf0 hf1 hfE hg0 hgE
  obtain ⟨h, hh0, hh⟩ := h1 K Unit f (g : MvPowerSeries Unit K) hf0 hf1 hg0
  have hI : IntegralMv h := funEqInv h2 h3 hk hS hf0 hf1 hfE h hh0 (by
    rw [hh]
    exact funEqType_unit (q_ne_zero hS) hgE)
  exact ⟨h, hh0, fun n => hI _, hh⟩

section FG

open Formalism.G.LogP

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

end FG

end Formalism.LT.Asm

namespace Formalism.LT

theorem FunEqGroup_of (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} :=
  Formalism.LT.Asm.FunEqGroup_of' h1 h2 h3 hk

theorem FunEqHom_of (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} :=
  Formalism.LT.Asm.FunEqHom_of' h1 h2 h3 hk

end Formalism.LT
end
end
