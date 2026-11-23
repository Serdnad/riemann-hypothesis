module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RunParametersOfLower

theorem real_bounds (f r m ρ w D q t : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hm : 1 ≤ m) (hmf : m ≤ f)
    (hf2 : f ^ 2 ≤ ρ) (hρ : 16 ≤ ρ) (hw0 : 0 ≤ w) (hw : w ≤ f ^ 2) (hD : 1 ≤ D)
    (hq : (ρ ^ 7) ^ 4 * (90 * (f * r + D)) * D * r ≤ q)
    (ht : t = q * (q / (90 * (f * r + D) * (ρ ^ 7) ^ 4))) :
    (2 * f * m) ^ 2 * (2 * w * ρ) * (f * (90 * (f * r + D)) * (ρ ^ 7) ^ 3) < q ∧
    1 ≤ q / (90 * (f * r + D) * (ρ ^ 7) ^ 4) ∧
    90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ q / 2 ∧ D ≤ q ∧
    4 * D * (7 + Real.log (q * D)) + 2 * f * m + 1 ≤ t ∧
    f * r * Real.log 2 + 2 * (2 * f * m) + 3 + (D + 1) * (r * Real.log r + 3 * r + 3) ≤ t := by
  have hρ1 : (1 : ℝ) ≤ ρ := by linarith
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hN : r ≤ f * r := by nlinarith
  have hN1 : 1 ≤ f * r := by linarith
  have hfρ : f ≤ ρ := by nlinarith
  have hfm : f * m ≤ ρ := by nlinarith
  have hm2 : m ^ 2 ≤ ρ := by nlinarith
  have hd0 : 0 ≤ 2 * f * m := by positivity
  have hd : 2 * f * m ≤ 2 * ρ := by linarith
  have hwρ : w ≤ ρ := hw.trans hf2
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlogr : Real.log r ≤ r := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < r by linarith); linarith
  have h3' : f * r * Real.log 2 ≤ f * r * 1 := by gcongr
  obtain ⟨N, hNdef⟩ : ∃ N, N = f * r := ⟨_, rfl⟩
  rw [← hNdef] at hq ht hN hN1 h3' ⊢
  obtain ⟨S, hS⟩ : ∃ S, S = 90 * (N + D) := ⟨_, rfl⟩
  rw [← hS] at hq ht ⊢
  have hS180 : 180 ≤ S := by linarith
  have hS0 : 0 < S := by linarith
  have hB : 0 < S * (ρ ^ 7) ^ 4 := by positivity
  have hDr : 1 ≤ D * r := one_le_mul_of_one_le_of_one_le hD hr
  have hDDr : D ≤ D * r := by nlinarith
  have hrDr : r ≤ D * r := by nlinarith
  have hq' : D * r * (S * (ρ ^ 7) ^ 4) ≤ q := by linarith
  have hBq : S * (ρ ^ 7) ^ 4 ≤ q := by
    have := mul_le_mul_of_nonneg_right hDr hB.le
    linarith
  have hq0 : 0 < q := by linarith
  have hb : D * r ≤ q / (S * (ρ ^ 7) ^ 4) := by rw [le_div_iff₀ hB]; exact hq'
  have htq : q * (D * r) ≤ t := by rw [ht]; gcongr
  have hT : ρ ^ 5 ≤ (ρ ^ 7) ^ 4 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hρ1 (by norm_num)
  have hT4 : 16 * ρ ^ 4 ≤ ρ ^ 5 := by
    rw [pow_succ' ρ 4]; gcongr
  have hT1 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have hqT : 180 * (ρ ^ 7) ^ 4 ≤ q := by
    have : 180 * (ρ ^ 7) ^ 4 ≤ S * (ρ ^ 7) ^ 4 := by gcongr
    linarith
  have hSρ : S * ρ ≤ q := by
    have : S * ρ ≤ S * (ρ ^ 7) ^ 4 := by
      have : ρ ≤ (ρ ^ 7) ^ 4 := by linarith
      gcongr
    linarith
  have hS16 : S * 16 ≤ S * ρ := by gcongr
  have hDq : D ≤ q := by linarith
  refine ⟨?_, by linarith, ?_, hDq, ?_, ?_⟩
  · have h1 : (2 * f * m) ^ 2 * (2 * w * ρ) * (f * S * (ρ ^ 7) ^ 3) ≤
        (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * S * (ρ ^ 7) ^ 3) := by
      gcongr
    have h2 : (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * S * (ρ ^ 7) ^ 3) = 8 * (S * ρ ^ 26) := by ring
    have h3 : S * (ρ ^ 7) ^ 4 = ρ ^ 2 * (S * ρ ^ 26) := by ring
    have h4 : 0 < S * ρ ^ 26 := by positivity
    have h5 : 8 * (S * ρ ^ 26) < ρ ^ 2 * (S * ρ ^ 26) :=
      mul_lt_mul_of_pos_right (by nlinarith) h4
    linarith
  · have h1 : 90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ 90 * ρ * (2 * ρ) ^ 2 * ρ := by gcongr
    have h2 : 90 * ρ * (2 * ρ) ^ 2 * ρ = 360 * ρ ^ 4 := by ring
    linarith
  · have h1 : Real.log q = Real.log (q / 16) + Real.log 16 := by
      rw [Real.log_div hq0.ne' (by norm_num)]; ring
    have h2 : Real.log (q / 16) ≤ q / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h4 : Real.log D ≤ Real.log q := Real.log_le_log (by linarith) hDq
    have h5 : Real.log (q * D) = Real.log q + Real.log D := Real.log_mul hq0.ne' (by linarith)
    have h6 : 4 * D * (7 + Real.log (q * D)) ≤ 4 * D * (q / 8 + 37) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    have h7 : (2 * ρ + 1) * 1 ≤ (2 * ρ + 1) * D := by gcongr
    have h8 : (q / 2 + 148 + (2 * ρ + 1)) * D ≤ q * D := by
      apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
    have h9 : q * D ≤ q * (D * r) := by gcongr
    linarith
  · have h2' : 0 ≤ Real.log r := Real.log_nonneg hr
    have h4 : r * Real.log r + 3 * r + 3 ≤ r * (N + 6) := by
      have : r * Real.log r ≤ r * N := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
      linarith
    have h5 : (D + 1) * (r * Real.log r + 3 * r + 3) ≤ (2 * D) * (r * (N + 6)) := by
      apply mul_le_mul (by linarith) h4 (by positivity) (by positivity)
    have h6 : (N + 4 * ρ + 3) * 1 ≤ (N + 4 * ρ + 3) * (D * r) := by gcongr
    have h7 : (N + 4 * ρ + 3 + 2 * (N + 6)) * (D * r) ≤ q * (D * r) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
    linarith

theorem runOK_of_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r DF q m : ℕ), 1 ≤ DF → 2 ≤ I2.PT.f E * r → 1 ≤ m → m ^ 4 ≤ I2.PT.f E → (I2.PT.f E : ℝ) ^ 2 ≤ I2.PT.rd E → 16 ≤ I2.PT.rd E → I2.RR (E := E) ^ 4 * (90 * (I2.PT.f E * r + DF)) * DF * r ≤ q → RunOK E r DF q (Real.sqrt (90 * (I2.PT.f E * r + DF))) m := by
  intro E _ _ _ r DF q m hDF hfr hm1 hmf hf2 hrd hlo
  have hf : 1 ≤ I2.PT.f E := by
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hfr; omega
    · exact h
  have hmf' : m ≤ I2.PT.f E := (Nat.le_self_pow (by norm_num) m).trans hmf
  have hfR : (1 : ℝ) ≤ I2.PT.f E := by exact_mod_cast hf
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hDR : (1 : ℝ) ≤ DF := by exact_mod_cast hDF
  have hmfR : (m : ℝ) ≤ I2.PT.f E := by exact_mod_cast hmf'
  have hfrR : (2 : ℝ) ≤ I2.PT.f E * r := by exact_mod_cast hfr
  have hfrd : (I2.PT.f E : ℝ) ≤ I2.PT.rd E := by nlinarith
  have hw : (I2.PT.f E : ℝ) ^ ((3 : ℝ) / 2) ≤ (I2.PT.f E : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hfR (by norm_num)
  have hS0 : (0 : ℝ) < 90 * (I2.PT.f E * r + DF) := by positivity
  have hsq : Real.sqrt (90 * (I2.PT.f E * r + DF)) ^ 2 = 90 * (I2.PT.f E * r + DF) := Real.sq_sqrt hS0.le
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := real_bounds (I2.PT.f E) r m (I2.PT.rd E) _ DF q
    (I2.t0 (E := E) q (Real.sqrt (90 * (I2.PT.f E * r + DF)))) hfR hrR hmR hmfR hf2 hrd
    (by positivity) hw hDR hlo (by unfold I2.t0 I2.b0 I2.RR; rw [hsq])
  have hc4 : DF ≤ q := by exact_mod_cast c4
  have hq1 : 1 ≤ q := hDF.trans hc4
  have hq0 : (0 : ℝ) < q := by linarith
  have hρ0 : 0 < I2.PT.rd E := by linarith
  have hd : (I2.dstar (E := E) m : ℝ) = 2 * I2.PT.f E * m := by unfold I2.dstar; push_cast; ring
  intro X hX hdim
  subst hX
  refine ⟨⟨q, _, m, hq1, hDF, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, ?_, ?_,
    hc4, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [hsq]
    unfold I2.PT.gA
    push_cast
    constructor <;> linarith
  · unfold I2.th I2.omStar I2.RR
    rw [Real.sq_sqrt (by positivity), ← mul_div_assoc, div_lt_one hq0, hsq, hd]
    exact c1
  · unfold I2.b0 I2.RR; rw [hsq]; exact c2
  · unfold I2.M1
    rw [hd]; exact c3
  · rw [hd]; linarith
  · unfold I2.PT.gA
    rw [hd]
    push_cast
    linarith

end GlobalTheory.RunParametersOfLower
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.IsPiAct

theorem negOnePow_natCast_mul (M : ℕ) (k : ℤ) :
    Int.negOnePow ((M : ℤ) * k) = Int.negOnePow k ^ M := by
  induction M with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_mul, _root_.one_mul, Int.negOnePow_add, ih, pow_succ]

theorem isPi_actL_of_isTorusOf :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsPeriod D ty Pm → IsTorusOf D ty Pm Hm T ψ → ∀ (α : 𝓞 E) (M : ℕ), α * H.bar α = (M : 𝓞 E) → I2.IsPi T M (vspActL α) := by
  intro E _ _ _ H D g ty Pm Hm T ψ hP hT α M hM
  obtain ⟨-, -, -, hL, hact, heps⟩ := hT

  have hnorm : ∀ τ : E →+* ℂ, τ (α : E) * starRingEnd ℂ (τ (α : E)) = (M : ℂ) := by
    intro τ
    have h := congrArg (fun x : 𝓞 E => τ (x : E)) hM
    push_cast at h
    have hb := congrArg τ (H.bar_eq α)
    rw [IsCMField.complexEmbedding_complexConj] at hb
    rw [map_mul, map_natCast] at h
    rw [← hb]
    exact h
  have hcoord : ∀ (u : I2.Vsp T.dim) i, (I2.act α u) i = i.1 (α : E) * u i := fun _ _ => rfl

  have hlat : ∀ a, I2.act α (ψ (Pm a)) = ψ (Pm (α • a)) := by
    intro a
    rw [← hact]
    congr 1
    funext k
    exact (hP.1 α a k).symm
  unfold I2.IsPi
  refine ⟨fun β v => ?_, fun x hx => ?_, fun v w => ?_, fun x hx => ?_⟩ <;>
    simp only [vspActL, LinearMap.coe_mk, AddHom.coe_mk]
  · ext i
    change i.1 (α : E) * (i.1 (β : E) * v i) = i.1 (β : E) * (i.1 (α : E) * v i)
    ring
  · obtain ⟨a, rfl⟩ := (hL x).1 hx
    rw [hlat, hL]
    exact ⟨α • a, rfl⟩
  · unfold I2.Hf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoord, hcoord, map_mul]
    linear_combination (v i * starRingEnd ℂ (w i)) * hnorm i.1
  · obtain ⟨a, rfl⟩ := (hL x).1 hx
    have hEF : D.EF (α • a) (H.w0 • α • a) = (M : ℤ) * D.EF a (H.w0 • a) := by
      have hc : H.bar α * H.w0 * α = (M : 𝓞 E) * H.w0 := by rw [← hM]; ring
      rw [D.adj, smul_smul, smul_smul, hc, mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    rw [hlat, heps, heps, hEF, negOnePow_natCast_mul, Units.val_pow_eq_pow_val]

end GlobalTheory.AnVal.IsPiAct
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ThetaIsotropy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Tate

variable {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_sum (I : TateIso Dw k Q act e) (m : ℕ) (hm : 0 < m) {n : ℕ} (a : Fin n → Dw.La) :
    I.ev m (∑ j, a j) = ∏ j, I.ev m (a j) := by
  have h0 : I.ev m 0 = 1 := (I.ker m hm 0).2 ⟨0, (smul_zero _).symm⟩
  let f : Multiplicative Dw.La →* Q :=
    { toFun := fun x => I.ev m x.toAdd, map_one' := h0, map_mul' := fun x y => I.add m _ _ }
  exact map_prod f (fun j => Multiplicative.ofAdd (a j)) Finset.univ

theorem dvd_EF_of_killed (m j : ℕ) (a b : Dw.La) (ha : ∀ c ∈ l.Mb ^ j, Dw.ModN m (c • a))
    (hb : ∀ c ∈ l.Mb ^ j, Dw.ModN m (c • b)) : (m : ℤ) ∣ Dw.EF a b := by
  have cop : l.Mb ^ j ⊔ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ j = ⊤ :=
    Ideal.sup_pow_eq_top' (Ideal.pow_sup_eq_top l.coprime)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (cop.ge (Submodule.mem_top : (1 : 𝓞 E) ∈ ⊤))
  rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  obtain ⟨a', ha'⟩ := ha r hr
  obtain ⟨b', hb'⟩ := hb p hp
  have e₁ : Dw.EF a b = Dw.EF a (p • b) + Dw.EF (r • a) b := by
    rw [Dw.adj, ← map_add (f := _), ← add_smul]
    have : p + H.bar r = 1 := hpq
    rw [this, one_smul]
  rw [e₁, ha', hb', map_nsmul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)

end Tate

variable (Xo : Moduli Dw l) {B : Type} [CommRing B] (x0 : Sp B ⟶ Xo.X)

noncomputable def bc {K : Type} [CommRing K] (χ : B →+* K) : ptO Xo (spMap χ ≫ x0) ⟶ ptO Xo x0 :=
  Over.homMk (spMap χ) rfl

theorem unit_eq_one (hL : Laws) (N : ℕ) (hN : 0 < N) (u : Γ((ptO Xo x0).left, ⊤)ˣ) (hu : u ^ (N ^ 2) = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K),
      Units.map (bc Xo x0 χ).left.appTop.hom.toMonoidHom u = 1) : u = 1 := by
  let i₀ := (Scheme.ΓSpecIso (CommRingCat.of B)).hom
  have hi : Function.Injective i₀.hom := (ConcreteCategory.bijective_of_isIso i₀).1
  have hU : IsUnit ((N ^ 2 : ℕ) : B) := by
    have := ((baseKA l).unit (N ^ 2) (pow_pos hN 2)).map (Spec.preimage (x0 ≫ Xo.s)).hom
    rwa [map_natCast] at this
  have key := (T.universal_weilPairing_pullback_exists_unique hL E H Dw l Xo N hN).2.2 B (i₀.hom u.val) (N ^ 2) hU
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]) (fun K _ _ χ => by
      have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
      have e := congrArg (fun φ => φ.hom u.val) nat
      have h1 : (spMap χ).appTop.hom u.val = 1 := congrArg Units.val (h K χ)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
      rw [← e]
      exact (congrArg _ h1).trans (map_one _))
  exact Units.ext (hi (key.trans (map_one _).symm))

theorem exists_tate (hL : Laws) (N : ℕ) (hN : 0 < N) (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K) :
    ∃ I : TateIso Dw K (ptO Xo (spMap χ ≫ x0) ⟶ Xo.univ.t.G) (fun a g => g ≫ Xo.univ.t.act.act a)
        (fun n g g' c => WeilIs Xo.univ.t.G Xo.univ.t.PP.L n g g' (unitOn c)),
      ∀ (x y : ptO Xo x0 ⟶ Xo.univ.t.G) (e : Γ((ptO Xo x0).left, ⊤)ˣ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 →
        WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e → ∀ a b, I.ev (N ^ 2) a = bc Xo x0 χ ≫ x →
        I.ev (N ^ 2) b = bc Xo x0 χ ≫ y →
        Units.map (bc Xo x0 χ).left.appTop.hom.toMonoidHom e = unitOn (I.ζ (N ^ 2) ^ Dw.EF a b) := by
  obtain ⟨-, I, -⟩ := Xo.univ.geom K (spMap χ ≫ x0) (Spec.preimage ((spMap χ ≫ x0) ≫ Xo.s)).hom
    (Spec.map_preimage _).symm
  refine ⟨I, fun x y e hx hy he a b ha hb => ?_⟩
  obtain ⟨W₁, W₂, -⟩ := T.universal_weilPairing_pullback_exists_unique hL E H Dw l Xo N hN
  have h₁ := W₁ _ _ (bc Xo x0 χ) x y e hx hy he
  have h₂ := I.isom (N ^ 2) (pow_pos hN 2) a b
  rw [ha, hb, Nat.cast_pow] at h₂
  obtain ⟨e₀, -, -, hu⟩ := W₂ _ (bc Xo x0 χ ≫ x) (bc Xo x0 χ ≫ y)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  exact (hu _ h₁).trans (hu _ h₂).symm

theorem unitOn_prod {K : Type} [CommRing K] {n : ℕ} (c : Fin n → Kˣ) : ∏ b, unitOn (c b) = unitOn (∏ b, c b) :=
  (map_prod (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom) c Finset.univ).symm

theorem prod_zpow_eq {U : Type} [CommGroup U] (z : U) {n : ℕ} (c : Fin n → ℤ) : ∏ b, z ^ c b = z ^ ∑ b, c b :=
  (map_prod (zpowersHom U z) (fun b => Multiplicative.ofAdd (c b)) Finset.univ).symm

theorem unitOn_one {K : Type} [CommRing K] : unitOn (1 : Kˣ) = 1 :=
  map_one (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)

theorem comp_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) : h ≫ (List.ofFn x).prod = ∏ j, h ≫ x j := by
  rw [List.prod_ofFn]
  let f : (T ⟶ G) →* (T' ⟶ G) :=
    { toFun := fun g => h ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun a b => MonObj.comp_mul _ _ _ }
  exact map_prod f x Finset.univ

end ThetaIsotropy


open ThetaIsotropy in
theorem zh_isotropic_and_half_isotropic : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → (∀ (a a' : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) (e : Fin n → Γ((ptO Xo x0).left, ⊤)ˣ), InZh Xo Λ N a → InZh Xo Λ N a' → (∀ b, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (a b) (a' b) (e b)) → ∏ b, e b = 1) ∧ ∀ (x y : ptO Xo x0 ⟶ Xo.univ.t.G) (j : ℕ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → KilledBy Xo (l.Mb ^ j) x → KilledBy Xo (l.Mb ^ j) y → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y 1 := by
  intro hL E _ _ _ H Dw l Xo B _ x0 n Λ N hΛ hN hle
  have hN2 : 0 < N ^ 2 := pow_pos hN 2
  obtain ⟨-, W₂, -⟩ := T.universal_weilPairing_pullback_exists_unique hL E H Dw l Xo N hN
  have tors : ∀ {K : Type} [CommRing K] (χ : B →+* K) {x : ptO Xo x0 ⟶ Xo.univ.t.G}, x ^ (N ^ 2) = 1 →
      (ThetaIsotropy.bc Xo x0 χ ≫ x) ^ (N ^ 2) = 1 := fun χ x hx => by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  refine ⟨fun a a' e ha ha' he => ?_, fun x y j hx hy kx ky => ?_⟩
  · refine ThetaIsotropy.unit_eq_one Xo x0 hL N hN _ ?_ fun K _ _ χ => ?_
    · rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun b _ => ?_
      obtain ⟨e₀, -, h₀, hu⟩ := W₂ _ (a b) (a' b) (ha.1 b) (ha'.1 b)
      rw [hu _ (he b), h₀]
    · obtain ⟨I, hI⟩ := ThetaIsotropy.exists_tate Xo x0 hL N hN K χ
      choose v hv using fun b => (I.onto _ hN2 _).1 (tors χ (ha.1 b))
      choose v' hv' using fun b => (I.onto _ hN2 _).1 (tors χ (ha'.1 b))
      have lat : ∀ {a : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)} {v : Fin n → Dw.La}, InZh Xo Λ N a →
          (∀ b, I.ev (N ^ 2) (v b) = ThetaIsotropy.bc Xo x0 χ ≫ a b) →
          ∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) →
            ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) →
              ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • v j) := fun {a v} ha hv mu hmu cm hcm i => by
        refine (I.ker _ hN2 _).1 ?_
        have h₁ := congrArg (ThetaIsotropy.bc Xo x0 χ ≫ ·) (ha.2 mu hmu cm hcm i)
        simp only [MonObj.comp_one] at h₁
        rw [ThetaIsotropy.comp_prod] at h₁
        rw [ThetaIsotropy.ev_sum I _ hN2, ← h₁]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [I.lin, hv, Category.assoc]
      have hd := T.sq_dvd_sum_alternating_forms_of_killed_lattice E H Dw n Λ N hΛ hN hle v v' (lat ha hv) (lat ha' hv')
      rw [map_prod, Finset.prod_congr rfl fun b _ => hI _ _ _ (ha.1 b) (ha'.1 b) (he b) _ _ (hv b) (hv' b)]
      refine (ThetaIsotropy.unitOn_prod _).trans ?_
      rw [ThetaIsotropy.prod_zpow_eq,
        ((I.ζ_prim _ hN2).zpow_eq_one_iff_dvd _).2 (by rwa [Nat.cast_pow]), ThetaIsotropy.unitOn_one]
  · obtain ⟨e, he, h₀, -⟩ := W₂ _ x y hx hy
    suffices e = 1 by rwa [this] at he
    refine ThetaIsotropy.unit_eq_one Xo x0 hL N hN _ h₀ fun K _ _ χ => ?_
    obtain ⟨I, hI⟩ := ThetaIsotropy.exists_tate Xo x0 hL N hN K χ
    obtain ⟨v, hv⟩ := (I.onto _ hN2 _).1 (tors χ hx)
    obtain ⟨v', hv'⟩ := (I.onto _ hN2 _).1 (tors χ hy)
    have lat : ∀ {x : ptO Xo x0 ⟶ Xo.univ.t.G} {v : Dw.La}, KilledBy Xo (l.Mb ^ j) x →
        I.ev (N ^ 2) v = ThetaIsotropy.bc Xo x0 χ ≫ x → ∀ c ∈ l.Mb ^ j, Dw.ModN (N ^ 2) (c • v) := fun {x v} kx hv c hc => by
      refine (I.ker _ hN2 _).1 ?_
      rw [I.lin, hv, Category.assoc, kx c hc, MonObj.comp_one]
    have hd := ThetaIsotropy.dvd_EF_of_killed (N ^ 2) j v v' (lat kx hv) (lat ky hv')
    rw [hI _ _ _ hx hy he _ _ hv hv', ((I.ζ_prim _ hN2).zpow_eq_one_iff_dvd _).2 hd]
    exact ThetaIsotropy.unitOn_one

end GlobalTheory
end
