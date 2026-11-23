module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2018
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparatesOnSmoothOfPair
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023

@[expose] public section

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.TorusTheta

theorem min_pow_le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) : min 1 c ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [zero_add, pow_one]
      exact (min_le_right _ _).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : 0 < t ⟨i.val + 1, hj⟩ := hpos _
      calc min 1 c ^ (k + 1 + 1) = min 1 c * min 1 c ^ (k + 1) := by ring
        _ ≤ min 1 c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_right (min_le_right _ _) h3.le
        _ ≤ t i := h2
  have := key (r - i.val - 1) i (by omega)
  refine le_trans ?_ this
  exact pow_le_pow_of_le_one hm0.le hm1 (by omega)

theorem mul_norm_le_norm_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] {c' : ℝ} (hc' : 0 < c')
    (s : ι → ℝ) (hs : ∀ i, c' ≤ s i) (v : ι → V) : c' * ‖v‖ ≤ ‖fun i => s i • v i‖ := by
  rw [← le_div_iff₀' hc']
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [le_div_iff₀' hc']
  have hsi : 0 < s i := hc'.trans_le (hs i)
  calc c' * ‖v i‖ ≤ s i * ‖v i‖ := mul_le_mul_of_nonneg_right (hs i) (norm_nonneg _)
    _ = ‖s i • v i‖ := by rw [norm_smul, Real.norm_of_nonneg hsi.le]
    _ ≤ ‖fun i => s i • v i‖ := norm_le_pi_norm (fun i => s i • v i) i

theorem prod_elim_pow {κ : Type} [Fintype κ] {r : ℕ} (blk : κ → Option (Fin r)) (t : Fin r → ℝ) (f d : ℕ)
    (hcard : ∀ i : Fin r, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) :
    ∏ j, (blk j).elim 1 t ^ f = (∏ i, t i ^ (f * d)) ^ 2 := by
  rw [← Finset.prod_fiberwise (Finset.univ : Finset κ) blk (fun j => ((blk j).elim 1 t : ℝ) ^ f)]
  have h1 : ∀ o : Option (Fin r), ∏ j ∈ Finset.univ.filter (fun j => blk j = o), (blk j).elim 1 t ^ f =
      (o.elim 1 t ^ f) ^ (Finset.univ.filter (fun j => blk j = o)).card := by
    intro o
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl (fun o _ => h1 o), Fintype.prod_option]
  simp only [Option.elim_none, Option.elim_some, one_pow, one_mul, hcard]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GlobalTheory.TorusTheta

namespace GlobalTheory.TorusTheta

theorem theta_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt c hc Φ hΦ
  obtain ⟨co, blk, hrat, hcard, hact⟩ := GlobalTheory.T.witt_frame_darboux_coordinates F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt
  obtain ⟨M₁, om₁, e, c₀, hco, hP₁, hc₀, he⟩ := GlobalTheory.T.darboux_coords_rational_points F E σ B n d X W M χX χW om r s r' s' hP co hrat
  obtain ⟨N₀, k₃, C₃, hlat⟩ := GlobalTheory.LatScaleSum.thetaSum_norm_le_pow F (Fin n × Fin d)
  have heΦ := (he Φ hΦ).1
  obtain ⟨C₁, k₁, hdec⟩ := GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ N₀
  obtain ⟨C₂, k₂, hden⟩ := GlobalTheory.T.schwartz_theta_polynomial_growth F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ
  set c' : ℝ := min 1 c ^ r₀ with hc'def
  have hc'0 : 0 < c' := pow_pos (lt_min one_pos hc) _
  have hc'1 : c' ≤ 1 := pow_le_one₀ (lt_min one_pos hc).le (min_le_left _ _)
  refine ⟨‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃, k₁ + k₂ * k₃, ?_⟩
  intro t htc a hta a' ha' y h
  have tlow : ∀ i, c' ≤ t i := min_pow_le_of_mem_cone hc htc
  have tpos : ∀ i, 0 < t i := fun i => hc'0.trans_le (tlow i)
  set u : Fin n × Fin d → ℝ := fun j => (blk j).elim 1 t with hudef
  have hulow : ∀ j, c' ≤ u j := by
    intro j
    simp only [hudef]
    cases blk j with
    | none => exact hc'1
    | some i => exact tlow i
  have hupos : ∀ j, 0 < u j := fun j => hc'0.trans_le (hulow j)
  obtain ⟨κ, hκ, hom⟩ := GlobalTheory.T.torus_action_model_coordinates F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ a' u hupos
    (by rw [hco]; exact hact t tpos a hta a' ha')

  have hΨ0 : om (y, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΦ
  have hT : om (a', 1) (om (y, h) Φ) ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΨ0
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = om₁ (y, h) (e Φ) := ⟨_, rfl⟩
  have hΨ : Ψ ∈ schA F (Fin n × Fin d) := hΨdef ▸ (IsUWeilPair.isUSplitting hP₁.weil).pres _ _ heΦ
  have hmul : ((a' * y, h) : UA σ X.J × UA σ W.J) = (a', 1) * (y, h) := by
    ext <;> simp
  have hsplit : om (a' * y, h) Φ = om (a', 1) (om (y, h) Φ) := by
    rw [hmul, map_mul, Module.End.mul_apply]
  have heT : e (om (a', 1) (om (y, h) Φ)) = om₁ (a', 1) Ψ := by
    rw [(he _ hΨ0).2.2, (he Φ hΦ).2.2, hΨdef]
  have hthT : thetaSum F (om (a', 1) (om (y, h) Φ)) = c₀⁻¹ * thetaSum F (om₁ (a', 1) Ψ) := by
    rw [← heT, (he _ hT).2.1, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
  have hfun : om₁ (a', 1) Ψ = fun x => κ * Ψ (fun j => infScale F (u j) * x j) := funext (hom Ψ hΨ)
  have hkey : theta om Φ (a' * y) h =
      c₀⁻¹ * (κ * thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))) := by
    show thetaSum F (om (a' * y, h) Φ) = _
    rw [hsplit, hthT, hfun]
    unfold thetaSum
    rw [tsum_mul_left]

  have hκ' : ‖κ‖ = ∏ i, t i ^ (Module.finrank ℚ F * d) := by
    have h2 : ‖κ‖ ^ 2 = (∏ i, t i ^ (Module.finrank ℚ F * d)) ^ 2 := by
      rw [hκ]
      exact prod_elim_pow blk t _ d hcard
    have hnn : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
      Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
    exact (pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).1 h2

  set P : ℝ := (ht y : ℝ) * ht h with hPdef
  have hP0 : 0 ≤ P := mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  obtain ⟨m, hm1, hmC, hmint⟩ := hden y h
  have hdecay : ∀ ξ : Fin n × Fin d → F,
      ‖Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j)‖ *
        (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := by
    intro ξ
    beta_reduce
    have h1 := hdec y h (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))
    rw [← hΨdef] at h1
    have hnorm : c' * ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
      simp only [evI_infScale_mul]
      exact mul_norm_le_norm_smul hc'0 u hulow _
    have hle : 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        c'⁻¹ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) := by
      have hi : 1 ≤ c'⁻¹ := one_le_inv₀ hc'0 |>.2 hc'1
      have h3 : ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
          c'⁻¹ * ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
        rw [le_inv_mul_iff₀ hc'0]; exact hnorm
      nlinarith [norm_nonneg (fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i)))]
    have hpow : (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤
        (c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀ := by
      have h0 : 0 ≤ 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ :=
        add_nonneg zero_le_one (norm_nonneg _)
      have h4 := pow_le_pow_left₀ h0 hle N₀
      rw [mul_pow] at h4
      exact h4
    calc ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀
        ≤ ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          ((c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (c'⁻¹) ^ N₀ * (‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) := by ring
      _ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hint : ∀ ξ : Fin n × Fin d → F,
      Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j) ≠ 0 →
        ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
    intro ξ hne
    rw [hΨdef] at hne
    exact hmint _ ξ (fun i => infScale_mul_snd F (u i) _) hne
  have hS := hlat ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) m (fun x => Ψ (fun j => infScale F (u j) * x j)) hm1 hdecay hint

  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmk : (m : ℝ) ^ k₃ ≤ |C₂| ^ k₃ * P ^ (k₂ * k₃) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hm0 (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hP0 _))) k₃
  have hS' : ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖ ≤
      |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by
    refine hS.trans ?_
    calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) * (m : ℝ) ^ k₃
        ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (m : ℝ) ^ k₃ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hm0 _)
          calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) ≤ |C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁))| := le_abs_self _
            _ = |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c'⁻¹) ^ N₀),
                abs_of_nonneg (pow_nonneg hP0 _)]
      _ ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (|C₂| ^ k₃ * P ^ (k₂ * k₃)) :=
          mul_le_mul_of_nonneg_left hmk (by positivity)
      _ = |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by ring
  rw [hkey, norm_mul, norm_mul, norm_inv, hκ']
  have hT0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
  calc ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) * ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖)
      ≤ ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) *
          (|C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃))) := by gcongr
    _ = _ := by ring

end GlobalTheory.TorusTheta
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SepCusp

section Geometry

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn exOf secZ)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.CompHt (genVal genPoint)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_of_ptY_eq {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (h : GenFrEx Xo c) (Z : Comp Xo c)
    {K : Type} [Field K] [Algebra c.F K] (φ φ' : Om Z →ₐ[c.F] K)
    (e : spMap φ.toRingHom ≫ X.ptY (genFr h Z) = spMap φ'.toRingHom ≫ X.ptY (genFr h Z)) : φ = φ' := by
  obtain ⟨y, hy⟩ := GlobalTheory.FlagMod.exists_frMap φ (genFr h Z)
  obtain ⟨y', hy'⟩ := GlobalTheory.FlagMod.exists_frMap φ' (genFr h Z)
  rw [X.ptY_frMap hy, X.ptY_frMap hy'] at e
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY y)
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) (X.lies_ptY y).1 k hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor (X.lies_ptY y)
  obtain ⟨t', ht'⟩ := hQ.exists_frBor (e ▸ X.lies_ptY y')
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K
  exact eq_of_heq (GlobalTheory.Reg.GenericFlagInj.eq_of_frBor h Z Z φ φ' y y' _ hy hy' (g1 _ _ _ _ _ (g2 _ _ _ ht) ht')).2

theorem exists_val_cuspSec {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (h : GenFrEx Xo c) (w : Sp (Om Z) ⟶ Y₀ X Z)
    (hw : w ≫ inc₀ X Z = X.ptY (genFr h Z)) (hU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z) (i : (L₀ X Z la).ι)
    (hi : ⊤ ≤ w ⁻¹ᵁ (L₀ X Z la).U i) :
    ∃ T : Om Z, T ≠ 0 ∧ ∀ g : Cusp Z U la, H0.val w i hU hi (cuspSec X Z U la g) = T * genVal Z g.1 := by
  have e₁ : w ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by rw [X.pt_inc]; exact hw
  have hO₂ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  have hk₂ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (i PUnit.unit) :=
    (le_iff_ptOf_mem _ _).2 (mem_pull.1 ((le_iff_ptOf_mem _ _).1 hi))
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U (i PUnit.unit) := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) (i PUnit.unit) hk₁
  have hQ₂ : X.F.ChartFr (i PUnit.unit) (w ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  refine ⟨((∏ ix, t ix ^ exOf Dw la 0 ix : (Om Z)ˣ) : Om Z)⁻¹, inv_ne_zero (Units.ne_zero _), fun g => ?_⟩
  have v₈ := evR_eq_val_secOf ⟨g.1, cusp_le_secZ Z U la g.2⟩ hO₂ hQ₂ ht
  have v₅ : H0.val w i hU hi (cuspSec X Z U la g) = H0.val (B := X.LL (exOf Dw la 0))
      (w ≫ inc₀ X Z) (i PUnit.unit) hO₂ hk₂ (secOf X _ ⟨g.1, cusp_le_secZ Z U la g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl w i hU hi hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  rw [v₅, v₆, v₈, inv_mul_cancel_left₀ (Units.ne_zero _)]

theorem val_eq_stalk {k K : Type} [CommRing k] [Field K] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens}
    (x : Sp K ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hy : ptOf x ∈ O) (hj : ptOf x ∈ B.U i)
    (f : H0 p B O) :
    H0.val x i hO hi f = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom (germ i (ptOf x) hy hj f) := by
  rw [H0.val_apply, H0.germ_apply]
  exact (stalkClosedPointTo_ger x _ _ _ (memInf hy hj)).symm

theorem gapGe_std (Dw : Datum H) : GapGe 1 (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw) := by
  intro τ k hk
  simp only [gap, dif_pos hk, GlobalTheory.CompHt.stdWt]
  push_cast
  omega

theorem gapGe_sub_std (m : ℕ) (b : AllWt.Weight Dw) (h : GapGe (m : ℤ) b) :
    GapGe 0 (b - m • (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw)) := by
  intro τ k hk
  have h1 := h τ k hk
  simp only [gap, dif_pos hk, Pi.sub_apply, Pi.smul_apply, GlobalTheory.CompHt.stdWt] at h1 ⊢
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linarith

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) :=
  map_nsmul (AddMonoidHom.mk' (fun a => cls (B a) (C.isLB a)) (cls_common_add C)) n a

end Geometry

theorem exists_fg_complexPoint (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [CharZero K] [Countable K]
    (hfg : (⊤ : IntermediateField K Ω).FG) (L : IntermediateField K Ω) (hL : L = ⊤) :
    ∃ (σ : K →+* ℂ) (A B : Subalgebra K Ω), A.FG ∧ B.FG ∧ B ≤ A ∧ (∀ b ∈ B, b ∈ L) ∧
      IntermediateField.adjoin K (A : Set Ω) = ⊤ ∧ (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ,
        (∀ k : K, x (algebraMap K A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧
          ∀ y : A →+* ℂ, (∀ k : K, y (algebraMap K A k) = σ k) → (∀ a : A, (a : Ω) ∈ B → y a = x a) → y = x) := by
  have : Countable Ω := TwoPoint.countable_of_fg _ _ hfg
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨i⟩ := TwoPoint.nonempty_ringHom_complex Ω
  obtain ⟨s, hs⟩ := hfg
  let A : Subalgebra K Ω := Algebra.adjoin K (s : Set Ω)
  exact ⟨i.comp (algebraMap _ _), A, A, ⟨s, rfl⟩, ⟨s, rfl⟩, le_rfl, fun b _ => hL ▸ IntermediateField.mem_top,
    eq_top_iff.2 (hs ▸ IntermediateField.adjoin.mono _ _ _ Algebra.subset_adjoin), fun b _ hb =>
    ⟨i.comp A.val.toRingHom, fun _ => rfl, fun _ => (map_ne_zero i).2 hb, fun y _ h => RingHom.ext fun a => h a a.2⟩⟩

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem gapGe_sub_kap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (hu : ∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      (((dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ u τ a - u τ b) :
    GlobalTheory.HSApp.GapGe (((FlagTan.dimFlag Dw + 2).choose 2 : ℕ) : ℤ) (u - FlagTan.kap Dw) := by
  intro τ k hk
  have h₁ := hu τ ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl
  have h₂ := GlobalTheory.HSApp.gap_kap_le (Dw := Dw) τ hk
  have h₃ := GlobalTheory.CompHS.gap_eq (u τ) (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl
  have h₄ : (FlagTan.dimFlag Dw + 2).choose 2 ≤ (FlagTan.dimFlag Dw + 3) ^ 2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) 2)
  have h₅ : (((FlagTan.dimFlag Dw + 2).choose 2 : ℕ) : ℤ) ≤ ((FlagTan.dimFlag Dw + 3) ^ 2 : ℕ) := by
    exact_mod_cast h₄
  rw [GlobalTheory.CompHS.dimFlag_eq] at h₁
  rw [Pi.sub_apply, GlobalTheory.HSApp.gap_sub]
  dsimp only at h₃
  push_cast at h₁ h₂ h₅ ⊢
  linarith


end GlobalTheory.SepCusp
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem comp_id_pow_eq {K : Type} [Field K] (A : AbVar K) {T : Over (Sp K)} (x : T ⟶ A.X) (n : ℕ) :
    x ≫ (𝟙 A.X) ^ n = x ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.comp_one]
  | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem exists_nsmul_eq_of_kills_torsion : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ),
    (n : K) ≠ 0 → (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1) → ∃ g : A ⟶ C, f = n • g := by
  intro K _ A C f n hn hf
  have hn0 : (n : ℤ) ≠ 0 := by
    intro h
    apply hn
    have : n = 0 := by exact_mod_cast h
    simp [this]
  obtain ⟨hiso, -⟩ := GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A (n : ℤ) hn0
  have hiso' : IsIsogeny (n • 𝟙 A) := by rwa [natCast_zsmul] at hiso
  have hkill := GlobalTheory.T.comp_eq_one_of_kills_geometric_torsionPoints K A C f n hn hf
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_factor_through_isogeny_of_kills_kernel K A A C (n • 𝟙 A) f hiso' (fun T x hx => by
    apply hkill T x
    rw [nsmul_hom, id_hom, comp_id_pow_eq] at hx
    exact hx)
  refine ⟨g, ?_⟩
  rw [← hg, Preadditive.nsmul_comp, Category.id_comp]

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem comp_pow_id_torscard {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x : T ⟶ G) (n : ℕ) :
    x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ k ih => rw [pow_succ, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem card_torsion_pt (K : Type) [Field K] (A : AbVar K) (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {x : A.Pt // x ^ n = 1} = n ^ (2 * A.dim) := by
  have hn0 : (n : ℤ) ≠ 0 := by
    intro h; apply hn; simp at h; simp [h]
  obtain ⟨hiso, hdeg⟩ := GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A (n : ℤ) hn0
  have hf : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X) ^ n := by
    rw [natCast_zsmul, nsmul_hom, id_hom]
  have hker : ∀ {T : Over (Sp K)} (x : T ⟶ A.X), x ≫ ((n : ℤ) • 𝟙 A).hom = x ^ n := by
    intro T x; rw [hf, comp_pow_id_torscard]
  have hd := GlobalTheory.T.isogenyDegree_eq_card_kernel_of_killed_by_invertible K A A ((n : ℤ) • 𝟙 A) n hn hiso (fun T x hx => by rw [← hker]; exact hx)
  rw [hdeg, Int.natAbs_natCast] at hd
  rw [hd]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun x => by rw [MonoidHom.mem_ker, ptMap_apply, hker])

end GlobalTheory.AV.AbVar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.archimedeanSchwartzDatum_stable_heisenbergDerivative : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ (f : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank))) a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ f₁ : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Γ.M.heisLine Bs.ψ u) f f₁ →
    ∃ a', IsDatumA W e Γ (tensT W a' τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) := by
  first | exact @GlobalTheory.BigNZ.DatRealStable.datum_stable | exact GlobalTheory.BigNZ.DatRealStable.datum_stable | (intros; apply GlobalTheory.BigNZ.DatRealStable.datum_stable <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_torsionTower_and_height_eq_two_dim : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A : AbVar k), (∃ G : PDivGroup p k, Nonempty (G.TorsionTower A.X)) ∧ ∀ (G : PDivGroup p k) (t : G.TorsionTower A.X), G.height = 2 * A.dim := by
  first | exact @GlobalTheory.AVTower.exists_tower_and_height_eq | exact GlobalTheory.AVTower.exists_tower_and_height_eq | (intros; apply GlobalTheory.AVTower.exists_tower_and_height_eq <;> assumption)
end
