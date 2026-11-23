module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle003
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle003
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle005
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace LimitVolumeRatio

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem linRoot_sub_smul (lam nu : Wt Ψ N) (s : ℝ) :
    linRoot (lam - s • nu) = linRoot lam - C s * linRoot nu := by
  simp only [linRoot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_neg, mul_assoc]
  ring

theorem linA_lamS (T : RootTower Ψ N) (u : Wt Ψ N) (s : ℝ) :
    linA (T.lamS u s) s = toA (linRoot u) + C s * (X none - toA (linRoot T.nu)) := by
  simp only [linA, RootTower.lamS, linRoot_sub_smul, toA, map_sub, map_mul, rename_C]
  ring

theorem cont_pow (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (P0 P1 : RPA Ψ N) (d : ℕ) :
    Continuous fun s : ℝ => Φ ((P0 + C s * P1) ^ d) := by
  have h : ∀ s : ℝ, Φ ((P0 + C s * P1) ^ d) =
      ∑ m ∈ Finset.range (d + 1), s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) := by
    intro s

    rw [add_pow, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) =
      Φ (s ^ (d - m) • (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N))) by rw [map_smul, smul_eq_mul]]
    congr 1
    rw [MvPolynomial.smul_eq_C_mul, mul_pow, ← map_pow]
    ring
  rw [show (fun s : ℝ => Φ ((P0 + C s * P1) ^ d)) = fun s : ℝ => ∑ m ∈ Finset.range (d + 1),
      s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) from funext h]
  fun_prop

theorem tendsto_lin (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (T : RootTower Ψ N) (u : Wt Ψ N) (d : ℕ) :
    Tendsto (fun s => Φ (linA (T.lamS u s) s ^ d)) (𝓝[>] 0) (𝓝 (Φ (toA (linRoot u ^ d)))) := by
  have hc := (cont_pow Φ (toA (linRoot u)) (X none - toA (linRoot T.nu)) d).tendsto 0
  simp only [map_zero, zero_mul, add_zero] at hc
  rw [show toA (linRoot u ^ d) = toA (linRoot u) ^ d by simp [toA, map_pow]]
  exact (hc.mono_left nhdsWithin_le_nhds).congr fun s => by rw [linA_lamS]

theorem gap_sub_smul (j : ℕ) (lam nu : Wt Ψ N) (s : ℝ) (τ : Ψ) :
    gap j (lam - s • nu) τ = gap j lam τ - s * gap j nu τ := by
  simp only [gap, ent]
  split_ifs <;> simp <;> ring

end LimitVolumeRatio

end GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace LimitVolumeRatio

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem eventually_dominant (T : RootTower Ψ N) (u : Wt Ψ N) (hu : RegDominant u) :
    ∀ᶠ s in 𝓝 (0 : ℝ), Dominant (T.lamS u s) := by
  have key : ∀ τ (a b : Fin N), ∀ᶠ s in 𝓝 (0 : ℝ), a ≤ b → (T.lamS u s) τ b ≤ (T.lamS u s) τ a := by
    intro τ a b
    by_cases hab : a < b
    · have h1 : Tendsto (fun s : ℝ => u τ b - s * T.nu τ b) (𝓝 0) (𝓝 (u τ b - 0 * T.nu τ b)) :=
        (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0
      have h2 : Tendsto (fun s : ℝ => u τ a - s * T.nu τ a) (𝓝 0) (𝓝 (u τ a - 0 * T.nu τ a)) :=
        (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0
      filter_upwards [h1.eventually_lt h2 (by simpa using hu τ a b hab)] with s hs _
      simpa [RootTower.lamS] using hs.le
    · exact Eventually.of_forall fun s h => by
        have : a = b := le_antisymm h (not_lt.mp hab)
        subst this
        exact le_rfl
  exact eventually_all.2 fun τ => eventually_all.2 fun a => eventually_all.2 fun b => key τ a b

theorem eventually_threshold [Nonempty Ψ] (T : RootTower Ψ N) (u : Wt Ψ N) (g : ℝ) (hw : WeightHyp T.j u g)
    (B : ℕ) (hB : bigB0 u g < B + 1) :
    ∀ᶠ s in 𝓝 (0 : ℝ), NefThreshold T.j B (T.lamS u s) := by
  have hF : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by have := T.j_pos; have := T.j_lt; omega)
  have hg : 0 < g := hw.1
  have hx : 0 ≤ ‖u‖ := norm_nonneg _
  set F : ℝ := (Fintype.card Ψ : ℝ)
  set x : ℝ := ‖u‖
  have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hB' : 4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3 < (B : ℝ) - 2 := by
    simp only [bigB0] at hB
    nlinarith
  have hxg : x / g * g = x := div_mul_cancel₀ x hg.ne'
  have hFN : (4 : ℝ) ≤ F * (N : ℝ) ^ 2 := by
    have := mul_le_mul hF hn2 (by norm_num) (by linarith)
    linarith
  have hpos : 0 < 4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3 := by
    have : 0 ≤ x / g := div_nonneg hx hg.le
    have h' : 0 ≤ 4 * F * (N : ℝ) ^ 2 * (x / g) := mul_nonneg (by positivity) this
    linarith
  have hB2 : 0 ≤ (B : ℝ) - 2 := by linarith
  have at0 : ∀ τ, 4 * F * x < ((B : ℝ) - 2) * gap T.j u τ := by
    intro τ
    have h1 : ((B : ℝ) - 2) * g ≤ ((B : ℝ) - 2) * gap T.j u τ :=
      mul_le_mul_of_nonneg_left (hw.2.2.1 τ) hB2
    have h2 := mul_lt_mul_of_pos_right hB' hg
    have h3 : (4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3) * g =
        4 * F * (N : ℝ) ^ 2 * g + 4 * F * (N : ℝ) ^ 2 * x - 3 * g := by
      rw [sub_mul, add_mul, mul_assoc (4 * F * (N : ℝ) ^ 2), hxg]
    have h4 : 4 * F * x ≤ 4 * F * (N : ℝ) ^ 2 * x := by
      have e : 4 * F * (N : ℝ) ^ 2 * x - 4 * F * x = (4 * F * x) * ((N : ℝ) ^ 2 - 1) := by ring
      have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * F) hx) (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ 2 - 1)
      linarith
    have h5 : 0 < 4 * F * (N : ℝ) ^ 2 * g - 3 * g := by
      have e : 4 * F * (N : ℝ) ^ 2 * g - 3 * g = g * (4 * (F * (N : ℝ) ^ 2) - 3) := by ring
      rw [e]
      exact mul_pos hg (by linarith)
    linarith
  have key : ∀ τ, ∀ᶠ s in 𝓝 (0 : ℝ), 4 * F * ‖T.lamS u s‖ ≤ ((B : ℝ) - 2) * gap T.j (T.lamS u s) τ := by
    intro τ
    have h1 : Tendsto (fun s : ℝ => 4 * F * ‖T.lamS u s‖) (𝓝 0) (𝓝 (4 * F * ‖T.lamS u 0‖)) :=
      ((continuous_const.mul (continuous_const.sub (continuous_id.smul continuous_const)).norm)).tendsto 0
    have h2 : Tendsto (fun s : ℝ => ((B : ℝ) - 2) * (gap T.j u τ - s * gap T.j T.nu τ)) (𝓝 0)
        (𝓝 (((B : ℝ) - 2) * (gap T.j u τ - 0 * gap T.j T.nu τ))) :=
      (continuous_const.mul (continuous_const.sub (continuous_id.mul continuous_const))).tendsto 0
    have h0 : 4 * F * ‖T.lamS u 0‖ < ((B : ℝ) - 2) * (gap T.j u τ - 0 * gap T.j T.nu τ) := by
      simpa [RootTower.lamS] using at0 τ
    filter_upwards [h1.eventually_lt h2 h0] with s hs
    rw [RootTower.lamS, gap_sub_smul]
    exact hs.le
  exact eventually_all.2 key

theorem tower_T1_limit_of_inputs : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ]
    (T : RootTower Ψ N), T.Proportional → T.I2 II → T.I3 → T.T1 II := by
  intro II Ψ _ _ N _ T hProp hI2 hI3 u g hw B hB c
  have hF : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by have := T.j_pos; have := T.j_lt; omega)
  have hB2 : 2 ≤ B := by
    have hq : 0 ≤ ‖u‖ / g := div_nonneg (norm_nonneg _) hw.1.le
    have : (16 : ℝ) ≤ bigB0 u g := by
      simp only [bigB0]
      have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      have hFN : (4 : ℝ) ≤ (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2 := by nlinarith
      have h1q : (1 : ℝ) ≤ 1 + ‖u‖ / g := by linarith
      have := mul_le_mul hFN h1q zero_le_one (by positivity)
      nlinarith
    have : (15 : ℝ) < B := by linarith
    exact_mod_cast (show (2 : ℝ) ≤ B by linarith)
  have hdom := eventually_dominant T u hw.2.1
  have hthr := eventually_threshold T u g hw B hB
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := eventually_mem_nhdsWithin

  obtain ⟨s₁, hs₁, C₂, hag⟩ := hI2 (l1 u)
  have hdiff : Tendsto (fun s => T.mbarTop II B c u s - T.PBs II B c (T.lamS u s) s) (𝓝[>] 0) (𝓝 0) := by
    have hlin : Tendsto (fun s : ℝ => C₂ * s) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlin
    filter_upwards [hpos, (eventually_le_nhds hs₁).filter_mono nhdsWithin_le_nhds,
      hdom.filter_mono nhdsWithin_le_nhds] with s h0 h1 h2
    exact hag B hB2 c u s le_rfl h0 h1 h2
  have hPB : Tendsto (fun s => T.PBs II B c (T.lamS u s) s) (𝓝[>] 0)
      (𝓝 (T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)))) :=
    LimitVolumeRatio.tendsto_lin ((T.M B c).PP II) T u (dimFl Ψ N + 1)
  have hbar : Tendsto (fun s => T.mbarTop II B c u s) (𝓝[>] 0)
      (𝓝 (T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)))) := by
    have h := hPB.add hdiff
    rw [add_zero] at h
    exact h.congr fun s => by ring
  have hdeg : Tendsto (fun s => T.mDeg B c u s) (𝓝[>] 0) (𝓝 (T.vol c * flagDeg u)) := by
    have h := LimitVolumeRatio.tendsto_lin (T.M B c).geoFun T u (dimFl Ψ N)
    rwa [hProp.2.1 B c] at h
  have hvpos : 0 < T.vol c * flagDeg u :=
    mul_pos (hProp.1 c) ((flagDeg_eq_weyl Ψ N u).2.1 hw.2.1)
  refine ⟨?_, hbar, hdeg, hvpos, ?_⟩
  · obtain ⟨s₀, hs₀, h3⟩ := hI3 (l1 u)
    filter_upwards [hpos, (eventually_le_nhds hs₀).filter_mono nhdsWithin_le_nhds,
      hdom.filter_mono nhdsWithin_le_nhds, hthr.filter_mono nhdsWithin_le_nhds] with s h0 h1 h2 h4
    exact h3 B hB2 c u s le_rfl h0 h1 h2 h4
  · have hne : ((dimFl Ψ N : ℝ) + 1) * (T.vol c * flagDeg u) ≠ 0 :=
      (mul_pos (by positivity) hvpos).ne'
    exact hbar.div (hdeg.const_mul _) hne

end LimitVolumeRatio

end GlobalTheory.CompanionTheory.Ar.Top
end
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

private theorem card_lt_lemma {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter fun i : Fin N => (i : ℕ) < j).card = j := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (show {i : Fin N // (i : ℕ) < j} ≃ Fin j from
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, lt_of_lt_of_le y.2 hj⟩, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl })]
  exact Fintype.card_fin j

theorem flag_degree_low_zero {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (hj : j ≤ N) (τ : Ψ) (Q : RP Ψ N) :
    degFl (pkLow j τ 0 * Q) = j * degFl Q := by
  have hp : (pkLow j τ 0 : RP Ψ N) = C (j : ℝ) := by
    unfold pkLow
    simp only [pow_zero, Finset.sum_const, card_lt_lemma hj, nsmul_eq_mul, mul_one]
    exact (map_natCast C j).symm
  rw [hp]
  unfold degFl
  simp only [coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem flat_85_bound : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C rd Lval : ℝ) (B₀ : ℕ) (A₀ b₀ : ℝ), T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C rd Lval → 128 ≤ B₀ → T.bad.card ≤ B₀ → T.IdentAt II hh frob B₀ A₀ b₀ → |T.j * A₀ + N * b₀| ≤ C * N * bigLam B₀ rd Lval := by
  intro II Ψ _ _ N T _ hh frob C rd Lval B₀ A₀ b₀ hP hI9 hF hB hbad hId
  unfold RootTower.Proportional at hP
  unfold I9 at hI9
  obtain ⟨τ⟩ := ‹Nonempty Ψ›
  obtain ⟨⟨Q, hQ, hdeg⟩, -⟩ := testForms_sh_tot Ψ N T.j τ T.j_pos T.j_lt
  obtain ⟨h, hPP, hbd⟩ := hF
  have hN : 1 ≤ N := le_trans T.j_pos T.j_lt.le
  have hQ' : Q.IsHomogeneous (dimFl Ψ N + 1 - 1) := by simpa using hQ
  have hid := hId τ 1 le_rfl hN Q hQ'
  have hhh : hh (pk τ 1 * Q) = 0 := hI9.2.2 τ Q hQ
  have hSh : ∀ σ, Sh T.j σ (pk τ 1 * Q) = if σ = τ then (T.j : ℝ) else 0 := by
    intro σ
    rw [(RootFieldNumerics.shift_power_sum_mul Ψ N T.j τ σ 1 Q le_rfl).1]
    simp [flag_degree_low_zero T.j T.j_lt.le τ Q, hdeg]
  have hTot : ∀ σ, Tot σ (pk τ 1 * Q) = if σ = τ then (N : ℝ) else 0 := by
    intro σ
    rw [(RootFieldNumerics.shift_power_sum_mul Ψ N T.j τ σ 1 Q le_rfl).2]
    simp [hdeg]
  have hrest : restSum T.j T.bad frob B₀ τ 1 Q = 0 := by
    simp [restSum, restTerm]
  have hL : T.PPt II B₀ (pk τ 1 * Q) = ∑ c, h B₀ c τ * T.vol c := by
    unfold RootTower.PPt
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hPP B₀ (by omega) c τ Q hQ, hdeg, mul_one]
  rw [hL, hhh, hrest] at hid
  simp only [hSh, hTot, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at hid
  have hvol : 0 < T.volT := Finset.sum_pos (fun c _ => hP.1 c) Finset.univ_nonempty
  have hv0 : T.volT ≠ 0 := hvol.ne'
  have key : (T.j : ℝ) * A₀ + N * b₀ = -(∑ c, h B₀ c τ * T.vol c) / T.volT := by
    rw [hid]
    field_simp
    ring
  rw [key, abs_div, abs_neg, abs_of_pos hvol, div_le_iff₀ hvol]
  calc |∑ c, h B₀ c τ * T.vol c| ≤ ∑ c, |h B₀ c τ * T.vol c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, |h B₀ c τ| * T.vol c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [abs_mul, abs_of_pos (hP.1 c)]
    _ ≤ ∑ c, C * N * bigLam B₀ rd Lval * T.vol c := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact mul_le_mul_of_nonneg_right (hbd B₀ hB hbad c τ) (hP.1 c).le
    _ = C * N * bigLam B₀ rd Lval * T.volT := by
        rw [← Finset.mul_sum]
        rfl

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem sum_group_apply_eq {Ψ : Type} (Γ : Subgroup (Equiv.Perm Ψ)) [Fintype Γ]
    (htr : ∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') (f : Ψ → ℝ) (τ τ' : Ψ) :
    ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ) = ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ') := by
  obtain ⟨ρ, hρ, rfl⟩ := htr τ' τ
  exact Fintype.sum_equiv (Equiv.mulRight (⟨ρ, hρ⟩ : Γ)) _ _ (fun g => by simp [Equiv.Perm.mul_apply])

theorem exists_group_mean {Ψ : Type} (Γ : Subgroup (Equiv.Perm Ψ)) [Fintype Γ]
    (htr : ∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') (f : Ψ → ℝ) :
    ∃ A : ℝ, ∀ τ, ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ) = (Fintype.card Γ : ℝ) * A := by
  rcases isEmpty_or_nonempty Ψ with h | ⟨⟨τ₀⟩⟩
  · exact ⟨0, fun τ => (h.false τ).elim⟩
  · have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    refine ⟨(∑ g : Γ, f ((g : Equiv.Perm Ψ) τ₀)) / (Fintype.card Γ : ℝ), fun τ => ?_⟩
    rw [mul_div_cancel₀ _ hc]
    exact sum_group_apply_eq Γ htr f τ τ₀

theorem mean_estimate {G Ψ : Type} [Fintype G] [Nonempty G] [Fintype Ψ] (P V H bd A Bs : ℝ) (S U : Ψ → ℝ)
    (a b : G → Ψ → ℝ) (hA : ∀ τ, ∑ g, a g τ = (Fintype.card G : ℝ) * A)
    (hB : ∀ τ, ∑ g, b g τ = (Fintype.card G : ℝ) * Bs)
    (h : ∀ g, |P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)| ≤ bd) :
    |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)| ≤ bd := by
  have hn : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card G : ℝ) with hndef
  have h1 : ∑ g, ∑ τ, (a g τ - b g τ) * S τ = n * ((A - Bs) * ∑ τ, S τ) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hA, hB]
    ring
  have h2 : ∑ g, ∑ τ, b g τ * U τ = n * (Bs * ∑ τ, U τ) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_mul, hB]
    ring
  have key : ∑ g : G, (P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)) =
      n * (P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)) := by
    have : ∀ g : G, P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ) =
        (P - V * H) + V * ∑ τ, (a g τ - b g τ) * S τ + V * ∑ τ, b g τ * U τ := fun g => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [← hndef]
    ring
  have hle : n * |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)| ≤ n * bd := by
    calc n * |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)|
        = |n * (P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ))| := by
          rw [abs_mul, abs_of_pos hn]
      _ = |∑ g : G, (P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ))| := by rw [key]
      _ ≤ ∑ g : G, |P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g : G, bd := Finset.sum_le_sum fun g _ => h g
      _ = n * bd := by simp [hndef]
  exact le_of_mul_le_mul_left hle hn

theorem thmBA_of_thmB_propA : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.ThmB II hh → T.PropA II →
    LabelInv (Ψ := Ψ) (N := N) hh → T.ThmBA II hh := by
  intro II Ψ _ _ N T hh hB hA hL
  obtain ⟨C, B₁, hC⟩ := hB
  obtain ⟨Γ, htr, hinv⟩ := hA
  have : Fintype Γ := Fintype.ofFinite _
  refine ⟨C, max B₁ 2, fun B hBge => ?_⟩
  obtain ⟨α, β, hm⟩ := hC B (le_trans (le_max_left _ _) hBge)
  obtain ⟨A, hAm⟩ := exists_group_mean Γ htr α
  obtain ⟨Bs, hBm⟩ := exists_group_mean Γ htr β
  refine ⟨A, Bs, fun m hdeg => ?_⟩
  refine mean_estimate (G := Γ) _ _ _ _ A Bs _ _ (fun g τ => α ((g : Equiv.Perm Ψ) τ))
    (fun g τ => β ((g : Equiv.Perm Ψ) τ)) hAm hBm fun g => ?_
  set F : RP Ψ N := monomial m 1 with hF
  set φ : Ψ × Fin N → Ψ × Fin N := fun x => ((g : Equiv.Perm Ψ) x.1, x.2) with hφ
  have hR : (monomial (m.mapDomain φ) 1 : RP Ψ N) = rename φ F := (rename_monomial φ m 1).symm
  have hest := hm (m.mapDomain φ) (by rw [Finsupp.degree_mapDomain]; exact hdeg)
  have anti := fun τ j => ((GlobalTheory.T.flag_degree_symmetries Ψ N).2 (g : Equiv.Perm Ψ) F).2 j τ
  have hS : ∑ τ, (α τ - β τ) * Sh T.j τ (rename φ F) =
      ∑ τ, (α ((g : Equiv.Perm Ψ) τ) - β ((g : Equiv.Perm Ψ) τ)) * Sh T.j τ F := by
    rw [← Equiv.sum_comp (g : Equiv.Perm Ψ)]
    exact Finset.sum_congr rfl fun τ _ => by rw [(anti τ T.j).1]
  have hU : ∑ τ, β τ * Tot τ (rename φ F) = ∑ τ, β ((g : Equiv.Perm Ψ) τ) * Tot τ F := by
    rw [← Equiv.sum_comp (g : Equiv.Perm Ψ)]
    exact Finset.sum_congr rfl fun τ _ => by rw [(anti τ T.j).2]
  rw [hR, hS, hU, hinv g g.2 B (le_trans (le_max_right _ _) hBge) F, hL g F] at hest
  exact hest

end GlobalTheory.CompanionTheory.Ar.Top
end

section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

def lieRank {Ψ : Type} (N j : ℕ) (s : Ψ ⊕ Ψ) : ℝ := if s.isLeft then (j : ℝ) else ((N - j : ℕ) : ℝ)

theorem delta_card_filter_lt {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).card = j := by
  have h : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).map Fin.valEmbedding = Finset.range j := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro ha
      exact ⟨⟨a, lt_of_lt_of_le ha hj⟩, ha, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Finset.card_range]

theorem delta_card_filter_ge {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ))).card = N - j := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  rw [delta_card_filter_lt hj] at h
  omega

theorem pLie_zero {Ψ : Type} {N j : ℕ} (hj : j ≤ N) (s : Ψ ⊕ Ψ) :
    (pLie j 0 s : RP Ψ N) = C (lieRank N j s) := by
  cases s with
  | inl τ =>
    simp only [pLie, pkLow, pow_zero, Finset.sum_const, delta_card_filter_lt hj, lieRank, Sum.isLeft_inl, if_true,
      nsmul_eq_mul, mul_one, map_natCast]
  | inr τ =>
    simp only [pLie, pow_zero, Finset.sum_const, delta_card_filter_ge hj, lieRank, Sum.isLeft_inr,
      Bool.false_eq_true, if_false, nsmul_eq_mul, mul_one, map_natCast]

theorem degFl_C_mul {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (c : ℝ) (Q : RP Ψ N) :
    degFl (C c * Q) = c * degFl Q := by
  simp only [degFl, coeff_C_mul]
  have h : ∀ f g : (Ψ → Equiv.Perm (Fin N)) → ℝ, ∑ σ, f σ * (c * g σ) = c * ∑ σ, f σ * g σ := by
    intro f g
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [h]
  ring

theorem deltaTerm_eq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), j ≤ N → 0 < N → FrobShape frob → ∃ κ : ℕ → ℝ, ∀ (p : ℕ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), 2 ≤ p → 1 ≤ k → deltaTerm j p τ (frob p τ) k Q = -(Real.log p / ((p : ℝ) - 1)) * ∑ σ, Sh j σ (pk τ k * Q) + κ p * ∑ σ, Tot σ (pk τ k * Q) + restTerm j p (frob p τ) k Q := by
  intro Ψ _ _ N j frob hj hN hF
  rcases isEmpty_or_nonempty Ψ with hE | ⟨⟨τ₀⟩⟩
  · exact ⟨0, fun _ τ => isEmptyElim τ⟩
  refine ⟨fun p => Real.log p / N * ∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * lieRank N j (frob p τ₀ n), ?_⟩
  intro p τ k Q hp hk
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hSh : ∑ σ, Sh j σ (pk τ k * Q) = k * degFl (pkLow j τ (k - 1) * Q) := by
    rw [Finset.sum_congr rfl (fun σ _ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N j τ σ k Q hk).1)]
    simp
  have hTot : ∑ σ, Tot σ (pk τ k * Q) = if k = 1 then N * degFl Q else 0 := by
    rw [Finset.sum_congr rfl (fun σ _ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N j τ σ k Q hk).2)]
    by_cases h1 : k = 1 <;> simp [h1]
  rw [hSh, hTot]
  by_cases h1 : k = 1
  · subst h1
    have hrank : ∀ n, degFl (pLie j (1 - 1) (frob p τ n) * Q) =
        lieRank N j (frob p τ₀ n) * degFl Q := by
      intro n
      have : lieRank N j (frob p τ n) = lieRank N j (frob p τ₀ n) := by
        simp only [lieRank, hF p n τ τ₀]
      rw [Nat.sub_self, pLie_zero hj, degFl_C_mul, this]
    have hsum : (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * degFl (pLie j (1 - 1) (frob p τ n) * Q)) =
        (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * lieRank N j (frob p τ₀ n)) * degFl Q := by
      rw [← tsum_mul_right]
      exact tsum_congr (fun n => by rw [hrank]; ring)
    simp only [deltaTerm, restTerm, hsum]
    simp only [if_true, Nat.one_lt_ofNat, Nat.not_ofNat_le_one, if_false]
    field_simp
    ring
  · have h2 : 2 ≤ k := by omega
    simp only [deltaTerm, restTerm, h1, if_false, h2, if_true]
    ring

end GlobalTheory.CompanionTheory.Ar.Top
end
end
