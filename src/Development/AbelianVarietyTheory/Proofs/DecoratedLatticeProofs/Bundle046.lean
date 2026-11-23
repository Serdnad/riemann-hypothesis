module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle038
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormaliserUnipSymCharPattern
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

namespace GlobalTheory.LowerHecke

theorem repsBuild : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ N : GL D k → Finset (Matrix D A k), (∀ g ∈ R, (∀ ν ∈ N g, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N g ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) → ∃ R' : Finset (GL (A ⊕ D) k), IsReps (mtor ϖ (indic s)) R' blockDet ∧ ∀ F : GL (A ⊕ D) k → ℂ, ∑ j ∈ R', F j = ∑ g ∈ R, ∑ ν ∈ N g, F (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ N hN
  classical
  set t : GL (A ⊕ D) k := mtor ϖ (indic s) with ht
  let f : (Σ _ : GL D k, Matrix D A k) → GL (A ⊕ D) k :=
    fun x => lowU x.2 * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ x.1)

  have key : ∀ g₁ ∈ R, ∀ ν₁ ∈ N g₁, ∀ g₂ ∈ R, ∀ ν₂ ∈ N g₂,
      (f ⟨g₁, ν₁⟩ * t)⁻¹ * (f ⟨g₂, ν₂⟩ * t) ∈ parahoric k A D → g₁ = g₂ ∧ ν₁ = ν₂ := by
    intro g₁ hg₁ ν₁ hν₁ g₂ hg₂ ν₂ hν₂ h
    obtain ⟨rfl, μ, hμ, hdiff⟩ := GlobalTheory.T.lowerUnipotent_blockDiag_cosets_distinct k A D ϖ hϖ s R hR κ κ' hκ g₁ hg₁ g₂ hg₂ ν₁ ν₂ h
    refine ⟨rfl, ?_⟩
    obtain ⟨hsmall, huniq⟩ := hN g₁ hg₁
    obtain ⟨ν', _, hν'⟩ := huniq ν₂ (hsmall ν₂ hν₂)
    have e2 : ν₂ = ν' := hν' ν₂ ⟨hν₂, 0, fun i a => by simp, by simp⟩
    have e1 : ν₁ = ν' := hν' ν₁ ⟨hν₁, μ, hμ, hdiff⟩
    rw [e1, e2]
  refine ⟨(R.sigma N).image f, ⟨?_, ?_⟩, ?_⟩
  · intro j hj
    obtain ⟨⟨g, ν⟩, hx, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_sigma] at hx
    obtain ⟨hg, hν⟩ := hx
    refine ⟨Subgroup.mul_mem _ (lowU_mem ((hN g hg).1 ν hν)) (emb_mem (hκ g hg).1), ?_⟩
    have h22 : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)).1.toBlocks₂₂ = (κ g).1 := by
      rw [Units.val_mul, val_emb_one, val_lowU, fromBlocks_multiply]; simp
    show ((blockDet (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) : kˣ) : k) = _
    rw [blockDet_lowU_emb, h22, GeneralLinearGroup.val_det_apply]
  · intro j hj
    obtain ⟨g, hg, ν₀, hν₀, hall⟩ := GlobalTheory.T.exists_lowerUnipotent_blockDiag_coset_rep k A D ϖ hϖ s R hR κ κ' hκ j hj
    obtain ⟨ν', ⟨hν'N, μ, hμ, hdiff⟩, -⟩ := (hN g hg).2 ν₀ hν₀
    refine ⟨f ⟨g, ν'⟩, ⟨Finset.mem_image.2 ⟨(⟨g, ν'⟩ : Σ _ : GL D k, Matrix D A k), Finset.mem_sigma.2 ⟨hg, hν'N⟩, rfl⟩,
      hall ν' ⟨μ, hμ, hdiff⟩⟩, ?_⟩
    rintro j' ⟨hj', hmem⟩
    obtain ⟨⟨g₂, ν₂⟩, hx, rfl⟩ := Finset.mem_image.1 hj'
    rw [Finset.mem_sigma] at hx
    have hmem' : (f ⟨g, ν'⟩ * t)⁻¹ * (j * t) ∈ parahoric k A D := hall ν' ⟨μ, hμ, hdiff⟩
    have hc : (f ⟨g₂, ν₂⟩ * t)⁻¹ * (f ⟨g, ν'⟩ * t) ∈ parahoric k A D := by
      have := Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hmem')
      simpa [mul_assoc] using this
    obtain ⟨rfl, rfl⟩ := key g₂ hx.1 ν₂ hx.2 g hg ν' hν'N hc
    rfl
  · intro F
    rw [Finset.sum_image, Finset.sum_sigma]
    rintro ⟨g₁, ν₁⟩ h₁ ⟨g₂, ν₂⟩ h₂ heq
    rw [Finset.coe_sigma, Set.mem_sigma_iff] at h₁ h₂
    have hc : (f ⟨g₁, ν₁⟩ * t)⁻¹ * (f ⟨g₂, ν₂⟩ * t) ∈ parahoric k A D := by
      rw [show f ⟨g₁, ν₁⟩ = f ⟨g₂, ν₂⟩ from heq, inv_mul_cancel]; exact Subgroup.one_mem _
    obtain ⟨rfl, rfl⟩ := key g₁ h₁.1 ν₁ h₁.2 g₂ h₂.1 ν₂ h₂.2 hc
    rfl

end GlobalTheory.LowerHecke
end

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.hondaFrobeniusTwistLog_additive_mod_prime : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ (i : ℕ), 0 < i → ∀ m, ‖MvPowerSeries.coeff m (Formalism.L2.Th1.C.be0 f e (frobOp σ l i f) (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)))‖ ≤ ‖(l : K)‖ := by
  first | exact @GlobalTheory.Honda.twistLog_additive_mod | exact GlobalTheory.Honda.twistLog_additive_mod | (intros; apply GlobalTheory.Honda.twistLog_additive_mod <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.hondaFrobeniusTwistLog_eigen_mod_prime : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → ∀ (i : ℕ), 0 < i → CoefLe ‖(l : K)‖ ((frobOp σ l i f).subst (Formalism.L2.Th1.C.mulBy f e w) - C ((σ ^ i) w) * frobOp σ l i f) := by
  first | exact @GlobalTheory.Honda.frobLog_eigen | exact GlobalTheory.Honda.frobLog_eigen | (intros; apply GlobalTheory.Honda.frobLog_eigen <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

open Classical

namespace GlobalTheory.ParHeckeTarget

theorem sum_reps_datum_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (R : Finset (GL (A ⊕ D') k)) d, IsReps (mtor ϖ (indic s)) R d → ∀ RK, IsRepsK (GlobalTheory.GLDoubling.torusElt k D' ϖ (indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, ∑ j ∈ R, ((ξ (d j) * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = ∑ g ∈ RK, liftS ξ (fun y => intInd ((g⁻¹).1 * y)) x := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ hξ s R d hR RK hRK x
  have hL : ∀ j ∈ R, ((ξ (d j) * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) =
      if InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) then datum ξ x else 0 := by
    intro j hj
    have h := GlobalTheory.T.parahoric_hecke_sum_term_at_coset k A D D' ϖ hϖ ξ hξ s j (hR.1 j hj).1 (d j) (hR.1 j hj).2 x
    split_ifs with hs
    · exact h.1 hs
    · rw [h.2 hs, mul_zero]
  have hRt : ∀ g ∈ RK, liftS ξ (fun y => intInd ((g⁻¹).1 * y)) x =
      if (∀ i l, ((g⁻¹).1 * schur x) i l ∈ 𝒪[k]) then datum ξ x else 0 := by
    intro g _
    simp only [liftS, intInd]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hRt, ← Finset.sum_filter, ← Finset.sum_filter,
    Finset.sum_const, Finset.sum_const]
  by_cases hx : InSupp x
  · rw [GlobalTheory.T.card_filter_parahoric_cosets_eq_schur_count k A D D' ϖ hϖ s R d hR RK hRK x hx]
  · have h0 : datum ξ x = 0 := by simp only [datum, dif_neg hx]
    simp [h0]

end GlobalTheory.ParHeckeTarget
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem finrank_ker_Pu_le_hsDev (D : D7) (u : D.what₂.Word) :
    (Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) : ℝ) ≤ hsDev D u := by
  unfold hsDev
  refine GlobalTheory.T.finrank_ker_le_hilbertSchmidtNormSq_sub_id (Kmat D.s u u) _ ?_
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hx' : D.s.Pu u x = 0 := hx
  simp [Kmat, hx']

end GlobalTheory.Core.Rk
end

section

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem dstar_pos_of (D : D7) (u : D.what₂.Word) : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos

theorem diagS_mono {D : D7} {u : D.what₂.Word} {e e' : ℝ} (h : DiagS D u e) (he : e ≤ e') : DiagS D u e' := by
  unfold DiagS at *
  exact h.trans (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))

theorem kfk_nonneg (D : D7) : 0 ≤ kfk D := by
  unfold kfk
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_natCast_nonneg _)

theorem diag_corollary :
    (∀ (D : D7) (u : D.what₂.Word) (A x κ : ℝ), 0 ≤ A → TwoTerm D u A x → (d0 D u : ℝ) ≤ κ * D.what₂.Dstar →
      DiagS D u (A * κ + x)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (L C : ℝ), 0 ≤ C * mfL D L → SDiag D u L C → Small D u L C →
      DiagS D u (eDiag D L C)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (Γ₀ : ℝ), SAbs D u Γ₀ ↔ TwoTerm D u Γ₀ (1 / 4)) := by
  have first : ∀ (D : D7) (u : D.what₂.Word) (A x κ : ℝ), 0 ≤ A → TwoTerm D u A x → (d0 D u : ℝ) ≤ κ * D.what₂.Dstar →
      DiagS D u (A * κ + x) := by
    intro D u A x κ hA h hd
    have hD := dstar_pos_of D u
    have hd0 : (0 : ℝ) ≤ (d0 D u : ℝ) := Nat.cast_nonneg _
    have hq : (d0 D u : ℝ) ^ 2 / D.what₂.Dstar ≤ κ * (d0 D u : ℝ) := by
      rw [div_le_iff₀ hD]
      have := mul_le_mul_of_nonneg_left hd hd0
      nlinarith
    unfold DiagS
    unfold TwoTerm at h
    calc hsDev D u ≤ A * (d0 D u : ℝ) ^ 2 / D.what₂.Dstar + x * (d0 D u : ℝ) := h
      _ = A * ((d0 D u : ℝ) ^ 2 / D.what₂.Dstar) + x * (d0 D u : ℝ) := by rw [mul_div_assoc]
      _ ≤ A * (κ * (d0 D u : ℝ)) + x * (d0 D u : ℝ) := by gcongr
      _ = (A * κ + x) * (d0 D u : ℝ) := by ring
  refine ⟨first, ?_, ?_⟩
  · intro D u L C hc hS hSm
    set c := C * mfL D L with hcdef
    have h2 : Real.exp (-(2 * C * mfL D L)) = Real.exp (-c) * Real.exp (-c) := by
      rw [← Real.exp_add]; congr 1; rw [hcdef]; ring
    have h1 : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
    have hle : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hpos : 0 < Real.exp (-c) := Real.exp_pos _
    have hk := kfk_nonneg D
    have hkk : Real.exp (-kfk D) ≤ Real.exp (-(kfk D / 2)) := Real.exp_le_exp.2 (by linarith)
    have hd := first D u (4 * (Real.exp c + 1)) (4 * Real.exp (-(kfk D / 2)) + 2 * Real.exp (-kfk D))
      (Real.exp (-(2 * C * mfL D L))) (by positivity) hS (by unfold Small at hSm; linarith [hSm])
    refine diagS_mono hd ?_
    unfold eDiag
    rw [h2, ← hcdef]
    have : 4 * (Real.exp c + 1) * (Real.exp (-c) * Real.exp (-c)) = 4 * Real.exp (-c) + 4 * (Real.exp (-c) * Real.exp (-c)) := by
      have e : 4 * (Real.exp c + 1) * (Real.exp (-c) * Real.exp (-c))
          = 4 * (Real.exp c * Real.exp (-c)) * Real.exp (-c) + 4 * (Real.exp (-c) * Real.exp (-c)) := by ring
      rw [e, h1]; ring
    rw [this]
    nlinarith
  · intro D u Γ₀
    unfold SAbs TwoTerm
    rw [show (1 / 4 : ℝ) * (d0 D u : ℝ) = (d0 D u : ℝ) / 4 by ring]

end GlobalTheory.Core.Rk
end

section

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem exp_neg_five_lt : Real.exp (-5) < 1 / 128 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2.7 : ℝ) ^ 5 < Real.exp 1 ^ 5 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h3 : (128 : ℝ) < Real.exp 5 := by
    rw [h5]; exact lt_trans (by norm_num) h2
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) h3

theorem five_le_half_kfk (D : D7) : 5 ≤ kfk D / 2 := by
  have hk : 5 ≤ D.R.k := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    omega
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.n := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.n := rfl
    omega
  have hkR : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hlog : 1 ≤ Real.log (D.R.k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hkf : (10 : ℝ) ≤ (D.R.k : ℝ) * D.R.f := by nlinarith
  have : (10 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * Real.log (D.R.k : ℝ) := by nlinarith
  unfold kfk
  linarith

theorem two_eDiag_lt : ∀ (D : D7) (u : D.what₂.Word) (L C : ℝ), 5 ≤ C * mfL D L → 4 * D.R.f + 1 ≤ (D.mem u).A.T → 2 * eDiag D L C < 1 - (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) := by
  intro D u L C hC hT
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.n := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.n := rfl
    omega
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hTR : 4 * (D.R.f : ℝ) + 1 ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT
  have hden : 0 < ((D.mem u).A.T : ℝ) - 1 := by linarith
  have hq : (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ hden]
    linarith
  have h5 := exp_neg_five_lt
  have hA : Real.exp (-(C * mfL D L)) ≤ Real.exp (-5) :=
    Real.exp_le_exp.mpr (by linarith)
  have hB : Real.exp (-(kfk D / 2)) ≤ Real.exp (-5) :=
    Real.exp_le_exp.mpr (by linarith [five_le_half_kfk D])
  unfold eDiag
  linarith

end GlobalTheory.Core.Rk
end

section

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace

theorem levelPrime_window : ∀ (D : D7) (u : D.what₂.Word),
    (RankMu D u → (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar) ∧
    (Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ)) ∧
    (∀ L C : ℝ, RankMu D u → 1 + 2 * C * mfL D L ≤ 2 * Real.log (D.mem u).A.GamP → Small D u L C) := by
  intro D u
  have hfN : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := Nat.one_le_two_pow (n := D.R.e)
    have := D.R.ord_pos
    omega
  have hkN : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hfN
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hkN
  have hfk : (0 : ℝ) < (D.R.f : ℝ) * D.R.k := by positivity
  have hdu : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  have hDs : 0 < (D.mem u).A.Dstar := (D.mem u).A.Dstar_pos
  have hDpos : 0 < D.what₂.Dstar := D.Dstar_eq u ▸ hDs
  have hq : 0 < (D.mem u).A.Dstar / (D.mem u).A.duStar := div_pos hDs hdu
  have hGp : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hXu : 0 < (D.mem u).A.Xu := Real.rpow_pos_of_pos hq _
  have hTs : 0 < (D.mem u).A.Tstar := mul_pos hXu (Real.rpow_pos_of_pos hGp _)
  have hlogTs : Real.log (D.mem u).A.Tstar =
      Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) := by
    unfold ColumnsAtT.Tstar
    rw [Real.log_mul hXu.ne' (Real.rpow_pos_of_pos hGp _).ne', Real.log_rpow hGp]
    ring
  obtain ⟨hT1, hT2⟩ := D.T_win u
  have hT0 : (0 : ℝ) < ((D.mem u).A.T : ℝ) := hTs.trans_le hT1
  have part2 : Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤
      Real.log ((D.mem u).A.T : ℝ) := by
    rw [← hlogTs]; exact Real.log_le_log hTs hT1
  have hTs_pow : (D.mem u).A.Tstar ^ (D.R.f * D.R.k) =
      (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 := by
    have hn : ((D.R.f * D.R.k : ℕ) : ℝ) = (D.R.f : ℝ) * D.R.k := by push_cast; ring
    rw [← Real.rpow_natCast, hn]
    unfold ColumnsAtT.Tstar ColumnsAtT.Xu
    rw [Real.mul_rpow (Real.rpow_pos_of_pos hq _).le (Real.rpow_pos_of_pos hGp _).le, ← Real.rpow_mul hq.le,
      ← Real.rpow_mul hGp.le, one_div_mul_cancel hfk.ne', div_mul_cancel₀ _ hfk.ne', Real.rpow_one,
      Real.rpow_neg hGp.le, Real.rpow_two, div_eq_mul_inv _ ((D.mem u).A.GamP ^ 2)]
  have hexp : (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 / ((D.R.f : ℝ) * D.R.k))
    calc (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k)
        ≤ Real.exp (1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have hTpow : ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k) ≤
      Real.exp 1 * ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2) := by
    calc ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k)
        ≤ ((1 + 1 / ((D.R.f : ℝ) * D.R.k)) * (D.mem u).A.Tstar) ^ (D.R.f * D.R.k) :=
          pow_le_pow_left₀ hT0.le hT2 _
      _ = (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) *
          ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2) := by
          rw [mul_pow, hTs_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)
  have part1 : RankMu D u → (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := by
    intro h
    unfold RankMu at h
    rw [h]
    have hT1' : (1 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by
      have : 0 < (D.mem u).A.T := by exact_mod_cast hT0
      exact_mod_cast this
    have hTk : 1 ≤ ((D.mem u).A.T : ℝ) ^ D.R.k := one_le_pow₀ hT1'
    have h1 : (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f ≤ ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k) := by
      rw [mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    calc ((D.mem u).A.duStar : ℝ) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f
        ≤ ((D.mem u).A.duStar : ℝ) *
          (Real.exp 1 * ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2)) :=
          mul_le_mul_of_nonneg_left (h1.trans hTpow) hdu.le
      _ = Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := by
          rw [← D.Dstar_eq u]
          first | (field_simp; ring) | field_simp
  refine ⟨part1, part2, fun L C hR hLC => ?_⟩
  unfold Small
  have hG2 : Real.exp (2 * Real.log (D.mem u).A.GamP) = (D.mem u).A.GamP ^ 2 := by
    rw [show 2 * Real.log (D.mem u).A.GamP = Real.log ((D.mem u).A.GamP ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  calc (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := part1 hR
    _ = D.what₂.Dstar * Real.exp (1 - 2 * Real.log (D.mem u).A.GamP) := by
        rw [Real.exp_sub, hG2]; ring
    _ ≤ D.what₂.Dstar * Real.exp (-(2 * C * mfL D L)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hDpos.le

end GlobalTheory.Core.Rk

end
end

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

theorem _root_.GlobalTheory.T.exists_normOne_with_residues_at_splitPlaces : ∀ {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A), (∀ a, σ (σ a) = a) → (∀ a ∈ S, σ a ∈ S) → ∀ (T : Finset P), (∀ Q ∈ T, ∀ Q' ∈ T, σ (Z.e Q) ≠ Z.e Q') → ∀ c : ∀ Q, (k Q)ˣ, ∃ z : S, (z : A) * σ z = 1 ∧ (∀ Q ∈ T, r Q z = c Q) ∧ ∀ b : A, (∀ Q ∈ T, Z.p Q b ∈ Z.O Q ∧ Z.p Q (σ b) ∈ Z.O Q) → (1 - (z : A)) * b ∈ S := by
  first | exact @GlobalTheory.LevNorm.exists_normOne_residues | exact GlobalTheory.LevNorm.exists_normOne_residues | (intros; apply GlobalTheory.LevNorm.exists_normOne_residues <;> assumption)
end

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

theorem _root_.GlobalTheory.T.isScalarMulIntegral_of_conj_integral_generators : ∀ (K : Type) [Field K] (O : ValuationSubring K) (n : ℕ) (m : GL (Fin n) K) (T : Set (GL (Fin n) O)), Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤ → (∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) → IsScal O m := by
  first | exact @GlobalTheory.ScalConj.isScal_of_conj | exact GlobalTheory.ScalConj.isScal_of_conj | (intros; apply GlobalTheory.ScalConj.isScal_of_conj <;> assumption)
end

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

theorem _root_.GlobalTheory.T.exists_unitary_integral_of_splitPlace_component : ∀ {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A), (∀ a, σ (σ a) = a) → (∀ a ∈ S, σ a ∈ S) → ∀ (n : ℕ) (G : GL (Fin n) S), cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) → ∀ Q Q' : P, σ (Z.e Q) = Z.e Q' → Q ≠ Q' → ∀ y : GL (Fin n) (Z.O Q), ∃ u : GL (Fin n) S, bc S.subtype u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧ bc (Z.pO Q) u = y ∧ ∀ Q'', Q'' ≠ Q → Q'' ≠ Q' → bc (Z.pO Q'') u = 1 := by
  first | exact @GlobalTheory.LevNorm.exists_unitary_int_of_component | exact GlobalTheory.LevNorm.exists_unitary_int_of_component | (intros; apply GlobalTheory.LevNorm.exists_unitary_int_of_component <;> assumption)
end

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

theorem _root_.GlobalTheory.T.normaliser_unipSym_char_pattern : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → 2 ≤ κ → ∀ ψ : AddChar k ℂ, ψ ≠ 1 → ∀ a : Fin n → Fin n → k, (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ M : GL (Fin n) k, (∀ h ∈ unipSym k n ρ κ, M * h * M⁻¹ ∈ unipSym k n ρ κ ∧ ψ (edgeVal ρ κ a (M * h * M⁻¹)) = ψ (edgeVal ρ κ a h)) → (∀ h ∈ unipSym k n ρ κ, M⁻¹ * h * M ∈ unipSym k n ρ κ) → ∃ s c : kˣ, ∃ h ∈ unipSym k n ρ κ, (M : Matrix (Fin n) (Fin n) k) = midDiag n ρ κ (s : k) (c : k) * (h : Matrix (Fin n) (Fin n) k) := by
  first | exact @GlobalTheory.SymNorm.normaliser_unipSym_char | exact GlobalTheory.SymNorm.normaliser_unipSym_char | (intros; apply GlobalTheory.SymNorm.normaliser_unipSym_char <;> assumption)
end
