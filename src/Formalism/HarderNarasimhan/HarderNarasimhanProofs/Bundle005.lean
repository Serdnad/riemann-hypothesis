module

public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNStep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle003
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle002
public import Lemmata.GeneralBFactLeftForm.Imports
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.CorankShare.StatementFR
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

section

open Module NumberField Finset Formalism.CorankShareLayerCake.FR

noncomputable section

namespace Formalism.HN

theorem frameB_share {I : Type} [Fintype I] (m : I → ℕ) (x : ∀ i, Fin (m i) → ℝ) (s u τ : ℝ)
    (hu : 0 < u) (hτ : 0 ≤ τ) (hsum : (∑ i, (m i : ℝ)) * s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s + u) :
    (∑ i, ((univ.filter (fun j => x i j < s - τ)).card : ℝ)) ≤ (∑ i, (m i : ℝ)) * (u / (u + τ)) := by
  have hone : ∀ i, ∑ j, x i j ≤ ((univ.filter (fun j => x i j < s - τ)).card : ℝ) * (s - τ) +
      ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) * (s + u) := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => x i j < s - τ)]
    have hc := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (m i))))
      (fun j => x i j < s - τ)
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have hc' : ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) =
        ((univ.filter (fun j => ¬ x i j < s - τ)).card : ℝ) := by
      have hc2 : ((univ.filter (fun j => x i j < s - τ)).card : ℝ) +
          ((univ.filter (fun j => ¬ x i j < s - τ)).card : ℝ) = (m i : ℝ) := by exact_mod_cast hc
      linarith
    rw [hc']
    have h1 : ∑ j ∈ univ.filter (fun j => x i j < s - τ), x i j ≤
        ∑ _j ∈ univ.filter (fun j => x i j < s - τ), (s - τ) :=
      Finset.sum_le_sum fun j hj => (Finset.mem_filter.1 hj).2.le
    have h2 : ∑ j ∈ univ.filter (fun j => ¬ x i j < s - τ), x i j ≤
        ∑ _j ∈ univ.filter (fun j => ¬ x i j < s - τ), (s + u) :=
      Finset.sum_le_sum fun j _ => hle i j
    rw [Finset.sum_const, nsmul_eq_mul] at h1 h2
    linarith
  have htot := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset I)) => hone i
  have hexp : ∑ i, (((univ.filter (fun j => x i j < s - τ)).card : ℝ) * (s - τ) +
      ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) * (s + u)) =
      (∑ i, (m i : ℝ)) * (s + u) - (∑ i, ((univ.filter (fun j => x i j < s - τ)).card : ℝ)) * (u + τ) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp] at htot
  have hut : 0 < u + τ := by linarith
  rw [mul_div_assoc', le_div_iff₀ hut]
  nlinarith

theorem frameB_count_lt {R V E : Type} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    (L : Submodule R V) (hL : IsLat ρ L) (θ : ℝ) :
    ((univ.filter (fun j => slopeList ρ L j < θ)).card : ℝ) =
      (rk ρ L : ℝ) - rk ρ (hnStep ρ L θ) := by
  have h2 := (polygon_slopes_characterization R V E ρ L hL).2.1 θ
  have h3 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (rk ρ L))))
    (fun j => θ ≤ slopeList ρ L j)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at h3
  have h4 : ((univ.filter (fun j => θ ≤ slopeList ρ L j)).card : ℝ) +
      ((univ.filter (fun j => slopeList ρ L j < θ)).card : ℝ) = (rk ρ L : ℝ) := by
    exact_mod_cast h3
  rw [h2] at h4
  linarith

theorem frameB_hnStep : HNStep.{0, 0, 0} :=
  hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties

def slopeNormalisingConstant (K : Type) [Field K] [NumberField K] : ℝ :=
  -Real.log 2 + logDisc K / (Module.finrank ℚ K : ℝ)

section Herm

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem frameB_muDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) :
    muDef b X L = 2 * slope (Formalism.HermitianLatticesTheory.realize b X) L + slopeNormalisingConstant K := by
  unfold muDef slopeNormalisingConstant; ring

theorem frameB_muMaxDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) :
    muMaxDef b X L = 2 * muMax (Formalism.HermitianLatticesTheory.realize b X) L + slopeNormalisingConstant K := by
  unfold muMaxDef slopeNormalisingConstant; ring

theorem frameB_muMinDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) :
    muMinDef b X L = 2 * muMin (Formalism.HermitianLatticesTheory.realize b X) L + slopeNormalisingConstant K := by
  unfold muMinDef slopeNormalisingConstant; ring

theorem frameB_rkK_top (b : Basis ι K V) (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) : rkK L = Fintype.card ι := by
  unfold rkK
  rw [hL, finrank_top, Module.finrank_eq_card_basis b]

end Herm

theorem frameB_sum_sl {R V E : Type} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    (L : Submodule R V) (hL : IsLat ρ L) (hr : rk ρ L ≠ 0) (a : ℝ) :
    ∑ j, (2 * slopeList ρ L j + a) = (rk ρ L : ℝ) * (2 * slope ρ L + a) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, (polygon_slopes_characterization R V E ρ L hL).2.2.1,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : slope ρ L = deg ρ L / rk ρ L := rfl
  have hr' : (rk ρ L : ℝ) ≠ 0 := by exact_mod_cast hr
  rw [hs]
  field_simp

theorem frameB_integral (u HH : ℝ) (hu : 0 < u) (hH : 0 ≤ HH) :
    ∫ τ in (0:ℝ)..HH, 4 * (u / (u + τ)) = 4 * u * Real.log (1 + HH / u) := by
  have h1 : ∫ τ in (0:ℝ)..HH, (u + τ)⁻¹ = Real.log ((u + HH) / u) := by
    have := intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) (a := 0) (b := HH) u
    rw [this, integral_inv_of_pos (by linarith) (by linarith)]
    simp
  have h2 : (1 + HH / u) = (u + HH) / u := by field_simp
  rw [h2, ← h1, ← intervalIntegral.integral_const_mul]
  congr 1; ext τ; ring

end Formalism.HN
end
end

section

open Module Submodule

noncomputable section

namespace Formalism.HN

universe u v w

theorem hnExtreme_mem_iff {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (θ : ℝ) (j : Fin n) :
    θ ≤ f j ↔ (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ f i)).card := by
  first | exact Bl.general_b_fact_left_form.goal1 .. | (apply Bl.general_b_fact_left_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_form.goal1 <;> first | assumption | infer_instance)

theorem hnExtreme_of (h1 : HNSlopes.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : HNStep.{u, v, w})
    (h4 : SatBasic.{u, v, w}) : HNExtreme.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L hL hL0
  obtain ⟨hanti, hcard, -⟩ := h1 R V E ρ L hL
  obtain ⟨B1, B2, B3, B4, B5, -, -, -⟩ := h4 R V E ρ L hL
  obtain ⟨M1, -, M3, -⟩ := h2 R V E ρ L hL hL0
  have key : ∀ (θ : ℝ) (j : Fin (rk ρ L)),
      θ ≤ slopeList ρ L j ↔ (j : ℕ) < rk ρ (hnStep ρ L θ) := by
    intro θ j
    rw [← hcard θ]
    exact hnExtreme_mem_iff _ hanti θ j
  have hSL : ∀ θ : ℝ, hnStep ρ L θ ≤ L := fun θ => (h3 R V E ρ L hL θ).1.1
  have hbot : rk ρ (⊥ : Submodule R V) = 0 := (B4 ⊥ bot_le).2 rfl
  have hrkpos : 0 < rk ρ L := by
    rcases Nat.eq_zero_or_pos (rk ρ L) with h | h
    · exact absurd ((B4 L le_rfl).1 h) hL0
    · exact h

  have hstepMin : hnStep ρ L (muMin ρ L) = L := by
    obtain ⟨-, -, S3, -⟩ := h3 R V E ρ L hL (muMin ρ L)
    exact le_antisymm (hSL _) (S3 L le_rfl hL0 le_rfl)
  have lowB : ∀ j, muMin ρ L ≤ slopeList ρ L j := by
    intro j
    rw [key, hstepMin]
    exact j.2

  have stepMax : ∀ θ : ℝ, hnStep ρ L θ ≠ ⊥ → θ ≤ muMax ρ L := by
    intro θ hne
    obtain ⟨-, S2, -, -⟩ := h3 R V E ρ L hL θ
    have hHL : IsLat ρ (hnStep ρ L θ) := B1 _ (hSL θ)
    obtain ⟨-, N2, -⟩ := h2 R V E ρ _ hHL hne
    have hθ := (N2 θ).1 (S2 hne) ⊥ bot_le
    simp only [hbot, B5, Nat.cast_zero, sub_zero] at hθ
    have hdeg := ((M1 (muMax ρ L)).1 le_rfl) _ (hSL θ)
    have hpos : (0 : ℝ) < rk ρ (hnStep ρ L θ) := by
      have : rk ρ (hnStep ρ L θ) ≠ 0 := fun h => hne ((B4 _ (hSL θ)).1 h)
      exact_mod_cast Nat.pos_of_ne_zero this
    exact le_of_mul_le_mul_right (le_trans hθ hdeg) hpos
  have upB : ∀ j, slopeList ρ L j ≤ muMax ρ L := by
    intro j
    apply stepMax
    intro h
    have := (key _ j).1 le_rfl
    rw [h, hbot] at this
    exact Nat.not_lt_zero _ this

  have hstepMaxNe : hnStep ρ L (muMax ρ L) ≠ ⊥ := by
    obtain ⟨N, hNs, hN0, hNsl⟩ := M3
    have hNL : N ≤ L := hNs.1
    have hNlat : IsLat ρ N := B1 N hNL
    obtain ⟨-, N2, -⟩ := h2 R V E ρ N hNlat hN0
    have hmin : muMax ρ L ≤ muMin ρ N := by
      rw [N2]
      intro Q hQ
      have hQd := ((M1 (muMax ρ L)).1 le_rfl) Q (le_trans hQ hNL)
      have hrkN : (rk ρ N : ℝ) ≠ 0 := by
        have : rk ρ N ≠ 0 := fun h => hN0 ((B4 N hNL).1 h)
        exact_mod_cast this
      have hsl : slope ρ N = deg ρ N / rk ρ N := rfl
      have hdegN : deg ρ N = muMax ρ L * rk ρ N := by
        rw [← hNsl, hsl, div_mul_cancel₀ _ hrkN]
      rw [mul_sub]
      linarith
    obtain ⟨-, -, S3, -⟩ := h3 R V E ρ L hL (muMax ρ L)
    have hle := S3 N hNL hN0 hmin
    intro h
    rw [h] at hle
    exact hN0 (le_bot_iff.1 hle)
  refine ⟨fun j => ⟨lowB j, upB j⟩, ⟨⟨0, hrkpos⟩, le_antisymm (upB _) ?_⟩,
    ⟨⟨rk ρ L - 1, by omega⟩, le_antisymm ?_ (lowB _)⟩⟩
  · rw [key]
    show 0 < rk ρ (hnStep ρ L (muMax ρ L))
    rcases Nat.eq_zero_or_pos (rk ρ (hnStep ρ L (muMax ρ L))) with h | h
    · exact absurd ((B4 _ (hSL _)).1 h) hstepMaxNe
    · exact h
  · by_contra hlt
    rw [not_le] at hlt
    set θ := slopeList ρ L ⟨rk ρ L - 1, by omega⟩ with hθdef
    have hj := (key θ ⟨rk ρ L - 1, by omega⟩).1 le_rfl
    simp only at hj
    obtain ⟨S1, S2, -, -⟩ := h3 R V E ρ L hL θ
    have hle := (B2 _ L (hSL θ) le_rfl).1
    have hrk : rk ρ L = rk ρ (hnStep ρ L θ) := by omega
    have heq : L = hnStep ρ L θ := B3 _ L S1 (hSL θ) le_rfl hrk
    have hne : hnStep ρ L θ ≠ ⊥ := by rw [← heq]; exact hL0
    have := S2 hne
    rw [← heq] at this
    linarith

theorem polygon_extreme_slopes : HNExtreme :=
  hnExtreme_of polygon_slopes_characterization slope_characterization (hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties) saturation_basic_properties

end Formalism.HN
end
end
