module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialAlexanderWhitneyHomotopyEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv.Recentre

variable {k : Type} [Field k] [ValuativeRel k]

theorem vecMul_bound {r : ℕ} (E : Matrix (Fin r) (Fin r) k) (δ b : ValueGroupWithZero k)
    (hδ : δ < 1) (hE : ∀ l l', valuation k (E l l') ≤ δ) (s w : Fin r → k)
    (hw : ∀ l, valuation k (w l) ≤ b) (hs : s ᵥ* (1 + E) = w) : ∀ l, valuation k (s l) ≤ b := by
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · intro l; exact isEmptyElim l
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image Finset.univ (fun l => valuation k (s l)) Finset.univ_nonempty
  have key : s l₀ = w l₀ - ∑ l, s l * E l l₀ := by
    have := congrFun hs l₀
    simp only [Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply] at this
    rw [← this]; simp [Matrix.vecMul, dotProduct]
  have hsum : valuation k (∑ l, s l * E l l₀) ≤ valuation k (s l₀) * δ := by
    apply Valuation.map_sum_le
    intro l _
    rw [map_mul]
    exact mul_le_mul' (hl₀ l (Finset.mem_univ _)) (hE l l₀)
  have hμ : valuation k (s l₀) ≤ max b (valuation k (s l₀) * δ) := by
    calc valuation k (s l₀) = valuation k (w l₀ - ∑ l, s l * E l l₀) := by rw [← key]
      _ ≤ max (valuation k (w l₀)) (valuation k (∑ l, s l * E l l₀)) := Valuation.map_sub _ _ _
      _ ≤ max b (valuation k (s l₀) * δ) := max_le_max (hw l₀) hsum
  have hμb : valuation k (s l₀) ≤ b := by
    rcases le_max_iff.1 hμ with h | h
    · exact h
    · by_cases h0 : valuation k (s l₀) = 0
      · rw [h0]; exact zero_le'
      · exfalso
        have h2 := mul_le_mul_left h (valuation k (s l₀))⁻¹
        rw [mul_inv_cancel₀ h0, mul_comm (valuation k (s l₀)) δ, mul_assoc, mul_inv_cancel₀ h0, mul_one] at h2
        exact absurd hδ (not_lt.2 h2)
  exact fun l => (hl₀ l (Finset.mem_univ _)).trans hμb

end GlobalTheory.RankCoinv.Recentre

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, valuation k (C i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν1 hνϖ i₀ r c m C H Q hHi₀ hH hcm hHC hQ hHCQ hCi₀
  classical
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hv0 : valuation k (ϖ : k) ≠ 0 := by simp
  have vpow : ∀ n : ℕ, valuation k (((ϖ ^ n : kˣ)) : k) = valuation k (ϖ : k) ^ n := by intro n; simp
  have vinv : valuation k ((((ϖ ^ c)⁻¹ : kˣ)) : k) = (valuation k (ϖ : k) ^ c)⁻¹ := by simp
  by_cases hex : ∃ X₂ ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m), X₂.rank ≤ r
  swap
  · apply Submodule.mem_sup_left
    refine ⟨GlobalTheory.RankCoinv.boxFn_mem_SB _ _ _, fun Y hY => ?_⟩
    unfold GlobalTheory.RankCoinv.boxFn
    apply Set.indicator_of_notMem
    intro hYb; exact hex ⟨Y, hYb, Nat.lt_succ_iff.1 hY⟩
  obtain ⟨X₂, hX₂, hrk⟩ := hex
  set u := valuation k (ϖ : k) with hu
  have hQ' : ∀ j l, valuation k (Q j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ j l)
  have hD : ∀ i j, valuation k ((X₂ - C) i j) ≤ u ^ m := fun i j => by
    rw [Matrix.sub_apply, ← vpow]; exact hX₂ i j
  have hHb : ∀ l i, valuation k (H l i) ≤ (u ^ c)⁻¹ := fun l i => (hH l i).trans_eq vinv
  have hHD : ∀ l j, valuation k ((H * (X₂ - C)) l j) ≤ (u ^ c)⁻¹ * u ^ m := fun l j => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro i _; rw [map_mul]
    exact mul_le_mul' (hHb l i) (hD i j)
  have hE : ∀ l l', valuation k ((H * (X₂ - C) * Q) l l') ≤ (u ^ c)⁻¹ * u ^ m := fun l l' => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ (u ^ c)⁻¹ * u ^ m * 1 := mul_le_mul' (hHD l j) (hQ' j l')
      _ = _ := mul_one _
  have hm1 : u ^ m ≤ u ^ (c + 1) := pow_le_pow_right_of_le_one' hlt.le hcm
  have hδ : (u ^ c)⁻¹ * u ^ m < 1 := by
    calc (u ^ c)⁻¹ * u ^ m ≤ (u ^ c)⁻¹ * u ^ (c + 1) := mul_le_mul' le_rfl hm1
      _ = u := by rw [pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ < 1 := hlt
  have hM : H * X₂ * Q = 1 + H * (X₂ - C) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hHCQ]; abel
  have hunit : IsUnit (H * X₂ * Q) := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro a a' haa
    have h0 : (a - a') ᵥ* (1 + H * (X₂ - C) * Q) = 0 := by
      rw [← hM, Matrix.sub_vecMul]; exact sub_eq_zero.2 haa
    funext l
    have h1 := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ 0 hδ hE (a - a') 0 (fun _ => by simp) h0 l
    have h2 : (a - a') l = 0 := (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    exact sub_eq_zero.1 h2
  obtain ⟨s, hs⟩ := GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X₂ H Q hrk hunit i₀
  have hsw : s ᵥ* (1 + H * (X₂ - C) * Q) = X₂ i₀ ᵥ* Q := by
    rw [← hM, ← Matrix.vecMul_vecMul, ← hs]
  have hX₂i₀ : ∀ j, valuation k (X₂ i₀ j) ≤ u ^ (c + 1) := fun j => by
    have h1 : valuation k (X₂ i₀ j - C i₀ j) ≤ u ^ (c + 1) := ((hX₂ i₀ j).trans_eq (vpow m)).trans hm1
    have h2 : valuation k (C i₀ j) ≤ u ^ (c + 1) := (hCi₀ j).trans_eq (vpow _)
    calc valuation k (X₂ i₀ j) = valuation k ((X₂ i₀ j - C i₀ j) + C i₀ j) := by rw [sub_add_cancel]
      _ ≤ _ := Valuation.map_add_le _ h1 h2
  have hw : ∀ l, valuation k ((X₂ i₀ ᵥ* Q) l) ≤ u ^ (c + 1) := fun l => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * 1 := mul_le_mul' (hX₂i₀ j) (hQ' j l)
      _ = _ := mul_one _
  have hsb := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ _ hδ hE s _ hw hsw
  have hsmall : ∀ j, valuation k ((s ᵥ* (H * (X₂ - C))) j) ≤ u ^ m := fun j => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro l _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * ((u ^ c)⁻¹ * u ^ m) := mul_le_mul' (hsb l) (hHD l j)
      _ = u * u ^ m := by
        rw [pow_succ, mul_comm (u ^ c) u, mul_assoc, ← mul_assoc (u ^ c), mul_inv_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ ≤ 1 * u ^ m := mul_le_mul_left hlt.le _
      _ = u ^ m := one_mul _
  set C' := Matrix.updateRow C i₀ 0 with hC'
  have hHC' : H * C' = H * C := by
    ext l j
    simp only [Matrix.mul_apply, C', Matrix.updateRow_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · subst h; simp [hHi₀]
    · rfl
  have hcore := GlobalTheory.T.box_function_twisted_coinvariant k A D ϖ hϖ ν β hν1 hνϖ i₀ r c m C' H Q hHi₀ hH hcm
    (by rw [hHC']; exact hHC) hQ (by rw [hHC']; exact hHCQ) (fun j => by simp [C'])
  have hstep := GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C' H s hHi₀ hH
    (fun l => (hsb l).trans (by rw [vpow]; exact pow_le_pow_right_of_le_one' hlt.le (Nat.le_succ c)))
  have e1 : s ᵥ* (H * C) = X₂ i₀ - s ᵥ* (H * (X₂ - C)) := by
    rw [Matrix.mul_sub, Matrix.vecMul_sub, ← hs, sub_sub_cancel]
  have hC'' : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) =
      Matrix.updateRow C i₀ (X₂ i₀ - s ᵥ* (H * (X₂ - C))) := by
    rw [hHC', e1]
    ext i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self, Matrix.updateRow_self, hC', Matrix.updateRow_self, zero_add]
    · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi, hC', Matrix.updateRow_ne hi]
  have hmem : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m) := by
    rw [hC'']
    intro i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self]
      calc valuation k ((X₂ i - s ᵥ* (H * (X₂ - C))) j - C i j)
          = valuation k ((X₂ i j - C i j) - (s ᵥ* (H * (X₂ - C))) j) := by
            congr 1; rw [Pi.sub_apply]; ring
        _ ≤ max (valuation k (X₂ i j - C i j)) (valuation k ((s ᵥ* (H * (X₂ - C))) j)) :=
            Valuation.map_sub _ _ _
        _ ≤ u ^ m := max_le ((hX₂ i j).trans_eq (vpow m)) (hsmall j)
        _ = _ := (vpow m).symm
    · rw [Matrix.updateRow_ne hi]; simp
  rw [GlobalTheory.RankCoinv.boxFn_eq_of_mem hmem] at hstep
  rw [← sub_add_cancel (GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m)) (GlobalTheory.RankCoinv.boxFn ϖ C' (fun _ => m))]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hstep) hcore
end

section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

theorem _root_.GlobalTheory.T.full_rank_zeta_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ h : GL (Fin d) k, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = 0) →
      Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  exact @GlobalTheory.FullRankCoinv.mem_augRk_of_fibre_eq_zero
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

theorem _root_.GlobalTheory.T.bisimplicialAlexanderWhitney_homotopyEquiv : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (H : ∀ n m : ℕ, bo n n ⟶ bo m m) (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b'), G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → (∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n) → (∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b') → ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  first | (exact @GlobalTheory.EZ.awHomotopyEquiv) | (exact GlobalTheory.EZ.awHomotopyEquiv) | (intros; apply GlobalTheory.EZ.awHomotopyEquiv  <;> assumption)
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

theorem _root_.GlobalTheory.T.alexander_whitney_homotopy_formula : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → ∃ K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b', ∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b' := by
  first | (exact @GlobalTheory.EZ.HTot.htot) | (exact GlobalTheory.EZ.HTot.htot) | (intros; apply GlobalTheory.EZ.HTot.htot <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

theorem _root_.GlobalTheory.T.cochainValueOnThickeningHom_eq_sub_of_glued : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)), (∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a)) → ∀ {T T' : TT s} (φ : T ⟶ T') (G : T.obj.B) (G' : T'.obj.B), (∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p) → (∀ p : Pair (pt T'), toSec R T'.obj.B p.1.1 G' = hSec f g T' p) → fv f φ = G' - φ.hom.φ G := by
  first | exact @GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued | exact GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued | (intros; apply GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued <;> assumption)
end

section

open Matrix Topology

theorem _root_.GlobalTheory.T.mirabolic_cutoffs_of_restriction_cutoffs : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h) → ∀ U : Subgroup (GL (Fin (m + 2)) F), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∀ z : GL (Fin (m + 2)) F, GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 2)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 2)) F))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1} := by
  first | exact @GlobalTheory.JSW.Cut.cuts_mir_of_res | exact GlobalTheory.JSW.Cut.cuts_mir_of_res | (intros; apply GlobalTheory.JSW.Cut.cuts_mir_of_res <;> assumption)
end

section

set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem exists_tensor_map_eq_of_exact {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [Module.Flat R M]
    [Module.Flat R N] [Module.Flat R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (h : Function.Exact f g) (F : N ⊗[R] N)
    (h₁ : g.rTensor N F = 0) (h₂ : g.lTensor N F = 0) :
    ∃ c : M ⊗[R] M, TensorProduct.map f f c = F := by
  obtain ⟨F', rfl⟩ := (Module.Flat.lTensor_exact N h F).1 h₂
  have h₃ : g.rTensor M F' = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := P) f hf
    rw [map_zero, ← h₁, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  obtain ⟨c, rfl⟩ := (Module.Flat.rTensor_exact M h F').1 h₃
  exact ⟨c, by rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]⟩

theorem PDivGroup.exists_tensorSquare_mulP_eq {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
    (n : ℕ) (F : G.A (n + 1) ⊗[R] G.A (n + 1))
    (h₁ : ((G.transl n).toLinearMap -
      (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) F = 0)
    (h₂ : ((G.transl n).toLinearMap -
      (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) F = 0) :
    ∃ c : G.A n ⊗[R] G.A n, pullbackTwo (G.mulP n) c = F := by
  refine exists_tensor_map_eq_of_exact (G.mulP n : G.A n →ₗ[R] G.A (n + 1)) _
    (Test.mulP_injective G n) (fun a => ⟨fun ha => ?_, ?_⟩) F h₁ h₂
  · exact GlobalTheory.T.exists_mulP_eq_of_transl_invariant G n a (sub_eq_zero.1 ha)
  · rintro ⟨e, rfl⟩
    exact sub_eq_zero.2 (G.transl_mulP n e)

end GlobalTheory
end

section

set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem exists_res_eq_of_transl_eq_add {b : G.A 1} (hb : cobOne R (G.A 1) b = 0) (n : ℕ)
    (x : G.A (n + 1)) (hx : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ∃ y : G.A (n + 2), G.transl (n + 1) y = y ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b ∧ G.res (n + 1) y = x := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.transl_coaction_free_coassoc_counital G (n + 1)
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_coaction_eq_add_of_primitive (G.transl (n + 1)) h1 h2 h3 b hb
  have hr : G.transl n (G.res (n + 1) x') = G.res (n + 1) x' ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    rw [transl_res, hx', map_add (f := _), LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    simp
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_mulP_eq_of_transl_invariant G n (G.res (n + 1) x' - x) (by
    rw [map_sub, hr, hx, sub_tmul]
    abel)
  obtain ⟨e', rfl⟩ := G.res_surjective n e
  refine ⟨x' - G.mulP (n + 1) e', ?_, ?_⟩
  · rw [map_sub, hx', transl_mulP, sub_tmul]
    abel
  · rw [map_sub, res_mulP, ← mulP_res, he, sub_sub_cancel]

theorem exists_funs_transl_eq_add {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
    (b : G.A 1) (hb : cobOne R (G.A 1) b = 0) :
    ∃ B : G.funs, B.1 1 = b ∧
      ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  choose f hf hres using G.exists_res_eq_of_transl_eq_add hb
  have h0 : G.transl 0 b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    have h : (G.resOne 0 : G.A 1 →ₗ[R] G.A 1) = LinearMap.id := by
      apply LinearMap.ext
      intro a
      simp only [BialgHom.coe_toLinearMap, LinearMap.id_apply, resOne_zero]
    rw [transl_apply, h, LinearMap.lTensor_id, LinearMap.id_apply]
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb
    exact hb
  let s : ∀ n, {x : G.A (n + 1) // G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b} := fun n =>
    Nat.rec (motive := fun n => {x : G.A (n + 1) // G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b})
      ⟨b, h0⟩ (fun n x => ⟨f n x.1 x.2, hf n x.1 x.2⟩) n
  refine ⟨⟨fun n => Nat.casesOn (motive := fun n => G.A n) n (G.res 0 b) fun n => (s n).1, ?_⟩,
    rfl, fun n => (s n).2⟩
  rintro (_ | n)
  · rfl
  · exact hres n (s n).1 (s n).2

end PDivGroup

end GlobalTheory
end

section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDiv

section PrimBaseChange

variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A]
  [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R']

theorem counit_comp_cartierBaseChange :
    (counitAlgHom R' (CartierDual R' (R' ⊗[R] A))).comp
        ((CartierDual.baseChange R R' A).toAlgEquiv : R' ⊗[R] CartierDual R A →ₐ[R'] _) =
      AugCot.baseChangeAug R' (counitAlgHom R (CartierDual R A)) := by
  refine AlgHom.ext fun x => ?_
  induction x with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r φ =>
    simp [Algebra.TensorProduct.one_def, Algebra.smul_def, mul_comm]

def cotBaseChange :
    Cot R' (CartierDual R' (R' ⊗[R] A)) ≃ₗ[R'] R' ⊗[R] Cot R (CartierDual R A) :=
  ((AugCot.baseChangeEquiv R' (counitAlgHom R (CartierDual R A))).trans
    (AugCot.congr (CartierDual.baseChange R R' A).toAlgEquiv
      (counit_comp_cartierBaseChange R'))).symm

theorem cotBaseChange_d (φ : CartierDual R A) :
    cotBaseChange R' (dUnit (R := R') (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) =
      (1 : R') ⊗ₜ dUnit (R := R) φ := by
  rw [cotBaseChange, LinearEquiv.symm_apply_eq, LinearEquiv.trans_apply,
    AugCot.baseChangeEquiv_tmul_d, one_smul, AugCot.congr_d]
  rfl

theorem cotBaseChange_hom_ext {N : Type} [AddCommGroup N] [Module R' N]
    {f g : Cot R' (CartierDual R' (R' ⊗[R] A)) →ₗ[R'] N}
    (h : ∀ φ : CartierDual R A, f (dUnit (R := R') (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) =
      g (dUnit (R := R') (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ)))) : f = g := by
  refine AugCot.hom_ext fun ψ => ?_
  obtain ⟨x, rfl⟩ := EquivLike.surjective (CartierDual.baseChange R R' A) ψ
  induction x with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r φ =>
    have e : r ⊗ₜ[R] φ = r • ((1 : R') ⊗ₜ[R] φ) := by simp [smul_tmul']
    rw [e, map_smul, map_smul, map_smul, map_smul]
    exact congrArg (r • ·) (h φ)

end PrimBaseChange

theorem liftSemi_prim_toBaseChange_bijective {R A : Type} (R' : Type) [CommRing R] [CommRing A]
    [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] [CommRing R']
    [Algebra R R'] (hC : Module.Projective R (Cot R (CartierDual R A))) :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  let u := (CartierDual.toDual R (Cot R (CartierDual R A))).symm.toLinearMap ∘ₗ primTangent R A
  have hu : Function.Bijective u :=
    (CartierDual.toDual R _).symm.bijective.comp (GlobalTheory.T.additiveFunctionCartierDualTangent_bijective (R := R) (A := A))
  have key : ⇑(primTangent R' (R' ⊗[R] A)) ∘ ⇑(liftSemi (toBaseChange R R' A).prim) =
      ⇑(CartierDual.toDual R' _) ∘
        ⇑(CartierDual.transpose (cotBaseChange (R := R) (A := A) R').toLinearMap) ∘
        ⇑(CartierDual.baseChangeLinear R R' (Cot R (CartierDual R A))) ∘
        ⇑(LinearMap.lTensor R' u) := by
    funext x
    induction x with
    | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
    | tmul r b =>
      refine cotBaseChange_hom_ext R' fun φ => ?_
      have h1 : primTangent R' (R' ⊗[R] A) (liftSemi (toBaseChange R R' A).prim (r ⊗ₜ b))
          (dUnit (R := R') (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) = φ b.1 • r := by
        rw [liftSemi_tmul, map_smul, LinearMap.smul_apply, primTangent_d, SemiBialgHom.prim_val,
          toBaseChange_apply, CartierDual.baseChange_tmul_tmul, smul_comm, mul_one, smul_eq_mul,
          mul_one]
      refine h1.trans (Eq.symm ?_)
      change CartierDual.baseChangeLinear R R' (Cot R (CartierDual R A)) (r ⊗ₜ u b)
        (cotBaseChange R' (dUnit (R := R') (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ)))) = _
      rw [cotBaseChange_d, CartierDual.baseChangeLinear_tmul_tmul, mul_one]
      exact congrArg (· • r) (primTangent_d b φ)
  refine (Function.Bijective.of_comp_iff' (GlobalTheory.T.additiveFunctionCartierDualTangent_bijective (R := R') (A := R' ⊗[R] A)) _).1 ?_
  rw [key]
  exact (CartierDual.toDual R' _).bijective.comp <|
    (CartierDual.transpose_bijective (cotBaseChange R').bijective).comp <|
    (CartierDual.baseChangeLinear_bijective R').comp
      (LinearEquiv.lTensor R' (LinearEquiv.ofBijective u hu)).bijective

end PDiv

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem pullbackGerm_finset_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {K : Type} (s : Finset K)
    (a : K → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem isMat_germ : ∀ {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left} {k : ℕ} {mA mB : ℕ} {bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))} {bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))} {eA : LB.Gen (L.pull (eSec A))} {eB : LB.Gen (M.pull (eSec B))} {R : Type} [CommRing R] {t : Sp R ⟶ Sp Rg} {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {c : Fin mA → Fin mB → Γ(Sp R, ⊤)}, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left), ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ ∀ (Z : Scheme.{0}) (e : Z ⟶ A'.left) (z : Z) (pM : Fin 1 → M.ι) (q : Fin 1 → L.ι), (e ≫ Φ'.left ≫ ψB) z ∈ (LPow B M (k : ℤ) (topS Rg)).U pM → (e ≫ ψA) z ∈ (LPow A L (k : ℤ) (topS Rg)).U q → ∃ u : (Z.presheaf.stalk z)ˣ, ∀ j, gs (e ≫ Φ'.left ≫ ψB) z _ ((bB j).f pM) = u * ∑ i, gs (e ≫ A'.hom) z ⊤ (c i j) * gs (e ≫ ψA) z _ ((bA i).f q) := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB R _ t A' B' _ _ φA' φB' Φ' c h
  obtain ⟨ψA, ψB, α, h1, h2, -, -, hch⟩ := h
  refine ⟨ψA, ψB, h1, h2, ?_⟩
  intro Z e z pM q hM hA
  have hz : e z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U (pM, q) := by
    refine ⟨?_, ?_⟩
    · refine Set.mem_iInter.2 fun i => ?_
      have := Set.mem_iInter.1 hM i
      simpa using this
    · refine Set.mem_iInter.2 fun i => ?_
      have := Set.mem_iInter.1 hA i
      simpa using this
  refine ⟨gm e z _ (α.s (pM, q)), fun j => ?_⟩
  have E := congrArg (gs e z ((isoLB (L := L) (M := M) k Φ' ψA ψB).U (pM, q))) (hch j (pM, q))
  erw [gs_mul _ _ _ hz] at E
  erw [gs_unit _ _ _ hz, pullbackGerm_finset_sum _ _ _ hz, gs_appLE _ _ _ _ _ _ hz] at E
  refine E.trans (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  erw [gs_mul _ _ _ hz, gs_appLE _ _ _ _ _ _ hz, gs_appLE _ _ _ _ _ _ hz]
  rfl

end GlobalTheory.HomFixMat
end
