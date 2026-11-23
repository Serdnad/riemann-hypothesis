module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle004
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle075
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle007
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle008
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem curveDeg_linear_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' a : ℝ), (∀ W, M.curveDeg (lam + mu) (s + s') W = M.curveDeg lam s W + M.curveDeg mu s' W) ∧ (∀ W, M.curveDeg (a • lam) (a * s) W = a * M.curveDeg lam s W) ∧ (∀ p, 0 ≤ s → M.NefAt p lam 0 → M.NefAt p 0 1 → M.NefAt p lam s) ∧ (0 ≤ s → M.NefGen lam 0 → M.NefGen 0 1 → M.NefGen lam s) :=
  @RootFieldNumerics.curveDeg_linear_and_nef

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem monoLines_monomial_word : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) (ℓ : J → HermLine ι) (w : Fin d → J), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ).degree = d ∧ ∃ σ : Equiv.Perm (Fin d), monoLines ℓ (∑ k, Finsupp.single (w k) 1) d = (fun k => ℓ (w k)) ∘ σ ∧ II K ι P d (monoLines ℓ (∑ k, Finsupp.single (w k) 1) d) = II K ι P d (fun k => ℓ (w k)) :=
  RootFieldNumerics.intersection_monomial_lines

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem clear_rat_weight_coef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j :=
  @RootFieldNumerics.exists_integer_coefficients_rational

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem nefFib_integral_multiple : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → (∀ W : Ideal (MRing M.ι), (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W) ∧ (M.NefFib lam s → NefOnFibres M.P (combLine (M.line t) n).a) :=
  RootFieldNumerics.curveDeg_eq_and_nefOnFibres_of_coef

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem semipositive_integral_multiple : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.Semipos t lam s → IsSemipositiveH M.P (combLine (M.line t) n) ∧ IsConjInvariantH (combLine (M.line t) n) :=
  RootFieldNumerics.root_model_line_semipositive

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ValLin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [DecidableEq K]
  {ι : K → Type} {σ : Type}

end GlobalTheory.CompanionTheory.Ar.Num.ValLin

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem locPair_val_linear : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (T : LocPair ι O σ) (P : Ideal (MRing ι O)), (∀ Gs Hs, T.val P (Gs + Hs) = T.val P Gs + T.val P Hs) ∧ (∀ (c : ℝ) Gs, T.val P (fun i => C c * Gs i) = c * T.val P Gs) ∧ ∀ (α : Type) (s : Finset α) (Gs : α → σ → MvPolynomial (σ ⊕ σ) ℝ), T.val P (fun i => ∑ a ∈ s, Gs a i) = ∑ a ∈ s, T.val P (Gs a) :=
  _root_.UpperTheory.Reformulated.B.Qp9.locPair_val_linear

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

namespace DeltaTermLin

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_add (F G : RP Ψ N) : degFl (F + G) = degFl F + degFl G := by
  simp only [degFl, MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

theorem degFl_zero : degFl (0 : RP Ψ N) = 0 := by
  simp [degFl]

theorem degFl_C_mul (a : ℝ) (F : RP Ψ N) : degFl (C a * F) = a * degFl F := by
  simp only [degFl, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem degFl_sum {ι : Type} (s : Finset ι) (f : ι → RP Ψ N) :
    degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [degFl_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, degFl_add, ih]

end DeltaTermLin

theorem log_mul_degFl_bracket_mul : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j p k : ℕ), 2 ≤ p → 1 ≤ k → ∀ (φ : Equiv.Perm (Ψ ⊕ Ψ)) (τ : Ψ) (Q : RP Ψ N), Real.log p * degFl (bracket j φ p k τ * Q) = deltaTerm j p τ (fun n => (φ ^ (n + 1)) (Sum.inl τ)) k Q := by
  intro Ψ _ _ N j p k hp hk φ τ Q
  have hlie : ∀ σ : Ψ ⊕ Ψ, liePs (N := N) j (k - 1) σ = pLie j (k - 1) σ := by
    rintro (s | s) <;> rfl
  have hco := co_series_three_step.1 (Ψ ⊕ Ψ) φ p k hp hk
    (fun σ => degFl (pLie (N := N) j (k - 1) σ * Q)) (Sum.inl τ)
  have hb : degFl (bracket j φ p k τ * Q) =
      (k : ℝ) * ∑ σ, co φ p k (Sum.inl τ) σ * degFl (pLie (N := N) j (k - 1) σ * Q) := by
    unfold bracket
    rw [mul_assoc, DeltaTermLin.degFl_C_mul, Finset.sum_mul, DeltaTermLin.degFl_sum]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_assoc, DeltaTermLin.degFl_C_mul, hlie]
  rw [hb, hco]
  simp only [deltaTerm, pLie]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.exists_mixed_difference_expansion : ∀ (σ : Type) [Fintype σ] (n : ℕ) (F : MvPolynomial σ ℝ), F.IsHomogeneous n → ∃ Gs, IsMixExpansion (n - 1) (mixDiff F) Gs := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff | exact GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.fibre_component_divisor_properties : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → (∀ W, IsFibreComp P W ↔ divCycle P (C ϖ) W ≠ 0) ∧ (∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ W, divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∈ W → IsFibreComp P W) ∧ ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g → ∀ W, ratDiv P f g W ≠ 0 → IsFibreComp P W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FibreComp.fibre_comp | exact GlobalTheory.CompanionTheory.Ar.Num.FibreComp.fibre_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FibreComp.fibre_comp <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.power_sum_mixed_expansion : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r k m : ℕ) (e : Fin r → σ) (G : MvPolynomial (σ ⊕ σ) ℝ), G.IsHomogeneous m → IsMixExpansion (k - 1 + m) (mixDiff (∑ a, X (e a) ^ k) * G) (fun i => (∑ a ∈ Finset.univ.filter (fun a => e a = i), rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) * G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.isMixExpansion_psum_mul | exact GlobalTheory.CompanionTheory.Ar.Num.isMixExpansion_psum_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.isMixExpansion_psum_mul <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.cycle_list_perm_invariant : (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)), l.Perm l' → intNumL F V l = intNumL F V l') ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Z : Ideal (MRing ι O) → ℤ) (l l' : List (K → ℤ)), l.Perm l' → cycList Z l = cycList Z l') := by
  exact GlobalTheory.CompanionTheory.Ar.Num.numbers_list_perm
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.local_pair_split_sum : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (j j' : ℕ) (T : LocPair ι O (Fin (j + j'))) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)), T.ck P k Q = (T.comp (Fin.castAdd j')).ck P k Q + (T.comp (Fin.natAdd j)).ck P k Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.CkAppend.ck_append | exact GlobalTheory.CompanionTheory.Ar.Num.CkAppend.ck_append | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.CkAppend.ck_append <;> assumption)
end
