module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle004
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle005
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem mean_slope_of_proportional_volume : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval := by
  intro II Ψ _ _ N T C rd Lval hP hV hT u g hu B hB hB0 hbad
  have hfd : 0 < flagDeg u := (GlobalTheory.T.flag_degree_weight_formula Ψ N u).2.1 hu.2.1
  obtain ⟨c0⟩ := T.neC
  have hv : 0 < T.vol c0 := hP.1 c0
  have hvc : ∀ c, T.vol c = T.vol c0 := fun c => hV c c0
  have hcard : (0:ℝ) < Fintype.card T.Comp := by exact_mod_cast Fintype.card_pos
  have hvolT : T.volT = Fintype.card T.Comp * T.vol c0 := by
    rw [RootTower.volT, Finset.sum_congr rfl fun c _ => hvc c]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hD : (0:ℝ) < (dimFl Ψ N : ℝ) + 1 := by positivity
  have key : (∑ c, T.slope II B c u) / Fintype.card T.Comp
      = T.PB II B u / (((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u)) := by
    have hs : ∀ c, T.slope II B c u
        = T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)) / (((dimFl Ψ N : ℝ) + 1) * (T.vol c0 * flagDeg u)) := by
      intro c
      rw [RootTower.slope, hvc c]
    rw [Finset.sum_congr rfl fun c _ => hs c, ← Finset.sum_div, RootTower.PB, RootTower.PPt, hvolT,
      div_div]
    congr 1
    ring
  have hpos : 0 < ((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u) := by
    rw [hvolT]
    exact mul_pos hD (mul_pos (mul_pos hcard hv) hfd)
  rw [key, le_div_iff₀ hpos]
  have h := hT u g hu B hB hB0 hbad
  linarith

end RootFieldNumerics
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

open Ii in
theorem intersection_multilinear_expansion : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin d → J → ℤ), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (fun k => combLine ℓ (n k)) = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) := by
  intro II hII K _ ι _ P d J _ _ ℓ n hP hℓ
  have hsm : ∀ c : J → ℤ, IsSmoothHerm (combLine ℓ c) := fun c => (combLine_smooth_conj_invariant K ι J ℓ c).1 hℓ
  have key : ∀ (c : Fin d → J → ℤ) (k : Fin d) (v : J → ℤ),
      II K ι P d (fun i => combLine ℓ (Function.update c k v i)) =
        ∑ j, (v j : ℝ) * II K ι P d (Function.update (fun i => combLine ℓ (c i)) k (ℓ j)) := by
    intro c k v
    have e : (fun i => combLine ℓ (Function.update c k v i)) =
        Function.update (fun i => combLine ℓ (c i)) k (combLine ℓ v) := by
      funext i
      by_cases h : i = k
      · subst h
        simp
      · simp [Function.update_of_ne h]
    rw [e, intersection_multilinear_one_position II hII K ι P d _ k J ℓ v hP (fun i => hsm _) hℓ]
  let f : MultilinearMap (Int.castRingHom ℝ) (fun _ : Fin d => J → ℤ) ℝ :=
    { toFun := fun c => II K ι P d (fun i => combLine ℓ (c i))
      map_update_add' := by
        intro inst c k x y
        obtain rfl := Subsingleton.elim inst (instDecidableEqFin d)
        simp only [key, ← Finset.sum_add_distrib, Pi.add_apply, Int.cast_add, add_mul]
      map_update_smul' := by
        intro inst c k a x
        obtain rfl := Subsingleton.elim inst (instDecidableEqFin d)
        simp only [key, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum, mul_assoc]
        rfl }
  have hn : (fun k => n k) = fun k => ∑ j, n k j • (Pi.single j (1 : ℤ) : J → ℤ) := by
    funext k
    conv_lhs => rw [← Finset.univ_sum_single (n k)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ext j'
    by_cases h : j' = j
    · subst h
      simp
    · simp [Pi.single_apply, h]
  calc II K ι P d (fun k => combLine ℓ (n k))
      = f (fun k => ∑ j, n k j • (Pi.single j (1 : ℤ) : J → ℤ)) := by
        rw [← hn]
        rfl
    _ = ∑ r : Fin d → J, f (fun k => n k (r k) • (Pi.single (r k) (1 : ℤ) : J → ℤ)) := f.map_sum _
    _ = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [f.map_smul_univ]
        simp [f, smul_eq_mul, combLine_single]

end RootFieldNumerics
end
