module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle009
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.Bundle001
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ReMulSignatureIPosOfHermitianTraceFormula
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.archEx_of :
    UpperTheory.Gal.W2.FMat → UpperTheory.Gal.W2.FForm → UpperTheory.Gal.W2.SN → UpperTheory.Gal.W2.ArchSpan → UpperTheory.Gal.W2.ArchEx := by
  intro hFM hFF hSN hAS p _ D G L hm
  obtain ⟨kp, σ, hk⟩ := hFM p D G L hm
  obtain ⟨A, hdet, hskew, hform, hcomm⟩ := hFF p D G L kp σ hk
  choose S lam hS hpsi hconj hAv using fun v => UpperTheory.exists_hermitian_diagonalization_at_infinitePlace_of_skewHermitian p G σ A hSN hdet hskew hcomm v
  let th : VQ D →+ Arch G :=
    { toFun := fun w v => S v *ᵥ fun i => v.embedding (kp w i)
      map_zero' := by
        funext v
        simp
        exact Matrix.mulVec_zero _
      map_add' := fun x y => by
        funext v
        have : (fun i => v.embedding (kp (x + y) i)) = (fun i => v.embedding (kp x i)) + (fun i => v.embedding (kp y i)) := by
          funext i; simp
        simp only [this, Matrix.mulVec_add]
        rfl }
  have hth : ∀ w v, th w v = S v *ᵥ fun i => v.embedding (kp w i) := fun _ _ => rfl
  have hact : ∀ (c : G.C) w v, th (L.rep c w) v = G.psi v c *ᵥ th w v := by
    intro c w v
    rw [hth, hth, Matrix.mulVec_mulVec, hpsi, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    rw [hk c w]

    simp [Matrix.mulVec, dotProduct, map_sum]
  have hform' : ∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re := by
    intro u w
    rw [hform u w]
    exact UpperTheory.trace_conj_dotProduct_eq_sum_infinitePlaces G.F G.n hAS A S G.gram lam hS hAv (kp u) (kp w)
  have hspan : Submodule.span ℝ (Set.range th) = ⊤ := by
    rw [← UpperTheory.span_real_matrix_mulVec_infinitePlace_embedding_eq_top G.F G.n hAS S hS]
    congr 1
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨kp w, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨kp.symm x, by funext v; simp [hth]⟩
  have hpos := UpperTheory.re_mul_signature_I_pos_of_hermitian_trace_formula p D G L th lam hact hform' hspan hconj
  obtain ⟨hd1, hd2⟩ := UpperTheory.finrank_archimedean_eq_two_mul_dim p D G L hm hAS
  have hs2 : ∀ v, sgnV L v * sgnV L v = 1 := by
    intro v
    unfold sgnV
    split_ifs <;> simp
  have hlamim : ∀ v, lam v = ((lam v * sgnV L v * Complex.I).re : ℂ) * (-(sgnV L v) * Complex.I) := by
    intro v
    have hre : (lam v).re = 0 := by
      have := congrArg Complex.re (hconj v)
      simp at this
      linarith
    have hreal : (lam v * sgnV L v * Complex.I).im = 0 := by
      unfold sgnV
      split_ifs <;> simp [hre]
    have hc : ((lam v * sgnV L v * Complex.I).re : ℂ) = lam v * sgnV L v * Complex.I := by
      apply Complex.ext <;> simp [hreal]
    rw [hc]
    have := hs2 v
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (lam v * Complex.I * Complex.I) * this + lam v * hI
  exact ⟨{
    th := th
    r := fun v => 2 * (lam v * sgnV L v * Complex.I).re
    r_pos := fun v => by have := hpos v; linarith
    act := hact
    form := by
      intro u w
      rw [hform' u w]
      refine Finset.sum_congr rfl fun v _ => ?_
      show 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re = 2 * (lam v * sgnV L v * Complex.I).re * (-(sgnV L v) * Complex.I * hv (G.gram v) (th u v) (th w v)).re
      conv_lhs => rw [hlamim v, mul_assoc ((lam v * sgnV L v * Complex.I).re : ℂ), Complex.re_ofReal_mul]
      ring
    span := hspan
    dim := hd1
    dimg := hd2 }⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private def unitBall (p : ℕ) [Fact p.Prime] : Subring (PadicAlgCl p) where
  carrier := {y | ‖y‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (PadicAlgCl.isNonarchimedean p a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by simp

private theorem den_of_norm {p : ℕ} [hp : Fact p.Prime] (q : ℚ) (h : ‖(q : ℚ_[p])‖ ≤ 1) :
    ¬ p ∣ q.den := by
  intro hd
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have h2 := Nat.dvd_gcd h1 hd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  have hn1 : ‖(q.num : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _)
      (not_lt.mp fun hlt => hnum (Padic.norm_intCast_lt_one_iff.mp hlt))
  have hd1 : ‖(q.den : ℚ_[p])‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hd
  have heq : (q : ℚ_[p]) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have hn := congrArg norm heq
  rw [norm_mul, hn1] at hn
  nlinarith [norm_nonneg (q.den : ℚ_[p]), norm_nonneg (q : ℚ_[p])]

private theorem coeff_den {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (x : F)
    (h : ∀ τ : F →+* PadicAlgCl p, ‖τ x‖ ≤ 1) (i : ℕ) : ¬ p ∣ ((minpoly ℚ x).coeff i).den := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  set P := (minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl p)) with hP
  have hPm : P.Monic := (minpoly.monic hx).map _
  have hroot : ∀ r ∈ P.roots, ‖r‖ ≤ 1 := by
    intro r hr
    have hr' : r ∈ (minpoly ℚ x).rootSet (PadicAlgCl p) := by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero hx, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.mem_roots hPm.ne_zero).mp hr
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hr'
    obtain ⟨ψ, rfl⟩ := hr'
    exact h ψ.toRingHom
  have hprod : (P.roots.map fun a => Polynomial.X - Polynomial.C a).prod = P :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm IsAlgClosed.card_roots_eq_natDegree
  have hlift : P ∈ Polynomial.lifts (unitBall p).subtype := by
    rw [← hprod]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro f hf
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hf
    exact ⟨Polynomial.X - Polynomial.C ⟨a, hroot a ha⟩, by simp⟩
  obtain ⟨y, hy⟩ := (Polynomial.lifts_iff_coeff_lifts P).mp hlift i
  have hn : ‖P.coeff i‖ ≤ 1 := by
    rw [← hy]
    exact y.2
  rw [hP, Polynomial.coeff_map] at hn
  apply den_of_norm
  have hc : algebraMap ℚ (PadicAlgCl p) ((minpoly ℚ x).coeff i)
      = algebraMap ℚ_[p] (PadicAlgCl p) (((minpoly ℚ x).coeff i : ℚ) : ℚ_[p]) := by
    simp only [eq_ratCast, map_ratCast]
  rw [hc] at hn
  exact (PadicAlgCl.norm_extends p _).symm.trans_le hn

private theorem integral_multiple_coprime {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (x : F)
    (h : ∀ i, ¬ p ∣ ((minpoly ℚ x).coeff i).den) :
    ∃ (m : ℕ) (c : 𝓞 F), m.Coprime p ∧ (c : F) = m * x := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  set P := minpoly ℚ x with hP
  set M : ℕ := ∏ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).den with hM
  have hMcop : M.Coprime p :=
    Nat.Coprime.prod_left fun i _ =>
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr (h i)).symm
  have hQ : P.scaleRoots (M : ℚ) ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    by_cases hi : i ≤ P.natDegree
    · rcases hi.lt_or_eq with hlt | heq
      · obtain ⟨k, hk⟩ : (P.coeff i).den ∣ M :=
          Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
        have hc : P.coeff i * M = (P.coeff i).num * k := by
          rw [hk]
          push_cast
          rw [← _root_.mul_assoc, Rat.mul_den_eq_num]
        have hpow : (M : ℚ) ^ (P.natDegree - i) = M * M ^ (P.natDegree - i - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        refine ⟨(P.coeff i).num * k * M ^ (P.natDegree - i - 1), ?_⟩
        rw [hpow, ← _root_.mul_assoc, hc]
        simp
      · subst heq
        refine ⟨1, ?_⟩
        rw [Nat.sub_self, pow_zero, _root_.mul_one, map_one]
        exact (minpoly.monic hx).leadingCoeff.symm
    · refine ⟨0, ?_⟩
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
  have hmon : (P.scaleRoots (M : ℚ)).Monic := (Polynomial.monic_scaleRoots_iff _).mpr (minpoly.monic hx)
  obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hQ hmon
  have hint : IsIntegral ℤ ((M : F) * x) := by
    refine ⟨Q, hQm, ?_⟩
    have h0 := Polynomial.scaleRoots_aeval_eq_zero (r := (M : ℚ)) (minpoly.aeval ℚ x)
    have hcast : Int.castRingHom ℚ = algebraMap ℤ ℚ := Subsingleton.elim _ _
    rw [← hP, ← hQmap, hcast, Polynomial.aeval_map_algebraMap, map_natCast] at h0
    rw [← Polynomial.aeval_def]
    exact h0
  exact ⟨M, ⟨(M : F) * x, hint⟩, hMcop, rfl⟩

theorem UpperTheory.Gal.W2.fInt_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FInt := by
  intro hE p _ G x hx
  apply integral_multiple_coprime
  apply coeff_den
  intro τ
  obtain ⟨w, σ, h | h⟩ := hE p G τ
  · rw [h x]
    calc ‖σ (G.emb w x)‖ = ‖G.emb w x‖ := (spectralNorm_eq_of_equiv σ _).symm
      _ ≤ 1 := (hx w).1
  · rw [h x]
    calc ‖σ (G.emb w ((IsCMField.complexConj G.F) x))‖
        = ‖G.emb w ((IsCMField.complexConj G.F) x)‖ := (spectralNorm_eq_of_equiv σ _).symm
      _ ≤ 1 := (hx w).2
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_inverse_different (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) ↔
        ‖((a * d : K) : PadicAlgCl p)‖ ≤ 1 := by
  classical
  have hpos : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hmin : ∀ z : K, minpoly ℚ_[p] (z : PadicAlgCl p) = minpoly ℚ_[p] z := fun z =>
    minpoly.algebraMap_eq (algebraMap K (PadicAlgCl p)).injective z
  have hsv : ∀ z : K, ‖(z : PadicAlgCl p)‖ = spectralValue (minpoly ℚ_[p] z) := by
    intro z
    rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, hmin]
  have hnat : ∀ m : ℕ, ‖(m : ℚ_[p])‖ ≤ 1 := fun m => by
    simpa using Padic.norm_int_le_one (p := p) (m : ℤ)
  have hTr : ∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K z‖ ≤ 1 := by
    intro z hz
    rw [hsv, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral z))] at hz
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, norm_mul, norm_neg]
    have h2 : ‖(minpoly ℚ_[p] z).nextCoeff‖ ≤ 1 := by
      unfold Polynomial.nextCoeff
      split_ifs
      · simp
      · exact hz _
    calc _ ≤ 1 * 1 := mul_le_mul (hnat _) h2 (norm_nonneg _) zero_le_one
      _ = 1 := _root_.one_mul 1
  have hdisc : ∀ x : K, x ≠ 0 → ∃ j : ℤ,
      ‖(x : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial = (p : ℝ) ^ j := by
    intro x hx
    have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
    have hdpos : 0 < (minpoly ℚ_[p] x).natDegree := minpoly.natDegree_pos hint
    have hdle : (minpoly ℚ_[p] x).natDegree ≤ Module.finrank ℚ_[p] K := minpoly.natDegree_le x
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hdpos hdle
    have hc0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
    have hx1 : ‖(x : PadicAlgCl p)‖ =
        ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / ((minpoly ℚ_[p] x).natDegree : ℝ)) := by
      rw [← PadicAlgCl.spectralNorm_eq,
        spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) (x : PadicAlgCl p),
        hmin]
    have hx2 : ‖(x : PadicAlgCl p)‖ ^ (minpoly ℚ_[p] x).natDegree = ‖(minpoly ℚ_[p] x).coeff 0‖ := by
      rw [hx1, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hdpos.ne']
    refine ⟨-((minpoly ℚ_[p] x).coeff 0).valuation * c, ?_⟩
    rw [hc, pow_mul, hx2, Padic.norm_eq_zpow_neg_valuation hc0, ← zpow_natCast, ← zpow_mul]
  have hn0 : ((Module.finrank ℚ_[p] K : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  set c : ℚ_[p] := ((p : ℚ_[p]) * (Module.finrank ℚ_[p] K : ℕ))⁻¹ with hcdef
  have hbd : ∀ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) →
        ‖(a : PadicAlgCl p)‖ < ‖c‖ := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    have ha0 : (a : PadicAlgCl p) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      exact absurd hlt (not_le.2 (norm_pos_iff.2 (inv_ne_zero (mul_ne_zero hp0 hn0))))
    have ha0' : a ≠ 0 := fun h => ha0 (by simp [h])
    have hz := ha (algebraMap ℚ_[p] K c * a⁻¹) (by
      rw [IntermediateField.coe_mul, IntermediateField.coe_inv, norm_mul, norm_inv]
      have hcn : ‖((algebraMap ℚ_[p] K c : K) : PadicAlgCl p)‖ = ‖c‖ :=
        PadicAlgCl.norm_extends p c
      rw [hcn, ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 ha0)]
      exact hlt)
    have e2 : a * (algebraMap ℚ_[p] K c * a⁻¹) = algebraMap ℚ_[p] K c := by
      rw [_root_.mul_comm, _root_.mul_assoc, inv_mul_cancel₀ ha0', _root_.mul_one]
    rw [e2, Algebra.trace_algebraMap, nsmul_eq_mul] at hz
    have e3 : ((Module.finrank ℚ_[p] K : ℕ) : ℚ_[p]) * c = (p : ℚ_[p])⁻¹ := by
      rw [hcdef]
      field_simp
    rw [e3, norm_inv, Padic.norm_p, inv_inv] at hz
    linarith
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt (‖c‖ ^ (Module.finrank ℚ_[p] K).factorial) hpos
  have hex := Int.exists_greatest_of_bdd (P := fun j : ℤ => ∃ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) ∧ a ≠ 0 ∧
        ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial = (p : ℝ) ^ j)
    ⟨B, fun j ⟨a, ha, _, hj⟩ => by
      have h1 : ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial <
          ‖c‖ ^ (Module.finrank ℚ_[p] K).factorial :=
        pow_lt_pow_left₀ (hbd a ha) (norm_nonneg _) (Nat.factorial_ne_zero _)
      rw [hj] at h1
      have h2 : (p : ℝ) ^ j < (p : ℝ) ^ (B : ℤ) := by
        rw [zpow_natCast]
        exact h1.trans hB
      exact ((zpow_lt_zpow_iff_right₀ hpos).1 h2).le⟩
    ⟨0, 1, fun z hz => by rw [_root_.one_mul]; exact hTr z hz, one_ne_zero, by simp⟩
  obtain ⟨jm, ⟨am, hamD, ham0, hamj⟩, hmax⟩ := hex
  have hamn : (am : PadicAlgCl p) ≠ 0 := fun h => ham0 (by exact_mod_cast h)
  refine ⟨am⁻¹, inv_ne_zero ham0, fun a => ?_⟩
  have key : ‖((a * am⁻¹ : K) : PadicAlgCl p)‖ ≤ 1 ↔
      ‖(a : PadicAlgCl p)‖ ≤ ‖(am : PadicAlgCl p)‖ := by
    rw [IntermediateField.coe_mul, IntermediateField.coe_inv, norm_mul, norm_inv,
      ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 hamn)]
  rw [key]
  constructor
  · intro ha
    by_cases ha0 : a = 0
    · simp [ha0]
    obtain ⟨j, hj⟩ := hdisc a ha0
    have hjle := hmax j ⟨a, ha, ha0, hj⟩
    have hle : ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial ≤
        ‖(am : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial := by
      rw [hj, hamj]
      exact zpow_le_zpow_right₀ hpos.le hjle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (Nat.factorial_ne_zero _)).1 hle
  · intro ha z hz
    have e : a * z = am * (am⁻¹ * a * z) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, mul_inv_cancel₀ ham0, _root_.one_mul]
    rw [e]
    apply hamD
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv,
      norm_mul, norm_mul, norm_inv]
    have h1 : ‖(am : PadicAlgCl p)‖⁻¹ * ‖(a : PadicAlgCl p)‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ (norm_pos_iff.2 hamn), _root_.mul_one]
      exact ha
    exact mul_le_one₀ h1 (norm_nonneg _) hz

theorem UpperTheory.Gal.W2.trDual_of :
    UpperTheory.Gal.W2.TrDual := by
  intro p _ G w
  exact exists_inverse_different p (G.Fw w)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem plat_core {V : Type} [AddCommGroup V] [Module ℚ V] (p : ℕ) (hp : p ≠ 0) (M : AddSubgroup V)
    (s : Finset V) (k : ℕ) (hs : Submodule.span ℚ (s : Set V) = ⊤)
    (hsat : ∀ (m : ℕ) x, m.Coprime p → m • x ∈ M → x ∈ M)
    (h1 : ∀ x ∈ s, p ^ k • x ∈ M)
    (h2 : ∀ x ∈ M, ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set V)) :
    ∃ t : Finset V, Submodule.span ℚ (t : Set V) = ⊤ ∧
      ∀ w, w ∈ M ↔ ∃ m : ℕ, m.Coprime p ∧ m • w ∈ AddSubgroup.closure (t : Set V) := by
  have hpk : ((p : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp)
  set q : ℚ := ((p : ℚ) ^ k)⁻¹ with hq
  let f : V →ₗ[ℤ] V := (LinearMap.lsmul ℚ V q).toAddMonoidHom.toIntLinearMap
  have hf : ∀ x, f x = q • x := fun x => rfl
  set W : Submodule ℤ V := Submodule.span ℤ (f '' (s : Set V)) with hW
  have hWfg : W.FG := Submodule.fg_span ((s.finite_toSet).image f)
  haveI : IsNoetherian ℤ W := isNoetherian_of_fg_of_noetherian W hWfg
  have hNfg : (AddSubgroup.toIntSubmodule M ⊓ W).FG :=
    Submodule.FG.of_le_of_isNoetherian inf_le_right
  obtain ⟨t, ht⟩ := hNfg
  have hcl : ∀ y, y ∈ AddSubgroup.closure (t : Set V) ↔ y ∈ M ∧ y ∈ W := by
    intro y
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, ht,
      Submodule.mem_inf]
    rfl
  have hsW : ∀ y ∈ AddSubgroup.closure (s : Set V), q • y ∈ W := by
    intro y hy
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup] at hy
    have hy' : f y ∈ (Submodule.span ℤ (s : Set V)).map f := Submodule.mem_map_of_mem hy
    rw [Submodule.map_span] at hy'
    rw [← hf]
    exact hy'
  refine ⟨t, ?_, fun w => ⟨fun hw => ?_, fun ⟨m, hm, hmw⟩ => hsat m w hm ((hcl _).1 hmw).1⟩⟩
  · rw [eq_top_iff, ← hs, Submodule.span_le]
    intro x hx
    have hx1 : p ^ k • x ∈ M := h1 x hx
    have e : p ^ k • x = q • ((p ^ k * p ^ k) • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      congr 1
      push_cast
      rw [hq, ← _root_.mul_assoc, inv_mul_cancel₀ hpk, _root_.one_mul]
    have hx2 : p ^ k • x ∈ W := by
      rw [e]
      exact hsW _ (AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure hx) _)
    have hmem : p ^ k • x ∈ Submodule.span ℚ (t : Set V) :=
      (AddSubgroup.closure_le (K := (Submodule.span ℚ (t : Set V)).toAddSubgroup)).2
        Submodule.subset_span ((hcl _).2 ⟨hx1, hx2⟩)
    have e2 : x = q • (p ^ k • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      push_cast
      rw [hq, inv_mul_cancel₀ hpk, one_smul]
    show x ∈ Submodule.span ℚ (t : Set V)
    rw [e2]
    exact Submodule.smul_mem _ q hmem
  · obtain ⟨m, hm, hmem⟩ := h2 w hw
    refine ⟨m, hm, (hcl _).2 ⟨M.nsmul_mem hw m, ?_⟩⟩
    have e : m • w = q • ((m * p ^ k) • w) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      congr 1
      push_cast
      rw [hq, _root_.mul_comm (m : ℚ), ← _root_.mul_assoc, inv_mul_cancel₀ hpk, _root_.one_mul]
    rw [e]
    exact hsW _ hmem

theorem UpperTheory.Gal.W2.pLatOf_of :
    UpperTheory.Gal.W2.PLatOf := by
  intro p _ D M s k hs hO hsat h1 h2
  exact ⟨hO, plat_core p (Fact.out : p.Prime).ne_zero M s k hs hsat h1 h2⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.powSm_of :
    UpperTheory.Gal.W2.PowSm := by
  intro X s d g hs hqc hsep A _ _ hA hg k
  have hP : IsProper (KS.pow A k).hom := KS.Leray.isProper_pow_hom A hA.proper k
  have hsm := FibPow.smoothOfRelativeDimension_fibrePower ℂ X s d g hs A hA hg k
  refine ⟨hsm, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · haveI : Smooth ((KS.pow A k).hom ≫ s) := hsm.smooth
    infer_instance
end
