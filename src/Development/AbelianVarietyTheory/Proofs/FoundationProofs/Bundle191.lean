module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle702
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeRowDifferenceSummableBound
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle181
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterNotPowModMaximalIdealAdjoinAlgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle105
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle184
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.RealPlaceAnalysis.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle017
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType

theorem conj_blockLower_mem_theta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ g ∈ grp ψ, (∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → g.val a b = 0) → z⁻¹ * g * z ∈ grp ψ ∧ theta ψ (z⁻¹ * g * z) = theta ψ g := by
  intro k _ _ _ _ n ψ r ϖ hϖ hv z hz g hg hup
  set d : Fin n → k := fun i => if (i : ℕ) < r then ϖ else 1 with hd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i; simp only [hd]; split_ifs <;> simp [hϖ]
  have h2 : diagonal (fun i => (d i)⁻¹) * z.val = 1 := by
    rw [hz, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hd0 i)
  have hzi : (z⁻¹).val = diagonal (fun i => (d i)⁻¹) := by
    calc (z⁻¹).val = (diagonal (fun i => (d i)⁻¹) * z.val) * (z⁻¹).val := by rw [h2, Matrix.one_mul]
      _ = diagonal (fun i => (d i)⁻¹) := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hent : ∀ i j, (z⁻¹ * g * z).val i j = (d i)⁻¹ * g.val i j * d j := by
    intro i j
    rw [Units.val_mul, Units.val_mul, hzi, hz, mul_diagonal, diagonal_mul]
  have hupper : ∀ i j : Fin n, i < j → (z⁻¹ * g * z).val i j = g.val i j := by
    intro i j hij
    rw [hent]
    have hij' : (i : ℕ) < j := hij
    by_cases hi : (i : ℕ) < r
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_pos hi, if_pos hj]; field_simp
      · rw [hup i j hi (not_lt.1 hj)]; simp
    · have hj : ¬ (j : ℕ) < r := by omega
      simp only [hd, if_neg hi, if_neg hj]; simp
  have hle : ∀ i j, valuation k ((z⁻¹ * g * z).val i j) ≤ valuation k (g.val i j) := by
    intro i j
    rw [hent]
    by_cases hi : (i : ℕ) < r
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_pos hi, if_pos hj]
        have : ϖ⁻¹ * g.val i j * ϖ = g.val i j := by field_simp
        rw [this]
      · rw [hup i j hi (not_lt.1 hj)]; simp
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_neg hi, if_pos hj, inv_one, one_mul, map_mul]
        calc valuation k (g.val i j) * valuation k ϖ ≤ valuation k (g.val i j) * 1 := by
              gcongr
          _ = _ := mul_one _
      · simp only [hd, if_neg hi, if_neg hj]; simp
  have hdet : (z⁻¹ * g * z).val.det = g.val.det := by
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul]
  have hminor : ∀ m, minor (z⁻¹ * g * z) m = minor g m := by
    intro m
    simp only [minor]
    set G := g.val.toSquareBlockProp (fun i => i ≤ m) with hG
    have e : (z⁻¹ * g * z).val.toSquareBlockProp (fun i => i ≤ m) =
        of fun (i j : {a // a ≤ m}) => (d i)⁻¹ * (of fun (i j : {a // a ≤ m}) => d j * G i j) i j := by
      ext i j
      simp only [hG, toSquareBlockProp_def, toBlock_apply, of_apply, hent]
      ring
    rw [e, det_mul_column (fun i : {a // a ≤ m} => (d i)⁻¹), det_mul_row (fun j : {a // a ≤ m} => d j) G,
      ← mul_assoc, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_one (fun (i : {a // a ≤ m}) _ => inv_mul_cancel₀ (hd0 i.1)), one_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hgk := (GlobalTheory.LocStd.mem_KO_iff_det.1 hg.1)
    refine GlobalTheory.LocStd.mem_KO_iff_det.2 ⟨fun i j => ?_, by rw [hdet]; exact hgk.2⟩
    exact (Valuation.mem_integer_iff _ _).2 ((hle i j).trans ((Valuation.mem_integer_iff _ _).1 (hgk.1 i j)))
  · intro i j hij
    rw [hupper i j hij]
    exact hg.2 i j hij
  · simp only [theta, hminor]

end GlobalTheory.PsType
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_gammaZeroPartitionWeight : ∀ L : ℕ, 0 < L → ∃ ρ, Wt L ρ := by
  first | exact @GlobalTheory.wt_exists | exact GlobalTheory.wt_exists | (intros; apply GlobalTheory.wt_exists <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eisensteinLattice_rowDifference_summable_bound : ∀ j L : ℕ, 2 ≤ j → 0 < L → ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, ∃ u : ℤ × ℤ → ℝ, Summable u ∧ ∑' x, u x ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧ ∀ (s : ℝ) (x : ℤ × ℤ), 0 ≤ s → s ≤ 1 → ‖dif L (0, 1) (fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ u x := by
  first | exact @GlobalTheory.RowBd.rowbd | exact GlobalTheory.RowBd.rowbd | (intros; apply GlobalTheory.RowBd.rowbd <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.modularForm_gammaOne_of_coeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 0 < L → N ∣ L → MF k L (ch ε) a → ∃ f : ModularForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  first | exact @GlobalTheory.EisM.modularForm_gammaOne_of_MF | exact GlobalTheory.EisM.modularForm_gammaOne_of_MF | (intros; apply GlobalTheory.EisM.modularForm_gammaOne_of_MF <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.exists_padic_cocycle_of_compatible_poly_family : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ → ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) ℤ_[l], IsCoc w (Gam N l) z ∧ ∀ n, Near (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (z δ)) (Φ n) := by
  first | exact @GlobalTheory.KZ.H3.cocycle_lift_of_fam | exact GlobalTheory.KZ.H3.cocycle_lift_of_fam | (intros; apply GlobalTheory.KZ.H3.cocycle_lift_of_fam <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.towerParameter_not_pow_mod_maximalIdeal_adjoin_algebraic : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgZp (p := p) s) →
  ∀ y ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)), IsInt (p := p) y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω)) := by
  intro p _ Ω _ _ hclo S hS y hy hyint
  rintro ⟨m, hm, hmint⟩
  classical
  have := Basic.charZero_of_isClo hclo
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have huni := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal := by
    rw [← huni]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [huni]
    exact GlobalTheory.T.unramified_integers_adic_complete p
  have := hclo.alg
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr
    (O0 p) Ω hclo.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hvp0 : 0 < v (p : Ω) := (Valuation.pos_iff v).2 hp0
  have hvp1 : v (p : Ω) < 1 := by
    have hpint : IsIntegral (O0 p) (p : Ω) := by
      simpa only [map_natCast] using
        (isIntegral_algebraMap (A := Ω) (x := (p : O0 p)))
    refine lt_of_le_of_ne ((hv _).2 hpint) ?_
    intro heq
    have hinv : IsInt (p := p) ((p : Ω)⁻¹) := (hv _).1 (by rw [map_inv₀, heq, inv_one])
    exact Basic.not_cong_one_zero hclo 1 one_ne_zero
      ⟨(p : Ω)⁻¹, hinv, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  let : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap ℤ_[p] Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have e := PadicInt.unitCoeff_spec hx0
    rw [e, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h | h
    · exact ((Units.isUnit _).map (algebraMap ℤ_[p] Ω)).ne_zero h
    · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h
  have hvint : ∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1 := fun x hx =>
    (hv x).2 (IsIntegral.tower_top (A := O0 p) hx)
  have hSalg : ∀ s ∈ S, IsAlgebraic ℤ_[p] s := by
    intro s hs
    obtain ⟨P, hP0, hP⟩ := hS s hs
    exact ⟨P, hP0, by rwa [Polynomial.aeval_map_algebraMap] at hP⟩
  obtain ⟨R, hRfin, hRpid, hRS⟩ := GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions p Ω hinj S hSalg
  obtain ⟨π, hπR, hπ0, hvπ, hpπ, f, hf, hstep⟩ :=
    GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr p Ω hinj v hvint hvp1 R hRfin hRpid
  have hfg : (Subalgebra.toSubmodule R).FG := Module.Finite.iff_fg.1 hRfin
  obtain ⟨T, hT⟩ := Subalgebra.fg_of_fg_toSubmodule hfg
  have hRB : ∀ x ∈ R, x ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
    intro x hx
    have hle : Algebra.adjoin ℤ_[p] (T : Set Ω) ≤
        (Algebra.adjoin (O0 p) (T : Set Ω)).restrictScalars ℤ_[p] :=
      Algebra.adjoin_le (fun t ht => (Subalgebra.mem_restrictScalars _).2 (Algebra.subset_adjoin ht))
    rw [hT] at hle
    exact (Subalgebra.mem_restrictScalars _).1 (hle hx)
  have hTR : ∀ t ∈ T, t ∈ R := fun t ht => hT ▸ Algebra.subset_adjoin (Finset.mem_coe.2 ht)
  have hTint : ∀ t ∈ T, IsIntegral (O0 p) t := fun t ht =>
    (IsIntegral.of_mem_of_fg R hfg t (hTR t ht)).tower_top
  obtain ⟨hdiv, hres⟩ := GlobalTheory.K5.NotPow.residue_core p (O0 p) Ω hmax v hv T hTint π (hRB _ hπR) hπ0 hvπ
    (hRB _ hpπ) f hf (fun t ht => hRB _ (hstep t (hTR t ht)))
  have hBint : ∀ x ∈ Algebra.adjoin (O0 p) (T : Set Ω), v x ≤ 1 := fun x hx =>
    (hv x).2 (Algebra.adjoin_le (S := integralClosure (O0 p) Ω) (fun t ht => hTint t ht) hx)
  have hclosed := GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer (O0 p) Ω v hv _ hBint π (hRB _ hπR) hπ0 hvπ hdiv
  have hsub : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) ≤
      Subfield.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω) := by
    rw [Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ c)
    · obtain ⟨a, ha, b, hb, rfl⟩ := hRS x hx
      exact div_mem (Subfield.subset_closure (hRB _ ha)) (Subfield.subset_closure (hRB _ hb))
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.1 (hsub hy)
  have hcl : ∀ z ∈ Subring.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω),
      z ∈ Algebra.adjoin (O0 p) (T : Set Ω) := fun z hz =>
    (Subring.closure_le (t := (Algebra.adjoin (O0 p) (T : Set Ω)).toSubring)).2 (fun _ h => h) hz
  have hyv : v y ≤ 1 := (hv y).2 hyint
  have hyB : y ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
    rw [← hab]
    exact hclosed a (hcl a ha) b (hcl b hb) (by rw [hab]; exact hyv)
  have hvq : v (y ^ p - algebraMap (O0 p) Ω (qO p)) < 1 := by
    have h1 := (hv _).2 hmint
    rw [map_div₀, map_pow] at h1
    have h2 : v (y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m < 1 :=
      lt_of_le_of_lt ((div_le_one₀ hvp0).1 h1) hvp1
    by_contra hc
    push Not at hc
    exact absurd h2 (not_lt.2 (one_le_pow₀ hc))
  obtain ⟨b, hb⟩ := hres y hyB (qO p) hvq
  have hbv : v (algebraMap (O0 p) Ω b) ≤ 1 := (hv _).2 isIntegral_algebraMap
  have hvb : v (algebraMap (O0 p) Ω (b ^ p - qO p)) < 1 := by
    have e : algebraMap (O0 p) Ω (b ^ p - qO p) = (y ^ p - algebraMap (O0 p) Ω (qO p)) -
        (y ^ p - (algebraMap (O0 p) Ω b) ^ p) := by
      rw [map_sub, map_pow]
      ring
    have hg : v (y ^ p - (algebraMap (O0 p) Ω b) ^ p) < 1 := by
      rw [← geom_sum₂_mul, map_mul]
      have hs : v (∑ i ∈ Finset.range p, y ^ i * (algebraMap (O0 p) Ω b) ^ (p - 1 - i)) ≤ 1 := by
        apply v.map_sum_le
        intro i _
        rw [map_mul, map_pow, map_pow]
        exact mul_le_one' (pow_le_one' hyv _) (pow_le_one' hbv _)
      calc _ ≤ 1 * v (y - algebraMap (O0 p) Ω b) := mul_le_mul_of_nonneg_right hs zero_le
        _ < 1 := by rw [one_mul]; exact hb
    rw [e]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hvq hg)
  have hdvd : (p : O0 p) ∣ b ^ p - qO p := by
    by_contra hnd
    have hu : IsUnit (b ^ p - qO p) := by
      by_contra hnu
      apply hnd
      have hmem : b ^ p - qO p ∈ IsLocalRing.maximalIdeal (O0 p) :=
        (IsLocalRing.mem_maximalIdeal _).2 hnu
      rw [huni] at hmem
      exact Ideal.mem_span_singleton.1 hmem
    obtain ⟨u, hu⟩ := hu
    have h1 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h2 : v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) ≤ 1 := (hv _).2 isIntegral_algebraMap
    rw [← hu] at hvb
    have h4 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) < 1 :=
      calc _ ≤ v (algebraMap (O0 p) Ω (u : O0 p)) * 1 := mul_le_mul_of_nonneg_left h2 zero_le
        _ < 1 := by rw [mul_one]; exact hvb
    rw [h1] at h4
    exact lt_irrefl _ h4
  exact GlobalTheory.K5.NotPow.q_not_pow_mod p b hdvd
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_qDerivation_completion_Zp : ∀ (p : ℕ) [Fact p.Prime], ∃ D : Derivation ℤ (O0 p) (O0 p), D (qO p) = qO p ∧
    ∀ r : ℤ_[p], D (algebraMap ℤ_[p] (O0 p) r) = 0 := by
  first | exact @GlobalTheory.K5.QDer.exists_qDer | exact GlobalTheory.K5.QDer.exists_qDer | (intros; apply GlobalTheory.K5.QDer.exists_qDer <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.centralIdempotent_irreducible_character_props : ∀ (G : Type) [Group G] [Fintype G], ∀ (V : FDRep ℂ G) [CategoryTheory.Simple V], IsProj (zc V.character) ∧ (∀ a : G → ℂ, conv (zc V.character) a = conv a (zc V.character)) ∧ (∀ (W : FDRep ℂ G) [CategoryTheory.Simple W], V.character ≠ W.character → conv (zc V.character) (zc W.character) = 0) ∧ ∀ e : G → ℂ, conv e e = e → conv (zc V.character) e 1 = (Module.finrank ℂ V : ℂ) * (rk V.ρ e : ℂ) / (Fintype.card G : ℂ) := by
  first | exact @GlobalTheory.BadShare.ZCalc.zc_calc | exact GlobalTheory.BadShare.ZCalc.zc_calc | (intros; apply GlobalTheory.BadShare.ZCalc.zc_calc <;> assumption)
end

section

open Formalism.BasicNotions.TH

namespace GlobalTheory

theorem mat_compact_eq_sum_units {n : ℕ} (Z : Mat n 0) :
    Z = ∑ a : Fin n, ∑ b : Fin n,
      Z (Sum.inl a) (Sum.inl b) • Eab (Sum.inl a : Ix n 0) (Sum.inl b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Eab,
    Matrix.smul_single, smul_eq_mul, mul_one]

theorem gkMod_compact_glRel {n : ℕ} (M : GKMod n 0) :
    Formalism.REAL.GlRel (fun a b : Fin n => M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b))) := by
  intro a b c d
  show M.act _ * M.act _ - M.act _ * M.act _ = _
  rw [← M.lie, map_sub]
  congr 1
  · split_ifs with h
    · subst h; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne, map_zero]
      intro h'; exact h (Sum.inl_injective h')
  · split_ifs with h
    · subst h; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne, map_zero]
      intro h'; exact h (Sum.inl_injective h')

theorem gkMod_compact_irr_units {n : ℕ} (M : GKMod n 0) (h : Formalism.MainNotions.SchurIrreducible.IrrGK M)
    (S : Submodule ℂ M.V)
    (hS : ∀ a b : Fin n, ∀ x ∈ S, M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b)) x ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  refine h.2 S fun Z y hy => ?_
  rw [mat_compact_eq_sum_units Z]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b y hy)

theorem gkMod_compact_isHW_units {n : ℕ} (M : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V)
    (h : IsHW M.act Λ v) :
    Formalism.REAL.IsHW (fun a b : Fin n => M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b)))
      (fun a => ((Λ (Sum.inl a) : ℚ) : ℂ)) v := by
  obtain ⟨-, h1, h2⟩ := h
  simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1 h2
  exact ⟨fun a => h1 _, fun a b hab => h2 (Sum.inl a) (Sum.inl b) hab⟩

theorem exists_intertwiner_map_highestVector :
    ∀ (n : ℕ) (M M' : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V) (v' : M'.V),
      Formalism.MainNotions.SchurIrreducible.IrrGK M → Formalism.MainNotions.SchurIrreducible.IrrGK M' → IsHW M.act Λ v → IsHW M'.act Λ v' →
      ∃ f : M.V →ₗ[ℂ] M'.V, f v = v' ∧ ∀ Z x, f (M.act Z x) = M'.act Z (f x) := by
  intro n M M' Λ v v' hM hM' hv hv'
  have w := gkMod_compact_isHW_units M Λ v hv
  have w' := gkMod_compact_isHW_units M' Λ v' hv'
  obtain ⟨T, hT⟩ := exists_linearEquiv_of_irreducible_isHW M.V M'.V n _ _ _ v v'
    (gkMod_compact_glRel M) (gkMod_compact_glRel M') (gkMod_compact_irr_units M hM)
    (gkMod_compact_irr_units M' hM') w w' hv.1 hv'.1
  obtain ⟨S, hS, hvS, htop⟩ :=
    exists_stable_submodule_topWeight_line M'.V n _ _ v' (gkMod_compact_glRel M') w'
  have hStop : S = ⊤ := by
    rcases gkMod_compact_irr_units M' hM' S hS with h | h
    · rw [h, Submodule.mem_bot] at hvS
      exact absurd hvS hv'.1
    · exact h
  obtain ⟨c, hc⟩ := htop (T v) (by rw [hStop]; trivial) (fun a => by
    rw [← hT a a v, w.1 a, map_smul])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, map_eq_zero_iff T T.injective] at hc
    exact hv.1 hc
  refine ⟨c⁻¹ • T.toLinearMap, ?_, fun Z x => ?_⟩
  · simp [hc, smul_smul, hc0]
  · have key : T (M.act Z x) = M'.act Z (T x) := by
      rw [mat_compact_eq_sum_units Z]

      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hT a b x]
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, key, map_smul]

end GlobalTheory
end

section

namespace GlobalTheory.BlochKato₂

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem localTheorem_iff (D : D7) : LocalSituation.Conclusion5 D ↔ BlochKatoReduction.adm3 D ∧
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
      LocalSituation.bkARightExact ((D.loc l).PD K) ∧ LocalSituation.bkC ((D.loc l).PD K) :=
  ⟨fun h => ⟨fun l _ K => ⟨(h l K).1, (h l K).2.1, (h l K).2.2.2.1⟩,
      fun l _ K => ⟨(h l K).2.2.1, (h l K).2.2.2.2⟩⟩,
    fun h l _ K => ⟨(h.1 l K).1, (h.1 l K).2.1, (h.2 l K).1, (h.1 l K).2.2, (h.2 l K).2⟩⟩

theorem duality_dim_of_localTheorem : ∀ D : D7, LocalSituation.Conclusion5 D → BlochKatoReduction.Gen.adm3 D ∧ BlochKatoReduction.adm3 D :=
  fun D h => ⟨((localTheorem_iff D).1 h).1, ((localTheorem_iff D).1 h).1⟩

end GlobalTheory.BlochKato₂
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.NormValExt

open IsDiscreteValuationRing

variable {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

theorem toNat_addVal_mul {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    (addVal R (a * b)).toNat = (addVal R a).toNat + (addVal R b).toNat := by
  rw [addVal_mul]
  exact ENat.toNat_add (fun h => ha ((addVal_eq_top_iff).mp h)) (fun h => hb ((addVal_eq_top_iff).mp h))

theorem nval_mul (l : ℕ) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    BlochKatoReduction.Gen.nval R l (a * b) =
      BlochKatoReduction.Gen.nval R l a + BlochKatoReduction.Gen.nval R l b := by
  unfold BlochKatoReduction.Gen.nval
  rw [toNat_addVal_mul ha hb, Nat.cast_add, add_div]

theorem vK_eq (l : ℕ) {x : FractionRing R} (hx : x ≠ 0) {a b : R} (hb : b ≠ 0)
    (h : x * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) :
    BlochKatoReduction.Gen.vK R l x =
      BlochKatoReduction.Gen.nval R l a - BlochKatoReduction.Gen.nval R l b := by
  unfold BlochKatoReduction.Gen.vK
  generalize_proofs hE
  have hinj := IsFractionRing.injective R (FractionRing R)
  have key : ∀ q : R × nonZeroDivisors R,
      x * algebraMap R (FractionRing R) q.2 = algebraMap R (FractionRing R) q.1 →
      BlochKatoReduction.Gen.nval R l q.1 - BlochKatoReduction.Gen.nval R l q.2 =
        BlochKatoReduction.Gen.nval R l a - BlochKatoReduction.Gen.nval R l b := by
    intro q hq
    have hq2 : (q.2 : R) ≠ 0 := nonZeroDivisors.ne_zero q.2.2
    have ha : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).mpr hb) h
    have hq1 : q.1 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hq
      exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).mpr hq2) hq
    have hcross : a * q.2 = q.1 * b := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hq]
      ring
    have hc := congrArg (BlochKatoReduction.Gen.nval R l) hcross
    rw [nval_mul l ha hq2, nval_mul l hq1 hb] at hc
    linarith
  exact key hE.choose hE.choose_spec

end GlobalTheory.NormValExt
end
