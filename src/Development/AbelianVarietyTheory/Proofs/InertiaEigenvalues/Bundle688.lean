module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle590
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle661
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle662
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle158
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle663
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem BK.exists_Ep_eq_X_pow_add {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : Polynomial (Wq l bk.a),
      bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
  have h : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, sub_zero]; exact bk.dvd_coeff i hi
    · rw [if_pos hi, hi, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg hi.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hi, sub_zero]; exact dvd_zero _
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by rw [← hq]; ring⟩

theorem BK.norm_toDisc_E_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 →
    ∀ y : bk.DS ρ, ‖toDisc l (X : bk.S) ρ bk.E * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  intro l _ K bk ρ h0 h1 y
  obtain ⟨_, _, ⟨hρ0, _, hρe⟩, _⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hρ : 0 < ρ := hρ0.trans_le h0
  rw [GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative l K bk ρ hρ h1]
  congr 1
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  apply le_antisymm
  · obtain ⟨q, hq⟩ := bk.exists_Ep_eq_X_pow_add
    have hE : bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * (q : bk.S) := by
      simp only [BK.E]
      conv_lhs => rw [hq]
      rw [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C,
        map_natCast]
    have hl' : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (l : bk.S)‖ ≤ (l : ℝ)⁻¹ :=
      gauge_le l (X : bk.S) ρ (by positivity) (Submodule.subset_span ⟨1, 0, 0,
        by rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], by simp⟩)
    have hX : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) ((X : bk.S) ^ bk.Ep.natDegree)‖ ≤
        (ρ : ℝ) ^ bk.Ep.natDegree :=
      (norm_ofPre l (X : bk.S) ρ _).symm.trans_le (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) _ hρ)
    have hup : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) bk.E‖ ≤ (ρ : ℝ) ^ bk.Ep.natDegree := by
      rw [hE, map_add (f := _), map_mul, norm_preDisc]
      refine (gauge_add_le_max l (X : bk.S) ρ _ _).trans (max_le ?_ ?_)
      · rw [← norm_preDisc]; exact hX
      · rw [← norm_preDisc]
        calc _ ≤ ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (l : bk.S)‖ *
              ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (q : bk.S)‖ := norm_mul_le _ _
          _ ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul hl' (norm_algebraMap_le _) (norm_nonneg _) (by positivity)
          _ = ((bk.ρ₀ ^ bk.Ep.natDegree : ℝ≥0) : ℝ) := by rw [hρe]; simp
          _ ≤ (ρ : ℝ) ^ bk.Ep.natDegree := by
            rw [NNReal.coe_pow]; exact pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast h0) _
    exact (norm_ofPre l (X : bk.S) ρ _).trans_le hup
  · obtain ⟨a, ha1, ha2, -, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ h1
    obtain ⟨-, -, -, hk⟩ := GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk
    have hc : coeff bk.Ep.natDegree bk.E = 1 := by
      rw [BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree]
    have h := ha2 bk.Ep.natDegree (toDisc l (X : bk.S) ρ bk.E)
    rw [ha1, hc, hk 1 isUnit_one, one_mul] at h
    exact h

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.NoPole

theorem mul_eq_smul_one_comm {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (X X' : Matrix (Fin d) (Fin d) R) (c : R) (hc : c ≠ 0)
    (h : X * X' = c • (1 : Matrix (Fin d) (Fin d) R)) : X' * X = c • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : X.det * X'.det = c ^ d := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hX : X.det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hdet; exact pow_ne_zero _ hc hdet.symm
  have key : X.det • (X' * X) = X.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
    calc X.det • (X' * X) = (X.adjugate * X) * (X' * X) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = X.adjugate * (X * X') * X := by simp only [Matrix.mul_assoc]
      _ = c • (X.adjugate * X) := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = X.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
          rw [Matrix.adjugate_mul, smul_comm]
  ext i j
  have := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hX this

theorem map_smul_ring {R S : Type*} [CommRing R] [CommRing S] {a b : Type*} (F : R →+* S) (c : R)
    (M : Matrix a b R) : (c • M).map F = F c • M.map F := by
  ext i j; simp

end GlobalTheory.NoPole

namespace GlobalTheory.NoPole

theorem core {S B : Type*} [CommRing S] [CommRing B] {d m : ℕ} (F G : S →+* B) (E : S) (v : B)
    (ℓ N c₂ k₀ : ℕ) (s : Matrix (Fin d) (Fin m) S) (n : Fin m → ℕ) (X X' R : Matrix (Fin d) (Fin d) S)
    (Q : Matrix (Fin m) (Fin d) S) (Q' : Matrix (Fin d) (Fin m) S)
    (hs : ∀ r i, F E ^ (2 * N) ∣ (ℓ : B) ^ k₀ * (F (s r i) - G (s r i)))
    (hv : v * F E = G E)
    (hX'X : X' * X = ((ℓ : S) ^ c₂ * E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) S))
    (hX : X = (s * Matrix.diagonal fun i => E ^ n i) * Q + E ^ (2 * N) • R)
    (hQ' : (ℓ : S) ^ c₂ • (s * Matrix.diagonal fun i => E ^ n i) = X * Q') :
    ∀ i j, F E ^ (2 * N) ∣ (ℓ : B) ^ (k₀ + c₂) * (X'.map F * X.map G) i j := by
  classical
  let π := Ideal.Quotient.mk (Ideal.span {F E ^ (2 * N)})
  let F' := π.comp F
  let G' := π.comp G
  have hFE : F' E ^ (2 * N) = 0 := by
    have h0 : π (F E ^ (2 * N)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    simpa only [F', RingHom.comp_apply, map_pow] using h0
  have hGE : G' E = π v * F' E := by
    simp only [G', F', RingHom.comp_apply]; rw [← map_mul, hv]
  have hGE0 : G' E ^ (2 * N) = 0 := by rw [hGE, mul_pow, hFE, mul_zero]
  have e2 : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • s.map G' = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • s.map F' := by
    ext r i
    have h : π ((ℓ : B) ^ k₀ * (F (s r i) - G (s r i))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (hs r i))
    simp only [map_mul, map_sub, map_pow, map_natCast] at h
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, F', G', RingHom.comp_apply]
    linear_combination (-1 : B ⧸ Ideal.span {F E ^ (2 * N)}) * h
  have hd : (Matrix.diagonal fun i => G' (E ^ n i)) =
      Matrix.diagonal (fun i => F' E ^ n i) * Matrix.diagonal (fun i => π v ^ n i) := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; rw [map_pow, hGE, mul_pow]; ring
  have e1 : X.map G' = (s.map G' * Matrix.diagonal (fun i => F' E ^ n i)) *
      (Matrix.diagonal (fun i => π v ^ n i) * Q.map G') := by
    rw [hX, Matrix.map_add _ (map_add G'), map_smul_ring, map_pow, hGE0, zero_smul, add_zero, Matrix.map_mul, Matrix.map_mul,
      Matrix.diagonal_map (map_zero _), hd]
    simp only [Matrix.mul_assoc]
  have e3 : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i)) = X.map F' * Q'.map F' := by
    have : ((ℓ : S) ^ c₂ • (s * Matrix.diagonal fun i => E ^ n i)).map F' = (X * Q').map F' := by rw [hQ']
    rw [map_smul_ring, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _), map_pow, map_natCast]
      at this
    simpa only [map_pow] using this
  have e4 : X'.map F' * X.map F' = 0 := by
    rw [← Matrix.map_mul, hX'X, map_smul_ring, map_mul, map_pow F' E, hFE, mul_zero, zero_smul]
  have hsuff : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ (k₀ + c₂)) • (X'.map F' * X.map G') = 0 := by
    have e2' : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map G' * Matrix.diagonal (fun i => F' E ^ n i)) =
        ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i)) := by
      rw [← Matrix.smul_mul, e2, Matrix.smul_mul]
    rw [e1]
    calc ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ (k₀ + c₂)) • (X'.map F' * ((s.map G' * Matrix.diagonal (fun i => F' E ^ n i)) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G')))
        = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (X'.map F' * ((((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map G' * Matrix.diagonal (fun i => F' E ^ n i))) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G'))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; congr 1; ring
      _ = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (X'.map F' * ((((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i))) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G'))) := by rw [e2']
      _ = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (X'.map F' * ((((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i))) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G'))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; congr 1; ring
      _ = 0 := by
          rw [e3]; simp only [← Matrix.mul_assoc, e4, Matrix.zero_mul, smul_zero]
  intro i j
  have := congrFun (congrFun hsuff i) j
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]

  simpa [Matrix.mul_apply, map_sum, F', G', π] using this

end GlobalTheory.NoPole


open GlobalTheory.NoPole in
theorem GlobalTheory.seed_nopole : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d m N c₂ : ℕ) (s : Matrix (Fin d) (Fin m) (bk.S)) (n : Fin m → ℕ) (X X' R : Matrix (Fin d) (Fin d) (bk.S)) (Q : Matrix (Fin m) (Fin d) (bk.S)) (Q' : Matrix (Fin d) (Fin m) (bk.S)), (∀ r i, (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (BK.hf f (s r i) - BK.hf g (s r i)))) → X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → X = (s * Matrix.diagonal fun i => bk.E ^ n i) * Q + bk.E ^ (2 * N) • R → (l : bk.S) ^ c₂ • (s * Matrix.diagonal fun i => bk.E ^ n i) = X * Q' → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) := by
  intro l _ K bk d m N c₂ s n X X' R Q Q' hs hXX' hX hQ' B f g
  classical
  have hl0 : (l : bk.S) ≠ 0 := by
    intro h0
    have h1 : bk.str.symm (Ideal.Quotient.mk _ (l : bk.S)) = 0 := by rw [h0, map_zero, map_zero]
    rw [map_natCast, map_natCast] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  have hc : ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ bk.E_ne_zero)
  have hX'X := mul_eq_smul_one_comm X X' _ hc hXX'
  choose k hk using fun (p : Fin d × Fin m) => hs p.1 p.2 B f g
  obtain ⟨v, hv⟩ : ∃ v, v * BK.hf f bk.E = BK.hf g bk.E := by
    have h1 := (GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal l K bk B f g).2.2
    have h2 := (GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal l K bk B g f).2.2
    have : BK.hf g bk.E ∈ B.I := by rw [h2]; exact Ideal.mem_span_singleton_self _
    rw [h1] at this
    exact Ideal.mem_span_singleton'.1 this
  refine ⟨Finset.univ.sup k + c₂, GlobalTheory.NoPole.core (BK.hf f) (BK.hf g) bk.E v l N c₂ _ s n X X' R Q Q' ?_ hv
    hX'X hX hQ'⟩
  intro r i
  have hle : k (r, i) ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ _)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact Dvd.dvd.mul_left (hk (r, i)) _
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh

namespace GlobalTheory.DiscreteSpectrumCM

theorem isUnitarisable_of_injective {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (q : ρ.IntertwiningMap τ)
    (hq : Function.Injective q) (hu : IsUnitarisable τ) : IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := hu
  let B' : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ := (B.compl₂ q.toLinearMap).comp q.toLinearMap
  have hB : ∀ v w, B' v w = B (q v) (q w) := fun _ _ => rfl
  refine ⟨B', fun v w => by rw [hB, hB, h1], fun v hv => by
    rw [hB]; exact h2 _ fun e => hv (hq (e.trans (map_zero q).symm)), fun g v w => ?_⟩
  rw [hB, hB, ← h3 g (q v) (q w)]
  rw [q.isIntertwining _ _ g v, q.isIntertwining _ _ g w]

section Local

open GlobalTheory.PRep GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem injective_of_irreducible {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (hi : ρ.IsIrreducible)
    (q : ρ.IntertwiningMap τ) (h0 : q.toLinearMap ≠ 0) : Function.Injective q := by
  rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hi).2 (LinearMap.ker q.toLinearMap) (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    change q (ρ g v) = 0
    rw [q.isIntertwining _ _ g v]
    change τ g (q.toLinearMap v) = 0
    rw [hv, map_zero]) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

theorem isUnitarisable_of_isSpeh_one {a : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GL (Fin a) k) X} (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    {τ : Representation ℂ (GL (Fin a) k) Y} (h : IsSpeh (IrrGL.of ρ hs hi) 1 τ) (hu : IsUnitarisable τ) :
    IsUnitarisable ρ := by
  obtain ⟨hd, hτ, p, hp, -⟩ := h
  have key : ∀ y : Fin 1 → IrrGL (k := k), y = (fun _ => IrrGL.of ρ hs hi) → ∀ hd : ∑ i, (y i).1 = a,
      Nonempty ((IrrGL.of ρ hs hi).rep.Equiv (prodIrr y hd)) := by
    rintro _ rfl hd
    exact nonempty_equiv_prodIrr_one _ hd
  obtain ⟨e⟩ := key _ (funext fun _ => by simp [spehFactor]) hd
  let q : ρ.IntertwiningMap τ := p.comp (e.toIntertwiningMap.comp (IrrGL.equivOf ρ hs hi).toIntertwiningMap)
  have hq : Function.Surjective q :=
    hp.comp (e.toLinearEquiv.surjective.comp (IrrGL.equivOf ρ hs hi).toLinearEquiv.surjective)
  refine isUnitarisable_of_injective q (injective_of_irreducible hi q fun h0 => ?_) hu
  have : Nontrivial Y := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hτ).1
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨v, rfl⟩ := hq y
  exact hy (LinearMap.congr_fun h0 v)

end Local

section Speh

open GlobalTheory.PRep GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E]

theorem isSpehQuot_of_isSpeh {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a)
    (σ' : LocIrr w N) (hs : IsSpeh (IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ) : IsSpehQuot h σ σ' := by
  obtain ⟨hd, -, p, hp, -⟩ := hs
  let T : ∀ i : Fin d, (_root_.GlobalTheory.SmGL.twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans
      ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  exact ⟨p.comp M.toIntertwiningMap, hp.comp M.toLinearEquiv.surjective⟩

end Speh

section Inf

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem hasInfCharGL_unique {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (h : HasInfCharGL V τ m) (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

end Inf

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  simp only [GlobalTheory.SphGal.spehInf, GlobalTheory.DefiniteBC.spehInf]
  rw [← List.sum_ofFn, ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
  rfl

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.DiscreteSpectrumCM

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.DownLift.GenFinite

theorem thetaKO_smul {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D S)
    (g : GA D T) (c : ℂ) (f : WO S T → ℂ) : thetaKO om h g (c • f) = c * thetaKO om h g f := by
  simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem integrableOn_downIntegrand : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP →
    ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ)
      (g : GA D (Wc D i)), IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y f l g hf
  have hm := hG.core.models
  have hom := (hP i t).datum
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hcont : Continuous fun h => l (R.extV i t y h) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx)
  have hinv : ∀ γ ∈ GQ (Vc D i), ∀ h, l (R.extV i t y (γ * h)) = l (R.extV i t y h) := fun γ hγ h =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx γ hγ h)
  have key := GlobalTheory.DefiniteQuotient.integrableOn_theta D R.ψ hom.std (Vc D i) (Wc D i) _ _ (R.ωP i t) hom hpos ℂ
    (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) f) (fun x => theta_smul x hf) (fun h => l (R.extV i t y h)) hcont hinv
    (R.νV i t) (R.fdV i t) (hm.νV i t).1.1 (hm.νV i t).2 g
  have e : (fun h => thetaKO (R.ωP i t) h g (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) f (l (R.extV i t y h)))) =
      fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h) := by
    funext h
    exact (thetaKO_smul (R.ωP i t) h g _ f).trans (mul_comm _ _)
  rw [e] at key
  exact key

end GlobalTheory.DownLift.GenFinite

end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.ToricValue

theorem exists_heckeL_toricSum : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : Formalism.L2.Host.HChar H.E), IsHostDatum H φ s κ 𝔣 χ → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ s ≠ 0 ∧ ∀ T : ℂ, IsToricSum φ s κ 𝔣 χ T ↔ T = Λ s := by
  intro R H I _ φ s κ 𝔣 χ hD
  have : IsCMField H.E := H.isCMField_hostE
  obtain ⟨hφ, -, hs, -, hb, hχ⟩ := hD
  have hn := GlobalTheory.ToricAssembly.not_isNormPow hb hχ
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 hn
  have h0 : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hχ.1 hn hΛ (by exact_mod_cast hs)
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 H.E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 H.E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricAssembly.toricSumFormula _ I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ (GlobalTheory.ToricDenomBridge.host_unramFin H) hs hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one] at t1
  have e : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  rw [e] at t1
  exact ⟨Λ, hΛ, h0, fun T => ⟨fun h => h.unique t1, fun h => h ▸ t1⟩⟩

end GlobalTheory.ToricValue
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

theorem _root_.GlobalTheory.T.unramifiedCocycle_descent_enlargement : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (I : Subgroup (Br.G D.nbr i w hw))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ Z1urD (latC C (locOC C M)) I → z ∈ Z1urD (Br.locLat D.nbr i w hw M) I := by
  first | exact @GlobalTheory.UseLoc.descUr_mem | exact GlobalTheory.UseLoc.descUr_mem | (intros; apply GlobalTheory.UseLoc.descUr_mem <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_uniformizerTorus_translate_unipotentQuotient : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (μ : Measure (GA E n)) [μ.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (𝓕 : Set (GA E n)),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕 μ → ∀ F : GA E n → ℝ≥0∞, Measurable F →
    (∀ u ∈ GlobalTheory.CellDec.NA E n, ∀ g, F (u * g) = F g) →
    ∫⁻ g in 𝓕, F ((GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g) ∂μ = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ∫⁻ g in 𝓕, F g ∂μ := by
  first | exact @GlobalTheory.CellDec.lintegral_tl_inv_mul | exact GlobalTheory.CellDec.lintegral_tl_inv_mul | (intros; apply GlobalTheory.CellDec.lintegral_tl_inv_mul <;> assumption)
end
