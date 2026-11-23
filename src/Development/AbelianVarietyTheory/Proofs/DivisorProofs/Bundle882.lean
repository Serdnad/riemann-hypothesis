module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle705
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle251
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle713
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
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
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

noncomputable section

namespace GlobalTheory.DiffSize

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_intCast (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    ‖((m : ℤ) : ℂ_[p])‖ = (p : ℝ) ^ (-(padicValInt p m : ℤ)) := by
  have e : ((m : ℤ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((m : ℚ) : ℚ_[p]) := by
    rw [Rat.cast_intCast, map_intCast]
  rw [e]
  refine (PadicComplex.norm_extends' (p := p) _).trans ?_
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm),
    padicValRat.of_int]
  push_cast; rfl

theorem pow_mem {K : Type} [Field K] [NumberField K] {I : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ I) (k : ℕ) :
    x ^ k ∈ I ^ k := by
  induction k with
  | zero => simpa using FractionalIdeal.one_mem_one (R := 𝓞 K) (K := K)
  | succ k ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih hx

theorem exists_int_mul_pow {F : Type} [Field F] [NumberField F] [IsGalois ℚ F] {y : F}
    (hy : y ∈ latM (1 : Frac F)) : ∃ c : 𝓞 F, (c : F) = (discr F : F) * y ^ Module.finrank ℚ F := by
  have hd : (discr F : F) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have h1 : latM (1 : Frac F) = ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    simp [latM]
  rw [h1] at hy
  have h2 := pow_mem hy (Module.finrank ℚ F)
  rw [inv_pow, ← FractionalIdeal.coeIdeal_pow, GlobalTheory.T.differentIdeal_pow_finrank_eq_span_discr' F, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv] at h2
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_spanSingleton _).1 h2
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def, map_intCast] at hc
  rw [← hc]; field_simp

theorem sz_invDiff : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [IsGalois ℚ F] (y : F) (i : Emb F), y ∈ latM (1 : Frac F) → Sz l lam ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F) ((i y : ℝ) : ℂ) := by
  intro l _ lam F _ _ _ _ y i hy
  obtain ⟨c, hc⟩ := exists_int_mul_pow hy
  let φ : F →+* ℂ := Complex.ofRealHom.comp i
  have hmem : ∀ x : F, φ x ∈ algebraicClosure ℚ ℂ := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic x).algHom φ.toRatAlgHom
  let ψ : F →+* algebraicClosure ℚ ℂ := φ.codRestrict (algebraicClosure ℚ ℂ) hmem
  let χ : F →+* ℂ_[l] := lam.comp ψ
  refine ⟨hmem y, ?_⟩
  change ‖χ y‖ ≤ _
  have hd0 : discr F ≠ 0 := discr_ne_zero F
  have hcint : ‖χ (c : F)‖ ≤ 1 :=
    norm_le_one_of_isIntegral (by convert map_isIntegral_int χ (RingOfIntegers.isIntegral_coe c); exact Subsingleton.elim _ _)
  have hdn : ‖χ (discr F : F)‖ = (l : ℝ) ^ (-(padicValInt l (discr F) : ℤ)) := by
    rw [map_intCast]; exact norm_intCast l _ hd0
  set n := Module.finrank ℚ F
  set v := padicValInt l (discr F)
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hkey : ‖χ y‖ ^ n * (l : ℝ) ^ (-(v : ℤ)) ≤ 1 := by
    rw [← hdn, ← norm_pow, ← norm_mul, ← map_pow, ← map_mul, mul_comm, ← hc]; exact hcint
  have hpow : ‖χ y‖ ^ n ≤ (l : ℝ) ^ (v : ℝ) := by
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(v : ℤ)) := zpow_pos hl0 _
    have := (le_div_iff₀ hpos).2 hkey
    rw [one_div, ← zpow_neg, neg_neg, zpow_natCast] at this
    rwa [Real.rpow_natCast]
  have hn : 0 < n := Module.finrank_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  calc ‖χ y‖ = (‖χ y‖ ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast (norm_nonneg _) hn.ne').symm
    _ ≤ ((l : ℝ) ^ (v : ℝ)) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = (l : ℝ) ^ ((v : ℝ) / n) := by rw [← Real.rpow_mul hl0.le, div_eq_mul_inv]

end GlobalTheory.DiffSize
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_torsion_matrix_of_conjugateTransport : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), ∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k' := by
  first | exact @GlobalTheory.WpFam.exists_torsion_matrix | exact GlobalTheory.WpFam.exists_torsion_matrix | (intros; apply GlobalTheory.WpFam.exists_torsion_matrix <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem rootSum_map_pullθ {F F' : Type} [Field F] [Field F'] [Algebra F F']
    (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F[X]) :
    rootSum θ k (P.map (algebraMap F F')) = rootSum (pullθ ι θ) k P := by
  unfold rootSum pullθ
  have e1 : (P.map (algebraMap F F')).map (algebraMap F' (AlgebraicClosure F')) =
      (P.map (algebraMap F (AlgebraicClosure F))).map (ι : AlgebraicClosure F →+* AlgebraicClosure F') := by
    rw [Polynomial.map_map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    congr 1
    ext x
    simp
  rw [e1, (IsAlgClosed.splits _).roots_map, Multiset.map_map]
  rfl

theorem charpoly_of_isConj {K : Type} [Field K] {n : ℕ} {a b : GL (Fin n) K} (h : IsConj a b) :
    Matrix.charpoly (a : Matrix (Fin n) (Fin n) K) = Matrix.charpoly (b : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem shLift_chG_rootSum : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) (k n : ℕ) (δ : GL (Fin n) F'), shLift s (chG (rootSum (pullθ ι θ) k) n) δ = chG (rootSum θ k) n (nrm s δ) := by
  intro F F' _ _ _ _ s hs ι θ k n δ
  have hex : ∃ γ, IsNorm s δ γ := GlobalTheory.T.every_element_is_norm F F' s hs n δ
  unfold shLift
  rw [dite_eq_left hex]
  generalize hex.choose = γ, hex.choose_spec = hγ
  unfold IsNorm at hγ
  unfold chG
  rw [← charpoly_of_isConj hγ]
  have hm : ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F') := by
    ext i j; rfl
  rw [hm, Matrix.charpoly_map, rootSum_map_pullθ]

end GlobalTheory.Shin
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.LatTorsVal

theorem exists_tors {L : PeriodPair} {c : ℂ} {τ : ℍ} (hτ : IsTauOf L c τ) (M : ℕ) [NeZero M] (P : ℂ)
    (hP : (M : ℂ) * P ∈ L.lattice) :
    ∃ x : Fin 2 → ZMod M, P - c * tors M τ x ∈ L.lattice ∧ (P ∉ L.lattice → x ≠ 0) := by
  have hom := GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf L c τ hτ
  have tm := GlobalTheory.WpFam.TorsMem.main M τ
  have hc : c ≠ 0 := hτ.1
  have hPz : P = c * (P / c) := by field_simp
  have hMz : (M : ℂ) * (P / c) ∈ (tauPair τ).lattice := by
    rw [← hom.1]
    have : c * ((M : ℂ) * (P / c)) = (M : ℂ) * P := by rw [hPz]; field_simp
    rw [this]; exact hP
  obtain ⟨x, hx⟩ := tm.2.2.2.2 (P / c) hMz
  refine ⟨x, ?_, ?_⟩
  · have := (hom.1 _).2 hx
    rwa [mul_sub, ← hPz] at this
  · rintro hPL rfl
    apply hPL
    have h0 := (tm.2.2.1 0).2 rfl
    have : P / c ∈ (tauPair τ).lattice := by
      have := add_mem hx h0
      simpa using this
    rw [hPz]; exact (hom.1 _).2 this

theorem wp_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (M : ℕ) (P : ℂ) (x : Fin 2 → ZMod M)
    (h : P - c * tors M τ x ∈ L.lattice) :
    L.weierstrassP P = L.weierstrassP (c * tors M τ x) ∧
      L.derivWeierstrassP P = L.derivWeierstrassP (c * tors M τ x) := by
  have e : P = c * tors M τ x + ((⟨P - c * tors M τ x, h⟩ : L.lattice) : ℂ) := by simp
  constructor
  · rw [e, L.weierstrassP_add_coe]
  · rw [e, L.derivWeierstrassP_add_coe]

theorem main : ∀ (L : PeriodPair) (β Ω : ℂ) (M : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → 0 < M → (∀ P, (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (12 * (M : ℂ) ^ 2 * L.weierstrassP P / Ω ^ 2) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * L.derivWeierstrassP P / Ω ^ 3)) ∧ ∀ P Q, P ∉ L.lattice → Q ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → (M : ℂ) * Q ∈ L.lattice → IsIntegral ℤ ((M : ℂ) ^ 2 * (L.weierstrassP P - L.weierstrassP Q) / Ω ^ 2) := by
  intro L β Ω M hβ hβi hΩ hM
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hj := GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication L c τ β hτ hβ hβi
  have hω := (GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD L c τ hτ).2 Ω hΩ
  have st := (GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau L c Ω τ hτ).2 M
  refine ⟨fun P hP => ?_, fun P Q hP hQ hMP hMQ => ?_⟩
  · obtain ⟨x, hx, -⟩ := exists_tors hτ M P hP
    obtain ⟨e1, e2⟩ := wp_eq M P x hx
    have hv := GlobalTheory.T.isIntegral_weierstrassP_torsion_integral_j M τ _ hj hω x
    rw [e1, e2, mul_div_assoc, mul_div_assoc, ← (st x).1, ← (st x).2, ← mul_div_assoc, ← mul_div_assoc]
    exact hv
  · obtain ⟨x, hx, hx0⟩ := exists_tors hτ M P hMP
    obtain ⟨y, hy, hy0⟩ := exists_tors hτ M Q hMQ
    have hv := GlobalTheory.T.isIntegral_weierstrassP_torsion_difference M τ _ hj hω x y (hx0 hP) (hy0 hQ)
    rw [(wp_eq M P x hx).1, (wp_eq M Q y hy).1, mul_div_assoc, sub_div, ← (st x).1, ← (st y).1, ← sub_div,
      ← mul_div_assoc]
    exact hv

end GlobalTheory.WpFam.LatTorsVal
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.transport_modularFamily_GL2ZMod_weierstrass : ∀ (g : ℂ ≃+* ℂ) (N N' w : ℕ) [NeZero N] (a : (ZMod N)ˣ) (A : GL (Fin 2) (ZMod N)) (F F' : GL (Fin 2) (ZMod N) → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N' → N ∣ N' → ZetaAct g N a → IsFam (gact N 1) w F → (∀ α, QConj g N' (F α) (F' (α * dg a))) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → (∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3) → ∀ α, g (F α τ₀ / ω₀ ^ w) = F' (α * A) τ₁ / ω₁ ^ w := by
  first | exact @GlobalTheory.WpFamGL.transport_GL | exact GlobalTheory.WpFamGL.transport_GL | (intros; apply GlobalTheory.WpFamGL.transport_GL <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.QuotLine

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem det_fac {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hM : ∀ i : Fin r, M i.succ 0 = 0) :
    M.det = M 0 0 * (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [hM]

theorem val_corner {r : ℕ} (v : Place k K) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hM : ∀ i : Fin r, M i.succ 0 = 0) (h1 : Unimod v M)
    (h2 : Unimod v (M.submatrix Fin.succ Fin.succ)) : v.1 (M 0 0) = 1 := by
  have h := h1.2
  rw [det_fac M hM, map_mul, h2.2, mul_one] at h
  exact h

theorem nrm_cons {n : ℕ} (v : Place k K) (x : K) (y : Fin n → K) :
    nrm v (Fin.cons x y : Fin (n + 1) → K) = max (v.1 x) (nrm v y) := by
  simp only [nrm, Fin.univ_succ, Finset.sup_cons, Finset.sup_map, Fin.cons_zero]
  rfl

theorem nrm_two (v : Place k K) (x y : K) : nrm v ![x, y] = max (v.1 x) (v.1 y) := by
  have h1 := nrm_cons v x ![y]
  have h2 := nrm_cons v y ![]
  have h3 : nrm v (![] : Fin 0 → K) = 0 := by simp [nrm]
  rw [h3, max_eq_left (zero_le' )] at h2
  exact h1.trans (by rw [← h2]; rfl)

theorem quot_line_le : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → (∀ (v : Place k F) (i : Fin r), g v i.succ 0 = 0) → admitted (fun v => (g v).submatrix Fin.succ Fin.succ) → ∀ b : ℝ, LinesLE g b → LinesLE (fun v => (g v).submatrix Fin.succ Fin.succ) (2 * b - (∑ᶠ v, ord v (g v 0 0) : ℤ)) := by
  intro k F _ _ _ _ _ hF r g hg hg0 hh b hb E _ _ _ _ _ ρ hρ m hm
  have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).2 E
  obtain ⟨hGa, -, -, hGL⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ (r + 1) g hg
  obtain ⟨hQa, -, -, -⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ r _ hh
  have hGb := hGL b hb

  have hcF : ∀ v, Unimod v (g v) → Unimod v ((g v).submatrix Fin.succ Fin.succ) → v.1 (g v 0 0) = 1 :=
    fun v h1 h2 => val_corner v (g v) (hg0 v) h1 h2
  have ha0 : ∀ v, g v 0 0 ≠ 0 := by
    intro v h0; apply hg.1 v; rw [det_fac (g v) (hg0 v), h0, zero_mul]
  obtain ⟨a1, ha1def⟩ : ∃ a1 : Place k F → Matrix (Fin 1) (Fin 1) F, a1 = fun v => !![g v 0 0] := ⟨_, rfl⟩
  have ha1 : admitted a1 := by
    refine ⟨fun v => by simp [ha1def, ha0 v], (hg.2.union hh.2).subset ?_⟩
    intro v hv
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    have h1 := hcF v hno.1 hno.2
    apply hv
    refine ⟨fun i j => ?_, ?_⟩
    · fin_cases i; fin_cases j; simp [ha1def, h1]
    · simp [ha1def, h1]
  obtain ⟨-, hdeg1, -, -⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ 1 a1 ha1
  generalize hGdef : pullAd ρ g = G at hGa hGb
  generalize hQdef : pullAd ρ (fun v => (g v).submatrix Fin.succ Fin.succ) = Q at hQa ⊢
  have hQG : ∀ p, Q p = (G p).submatrix Fin.succ Fin.succ := by
    intro p; rw [← hQdef, ← hGdef]; rfl
  have hG0 : ∀ p (i : Fin r), G p i.succ 0 = 0 := by
    intro p i; rw [← hGdef]; simp [pullAd, hg0]
  have hS : ∑ᶠ p, ord p (G p 0 0) = Module.finrank F E * ∑ᶠ v, ord v (g v 0 0) := by
    have e1 : deg (pullAd ρ a1) = ∑ᶠ p, ord p (G p 0 0) := by
      unfold deg; apply finsum_congr; intro p; rw [← hGdef]; simp [pullAd, ha1def]
    have e2 : deg a1 = ∑ᶠ v, ord v (g v 0 0) := by
      unfold deg; apply finsum_congr; intro v; simp [ha1def]
    rw [← e1, hdeg1, e2]
  obtain ⟨-, hQm⟩ := GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k E hE r Q hQa
  obtain ⟨hfinQm, hnz⟩ := hQm m hm
  have hord := fun p : Place k E => GlobalTheory.T.functionFieldPlaceOrder_calculus k E p
  choose idx hidx using fun p : Place k E => (hord p).2.2.2.2.2.2.1 r (Q p *ᵥ m) (hnz p)
  obtain ⟨t, ht⟩ : ∃ t : Place k E → Matrix (Fin 2) (Fin 2) E, t = fun p =>
      !![G p 0 0, ∑ j : Fin r, G p 0 j.succ * m j; 0, (Q p *ᵥ m) (idx p)] := ⟨_, rfl⟩
  have hdett : ∀ p, (t p).det = G p 0 0 * (Q p *ᵥ m) (idx p) := by
    intro p; rw [ht, Matrix.det_fin_two_of]; ring
  have hG00 : ∀ p, G p 0 0 ≠ 0 := by
    intro p h0; apply hGa.1 p; rw [det_fac (G p) (hG0 p), h0, zero_mul]
  have hcE : ∀ p, Unimod p (G p) → Unimod p (Q p) → p.1 (G p 0 0) = 1 :=
    fun p h1 h2 => val_corner p (G p) (hG0 p) h1 (by rw [← hQG]; exact h2)
  have hmfin : ∀ j, {p : Place k E | ¬ p.1 (m j) ≤ 1}.Finite := by
    intro j
    by_cases hj : m j = 0
    · simp [hj]
    · exact ((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k E hE (m j) hj).1).subset fun p hp h1 => hp (le_of_eq h1)
  have hta : admitted t := by
    refine ⟨fun p => by rw [hdett]; exact mul_ne_zero (hG00 p) (hidx p).1, ?_⟩
    refine ((hGa.2.union hQa.2).union (hfinQm.union (Set.finite_iUnion hmfin))).subset ?_
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hno
    obtain ⟨⟨hGu, hQu⟩, hn1, hmj⟩ := hno
    apply hp
    have hc1 : p.1 (G p 0 0) = 1 := hcE p hGu hQu
    have hm1 : p.1 ((Q p *ᵥ m) (idx p)) = 1 := by rw [← (hidx p).2.1]; exact hn1
    have hcs : p.1 (∑ j : Fin r, G p 0 j.succ * m j) ≤ 1 :=
      Valuation.map_sum_le _ fun j _ => by rw [map_mul]; exact mul_le_one' (hGu.1 0 j.succ) (hmj j)
    refine ⟨fun i j => ?_, ?_⟩
    · rw [ht]; fin_cases i <;> fin_cases j <;> simp [hc1, hm1, hcs]
    · rw [hdett, map_mul, hc1, hm1, one_mul]
  have htL : LinesLE t (b * Module.finrank F E) := by
    intro E' _ _ _ _ _ ρ' hρ' w hw
    have hres := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k E E').2 ρ' hρ'
    obtain ⟨w', hw'def⟩ : ∃ w' : Fin (r + 1) → E', w' = Fin.cons (w 0) (fun j => w 1 * algebraMap E E' (m j)) :=
      ⟨_, rfl⟩
    have hw' : w' ≠ 0 := by
      intro h0
      apply hw
      have h00 : w 0 = 0 := by simpa [hw'def] using congr_fun h0 0
      obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
        by_contra hc; push_neg at hc; exact hm (funext hc)
      have h1 : w 1 * algebraMap E E' (m j) = 0 := by simpa [hw'def] using congr_fun h0 j.succ
      have h11 : w 1 = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact h
        · exact absurd ((map_eq_zero_iff _ (algebraMap E E').injective).1 h) hj
      ext i; fin_cases i <;> simp [h00, h11]
    have hloc : ∀ p', nrm p' (pullAd ρ' t p' *ᵥ w) = nrm p' (pullAd ρ' G p' *ᵥ w') := by
      intro p'
      obtain ⟨e, -, he, -⟩ := hres p'
      have v1 : pullAd ρ' t p' *ᵥ w = ![algebraMap E E' (G (ρ' p') 0 0) * w 0 +
          algebraMap E E' (∑ j : Fin r, G (ρ' p') 0 j.succ * m j) * w 1,
          algebraMap E E' ((Q (ρ' p') *ᵥ m) (idx (ρ' p'))) * w 1] := by
        ext i; fin_cases i <;> simp [pullAd, ht, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have v2 : pullAd ρ' G p' *ᵥ w' = Fin.cons (algebraMap E E' (G (ρ' p') 0 0) * w 0 +
          algebraMap E E' (∑ j : Fin r, G (ρ' p') 0 j.succ * m j) * w 1)
          (fun i => w 1 * algebraMap E E' ((Q (ρ' p') *ᵥ m) i)) := by
        ext i; refine Fin.cases ?_ (fun i => ?_) i

        · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hw'def, Fin.cons_zero, Fin.cons_succ,
            pullAd, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Fin.cases_zero]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring

        · simp [pullAd, hw'def, hQG, hG0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, map_sum,
          Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      rw [v1, v2, nrm_two, nrm_cons]
      congr 1
      have hs : (fun i => w 1 * algebraMap E E' ((Q (ρ' p') *ᵥ m) i)) =
          w 1 • (fun i => algebraMap E E' ((Q (ρ' p') *ᵥ m) i)) := by
        ext; simp [smul_eq_mul]
      rw [hs, (GlobalTheory.T.functionFieldPlaceOrder_calculus k E' p').2.2.2.2.2.2.2.1, map_mul, mul_comm]
      congr 1
      apply le_antisymm
      · exact Finset.le_sup (f := fun i => p'.1 (algebraMap E E' ((Q (ρ' p') *ᵥ m) i)))
          (Finset.mem_univ (idx (ρ' p')))
      · apply Finset.sup_le; intro j _
        rw [he, he]; exact pow_le_pow_left' ((hidx (ρ' p')).2.2.2 j) e
    have heq : degLine (pullAd ρ' t) w = degLine (pullAd ρ' G) w' := by
      simp only [degLine, ordVec, hloc]
    rw [heq]; exact hGb E' ρ' hρ' w' hw'
  have hdeg := GlobalTheory.T.adelicMatrixDegree_le_two_mul_of_upperTriangular k E hE t hta (fun p => by simp [ht]) _ htL
  have hs1 : (Function.support fun p : Place k E => ord p (G p 0 0)).Finite := by
    refine (hGa.2.union hQa.2).subset ?_
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    apply hp
    simp [ord, hcE p hno.1 hno.2]
  have hs2 : (Function.support fun p : Place k E => ordVec p (Q p *ᵥ m)).Finite := by
    refine hfinQm.subset ?_
    intro p hp hn
    apply hp
    simp [ordVec, hn]
  have hsplit : deg t = (∑ᶠ p, ord p (G p 0 0)) + degLine Q m := by
    unfold deg degLine
    rw [← finsum_add_distrib hs1 hs2]
    apply finsum_congr; intro p
    rw [hdett, (hord p).1 _ _ (hG00 p) (hidx p).1, (hidx p).2.2.1]
  rw [hS] at hsplit
  have hc : (degLine Q m : ℝ) = (deg t : ℝ) - (Module.finrank F E : ℝ) * ((∑ᶠ v, ord v (g v 0 0) : ℤ) : ℝ) := by
    rw [hsplit]; push_cast; ring
  rw [hc]
  nlinarith [hdeg]

end GlobalTheory.Nef.QuotLine
end
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_peak_section_small_dbar_energy : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La) (i : ι) (p : V n) (ρ c : ℝ) (q f : V n → ℂ), 0 < ρ → 0 < c → closedBall p ρ ⊆ (A.chart i).target → Differentiable ℂ q → Differentiable ℂ f → (∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ A.ph H i ((A.chart i).symm v) - 2 * (q v).re) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ v ∈ ball p (ρ / 2), F0 i ((A.chart i).symm v) = f v * Complex.exp (k * q v)) ∧ (∀ j y, y ∉ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ → F0 j y = 0) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
  first | exact @GlobalTheory.OTY.peak_section | exact GlobalTheory.OTY.peak_section | (intros; apply GlobalTheory.OTY.peak_section <;> assumption)
end
