module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuadraticCharNegOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle254
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle181
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle260
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.Statement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise
open Formalism.FrobeniusOrbits GlobalTheory.NormSign

namespace GlobalTheory.NormSignInert

theorem descent_rat {d q : ℕ} [Fact d.Prime] (hq : q.Prime) (hne : q ≠ d) {u : ℤ}
    (hu : quadraticChar (ZMod d) (-(u : ZMod d)) = -1) (C X Y : ℚ)
    (h : C ^ 2 * u + X ^ 2 = q * d * Y ^ 2) : C = 0 := by
  have key := descent hq hne (quadraticChar_neg_one_iff_not_isSquare.1 hu) _ (C.num * X.den * Y.den)
    (X.num * C.den * Y.den) (Y.num * C.den * X.den) rfl (by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [← Rat.mul_den_eq_num C, ← Rat.mul_den_eq_num X, ← Rat.mul_den_eq_num Y]
      linear_combination ((C.den : ℚ) ^ 2 * X.den ^ 2 * Y.den ^ 2) * h)
  simpa [X.den_nz, Y.den_nz] using key

theorem char_eq {d q : ℕ} [Fact d.Prime] [Fact q.Prime] (hd : d % 4 = 3) (h2 : q ≠ 2) (hne : q ≠ d) :
    quadraticChar (ZMod d) q = quadraticChar (ZMod q) (-(d : ZMod q)) := by
  have hl2 : ringChar (ZMod d) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have h := quadraticChar_card_card hl2 (F' := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
    (by rwa [ZMod.ringChar_zmod_n, ZMod.ringChar_zmod_n])
  rw [quadraticChar_neg_one' hd, ZMod.card, ZMod.card] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem no_rat_inert {q d : ℕ} [Fact d.Prime] (h : HostHyp q d) {m : ℕ} (hm : EvenSq d m) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : Odd f) (hpd : p ≠ d → ¬ IsSquare (-(d : ZMod p))) (A W : ℚ) :
    W ^ 2 ≠ q * d * (A ^ 2 - 4 * (p ^ f * m)) := by
  obtain ⟨hq, hd, hq8, hd16, hj⟩ := h
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, u, rfl, hu⟩ := hm
  have h1 := hq.pos
  have h2 := hd.pos
  intro hW
  push_cast at hW
  by_cases hpd' : p = d
  · subst hpd'
    obtain ⟨j, rfl⟩ := hf
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym] at hj
    push_cast at hj
    rw [← char_eq (d := p) (q := q) (by omega) (by omega) (by omega)] at hj
    have key := descent_rat (d := p) hq (by omega) (u := q * u) (by
      rw [← neg_one_mul, map_mul, quadraticChar_neg_one' (by omega)]
      push_cast
      rw [map_mul, hj, hu]; norm_num) (2 * p ^ (j + k + 1)) W A (by
      push_cast
      linear_combination hW)
    have : (0 : ℚ) < 2 * p ^ (j + k + 1) := by positivity
    exact this.ne' key
  · have h3 := quadraticChar_neg_one_iff_not_isSquare.2 (hpd hpd')
    rw [← char_eq (d := d) (q := p) (by omega) hp2 hpd'] at h3
    have key := descent_rat (d := d) hq (by omega) (u := -(p ^ f * u)) (by
      push_cast
      rw [neg_neg, map_mul, map_pow, h3, hu, hf.neg_one_pow]; norm_num) (2 * q * d * d ^ k) (q * d * A) W (by
      push_cast
      linear_combination (-(q * d : ℚ)) * hW)
    have : (0 : ℚ) < 2 * q * d * d ^ k := by positivity
    exact this.ne' key

theorem exists_norm {R : Ranks} (H : Host R) (t : H.E) (ht : H.conj t = t) :
    ∃ n A W : ℚ, (n : H.E) = part H t (1, 1) * part H t (-1, 1) ∧ W ^ 2 = H.q * H.d * (A ^ 2 - 4 * n) := by
  have ha : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  set s := part H (t : H.E) (1, 1) with hs
  set s' := part H (t : H.E) (-1, 1) with hs'
  have e1 : part H (t : H.E) (-1, -1) = s := by rw [part_neg H ht]; simp [hs]
  have e2 : part H (t : H.E) (1, -1) = s' := by rw [part_neg H ht]; simp [hs']
  have key : ∀ g : R.GG, (g.1.1 * g.1.2 = 1 ∧ H.sigmaOf g s = s ∧ H.sigmaOf g s' = s') ∨
      (g.1.1 * g.1.2 = -1 ∧ H.sigmaOf g s = s' ∧ H.sigmaOf g s' = s) := by
    rintro ⟨⟨u, v⟩, h⟩
    rw [hs, hs', sigmaOf_part, sigmaOf_part]
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [e1, e2, ← hs, ← hs']
  obtain ⟨n, hn⟩ := exists_rat H (x := s * s') fun g => by
    rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_mul, h1, h2]
    ring
  obtain ⟨A, hA⟩ := exists_rat H (x := s + s') fun g => by
    rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_add (f := _), h1, h2]
    ring
  obtain ⟨W, hW⟩ := exists_rat H (x := (s - s') * (H.sqq * H.sqd)) fun g => by
    rw [map_mul, map_mul, map_sub, sigmaOf_aE, sigmaOf_bE, mul_mul_mul_comm, ← Int.cast_mul, ← Units.val_mul]
    rcases key g with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> push_cast <;> ring
  refine ⟨n, A, W, hn, ?_⟩
  apply Rat.cast_injective (α := H.E)
  push_cast
  rw [hW, hA, hn, mul_pow, mul_pow, ha, hb]
  ring

theorem norm_neg : ∀ (D : D7) (t : 𝓞 D.host.E) (P B : Ideal (𝓞 D.host.E)), t ≠ 0 →
    D.host.conj (t : D.host.E) = t → P.IsMaximal → D.host.conj • P = P →
    Ideal.span {t} = P * B * (D.host.conj • B) → (∏ τ, embT D τ (t : D.host.E)).re < 0 := by
  intro D t P B ht0 ht hP hc hB
  obtain ⟨-, p, f, hp, -, hp2, -, hf, hN, hpd⟩ := (GlobalTheory.T.absNorm_cmPrime_inertPrime_sign D P hP).2.1 hc
  rw [prod_embT]
  generalize D.host = H at *
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have ha : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    exact ht0 (by simpa using hB)
  have hm := evenSq_absNorm H.hyp ha hb B hB0
  have hm0 : 0 < Ideal.absNorm B := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨n, A, W, hn, hWn⟩ := exists_norm H (t : H.E) ht
  have hn2 : n ^ 2 = ((p : ℚ) ^ f * (Ideal.absNorm B : ℚ)) ^ 2 := by
    have h1 : Algebra.norm ℚ (t : H.E) = n ^ 2 := by
      apply Rat.cast_injective (α := H.E)
      rw [norm_eq H ht]
      push_cast
      rw [hn]
    have h2 := congrArg Ideal.absNorm hB
    rw [map_mul, map_mul, absNorm_smul, Ideal.absNorm_span_singleton, hN] at h2
    have h3 := congrArg (fun k : ℕ => ((k : ℤ) : ℚ)) h2
    simp only [Int.natCast_natAbs] at h3
    push_cast at h3
    rw [Algebra.coe_norm_int, h1, abs_of_nonneg (sq_nonneg _)] at h3
    rw [h3]; ring
  rw [← hn, map_ratCast, Complex.ratCast_re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hn2 with h | h
  · exact absurd (by rw [hWn, h]) (no_rat_inert H.hyp hm hp hp2 hf hpd A W)
  · have := hp.pos
    have h0 : (0 : ℚ) < (p : ℚ) ^ f * (Ideal.absNorm B : ℚ) := by positivity
    have h1 : n < 0 := by rw [h]; exact neg_neg_of_pos h0
    exact_mod_cast h1

end GlobalTheory.NormSignInert
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.ZmChar

theorem ch_mul {M : ℕ} (χ : DirichletCharacter ℂ M) (x y : ℤ) : ch χ (x * y) = ch χ x * ch χ y := by
  simp [ch]

theorem ch_add_dvd {M : ℕ} (χ : DirichletCharacter ℂ M) (K : ℕ) (h : M ∣ K) (x : ℤ) : ch χ (x + K) = ch χ x := by
  obtain ⟨t, rfl⟩ := h
  simp [ch, ZMod.natCast_self]

theorem ch_zero {M : ℕ} [Fact (1 < M)] (χ : DirichletCharacter ℂ M) : ch χ 0 = 0 := by
  simp only [ch, Int.cast_zero]
  exact MulChar.map_nonunit χ not_isUnit_zero

theorem inv_apply_neg_one {M : ℕ} (χ : DirichletCharacter ℂ M) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply]
  have : Ring.inverse (-1 : ZMod M) = -1 := by simpa using Ring.inverse_unit (-1 : (ZMod M)ˣ)
  rw [this]

theorem isUnit_of_coprime {M : ℕ} (d : ℤ) (h : IsCoprime d (M : ℤ)) : IsUnit (d : ZMod M) := by
  obtain ⟨a, b, hab⟩ := h
  have := congrArg (Int.cast : ℤ → ZMod M) hab
  push_cast at this
  simp [ZMod.natCast_self] at this
  exact isUnit_iff_exists_inv.2 ⟨a, by rw [mul_comm]; exact this⟩

theorem mul_inv_unit {M : ℕ} (χ : DirichletCharacter ℂ M) (d : ℤ) (h : IsUnit (d : ZMod M)) : ch χ d * ch χ⁻¹ d = 1 := by
  show χ (d : ZMod M) * χ⁻¹ (d : ZMod M) = 1
  rw [← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.one_apply h

end GlobalTheory.EisM.ZmChar

namespace GlobalTheory.EisM.ZmChar

theorem cop_dvd {d : ℤ} {A B : ℕ} (h : IsCoprime d (B : ℤ)) (hAB : A ∣ B) : IsCoprime d (A : ℤ) :=
  h.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hAB)

end GlobalTheory.EisM.ZmChar


open GlobalTheory.EisM.ZmChar in
theorem GlobalTheory.zm_char_mf : ∀ (k j N l m : ℕ) (ε : DirichletCharacter ℂ N) (u : ℤ → ℂ) (θ ν : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ (l ^ m)), j + 2 ≤ k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → (∀ x, u (x + N) = u x) → (∀ d x : ℤ, IsCoprime d N → u (x * d) = ch θ⁻¹ d * u x) → ε = θ⁻¹ * ν → ψ (-1) * θ (-1) = (-1) ^ (k - 1 - j) → ψ (-1) * ν (-1) = (-1) ^ (j + 1) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l u (ch ν) (fun x y => ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ j)) := by
  intro k j N l m ε u θ ν ψ hjk hN hl hm hlN hu hmul hε hpar1 hpar2
  have hl1 : 1 < l ^ m := Nat.one_lt_pow (by omega) hl.one_lt
  haveI : Fact (1 < l ^ m) := ⟨hl1⟩
  have hlm : 0 < l ^ m := by omega
  have hup : ∀ K : ℕ, N ∣ K → ∀ x, u (x + K) = u x := by
    intro K hK x
    obtain ⟨t, rfl⟩ := hK
    have e : ((N * t : ℕ) : ℤ) = (t : ℤ) * N := by push_cast; ring
    rw [e]
    exact (Function.Periodic.nat_mul (show Function.Periodic u (N : ℤ) from hu) t) x
  obtain ⟨c, hE1⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (k - 1 - j) (N * l ^ m) 1 (fun x => u x * ch ψ x) (fun _ => 1)
    (fun d => ch θ⁻¹ d * ch ψ d) (fun _ => 1) (by omega) (by positivity) one_pos (by simp [ch_zero])
    (fun x => by rw [hup _ (dvd_mul_right _ _), ch_add_dvd _ _ (dvd_mul_left _ _)]) (fun _ => rfl)
    (fun d hd => by
      have hdN : IsCoprime d (N : ℤ) := cop_dvd hd (by simp)
      refine ⟨fun x => ?_, fun x => by ring⟩
      rw [hmul d x hdN, ch_mul]
      ring)
    (by simp only [ch, Int.cast_neg, Int.cast_one, mul_one]; rw [inv_apply_neg_one, mul_comm, hpar1])
  obtain ⟨c', hE2⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (j + 1) (l ^ m) N (ch ψ⁻¹) (ch ν) (ch ψ⁻¹) (ch ν) (by omega) hlm hN
    (ch_zero _) (ch_add_dvd _ _ dvd_rfl) (ch_add_dvd _ _ dvd_rfl)
    (fun d _ => ⟨fun x => by rw [ch_mul, mul_comm], fun x => by rw [ch_mul, mul_comm]⟩)
    (by simp only [ch, Int.cast_neg, Int.cast_one]; rw [inv_apply_neg_one, hpar2])
  have hD1 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion (k - 1 - j) (N * l ^ m * 1) l _ _ (by omega) hl
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self l (by omega)) _) _)
    (fun d => by rw [ch_add_dvd _ _ (dvd_mul_of_dvd_left (dvd_mul_right _ _) _),
      ch_add_dvd _ _ (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)]) hE1).2
  have hD2 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion (j + 1) (l ^ m * N) l _ _ (by omega) hl
    (dvd_mul_of_dvd_left (dvd_pow_self l (by omega)) _)
    (fun d => by rw [ch_add_dvd _ _ (dvd_mul_right _ _), ch_add_dvd _ _ (dvd_mul_left _ _)]) hE2).2
  have hD1' := (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.2.1 (N * l ^ (m + 1)) _ ⟨1, by ring⟩ hD1
  have hD2' := (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.2.1 (N * l ^ (m + 1)) _ ⟨1, by ring⟩ hD2
  have P := GlobalTheory.EisM.mul_main.2 _ _ _ _ _ _ _ hD1' hD2'
  rw [GlobalTheory.T.eisensteinProductSeries_eq_depleted_eisenstein_product k l j u (ch ν) (ch ψ) (ch ψ⁻¹) c c' hjk]
  have hk : k - 1 - j + (j + 1) = k := by omega
  rw [hk] at P
  refine (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.1 (ch ε) _ (fun d hd => ?_) P
  have hU := mul_inv_unit ψ d (isUnit_of_coprime d (cop_dvd hd (dvd_mul_of_dvd_right (pow_dvd_pow l (by omega)) _)))
  subst hε
  simp only [ch, MulChar.mul_apply] at hU ⊢
  linear_combination (θ⁻¹ (d : ZMod N) * ν (d : ZMod N)) * hU
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.transportedLattice_localization_free_le_coefficientSpace : NabDelLoc ∧ NabDelFree ∧ NabLeVV := by
  first | exact @GlobalTheory.TransLoc.nabDelLoc_free_leVV | exact GlobalTheory.TransLoc.nabDelLoc_free_leVV | (intros; apply GlobalTheory.TransLoc.nabDelLoc_free_leVV <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogShift

open MvPowerSeries

theorem expMv_phAt_sub_nsmul : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (h : PowerSeries ℂ_[p]) (n : ℕ), PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 → PowerSeries.constantCoeff h = 0 → MvPowerSeries.constantCoeff ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = 0 ∧ expMv ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = ((PowerSeries.subst h (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ n : PowerSeries ℂ_[p]) := by
  intro p _ g h n hE hh
  have exp_add {f g : MvPowerSeries Unit ℂ_[p]} (hf : constantCoeff f = 0)
      (hg : constantCoeff g = 0) : expMv (f + g) = expMv f * expMv g := by
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst hg,
      GlobalTheory.ExpLogMv.expMv_eq_subst (by simp [hf, hg])]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg
  have exp_zero : expMv (0 : MvPowerSeries Unit ℂ_[p]) = 1 := by
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst (by simp)]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero
  have cc_ph : PowerSeries.constantCoeff g.ph = 0 := by
    have ht := (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).1
    show constantCoeff (-GL3Theta.logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) = 0
    rw [map_neg, ht, neg_zero]
  have cc_phAt {y : MvPowerSeries Unit ℂ_[p]} (hy : constantCoeff y = 0) :
      constantCoeff (g.phAt y) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hy _ cc_ph
  have exp_sum {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries Unit ℂ_[p]}
      (hf : ∀ i, constantCoeff (f i) = 0) : expMv (∑ i ∈ s, f i) = ∏ i ∈ s, expMv (f i) := by
    induction s using Finset.induction_on with
    | empty => simpa using exp_zero
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, exp_add (hf i) (by simp [map_sum, hf]), ih]
  have subst_exp {a : Unit → MvPowerSeries Unit ℂ_[p]} (ha : ∀ i, constantCoeff (a i) = 0)
      {f : MvPowerSeries Unit ℂ_[p]} (hf : constantCoeff f = 0) : subst a (expMv f) = expMv (subst a f) := by
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst (constantCoeff_subst_eq_zero hs ha hf)]
    rw [PowerSeries.subst_def, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const hs]
    rfl
  have inv_ePhi1 {y : MvPowerSeries Unit ℂ_[p]} (hy : constantCoeff y = 0) :
      (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = expMv (g.phAt y) := by
    have hs : HasSubst (fun _ : Unit => y) := hasSubst_of_constantCoeff_zero fun _ => hy
    have ht := congrArg (subst (fun _ : Unit => y)) (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2
    rw [subst_mul hs, subst_exp (f := -GL3Theta.logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) (fun _ => hy) cc_ph, ← coe_substAlgHom hs (R := ℂ_[p]), map_one,
      coe_substAlgHom] at ht
    have h1 : constantCoeff (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq)) ≠ 0 := by
      rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hy, hE]; exact one_ne_zero
    rw [MvPowerSeries.inv_eq_iff_mul_eq_one h1]
    exact ht
  have hh' : MvPowerSeries.constantCoeff (h : MvPowerSeries Unit ℂ_[p]) = 0 := hh
  have hX : MvPowerSeries.constantCoeff (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by
    simp [GL3Theta.Xv]
  have ha : MvPowerSeries.constantCoeff (g.phAt (h : MvPowerSeries Unit ℂ_[p])) = 0 :=
    cc_phAt hh'
  have hb : MvPowerSeries.constantCoeff (g.phAt (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p])) = 0 :=
    cc_phAt hX
  refine ⟨by simp [map_sub, map_mul, ha, hb], ?_⟩
  set b : MvPowerSeries Unit ℂ_[p] := g.phAt (GL3Theta.Xv ()) with hbdef
  set F : PowerSeries ℂ_[p] := ePhi1 g.lam g.abelian₂ g.C g.wq with hF

  have hbph : b = (g.ph : MvPowerSeries Unit ℂ_[p]) := by
    show PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.ph = g.ph
    rw [← PowerSeries.map_algebraMap_eq_subst_X]; simp

  have hbF : expMv b * (F : MvPowerSeries Unit ℂ_[p]) = 1 := by
    rw [hbph]; exact (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2
  have hnb : MvPowerSeries.constantCoeff (-b) = 0 := by simp [hb]

  have hneg : expMv (-b) = (F : MvPowerSeries Unit ℂ_[p]) := by
    have h0 : expMv b * expMv (-b) = 1 := by
      rw [← exp_add hb hnb, add_neg_cancel, exp_zero]
    calc expMv (-b) = expMv (-b) * (expMv b * (F : MvPowerSeries Unit ℂ_[p])) := by rw [hbF, mul_one]
      _ = (expMv b * expMv (-b)) * F := by ring
      _ = F := by rw [h0, one_mul]
  have hsum : (g.phAt (h : MvPowerSeries Unit ℂ_[p])) - MvPowerSeries.C (n : ℂ_[p]) * b =
      g.phAt (h : MvPowerSeries Unit ℂ_[p]) + ∑ _i ∈ Finset.range n, -b := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_eq_add_neg, ← neg_mul]
    congr 1
    rw [neg_mul, mul_neg]
    congr 1
  have hsum0 : MvPowerSeries.constantCoeff (∑ _i ∈ Finset.range n, -b) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simp [hb]
  rw [hsum, exp_add ha hsum0,
    exp_sum _ (fun _ => hnb), Finset.prod_const, Finset.card_range, hneg,
    ← inv_ePhi1 hh']

end GlobalTheory.ExpLogShift
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_traceOne_evenNorm_unit_at_two : ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∃ (a : 𝓞 D.host.K) (β : ℂ) (k : ℕ), D.host.φ₀ (((a : D.host.K) : D.host.E)) = β ∧ β ∈ Qbar ∧ ‖lamC lam β‖ = 1 ∧ β + starRingEnd ℂ β = 1 ∧ β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) ∧ ∀ (Λ : AddSubgroup ℂ) (t₀ : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D Λ t₀ → β * t₀ ∉ Λ ∧ (1 - β) * t₀ ∉ Λ := by
  first | exact @GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two | exact GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two | (intros; apply GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.det_column_operations_model_parameter : ∀ (p : ℕ) [Fact p.Prime] (E wq : PowerSeries ℂ_[p]) (ε r a₁ a₃ : ℂ_[p]) (s d₁ d₂ d₃ : MvPowerSeries (Fin 3) ℂ_[p]), ε ≠ 0 → PowerSeries.constantCoeff wq = 1 → MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff d₁ = 0 → MvPowerSeries.constantCoeff d₂ = 0 → MvPowerSeries.constantCoeff d₃ = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (![PowerSeries.C (ε ^ 3) * PowerSeries.X ^ 3 * E ^ 3, PowerSeries.C ε * E ^ 3 * (PowerSeries.X * wq⁻¹ + PowerSeries.C (ε ^ 2 * r) * PowerSeries.X ^ 3), E ^ 3 * wq⁻¹ * (PowerSeries.C a₁ * PowerSeries.X + PowerSeries.C a₃ * PowerSeries.X ^ 3 * wq - 2)] j) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst s (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₁ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₂ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₃ (PowerSeries.C ε * PowerSeries.X * E) → ((GL3Theta.Xv 0) ^ 3 * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 2 - GL3Theta.Xv 1) + (GL3Theta.Xv 1) ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 0 - GL3Theta.Xv 2) + (GL3Theta.Xv 2) ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 1 - GL3Theta.Xv 0)) * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 = PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (s * PowerSeries.subst s E) * (d₁ * PowerSeries.subst d₁ E) * (d₂ * PowerSeries.subst d₂ E) * (d₃ * PowerSeries.subst d₃ E) := by
  first | exact @GlobalTheory.FrobStick.det_column_ops | exact GlobalTheory.FrobStick.det_column_ops | (intros; apply GlobalTheory.FrobStick.det_column_ops <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.duplicationFormula_maxNorm_eq_cp_unitDiscriminant : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.a₃‖ ≤ 1 → ‖W.a₄‖ ≤ 1 → ‖W.a₆‖ ≤ 1 → ‖W.Δ‖ = 1 → ∀ x : ℂ_[p], max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ = max 1 ‖x‖ ^ 4 := by
  first | exact @GlobalTheory.DupNorm.max_norm_eq_padicComplex | exact GlobalTheory.DupNorm.max_norm_eq_padicComplex | (intros; apply GlobalTheory.DupNorm.max_norm_eq_padicComplex <;> assumption)
end
