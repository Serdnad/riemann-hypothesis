module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle267
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitJPolynomialBoundedDenominators
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle274
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle273
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (M c : ℕ), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] → ∀ f ∈ Algebra.adjoin Ω ({X.jK} ∪ {g | ∃ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧ g = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]}), ∀ γ : SL(2, ℤ), (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp (X.sl (ofSL γ) f)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ IsIntegral ℤ ((D : Ω) * (X.exp (X.sl (ofSL γ) f)).coeff r)) := by
  first | exact @GlobalTheory.FracBd.frac_bd | exact GlobalTheory.FracBd.frac_bd | (intros; apply GlobalTheory.FracBd.frac_bd <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.InertParity.LengthSign

theorem not_dvd_relIndex {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (h0 : A.relIndex B ≠ 0) {q s : ℕ}
    (hq : q.Prime) (hs : Nat.Coprime s q) (h : ∀ x ∈ B, s • x ∈ A) : ¬ q ∣ A.relIndex B := by
  intro hd
  have : Fact q.Prime := ⟨hq⟩
  have : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h0
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ A.addSubgroupOf B) q hd
  have : s • x = 0 := by
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact h y y.2
  have h1 := addOrderOf_dvd_of_nsmul_eq_zero this
  rw [hx] at h1
  exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hs.symm h1)

theorem factorization_relIndex_eq {G : Type} [AddCommGroup G] (A A' B : AddSubgroup G) (h0 : A.relIndex B ≠ 0)
    (h0' : A'.relIndex B ≠ 0) {q s : ℕ} (hq : q.Prime) (hs : Nat.Coprime s q) (h : ∀ x ∈ A, s • x ∈ A')
    (h' : ∀ x ∈ A', s • x ∈ A) : (A.relIndex B).factorization q = (A'.relIndex B).factorization q := by
  have hX : (A ⊓ A').relIndex B ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h0 h0'
  have e1 := AddSubgroup.relIndex_inf_mul_relIndex A A' B
  have e2 := AddSubgroup.relIndex_inf_mul_relIndex A' A B
  rw [inf_comm A' A] at e2
  have n1 : A.relIndex (A' ⊓ B) ≠ 0 := left_ne_zero_of_mul (e1 ▸ hX)
  have n2 : A'.relIndex (A ⊓ B) ≠ 0 := left_ne_zero_of_mul (e2 ▸ hX)
  have d1 := not_dvd_relIndex A (A' ⊓ B) n1 hq hs fun x hx => h' x hx.1
  have d2 := not_dvd_relIndex A' (A ⊓ B) n2 hq hs fun x hx => h x hx.1
  have e := congrArg (fun m : ℕ => m.factorization q) (e1.trans e2.symm)
  simp only [Nat.factorization_mul n1 h0', Nat.factorization_mul n2 h0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd d1, Nat.factorization_eq_zero_of_not_dvd d2, zero_add] at e
  exact e.symm

theorem finite_quot {E : Type} [Field E] [NumberField E] {n : ℕ} (L₀ L : Submodule (𝓞 E) (Fin n → E))
    (h₀ : L₀.FG) (h : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := by
  first
  | exact @_root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap
  | exact _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap
  | (apply _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap ..)

theorem eq_lat {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : Moves D g L) : L = AdLattice.lat g := by
  ext x
  exact (h x).trans (AdLattice.mem_lat g x).symm

theorem finite_lat (D : D7) {n : ℕ} (g : GL (Fin n) (AE D)) :
    Finite (stdL D n ⧸ Submodule.comap (stdL D n).subtype (AdLattice.lat g)) :=
  finite_quot _ _ (AdLattice.lat_one_eq D n ▸ (AdLattice.lat_isLattice _).fg) (AdLattice.lat_isLattice g).span_eq_top

theorem idx_lat_ne_zero (D : D7) {n : ℕ} (g : GL (Fin n) (AE D)) : idx D (AdLattice.lat g) ≠ 0 := by
  have := finite_lat D g
  exact Nat.card_pos.ne'

theorem exists_int_mul (D : D7) {N : ℕ} (q : ℕ) (k : GA D N) (h : TrivAt D q (k : GL (Fin N) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) ∧
      ∀ i j, (s : AE D) * (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
        Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  have h0 : ∀ i j, ∃ m : ℕ, Nat.Coprime m q ∧ (m : AE D) *
      (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
        (1 : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ OhE D := by
    intro i j
    obtain ⟨m, -, hm, s, hs, he⟩ := h i j 0
    refine ⟨m, hm, ?_⟩
    rw [pow_zero, one_mul] at he
    rw [he]
    exact hs
  choose m hm hmS using h0
  set s : ℕ := ∏ r : Fin N × Fin N, m r.1 r.2 with hs
  have hint : ∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
    intro i j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun r : Fin N × Fin N => m r.1 r.2) (Finset.mem_univ (i, j))
    have h1 : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have : (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j = (c : AE D) * ((m i j : AE D) *
        (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
          (1 : Matrix (Fin N) (Fin N) (AE D)) i j)) + (s : AE D) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j := by
      rw [hs, hc]; push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ c) (hmS i j)) (mul_mem (natCast_mem _ s) h1)
  refine ⟨s, Nat.Coprime.prod_left fun r _ => hm r.1 r.2, hint, fun i j => ?_⟩
  rw [AdLattice.inv_entry (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) _ k.2]
  have := Formalism.UG.P.csDual_sig_mem (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) (hint j i)
  rwa [map_mul, map_natCast] at this

theorem agree (D : D7) {n : ℕ} (q : ℕ) (g k : GA D n) (h : TrivAt D q (k : GL (Fin n) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ x ∈ AdLattice.lat (g : GL (Fin n) (AE D)), s • x ∈ AdLattice.lat ((g * k : GA D n) : GL (Fin n) (AE D))) ∧
      ∀ x ∈ AdLattice.lat ((g * k : GA D n) : GL (Fin n) (AE D)), s • x ∈ AdLattice.lat (g : GL (Fin n) (AE D)) := by
  obtain ⟨s, hs, h1, h2⟩ := exists_int_mul D q k h
  refine ⟨s, hs, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul D.host.E]
    refine AdLattice.smul_mem_lat s ?_ hx
    rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]
    exact h2
  · rw [← Nat.cast_smul_eq_nsmul D.host.E]
    refine AdLattice.smul_mem_lat s ?_ hx
    rw [Subgroup.coe_mul, inv_mul_cancel_left]
    exact h1

theorem finite_of_moves {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : Moves D g L) : Finite (stdL D n ⧸ Submodule.comap (stdL D n).subtype L) := by
  rw [eq_lat h]
  exact finite_lat D g

theorem relIndex_ne_zero_of_moves {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Moves D g L) :
    L.toAddSubgroup.relIndex (stdL D n).toAddSubgroup ≠ 0 := by
  rw [← idx_eq_relIndex, eq_lat h]
  exact idx_lat_ne_zero D g

theorem agree_of_moves {D : D7} {n : ℕ} {q : ℕ} {g k : GA D n} (h : TrivAt D q (k : GL (Fin n) (AE D)))
    {L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : Moves D (g : GL (Fin n) (AE D)) L)
    (hL' : Moves D ((g * k : GA D n) : GL (Fin n) (AE D)) L') :
    ∃ s : ℕ, Nat.Coprime s q ∧ (∀ x ∈ L.toAddSubgroup, s • x ∈ L'.toAddSubgroup) ∧
      ∀ x ∈ L'.toAddSubgroup, s • x ∈ L.toAddSubgroup := by
  rw [eq_lat hL, eq_lat hL']
  exact agree D q g k h

theorem agree_std {D : D7} {n : ℕ} {q : ℕ} {k : GA D n} (h : TrivAt D q (k : GL (Fin n) (AE D)))
    {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : Moves D (k : GL (Fin n) (AE D)) L) :
    ∃ s : ℕ, Nat.Coprime s q ∧ ∀ x ∈ (stdL D n).toAddSubgroup, s • x ∈ L.toAddSubgroup := by
  obtain ⟨s, hsq, h, -⟩ := agree D q 1 k h
  rw [one_mul, OneMemClass.coe_one, AdLattice.lat_one_eq, ← eq_lat hL] at h
  exact ⟨s, hsq, h⟩

theorem neg_one_pow_lenQ : ∀ (D : D7) (n : ℕ) (gs gi : GA D n) (Li L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), SuppSplit D (gs : GL (Fin n) (AE D)) → SuppInert D (gi : GL (Fin n) (AE D)) → Moves D (gi : GL (Fin n) (AE D)) Li → Moves D ((gi * gs : GA D n) : GL (Fin n) (AE D)) L → (-1 : ℂ) ^ lenQ D (stdL D n) Li = sgn D (idx D L) := by
  intro D n gs gi Li L hs hi hLi hL
  have := finite_of_moves hLi
  have h1 : sgn D (idx D Li) = (-1 : ℂ) ^ lenQ D (stdL D n) Li := by
    refine (GlobalTheory.T.finite_module_sign_eq_neg_one_pow_length D (stdL D n ⧸ Submodule.comap (stdL D n).subtype Li)).2 fun q hq hd => ?_
    by_contra hn
    obtain ⟨s, hsq, h⟩ := agree_std (hi q hq hn) hLi
    exact not_dvd_relIndex _ _ (relIndex_ne_zero_of_moves hLi) hq hsq h ((idx_eq_relIndex Li) ▸ hd)
  rw [← h1]
  refine sgn_congr fun q hq hiq => ?_
  obtain ⟨s, hsq, h, h'⟩ := agree_of_moves (hs q hq hiq) hLi hL
  rw [idx_eq_relIndex, idx_eq_relIndex]
  exact factorization_relIndex_eq _ _ _ (relIndex_ne_zero_of_moves hLi) (relIndex_ne_zero_of_moves hL) hq hsq h h'

end GlobalTheory.InertParity.LengthSign
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Param

open PowerSeries

theorem isWpSer_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) {a b : K} {P : PowerSeries K}
    (h : IsWpSer a b P) : IsWpSer (f a) (f b) (PowerSeries.map f P) := by
  have hd : derivativeFun (PowerSeries.map f P) = PowerSeries.map f (derivativeFun P) := by
    ext n
    simp [derivativeFun, coeff_derivative]
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.1, map_one]
  · have := congrArg (PowerSeries.map f) h.2
    simp only [map_pow, map_sub, map_mul, map_C, map_X, map_ofNat] at this
    rw [hd]
    exact this

theorem isWpSer_rescale {K : Type*} [CommRing K] (e : K) {a b : K} {P : PowerSeries K}
    (h : IsWpSer a b P) : IsWpSer (e ^ 4 * a) (e ^ 6 * b) (rescale e P) := by
  have hd : X * derivativeFun (rescale e P) = rescale e (X * derivativeFun P) := by
    ext n
    cases n with
    | zero => simp [coeff_rescale]
    | succ n => simp [coeff_rescale, coeff_succ_X_mul, derivativeFun, coeff_derivative, mul_assoc, pow_succ']
  have hC : ∀ c : K, rescale e (C c) = C c := by
    intro c
    ext n
    cases n <;> simp [coeff_rescale, coeff_C]
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply, h.1]
    simp
  · have := congrArg (rescale e) h.2
    rw [hd]
    rw [map_pow, map_sub] at this
    simp only [map_pow (rescale e), map_sub (rescale e), map_mul (rescale e) _ P, map_mul (rescale e) (C _),
      map_mul (rescale e) 4, hC, rescale_X, map_ofNat] at this
    rw [this]
    simp only [map_mul, map_pow]
    ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe' (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC]

theorem theta_series_map_coefficients (lam : Qbar →+* ℂ_[p]) (F : ℂ → ℂ) (T : PowerSeries Qbar)
    (h : PowerSeries.mk (coef1 F) = PowerSeries.map (algebraMap Qbar ℂ) T) :
    GL3Theta.ser1 lam F = PowerSeries.map lam T := by
  ext n
  have := congrArg (coeff n) h
  rw [coeff_mk, coeff_map] at this
  rw [GL3Theta.ser1, coeff_mk, coeff_map, ← lamC_coe']
  exact congrArg (lamC lam) this

theorem invariants (g : GL3Theta.G1 p) (a b : Qbar) (ha : g2 g.abelian₂ = a) (hb : g3 g.abelian₂ = b) :
    g.W.c₄ / 12 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 4 * g.lam a ∧
    g.W.c₆ / 216 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 * g.lam b ∧
    g.W.b₂ / 12 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r := by
  have e : ∀ x : Qbar, lamC g.lam (-(x : ℂ) / 4) = -g.lam x / 4 := by
    intro x
    have : -(x : ℂ) / 4 = ((-x / 4 : Qbar) : ℂ) := by
      push_cast; rfl
    rw [this, lamC_coe', map_div₀, map_neg, map_ofNat]
  unfold GL3Theta.G1.W
  rw [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_c₆,
    WeierstrassCurve.variableChange_b₂]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, wModel, ha, hb, e]
  refine ⟨by ring, by ring, by ring⟩

theorem exists_algebraic_series (Λ : AddSubgroup ℂ) (hL : IsLat Λ) (a b w : Qbar) (ha : g2 Λ = a) (hb : g3 Λ = b)
    (hσ : AlgEnt (sgStar Λ)) (v : ℂ) (hv : v ∉ Λ) (hw : wpF Λ v = w) :
    ∃ P₀ S : PowerSeries Qbar, IsWpSer a b P₀ ∧
      PowerSeries.mk (coef1 (sgStar Λ)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) ∧
      PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.map (algebraMap Qbar ℂ) (S ^ 2 * lineSer P₀ w) := by
  obtain ⟨P, hP, hPv⟩ := GlobalTheory.T.exists_weierstrassPSeries_and_sigmaStarQuotientSeries Λ hL
  obtain ⟨P₀, hP₀, -⟩ := GlobalTheory.T.existsUnique_isWeierstrassPSeries Qbar a b
  rw [ha, hb] at hP
  have hPP : P = PowerSeries.map (algebraMap Qbar ℂ) P₀ :=
    (GlobalTheory.T.existsUnique_isWeierstrassPSeries ℂ a b).unique hP (isWpSer_map (algebraMap Qbar ℂ) hP₀)
  have h0 : coef1 (sgStar Λ) 0 = 0 := by
    simp [coef1, (hL.sg_eq_zero 0).2 (zero_mem _)]
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 (sgStar Λ)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) := by
    refine ⟨PowerSeries.mk fun n => ⟨coef1 (sgStar Λ) (n + 1), hσ.2 _⟩, ?_⟩
    ext n
    cases n with
    | zero => simp [h0]
    | succ n => rw [coeff_map, coeff_succ_X_mul, coeff_mk, coeff_mk]; rfl
  refine ⟨P₀, S, hP₀, hS, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := ℂ)))
  rw [hPv v hv, hS, hPP, hw]
  simp only [lineSer, map_mul, map_pow, map_sub, map_X, map_C]
  have : algebraMap Qbar ℂ w = (w : ℂ) := rfl
  rw [this]
  ring

theorem subst_lineSer {K : Type*} [Field K] (l E q S P : PowerSeries K) (ε r w : K) (hl0 : constantCoeff l = 0)
    (hE : X * E = l * subst (C ε * l) S)
    (hform : X ^ 2 * (subst l (rescale ε P) : PowerSeries K) = l ^ 2 * lineSer q (-(ε ^ 2 * r))) :
    (subst (C ε * l) (S ^ 2 * lineSer P w) : PowerSeries K) = E ^ 2 * lineSer q (ε ^ 2 * (w - r)) := by
  have hl : HasSubst l := HasSubst.of_constantCoeff_zero' hl0
  have hel : HasSubst (C ε * l) := HasSubst.of_constantCoeff_zero' (by simp [hl0])
  have hres : subst l (rescale ε P) = (subst (C ε * l) P : PowerSeries K) := by
    rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' ε) hl, subst_smul hl, subst_X hl, smul_eq_C_mul]
  rw [hres] at hform
  have hCs : subst (C ε * l) (C w : PowerSeries K) = (C w : PowerSeries K) := by
    rw [← coe_substAlgHom hel]
    exact (substAlgHom hel).commutes w
  apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := K)))
  rw [← mul_assoc, ← mul_pow, hE]
  simp only [lineSer, map_mul, map_pow, map_sub, map_neg] at hform ⊢
  rw [subst_mul hel, subst_pow hel, subst_sub hel, subst_mul hel, subst_pow hel, subst_X hel, hCs]
  linear_combination (subst (C ε * l) S : PowerSeries K) ^ 2 * hform

theorem constantCoeff_l (g : GL3Theta.G1 p) : constantCoeff g.l = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, GL3Theta.G1.l, flog, coeff_mk]; simp

theorem X_mul_ePhi1 (g : GL3Theta.G1 p) (S : PowerSeries ℂ_[p]) (hS : GL3Theta.ser1 g.lam (sgStar g.abelian₂) = X * S) :
    X * ePhi1 g.lam g.abelian₂ g.C g.wq = g.l * subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) S := by
  have hl0 := constantCoeff_l g
  have hel : HasSubst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_mul, hl0, mul_zero])
  have hS' : sgSer g.lam g.abelian₂ = X * S := hS
  ext n
  cases n with
  | zero => rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, map_mul, hl0,
      constantCoeff_X, zero_mul, zero_mul]
  | succ n =>
    rw [coeff_succ_X_mul, ePhi1, coeff_mk, hS', ← C_eq_algebraMap, ← GL3Theta.G1.W, ← GL3Theta.G1.l,
      subst_mul hel, subst_X hel, mul_assoc, coeff_C_mul, inv_mul_cancel_left₀ (Units.ne_zero _)]

theorem sqTh_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (sqTh g.abelian₂ v) ∧ g.atU (sqTh g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v) := by
  intro p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨a, ha⟩ : ∃ a : Qbar, g2 g.abelian₂ = a := ⟨⟨_, h2⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Qbar, g3 g.abelian₂ = b := ⟨⟨_, h3⟩, rfl⟩
  obtain ⟨w, hw'⟩ : ∃ w : Qbar, wpF g.abelian₂ v = w := ⟨⟨_, hw⟩, rfl⟩
  obtain ⟨P₀, S, hP₀, hS, hT⟩ := exists_algebraic_series g.abelian₂ hL a b w ha hb hσ v hv hw'
  refine ⟨⟨hL.differentiable_sqTh v, fun n => ?_⟩, ?_⟩
  · have := congrArg (coeff n) hT
    rw [coeff_mk, coeff_map] at this
    rw [this]
    exact SetLike.coe_mem _
  obtain ⟨i4, i6, i2⟩ := invariants g a b ha hb
  have hform := GlobalTheory.T.weierstrassP_formalGroupLog_uniformises p g.W g.wq
    (rescale ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) (PowerSeries.map g.lam P₀)) hq
    (by rw [i4, i6]; exact isWpSer_rescale _ (isWpSer_map g.lam hP₀))
  rw [i2, ← GL3Theta.G1.l] at hform
  have hE := X_mul_ePhi1 g (PowerSeries.map g.lam S) (by rw [theta_series_map_coefficients g.lam _ _ hS, map_mul, map_X])
  have hm : PowerSeries.map g.lam (S ^ 2 * lineSer P₀ w) =
      PowerSeries.map g.lam S ^ 2 * lineSer (PowerSeries.map g.lam P₀) (g.lam w) := by
    simp only [lineSer, map_mul, map_pow, map_sub, map_X, map_C]
  rw [GL3Theta.G1.atU, ← C_eq_algebraMap, theta_series_map_coefficients g.lam _ _ hT, hm, xAt, hw', lamC_coe']
  exact subst_lineSer _ _ _ _ _ _ _ _ (constantCoeff_l g) hE hform

end GlobalTheory.EvenTheta.Param
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.U1_sq_mul_U1_th0_sq_eq_sgStar : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ t, t ∉ Λ → ∀ z, U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (GL3Theta.th0 Λ t₀) z ^ 2 = -(U1 Λ (2 * t) (sgStar Λ) z * sgStar Λ z) + (wpF Λ t - wpF Λ t₀) * U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (sgStar Λ) z ^ 2 := by
  first | exact @GlobalTheory.EvenTheta.IsLat.evenTheta_translate_sq_eq_sigmaStar | exact GlobalTheory.EvenTheta.IsLat.evenTheta_translate_sq_eq_sigmaStar | (intros; apply GlobalTheory.EvenTheta.IsLat.evenTheta_translate_sq_eq_sigmaStar <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

theorem _root_.GlobalTheory.T.bettiKummerRelationPadic_add : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (b b' : X.Fn l) (c c' : Gam N l → MvPolynomial (Fin 2) ℤ_[l]), BtZ X N l b c → BtZ X N l b' c' → BtZ X N l (b + b') (c + c') := by
  first | exact @GlobalTheory.KZ.BettiB.Add.btZ_add | exact GlobalTheory.KZ.BettiB.Add.btZ_add | (intros; apply GlobalTheory.KZ.BettiB.Add.btZ_add <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

theorem _root_.GlobalTheory.T.bettiKummerRelationPadic_smul : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (r : ℤ_[l]) (b : X.Fn l) (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]), BtZ X N l b c → BtZ X N l (r • b) (r • c) := by
  first | exact @GlobalTheory.KZ.BettiB.btZ_smul | exact GlobalTheory.KZ.BettiB.btZ_smul | (intros; apply GlobalTheory.KZ.BettiB.btZ_smul <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

theorem _root_.GlobalTheory.T.gammaOneGammaZeroHomogeneousCocycles_finite : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → Module.Finite ℤ_[l] (Z1 N l w) := by
  first | exact @GlobalTheory.KZ.BettiB.module_finite_z1_padicInt | exact GlobalTheory.KZ.BettiB.module_finite_z1_padicInt | (intros; apply GlobalTheory.KZ.BettiB.module_finite_z1_padicInt <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

theorem _root_.GlobalTheory.T.eq_zero_of_bettiKummerRelationPadic_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l : ℕ) [Fact l.Prime], 0 < N → ∀ b : X.Fn l, BtZ X N l b 0 → b = 0 := by
  first | exact @GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero | exact GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero | (intros; apply GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.DistTriple

theorem bc_eq_one {D : D7} {T : Tor D} {N N' : ℕ} {A₁ A₂ A₃ : AddSubgroup (VC D N N')}
    (h₁ : Nice D T A₁) (h₂ : Nice D T A₂) (h₃ : Nice D T A₃) (hd : Dist A₁ A₂ A₃)
    {x y : VC D N N'} (hx : x ∈ A₂) (hy : y ∈ A₃) (hxy : y + x ∈ A₁) : bc D T y x = 1 := by
  have hm := hd x hx y hy (by rwa [add_comm])
  obtain ⟨x₁, hx₁, x₃, hx₃, rfl⟩ := AddSubgroup.mem_sup.1 hm
  have hy₃ : y + x₃ ∈ A₁ := by
    have := A₁.sub_mem hxy hx₁.1
    have e : y + (x₁ + x₃) - x₁ = y + x₃ := by abel
    rwa [e] at this
  have e1 := h₁.2.1 _ hy₃ _ hx₁.1
  rw [bc_add_left, h₂.2.1 _ hx₃.1 _ hx₁.2, mul_one] at e1
  rw [bc_add_right, e1, h₃.2.1 _ hy _ hx₃.2, mul_one]

theorem const_eq_one : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N'))
    (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → Dist A₁ A₂ A₃ → μ = 1 := by
  intro D T N N' A₁ A₂ A₃ e μ ht hd
  obtain ⟨r, hr, hs⟩ := GlobalTheory.T.thetaTripleConstant_eq_cocycle_sum D T N N' A₁ A₂ A₃ e μ ht
  obtain ⟨h₁, h₂, h₃, -, -, -, -, -, h8, -⟩ := ht
  have key : ∃ s : ℝ, 0 ≤ s ∧ μ * (r : ℂ) = (s : ℂ) := by
    rw [hs]
    refine finsum_induction (fun z : ℂ => ∃ s : ℝ, 0 ≤ s ∧ z = (s : ℂ)) ⟨0, le_rfl, by simp⟩ ?_ ?_
    · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_nonneg ha hb, by push_cast; rfl⟩
    · intro p
      split_ifs with h
      · exact ⟨1, zero_le_one, by
          rw [bc_eq_one h₁ h₂ h₃ hd (Quotient.out p.2 : A₂).2 (Quotient.out p.1 : A₃).2 h]; simp⟩
      · exact ⟨0, le_rfl, by simp⟩
  obtain ⟨s, hs0, hμ⟩ := key
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hμ' : μ = ((s / r : ℝ) : ℂ) := by
    push_cast; rw [eq_div_iff hr', hμ]
  rw [hμ'] at h8 ⊢
  have h8' : (s / r) ^ 8 = 1 := by exact_mod_cast h8
  have := (pow_eq_one_iff_of_nonneg (div_nonneg hs0 hr.le) (by norm_num)).1 h8'
  rw [this]; simp

end GlobalTheory.DistTriple
end
