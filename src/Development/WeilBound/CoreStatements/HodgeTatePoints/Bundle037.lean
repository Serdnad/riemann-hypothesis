module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ROmVia
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FinClosure
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle036
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle035
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle053
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle056
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle049
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle044
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem prod_ext {n : ℕ} (s : Fin n → NNReal) :
    ∏ i ∈ Finset.range n, (fun i => if h : i < n then s ⟨i, h⟩ else 1) i = ∏ i, s i := by
  rw [Finset.prod_range]
  simp

theorem prod_ext_min {n : ℕ} (s : Fin n → NNReal) (j : ℕ) :
    ∏ i ∈ Finset.range (min j n), (fun i => if h : i < n then s ⟨i, h⟩ else 1) i =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i := by
  have key : Finset.range (min j n) = (Finset.range n).filter (fun i => i < j) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_filter, lt_min_iff]
    tauto
  rw [key, Finset.prod_filter, Finset.prod_filter,
    ← Fin.prod_univ_eq_prod_range (fun i => if i < j then (if h : i < n then s ⟨i, h⟩ else 1) else 1) n]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp

theorem flag_om_of (hex : type_of% @GlobalTheory.T.teichmuller_character_exists) (hsq : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_restriction)
    (hsplit : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_ideal) (hos : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_characters) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r := by
  intro p _ C _ _ _ v R _ _ hR hp F _ _ _ _ f hcard N _ _ _ _ AA hst n b χ s r hs hr
  have key := chain_le hex hsq hsplit hos p C v R hR hp F f hcard χ n N AA hst (flagSub b)
    (fun i => if h : i < n then b ⟨i, h⟩ else 0) (isChain_flag b)
    (fun i => if h : i < n then s ⟨i, h⟩ else 1) r
    (by
      intro i hi
      have e1 : (if h : i < n then b ⟨i, h⟩ else 0) = b ⟨i, hi⟩ := dif_pos hi
      have e2 : (if h : i < n then s ⟨i, h⟩ else 1) = s ⟨i, hi⟩ := dif_pos hi
      show HasLen v R (OmType (stepOrder AA.carrier (flagSub b i)
        (if h : i < n then b ⟨i, h⟩ else 0)) χ) (if h : i < n then s ⟨i, h⟩ else 1)
      rw [e1, e2]
      exact hs ⟨i, hi⟩) hr
  rwa [prod_ext] at key

theorem gr_partial_of (hex : type_of% @GlobalTheory.T.teichmuller_character_exists) (hsq : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_restriction)
    (hstep : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_translation) (hsplit : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_ideal)
    (hos : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_characters) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) := by
  intro p _ C _ _ _ v R _ _ hR hp F _ _ _ _ f hcard N _ _ _ _ AA hst n b χ s hs hr j
  have key := chain_partial hex hsq hsplit hos p C v R hR hp F f hcard hstep χ n N AA hst (flagSub b)
    (fun i => if h : i < n then b ⟨i, h⟩ else 0) (isChain_flag b)
    (fun i => if h : i < n then s ⟨i, h⟩ else 1)
    (by
      intro i hi
      have e1 : (if h : i < n then b ⟨i, h⟩ else 0) = b ⟨i, hi⟩ := dif_pos hi
      have e2 : (if h : i < n then s ⟨i, h⟩ else 1) = s ⟨i, hi⟩ := dif_pos hi
      show HasLen v R (OmType (stepOrder AA.carrier (flagSub b i)
        (if h : i < n then b ⟨i, h⟩ else 0)) χ) (if h : i < n then s ⟨i, h⟩ else 1)
      rw [e1, e2]
      exact hs ⟨i, hi⟩)
    (by rwa [prod_ext]) j
  rwa [prod_ext_min] at key

end PositivityTheory.HtPt.Rd
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rom

theorem a_nonunit_of (h : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_powers) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) :=
  PositivityTheory.HtPt.Rd.a_nonunit_rom_of (@r_om_of h)

end PositivityTheory.HtPt.Rom
end

section

noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

section Alg

variable {k : Type} [CommRing k]

theorem aug_mk {κ : Type} (m : ℕ) (P : MvPolynomial κ k) :
    (jetAug : Jet k κ m →ₐ[k] k) (Ideal.Quotient.mk _ P) = MvPolynomial.constantCoeff P := by
  have : (jetAug : Jet k κ m →ₐ[k] k) (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (fun _ => (0 : k)) P := rfl
  rw [this, MvPolynomial.aeval_zero']
  rfl

theorem substP_X {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' k) (i : κ) :
    jetSubstP m φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) := by
  rw [jetSubstP, jetMap_mk, MvPolynomial.aeval_X]

theorem psTrunc_expand {σ : Type} [Fintype σ] [DecidableEq σ] (p : ℕ) (hp : p ≠ 0) (V : MvPowerSeries σ k)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    psTrunc p (MvPowerSeries.expand p hp V) =
      ∑ j, MvPolynomial.C (MvPowerSeries.coeff (Finsupp.single j 1) V) * MvPolynomial.X j ^ p := by
  ext e
  have hR : AddMonoidAlgebra.coeff (∑ j, MvPolynomial.C (MvPowerSeries.coeff (Finsupp.single j 1) V) * MvPolynomial.X j ^ p : MvPolynomial σ k)
      e =
      ∑ j, if Finsupp.single j p = e then MvPowerSeries.coeff (Finsupp.single j 1) V else 0 := by
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
    split_ifs <;> simp
  rw [hR]
  by_cases hs : ∃ j, Finsupp.single j p = e
  · obtain ⟨j, rfl⟩ := hs
    rw [GermFun.coeff_psTrunc _ _ _ (by simp), Finset.sum_eq_single j, if_pos rfl]
    · have : Finsupp.single j p = p • Finsupp.single j 1 := by simp
      rw [this, MvPowerSeries.coeff_expand_smul]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb ((Finsupp.single_left_inj hp).1 h)
    · simp
  · rw [Finset.sum_eq_zero fun j _ => if_neg fun h => hs ⟨j, h⟩]
    by_cases hd : e.degree ≤ p
    · rw [GermFun.coeff_psTrunc _ _ _ hd]
      by_cases hdv : ∀ i, p ∣ e i
      · choose c hc using hdv
        let e' : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm c
        have he : e = p • e' := by ext i; simp [e', hc]
        have hdeg : e'.degree ≤ 1 := by
          rw [he, map_nsmul, smul_eq_mul] at hd
          by_contra hh
          have : p * 2 ≤ p * e'.degree := Nat.mul_le_mul_left _ (by omega)
          omega
        rw [he, MvPowerSeries.coeff_expand_smul]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hdeg with h0 | h1
        · rw [(Finsupp.degree_eq_zero_iff _).1 h0]
          simpa using hV
        · exfalso
          have h1' : e' ∈ {d : σ →₀ ℕ | d.degree = 1} := h1
          rw [← Finsupp.range_single_one] at h1'
          obtain ⟨j, hj⟩ := h1'
          exact hs ⟨j, by rw [he, ← hj]; simp⟩
      · push Not at hdv
        obtain ⟨i, hi⟩ := hdv
        exact MvPowerSeries.coeff_expand_of_not_dvd _ _ _ hi
    · rw [psTrunc, MvPolynomial.coeff_sum]
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [MvPolynomial.coeff_monomial, if_neg]
      rintro rfl
      apply hd
      have := (Finset.mem_filter.1 hb).2
      simpa [Finsupp.degree_apply, Finsupp.sum] using this

theorem comp1_point_power_expand {d : ℕ} (p : ℕ) (hp : p ≠ 0) (V : Germ.Pt k 1 d) (i : Fin d) :
    Germ.comp1 V (ptPow k d p (0 : Fin 1)) i = MvPowerSeries.expand p hp (V i) := by
  have : (fun q : Fin 1 × Fin d => (![ptPow k d p (0 : Fin 1)] : Fin 1 → Germ.Pt k 1 d) q.1 q.2) =
      fun q => MvPowerSeries.X q ^ p := by
    funext ⟨a, b⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  rw [Germ.comp1, Germ.ev, this, MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]

def trTo (k : Type) [CommRing k] (κ : Type) {m n : ℕ} (h : n ≤ m) : Jet k κ m →ₐ[k] Jet k κ n :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

theorem trTo_mk {κ : Type} {m n : ℕ} (h : n ≤ m) (P : MvPolynomial κ k) :
    trTo k κ h (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ P := rfl

theorem mem_orig_of_aug {κ : Type} {m : ℕ} {P : MvPolynomial κ k}
    (h : (jetAug : Jet k κ m →ₐ[k] k) (Ideal.Quotient.mk _ P) = 0) : P ∈ orig k κ := by
  rw [aug_mk] at h
  simpa [h] using sub_const_mem_orig P

theorem exists_low {κ κ' : Type} {m n : ℕ} (h : n ≤ m) (χ : Jet k κ m →ₐ[k] Jet k κ' m)
    (hχ : ∀ q, (jetAug : Jet k κ' m →ₐ[k] k) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) :
    ∃ χ' : Jet k κ n →ₐ[k] Jet k κ' n,
      (∀ q, (jetAug : Jet k κ' n →ₐ[k] k) (χ' (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧
      χ'.comp (trTo k κ h) = (trTo k κ' h).comp χ := by
  choose P hP using fun q => Ideal.Quotient.mk_surjective (χ (Ideal.Quotient.mk _ (MvPolynomial.X q)))
  have hm : ∀ q, P q ∈ orig k κ' := fun q => mem_orig_of_aug (by rw [hP]; exact hχ q)
  refine ⟨jetMap P hm, fun q => ?_, jet_hom_ext fun q => ?_⟩
  · rw [jetMap_mk, MvPolynomial.aeval_X, aug_mk, ← aug_mk m, hP]
    exact hχ q
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, trTo_mk, jetMap_mk, MvPolynomial.aeval_X, ← hP, trTo_mk]

theorem pow_eq_of_first {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) {κ : Type}
    (a b : Jet k κ p) (h : trTo k κ hp a = trTo k κ hp b) : a ^ p = b ^ p := by
  haveI : CharP (MvPolynomial κ k) p := inferInstance
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [trTo_mk, trTo_mk, Ideal.Quotient.eq] at h
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq, ← sub_pow_char]
  have := Ideal.pow_mem_pow h p
  rw [← pow_mul] at this
  exact Ideal.pow_le_pow_right (by omega) this

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0}

theorem act_nat (t : SAB H X0) (n : ℕ) : t.act.act (n : 𝓞 E) = (𝟙 t.G) ^ n := by
  induction n with
  | zero =>
    have := t.act.add 0 0
    rw [add_zero] at this
    simpa using this
  | succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, pow_succ]

theorem pow_eq_act {T : Over X0} (y : T ⟶ t.G) (n : ℕ) : y ^ n = y ≫ t.act.act (n : 𝓞 E) := by
  rw [act_nat, MonObj.comp_pow, Category.comp_id]

variable {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d : ℕ} (g : GermAt t x d)

theorem x_trTo {m n : ℕ} (h : n ≤ m) : homAt x (trTo S (Fin 1 × Fin d) h) ≫ g.x m = g.x n := by
  induction m, h using Nat.le_induction with
  | base =>
    have : trTo S (Fin 1 × Fin d) (le_refl n) = AlgHom.id S _ := jet_hom_ext fun _ => rfl
    rw [this, homAt_id, Category.id_comp]
  | succ m h ih =>
    have : trTo S (Fin 1 × Fin d) (h.trans (Nat.le_succ m)) = (trTo S (Fin 1 × Fin d) h).comp jetTrunc :=
      jet_hom_ext fun _ => rfl
    rw [this, ← homAt_comp, Category.assoc, g.chart.trunc, ih]

theorem x_zero {A : Type} [CommRing A] [Algebra S A] {m : ℕ} (χ : Jet S (Fin 1 × Fin d) m →ₐ[S] A)
    (hχ : ∀ q, χ (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0) : homAt x χ ≫ g.x m = 1 := by
  have : χ = (Algebra.ofId S A).comp jetAug := jet_hom_ext fun q => by
    rw [hχ, AlgHom.comp_apply, aug_mk]
    simp
  rw [this, ← homAt_comp, Category.assoc, g.chart.zero, MonObj.comp_one]

theorem pow_coord {A : Type} [CommRing A] [Algebra S A] (p : ℕ) (hp : p ≠ 0)
    (hV : ∃ V : Germ.Pt S 1 d, (∀ i, MvPowerSeries.constantCoeff (V i) = 0) ∧
      g.B.A.act (p : 𝓞 E) = Germ.comp1 V (ptPow S d p 0) ∧ lin V 1 = hw g.B p)
    (χ : Jet S (Fin 1 × Fin d) p →ₐ[S] A) :
    ∃ ψ : Jet S (Fin 1 × Fin d) p →ₐ[S] A, (homAt x χ ≫ g.x p) ^ p = homAt x ψ ≫ g.x p ∧
      ∀ q, ψ (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
        ∑ j, algebraMap S A (hw g.B p q.2 j) * χ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) ^ p := by
  obtain ⟨V, hc, hV, hl⟩ := hV
  refine ⟨χ.comp (jetSubstP p fun q : Fin 1 × Fin d => psTrunc p (g.B.A.act (p : 𝓞 E) q.2)), ?_, fun q => ?_⟩
  · rw [pow_eq_act, Category.assoc, g.chart.act, ← Category.assoc, homAt_comp]
  · rw [AlgHom.comp_apply, substP_X, hV, comp1_point_power_expand p hp, psTrunc_expand p hp _ (hc _), ← hl]

    simp only [map_sum, map_mul, map_pow, MvPolynomial.constantCoeff_X, zero_pow hp, mul_zero,
    Finset.sum_const_zero, map_zero, sub_zero, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact χ.commutes _

end Geo

end PositivityTheory.HtPt.Ce
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite

theorem mem_regAt_genPt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap]
  rw [e]
  erw [Category.id_comp]
  exact hs

theorem exists_eq_div_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type}
    [Finite κ] {x : κ → Ω} (M : PModel o x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v := by
  have hp : InChart M.ξ x c ⟨genPt M.ξ, specializes_rfl⟩ :=
    ⟨hc, fun c' => mem_regAt_genPt M.tie.gen _⟩
  obtain ⟨u, hu, v, hv, -, e⟩ :=
    ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hp).2 a).1 (mem_regAt_genPt M.tie.gen a)
  exact ⟨u, hu, v, hv, e⟩

theorem finite_integralClosure_chRing {o : Type} [CommRing o] [Algebra.EssFiniteType ℤ o] {Ω : Type}
    [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω']
    [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ)
    (hc : x c ≠ 0) :
    Module.Finite (chRing o (fun k => algebraMap Ω Ω' (x k)) c)
      (integralClosure (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω') := by
  let φ : Ω →ₐ[o] Ω' := IsScalarTower.toAlgHom o Ω Ω'
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have hmap : (chRing o x c).map φ = chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
    simp only [chRing]
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    ext j
    simp [φ]
  let e : chRing o x c ≃ₐ[o] chRing o (fun k => algebraMap Ω Ω' (x k)) c :=
    ((chRing o x c).equivMapOfInjective φ hφ).trans (Subalgebra.equivOfEq _ _ hmap)
  have he : ∀ a, ((e a : chRing o (fun k => algebraMap Ω Ω' (x k)) c) : Ω') =
      algebraMap Ω Ω' (a : Ω) := fun a => rfl
  haveI : Algebra.FiniteType o (chRing o (fun k => algebraMap Ω Ω' (x k)) c) := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩
  haveI : Algebra.EssFiniteType o (chRing o (fun k => algebraMap Ω Ω' (x k)) c) :=
    Algebra.EssFiniteType.of_finiteType _ _
  haveI : Algebra.EssFiniteType ℤ (chRing o (fun k => algebraMap Ω Ω' (x k)) c) :=
    Algebra.EssFiniteType.comp ℤ o _
  letI : Algebra (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    ((chRing o x c).val.toRingHom.comp e.symm.toRingEquiv.toRingHom).toAlgebra
  have hmapΩ : ∀ a : chRing o x c,
      algebraMap (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω (e a) = (a : Ω) := by
    intro a
    change ((e.symm (e a) : chRing o x c) : Ω) = a
    rw [AlgEquiv.symm_apply_apply]
  haveI : IsScalarTower (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω Ω' :=
    IsScalarTower.of_algebraMap_eq fun a => by
      obtain ⟨b, rfl⟩ := e.surjective a
      rw [hmapΩ]
      exact he b
  haveI : FaithfulSMul (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h => by
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨b, rfl⟩ := e.surjective b
      rw [hmapΩ, hmapΩ] at h
      rw [Subtype.ext h]
  haveI : IsFractionRing (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨u, hu, v, hv, rfl⟩ := exists_eq_div_chRing M hc z
      exact ⟨e ⟨u, hu⟩, e ⟨v, hv⟩, by rw [hmapΩ, hmapΩ]⟩
  exact PositivityTheory.HtPt.Mb.fin_closure _ Ω Ω'

end PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.finite_ext : ∀ {o : Type} [CommRing o] [Algebra.EssFiniteType ℤ o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → Module.Finite (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (integralClosure (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω') :=
  @PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite.finite_integralClosure_chRing
end
end

section

namespace PositivityTheory.HtPt.Kra

universe u w

theorem kleiman_input : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{u, w} :=
  GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.proof interNumEventual interNumAdditive
    (intersectionNumberCut_of_mixedTwistShift mixedTwistShift) interNumPointDeg

theorem kleiman_input_universe_zero : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} := kleiman_input

end PositivityTheory.HtPt.Kra
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace PositivityTheory.HtPt.Siub

theorem siu_segre :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (μ : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a : ℕ, 1 ≤ a ∧ ∃ σ ∈ secOver F y (a • μ - 1), σ ≠ 0 :=
  siu_segre_of PositivityTheory.HtPt.Siua.siu_num

end PositivityTheory.HtPt.Siub
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PositivityTheory.HtPt.Aig

theorem coordFibreDeg : GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.Statement :=
  GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.proof GroundTheory.Heights₂.Heights.Targets.FibreMultiHomog.proof
    (GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof
      GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.proof)
    GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg.proof

theorem genDeg_of_coord (hPF : PFCoordStatement) (hFD : FibreDimStatement) : GenDegStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G J L L' hv hP' hP hJ hL hLL'
  obtain ⟨Ω, _, y, hy, -⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.proof K' ι' P' d hP'
  subst hy
  have : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hz : ((n : ℤ) : Ω) = 0 := by exact_mod_cast hn
    have hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y := by
      simp only [mCoordIdeal, RingHom.mem_ker, mConeMap, eq_intCast]
      rw [map_intCast, ← map_intCast (C : Ω →+* MvPolynomial K' Ω), hz, map_zero]
    have h2 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι') := hmem
    rw [hP'.2.2.1] at h2
    exact_mod_cast (Ideal.mem_bot).1 h2
  have hV : IsProjVarF (fibreIdeal κ G) 0 := hFD K ι K' ι' κ v (mCoordIdeal y) d 0 G hv hP' hP
  choose i hi using hV.1.2.2
  have h0 := hJ.1 (fibreIdeal κ G) Fin.elim0 i hV hi
  rw [hPF I hI K ι K' ι' κ v Ω y d L L' hv hP' hP hL hLL', h0,
    coordFibreDeg K ι K' ι' κ v Ω y d G i hv hP' hP hi, Int.cast_natCast]

theorem genDeg : PFCoordStatement → FibreDimStatement → GenDegStatement :=
  genDeg_of_coord

end PositivityTheory.HtPt.Aig
end
