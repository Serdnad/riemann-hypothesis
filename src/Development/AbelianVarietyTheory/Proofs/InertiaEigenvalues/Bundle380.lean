module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle180
public import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle357
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle265
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle358
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle354
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle359
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField

variable {l : ℕ} [Fact l.Prime]

theorem norm_aeval_of_norm_eq (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X]) (hp : p ≠ 0)
    (hd : p.natDegree < N) : ∃ n : ℤ, ‖aeval π p‖ = (l : ℝ) ^ ((n : ℝ) / (N : ℝ)) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have key : ∀ i ∈ p.support, ∃ n : ℤ,
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0
    refine ⟨n, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, hn⟩ := key i hi
    obtain ⟨m, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_self _)]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs] at h6
  obtain ⟨i, hi, hi'⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.2 hp)
    (fun i => ‖p.coeff i • π ^ i‖₊)
  obtain ⟨n, hn⟩ := key i hi
  refine ⟨n * N - i, ?_⟩
  have h7 : ‖aeval π p‖ = ‖p.coeff i • π ^ i‖ := congrArg NNReal.toReal (h6.trans hi')
  rw [h7, hn]
  congr 1
  push_cast
  field_simp

theorem norm_of_mem_Ks : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (j : ℕ), 1 ≤ j →
    ∀ x : Om l, x ∈ Ks K j → x ≠ 0 →
      ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ ((n : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  intro l _ K j hj x hx hx0
  have hlp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [Ks_eq_restrictScalars K j ζ hζ, IntermediateField.mem_restrictScalars] at hx
  have hx' : x ∈ Algebra.adjoin ↥(K0 K) {ζ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨q, hq⟩ := hx'
  have hcast : ((Nat.totient (l ^ j) : ℕ) : ℝ) = (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1) := by
    rw [Nat.totient_prime_pow hlp hj]
    push_cast [Nat.cast_sub hlp.one_le]
    rfl
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ)) := by
    have h1 := norm_primitiveRoot_sub_one l j hj (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    rw [hcast, ← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  set r := q %ₘ minpoly ↥(K0 K) ζ with hr
  have hrx : aeval ζ r = x := by
    rw [hr, aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)]
    exact hq
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, map_zero] at hrx
    exact hx0 hrx.symm
  have hdeg : r.natDegree < Nat.totient (l ^ j) := by
    have := natDegree_lt_natDegree hr0 (degree_modByMonic_lt q (minpoly.monic hint))
    rwa [minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, natDegree_cyclotomic] at this
  obtain ⟨n, hn⟩ := norm_aeval_of_norm_eq K _ (ζ - 1) hnorm (Polynomial.taylor 1 r)
    (fun h => hr0 (Polynomial.taylor_injective 1 (by rw [h, map_zero]))) (by rwa [Polynomial.natDegree_taylor])
  refine ⟨n, ?_⟩
  rw [← hcast, ← hn, ← hrx, Polynomial.taylor_apply, aeval_comp]
  simp

end GlobalTheory.Cyc
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.QDDeg

theorem locDeg_sum_le_and_ge : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := by
  intro D h1 i hi s hs
  have hl : (D.nd.l i).Prime := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.hyp.1
    · exact D.host.hyp.2.1
  have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
    rcases hi with h | h <;> simp [h]
  obtain ⟨hpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le D.host.E (D.nd.l i) hl
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  refine ⟨(hsum s hs).trans hfr.le, ?_⟩
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun w hw => ?_
  have he : w.asIdeal.ramificationIdx ℤ = 2 := ((h1 _ hmem).2 w (hs w hw)).1
  have hp := hpos w
  unfold Formalism.MainNotions.N.locDeg at hp ⊢
  rw [he] at hp ⊢
  omega

end GlobalTheory.Proof.QDDeg
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.TypePrimesQD

theorem not_split_of_ram_two (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hram : ∀ v ∈ placesOver E l, v.asIdeal.ramificationIdx ℤ = 2)
    (hsplit : (placesOver E l).ncard = Module.finrank ℚ E) : False := by
  classical
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : (placesOver E l).Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨hdpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le E l hl
  have hle := hsum hfin.toFinset (fun v hv => hfin.mem_toFinset.1 hv)
  have hge : ∑ v ∈ hfin.toFinset, 2 ≤ ∑ v ∈ hfin.toFinset, Formalism.MainNotions.N.locDeg E v := by
    refine Finset.sum_le_sum fun v hv => ?_
    have h2 := hram v (hfin.mem_toFinset.1 hv)
    have hp := hdpos v
    unfold Formalism.MainNotions.N.locDeg at hp ⊢
    rw [h2] at hp ⊢
    omega
  rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hsplit] at hge
  omega

theorem qd_ne_typePrimes : ∀ (D : D7), Formalism.MainNotions.EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc,
    (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := by
  intro D h1 i hl
  have key : ∀ k : Fin 2, D.nd.l i ≠ D.host.g k := by
    intro k hk
    have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
      rcases hl with h | h <;> simp [h]
    have hram := (h1 _ hmem).2
    rw [hk] at hram
    exact not_split_of_ram_two D.host.E (D.host.g k) (D.host.g_prime k)
      (fun v hv => (hram v hv).1) (D.nd.g_split k)
  exact ⟨key 0, key 1⟩

end GlobalTheory.Proof.TypePrimesQD
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.inertiaCocycleBlock_length_le_of_quadraticRelation : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  first | exact @GlobalTheory.Cut.QuadN.main | exact GlobalTheory.Cut.QuadN.main | (intros; apply GlobalTheory.Cut.QuadN.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.inertia_restriction_polynomial_condition_second_form : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v ∈ D.nd.S i, PolyAt i r Xs π v → ∀ c : Fin D.R.t, resIne i (cocChi i r S Xs c) v = ⊥ := by
  first | exact @GlobalTheory.Cut.PolynomialInertiaAction.main | exact GlobalTheory.Cut.PolynomialInertiaAction.main | (intros; apply GlobalTheory.Cut.PolynomialInertiaAction.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.length_heckeValueIdeal_le_determinant_bound : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → π ∈ D.nd.Z i → NoChiOff i r Xs → Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Xs π) ≤ Module.length (D.nd.O i) ↥(cocRho i r S Xs) + ∑ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Xs c) := by
  first | exact @GlobalTheory.CutDetOrd.main | exact GlobalTheory.CutDetOrd.main | (intros; apply GlobalTheory.CutDetOrd.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev gl (g : Br.G D.nbr i w hw) : GE D.nd := ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)

def vecL {a : ℕ} (v : Fin a → Fin D.R.nV → KK D.nd i) : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw :=
  fun b j => Br.toLLK (D.nbr i w hw) (v b j)

def spanL {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule (Br.LL D.nbr i w hw) (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) :=
  Submodule.span _ (vecL i w hw '' (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)))

theorem loc_mulVec {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (v : Fin k → KK D.nd i) :
    (Br.loc D.nbr i w hw M g).mulVec (fun j => Br.toLLK (D.nbr i w hw) (v j)) =
      fun j => Br.toLLK (D.nbr i w hw) ((mapM (toK D.nd i) M (gl i w hw g)).mulVec v j) := by
  funext j
  rw [RingHom.map_mulVec]
  congr 1
  ext p q
  simp [Br.loc, Br.locM, Br.locO, mapM, Br.iota, Br.toLLK_alg]
  rfl

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))

theorem contTw (hr : GoodR D.nd i r) (x : ↥Xs) (v : Fin D.R.nV → Br.LL D.nbr i w hw) :
    Continuous fun g => (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec v :=
  (GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.T.twisted_dual_families_continuous D i r hr x).1).matrix_mulVec continuous_const

def sumG (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  GRep.sum (fun x : ↥Xs => Br.loc D.nbr i w hw (rTwO D.nd i r x)) (contTw i w hw r Xs hr) x

def actK {a : ℕ} (x : Fin a → ↥Xs) (γ : GE D.nd) (v : Fin a → Fin D.R.nV → KK D.nd i) :
    Fin a → Fin D.R.nV → KK D.nd i :=
  fun b => (mapM (toK D.nd i) (rTwO D.nd i r (x b)) γ).mulVec (v b)

theorem sumG_vecL (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs) (g : Br.G D.nbr i w hw)
    (v : Fin a → Fin D.R.nV → KK D.nd i) :
    (sumG i w hw r Xs hr x).ρ g (vecL i w hw v) = vecL i w hw (actK i r Xs x (gl i w hw g) v) := by
  funext b
  exact loc_mulVec i w hw _ g (v b)

theorem spanL_stable (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) :
    ∀ g, ∀ u ∈ spanL i w hw Y, (sumG i w hw r Xs hr x).ρ g u ∈ spanL i w hw Y := by
  intro g u hu
  have h : spanL i w hw Y ≤ (spanL i w hw Y).comap ((sumG i w hw r Xs hr x).ρ g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    show (sumG i w hw r Xs hr x).ρ g (vecL i w hw y) ∈ spanL i w hw Y
    rw [sumG_vecL]
    exact Submodule.subset_span ⟨_, hst _ y hy, rfl⟩
  exact h hu

def XG (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  (sumG i w hw r Xs hr x).sub (spanL i w hw Y) (spanL_stable i w hw r Xs hr x Y hst)

def latY {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule (Br.OLL D.nbr i w hw) ↥(spanL i w hw Y) :=
  Submodule.span _ {u | (u : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) ∈ vecL i w hw '' (Y : Set _)}

def yfun {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (E : Fin a → Fin D.R.nV → KK D.nd i) (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (g : Br.G D.nbr i w hw) : ↥(spanL i w hw Y) :=
  ⟨vecL i w hw (actK i r Xs x (gl i w hw g) E - E), Submodule.subset_span ⟨_, hE _, rfl⟩⟩

end GlobalTheory.Pass.LocDual.OneX

end
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.wachHypothesis_crystallineLattices : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm → DeltaInvariantLattices.ConclusionE D HW F → CrysOnCond D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie := by
  first | exact @GlobalTheory.WachHyp.hypW_crystalline | exact GlobalTheory.WachHyp.hypW_crystalline | (intros; apply GlobalTheory.WachHyp.hypW_crystalline <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.padicIntegers_finiteExt_goodCoefficientRing : LitGoodO := by
  first | exact @GlobalTheory.LitGood.litGoodO | exact GlobalTheory.LitGood.litGoodO | (intros; apply GlobalTheory.LitGood.litGoodO <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.tame_descent_conditions_every_localisation : ∀ (D : D7) (i : D.nd.Loc), TameCharacterConditions D i ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := by
  first | exact @GlobalTheory.TameDesign.main | exact GlobalTheory.TameDesign.main | (intros; apply GlobalTheory.TameDesign.main <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.decW_of_matrix_criterion : ∀ (S : Sit) (E : S.Comparison₂), (∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) S.W.EE), (∀ y : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (y i) = y i) → ∃ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) ∧ ∀ i, ∃ e, y i - (∑ k, E.ioE (Pm i k) * S.φR (z k) - z i) = E.ioE e) ∧ (∀ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) → (∀ i, ∃ e, ∑ k, E.ioE (Pm i k) * S.φR (z k) - z i = E.ioE e) → ∀ i, ∃ e, z i = E.ioE e)) → DecW S E := by
  first | exact @GlobalTheory.DecomplRed.decW_of_matrix | exact GlobalTheory.DecomplRed.decW_of_matrix | (intros; apply GlobalTheory.DecomplRed.decW_of_matrix <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.wach_lattice_sandwich_Ainf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (N : Submodule (LetA S.O S.n) (S.W.DD T)), WClauses S E T M0 h0 N → (∀ y ∈ N, (S.inclR (E.io S.W.X)) ^ M0 • E.jD T y ∈ LinearMap.range (TWincl S.inclR T)) ∧ ∀ t : ↥T.L.T, (S.inclR (E.io S.W.X)) ^ h0 • ((1 : S.RW) ⊗ₜ[S.O] t) ∈ Submodule.span S.O {z : TW S.RW T | ∃ (a : S.RA), ∃ y ∈ N, z = S.inclR a • E.jD T y} := by
  first | exact @GlobalTheory.Sandwich.sandwich | exact GlobalTheory.Sandwich.sandwich | (intros; apply GlobalTheory.Sandwich.sandwich <;> assumption)
end
