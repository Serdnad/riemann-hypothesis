module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Sigma
public import Mathlib.Order.Sum.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Unramified.Locus
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle015
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
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
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.Instances.AddCircle.Real
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex : ∀ (s : ℕ) (t : Fin s → ℕ), StrictMono fun c : Fin (∑ a, t a) => (toLex (finSigmaFinEquiv.symm c) : Σₗ a, Fin (t a)) := by
  first | exact @GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex | exact GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex | (intros; apply GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex <;> assumption)
end

section

open GlobalTheory.Cong

namespace GlobalTheory

theorem exists_matrix_no_invariant_subspace :
    ∀ (κ : Type) [Field κ] [Finite κ] (a : ℕ), 1 ≤ a → ∃ B : Matrix (Fin a) (Fin a) κ,
      ∀ W : Submodule κ (Fin a → κ), (∀ v ∈ W, B.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro κ _ _ a ha
  obtain ⟨p, hp⟩ := CharP.exists κ
  haveI : Fact p.Prime := ⟨CharP.char_is_prime κ p⟩
  haveI : NeZero a := ⟨by omega⟩
  let L := FiniteField.Extension κ p a
  let b : Module.Basis (Fin a) κ L :=
    Module.finBasisOfFinrankEq κ L (FiniteField.finrank_extension κ p a)
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Lˣ)
  let β : L := (g : L)
  refine ⟨LinearMap.toMatrix b b (Algebra.lmul κ L β), fun W hW => ?_⟩

  let e := b.equivFun
  have key : ∀ x : L, (LinearMap.toMatrix b b (Algebra.lmul κ L β)).mulVec (e x) = e (β * x) := by
    intro x
    simpa [e, Module.Basis.equivFun_apply] using LinearMap.toMatrix_mulVec_repr b b (Algebra.lmul κ L β) x

  have stepβ : ∀ x : L, e x ∈ W → e (β * x) ∈ W := fun x hx => key x ▸ hW _ hx
  have stepPow : ∀ n : ℕ, ∀ x : L, e x ∈ W → e (β ^ n * x) ∈ W := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have := stepβ _ (ih x hx)
      simpa [pow_succ', mul_assoc] using this
  have stepAll : ∀ y x : L, e x ∈ W → e (y * x) ∈ W := by
    intro y x hx
    by_cases hy : y = 0
    · subst hy; simpa using W.zero_mem
    · obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg (Units.mk0 y hy))
      have : β ^ n = y := by
        have := congrArg (fun u : Lˣ => (u : L)) hn
        simpa [β] using this
      rw [← this]; exact stepPow n x hx
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hx0 : e.symm v ≠ 0 := by
      intro h0; apply hv0; simpa using congrArg e h0
    have hxW : e (e.symm v) ∈ W := by simpa using hvW
    rw [eq_top_iff]
    intro u _
    have := stepAll (e.symm u * (e.symm v)⁻¹) (e.symm v) hxW
    rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at this
    simpa using this

end GlobalTheory
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lexSum_splitFirstBlock_strictMono : ∀ (s : ℕ) (t : Fin (s + 1) → ℕ), StrictMono fun c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) => (Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a))) (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c) : Σₗ a, Fin (t a)) := by
  first | exact @GlobalTheory.lexSumSplit_strictMono | exact GlobalTheory.lexSumSplit_strictMono | (intros; apply GlobalTheory.lexSumSplit_strictMono <;> assumption)
end

section


theorem _root_.GlobalTheory.T.isSemisimple_of_locallyFinite_compactGroup : ∀ (K V : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), (∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) → ρ.IsSemisimpleRepresentation ∧ (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) ∧ ∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  first | exact @GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite | exact GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite | (intros; apply GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite <;> assumption)
end

section

open GlobalTheory.Cong

namespace GlobalTheory.PowerSumPoly
open MvPolynomial

theorem exists_intPoly_psum_eq : ∀ a n : ℕ, 1 ≤ n → ∃ P : MvPolynomial (Fin (a + 1)) ℤ, ∀ s : Multiset ℂ,
    Multiset.card s = a → MvPolynomial.aeval (fun j : Fin (a + 1) => s.esymm j) P = (s.map (· ^ n)).sum := by
  intro a n _
  obtain ⟨Q, hQ⟩ := esymmAlgHom_surjective ℤ (σ := Fin a) (n := a) (by simp)
    ⟨psum (Fin a) ℤ n, psum_isSymmetric (Fin a) ℤ n⟩
  have hQ' : aeval (fun i : Fin a => esymm (Fin a) ℤ (i + 1)) Q = psum (Fin a) ℤ n := by
    rw [← esymmAlgHom_apply, hQ]
  refine ⟨rename Fin.succ Q, fun s hs => ?_⟩
  set f : Fin a → ℂ := fun i => s.toList[(i : ℕ)]'(by simp [hs]) with hf
  have hsf : (Finset.univ.val.map f) = s := by
    rw [Fin.univ_val_map]
    conv_rhs => rw [← Multiset.coe_toList s]
    congr 1
    apply List.ext_getElem (by simp [hs])
    intro i h1 h2
    simp [f]
  have key : aeval f (aeval (fun i : Fin a => esymm (Fin a) ℤ (i + 1)) Q) =
      aeval (fun i : Fin a => aeval f (esymm (Fin a) ℤ (i + 1))) Q := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rw [hQ'] at key
  rw [aeval_rename]
  have lhs : (fun j : Fin (a + 1) => s.esymm j) ∘ Fin.succ = fun i : Fin a => aeval f (esymm (Fin a) ℤ (i + 1)) := by
    funext i
    simp [aeval_esymm_eq_multiset_esymm, hsf]
  rw [lhs, ← key]

  rw [psum, map_sum]
  simp only [map_pow, aeval_X]
  conv_rhs => rw [← hsf]
  simp [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

end GlobalTheory.PowerSumPoly
end

section

open GlobalTheory.Cong

namespace GlobalTheory

theorem natCast_dvd_of_pow_dvd_of_not_isUnit (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    (l : ℕ) (hl : l.Prime) (hu : ¬ IsUnit (l : R)) :
    ∀ (m k : ℕ), (l : R) ^ m ∣ (k : R) → l ^ m ∣ k := by
  intro m
  induction m with
  | zero => intro k _; simp
  | succ m ih =>
    intro k hk
    have h1 : (l : R) ∣ (k : R) := (dvd_pow_self _ (Nat.succ_ne_zero m)).trans hk
    have h2 : l ∣ k := by
      by_contra hnd
      have hcop : Nat.Coprime l k := (Nat.Prime.coprime_iff_not_dvd hl).2 hnd
      have hg := Nat.gcd_eq_gcd_ab l k
      rw [hcop] at hg
      apply hu
      obtain ⟨c, hc⟩ := h1
      refine isUnit_of_dvd_one ⟨(Nat.gcdA l k : R) + (Nat.gcdB l k : R) * c, ?_⟩
      have := congrArg (fun z : ℤ => (z : R)) hg
      simp only [Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] at this
      rw [this, hc]; ring
    obtain ⟨k', rfl⟩ := h2
    have hl0 : (l : R) ≠ 0 := by exact_mod_cast hl.ne_zero
    have hk' : (l : R) ^ m ∣ (k' : R) := by
      obtain ⟨c, hc⟩ := hk
      refine ⟨c, ?_⟩
      apply mul_left_cancel₀ hl0
      rw [Nat.cast_mul] at hc
      rw [hc]; ring
    rw [pow_succ, mul_comm]
    exact mul_dvd_mul_left l (ih k' hk')

theorem exists_addHom_zmod_pow_one_of_not_isUnit :
    ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (l m : ℕ), l.Prime → ¬ IsUnit (l : R) →
      ∃ φ : R →+ ZMod (l ^ m), φ 1 = 1 ∧ ∀ x, φ ((l : R) ^ m * x) = 0 := by
  intro R _ _ _ l m hl hu
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set I : Ideal R := Ideal.span {(l : R) ^ m} with hI
  have hlI : (((l ^ m : ℕ) : ℤ) : R ⧸ I) = 0 := by
    rw [Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem,
      hI, Nat.cast_pow]
    exact Ideal.subset_span rfl
  let f : ZMod (l ^ m) →+ R ⧸ I := ZMod.lift (l ^ m) ⟨Int.castAddHom (R ⧸ I), by
    simpa using hlI⟩
  have hf_nat : ∀ k : ℕ, f (k : ZMod (l ^ m)) = (k : R ⧸ I) := by
    intro k
    have := ZMod.lift_coe (l ^ m) ⟨Int.castAddHom (R ⧸ I), by simpa using hlI⟩ (k : ℤ)
    simpa using this
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    rw [← ZMod.natCast_zmod_val x, hf_nat, ← map_natCast (Ideal.Quotient.mk I),
      Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton] at hx
    have hd := natCast_dvd_of_pow_dvd_of_not_isUnit R l hl hu m _ hx
    have hlt := ZMod.val_lt x
    have h0 : x.val = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    rw [← ZMod.natCast_zmod_val x, h0, Nat.cast_zero]
  obtain ⟨Λ, hΛ⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
    f hinj (ZMod.toAddCircle (N := l ^ m))
  have hΛ' : ∀ z, Λ (f z) = ZMod.toAddCircle z := fun z => DFunLike.congr_fun hΛ z
  have htor : ∀ q : R ⧸ I, ∃ k : ZMod (l ^ m), ZMod.toAddCircle k = Λ q := by
    intro q
    have h0 : (l ^ m) • Λ q = 0 := by
      rw [← map_nsmul]
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I), ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2, map_zero]
      rw [hI, Ideal.mem_span_singleton, Nat.cast_pow]
      exact dvd_mul_right _ _
    obtain ⟨k, -, hk⟩ := (AddCircle.nsmul_eq_zero_iff (pow_pos hl.pos _)).1 h0
    refine ⟨k, ?_⟩
    rw [ZMod.toAddCircle_natCast, ← hk, mul_one]
  choose a ha using htor
  let A : R ⧸ I →+ ZMod (l ^ m) := AddMonoidHom.mk' a (by
    intro x y
    apply ZMod.toAddCircle_injective
    rw [map_add (f := _), ha, ha, ha, map_add (f := _)])
  refine ⟨A.comp (Ideal.Quotient.mk I).toAddMonoidHom, ?_, ?_⟩
  · show a (Ideal.Quotient.mk I 1) = 1
    apply ZMod.toAddCircle_injective
    rw [ha, map_one]
    have := hΛ' 1
    rw [show (1 : ZMod (l ^ m)) = ((1 : ℕ) : ZMod (l ^ m)) by simp, hf_nat] at this
    simpa using this
  · intro x
    show a (Ideal.Quotient.mk I ((l : R) ^ m * x)) = 0
    have hmem : (l : R) ^ m * x ∈ I := by
      rw [hI]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hmem]
    apply ZMod.toAddCircle_injective
    rw [ha, map_zero, map_zero]

end GlobalTheory
end

section

open GlobalTheory.EtC

namespace GlobalTheory

theorem integralClosure_maximal_residue_algClosed : ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (D : Subring K) (m₀ : Ideal D),
    φ.range ≤ D → m₀.IsMaximal → (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) →
    (∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x)) →
    ∃ (R : Subring K) (𝔪 : Ideal R), φ.range ≤ R ∧ 𝔪.IsMaximal ∧ (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) ∧
      (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) ∧ ∀ x : K, IsIntegral R x → x ∈ R := by
  intro k K _ _ _ φ D m₀ hφD hm₀ hres hfrac
  let A := integralClosure D K
  have hφA : ∀ c : k, φ c ∈ A := fun c =>
    isIntegral_algebraMap (R := D) (x := (⟨φ c, hφD ⟨c, rfl⟩⟩ : D))
  have hker : RingHom.ker (algebraMap D A) ≤ m₀ := by
    intro d hd
    have h0 : (algebraMap D A d : K) = 0 := by rw [RingHom.mem_ker.mp hd]; rfl
    have : d = 0 := Subtype.ext h0
    simp [this]
  obtain ⟨𝔪, h𝔪max, h𝔪comap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) m₀ hker
  let φA : k →+* A := φ.codRestrict A hφA
  let ψ : k →+* A ⧸ 𝔪 := (Ideal.Quotient.mk 𝔪).comp φA
  have hcoef : ∀ d : D, algebraMap D (A ⧸ 𝔪) d ∈ Set.range ψ := by
    intro d
    obtain ⟨c, hc, hdc⟩ := hres d
    refine ⟨c, ?_⟩
    have hmem : algebraMap D A (d - ⟨φ c, hc⟩) ∈ 𝔪 := by
      rw [← Ideal.mem_comap]
      change d - ⟨φ c, hc⟩ ∈ Ideal.under D 𝔪
      rw [h𝔪comap]
      exact hdc
    change Ideal.Quotient.mk 𝔪 (φA c) = Ideal.Quotient.mk 𝔪 (algebraMap D A d)
    symm
    rw [map_sub] at hmem
    exact Ideal.Quotient.eq.mpr hmem
  have hres' : ∀ r : A, ∃ c : k, r - φA c ∈ 𝔪 := by
    intro r
    letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    letI : Algebra k (A ⧸ 𝔪) := ψ.toAlgebra
    have hr : IsIntegral D (Ideal.Quotient.mkₐ D 𝔪 r) :=
      (Algebra.IsIntegral.isIntegral (R := D) r).map (Ideal.Quotient.mkₐ D 𝔪)
    obtain ⟨f, hfm, hf⟩ := hr
    have hlift : f.map (algebraMap D (A ⧸ 𝔪)) ∈ Polynomial.lifts ψ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; rw [Polynomial.coeff_map]; exact hcoef _
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hfm.map _)
    have hint : IsIntegral k (Ideal.Quotient.mk 𝔪 r) := by
      refine ⟨q, hqm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map]
      change Polynomial.eval _ (q.map ψ) = 0
      rw [hq, ← Polynomial.eval₂_eq_eval_map]
      exact hf
    have h1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k _ h1
    exact ⟨c, Ideal.Quotient.eq.mp hc.symm⟩
  refine ⟨A.toSubring, 𝔪, ?_, h𝔪max, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩; exact hφA c
  · intro r
    obtain ⟨c, hc⟩ := hres' r
    exact ⟨c, hφA c, hc⟩
  · intro x
    obtain ⟨d, hd, hint⟩ := hfrac x
    refine ⟨⟨(d : K), Subalgebra.algebraMap_mem A d⟩, ?_, hint⟩
    intro h
    apply hd
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  · intro x hx
    have hx' : IsIntegral A x := hx
    exact isIntegral_trans x hx'

end GlobalTheory
end

section

open GlobalTheory.Cong

namespace GlobalTheory.CongChar

variable {R : Type} [CommRing R] [IsDomain R] {a : ℕ} {c : R}

theorem exists_eq_one_add_smul
    (g : (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker) :
    ∃ x : Matrix (Fin a) (Fin a) R, (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x := by
  have hg := g.2
  rw [MonoidHom.mem_ker] at hg
  have h : ∀ i j, (g.1 : Matrix (Fin a) (Fin a) R) i j - (1 : Matrix (Fin a) (Fin a) R) i j
      ∈ Ideal.span {c} := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun M : GL (Fin a) (R ⧸ Ideal.span {c}) => M.1 i j) hg
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  choose x hx using fun i j => Ideal.mem_span_singleton'.1 (h i j)
  refine ⟨Matrix.of x, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  linear_combination (-1 : R) * hx i j

theorem smul_injective (hc : c ≠ 0) {x y : Matrix (Fin a) (Fin a) R}
    (h : (1 : Matrix (Fin a) (Fin a) R) + c • x = 1 + c • y) : x = y := by
  have h' : c • x = c • y := add_left_cancel h
  ext i j
  have := congrArg (fun M => M i j) h'
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

variable {A : Type} [AddCommGroup A]

theorem one_add_smul_mul (x y : Matrix (Fin a) (Fin a) R) :
    ((1 : Matrix (Fin a) (Fin a) R) + c • x) * (1 + c • y) = 1 + c • (x + y + c • (x * y)) := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  abel

noncomputable def congChar (hc : c ≠ 0) (φ : R →+ A) (hφ : ∀ x, φ (c * x) = 0)
    (B : Matrix (Fin a) (Fin a) R) :
    (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker →*
      Multiplicative A :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (φ (B * Classical.choose (exists_eq_one_add_smul g)).trace))
    (by
      intro g h
      have hg := Classical.choose_spec (exists_eq_one_add_smul g)
      have hh := Classical.choose_spec (exists_eq_one_add_smul h)
      have hgh := Classical.choose_spec (exists_eq_one_add_smul (g * h))
      set x := Classical.choose (exists_eq_one_add_smul g)
      set y := Classical.choose (exists_eq_one_add_smul h)
      set z := Classical.choose (exists_eq_one_add_smul (g * h))
      have hz : z = x + y + c • (x * y) := by
        apply smul_injective hc
        rw [← hgh, ← one_add_smul_mul, ← hg, ← hh]
        rfl
      show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
      rw [← ofAdd_add, hz]
      congr 1
      rw [mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, map_add (f := _), map_add (f := _),
        Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hφ, add_zero])

theorem congChar_apply (hc : c ≠ 0) (φ : R →+ A) (hφ : ∀ x, φ (c * x) = 0)
    (B : Matrix (Fin a) (Fin a) R) (g) (x : Matrix (Fin a) (Fin a) R)
    (hx : (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x) :
    congChar hc φ hφ B g = Multiplicative.ofAdd (φ (B * x).trace) := by
  have hs := Classical.choose_spec (exists_eq_one_add_smul g)
  have : Classical.choose (exists_eq_one_add_smul g) = x := smul_injective hc (hs.symm.trans hx)
  simp only [congChar, MonoidHom.mk'_apply, this]

end GlobalTheory.CongChar

namespace GlobalTheory

theorem congChar_exists : ∀ (R A : Type) [CommRing R] [IsDomain R] [AddCommGroup A] (a : ℕ) (c : R), c ≠ 0 → ∀ (φ : R →+ A), (∀ x, φ (c * x) = 0) → ∀ B : Matrix (Fin a) (Fin a) R, ∃ lam : (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker →* Multiplicative A, ∀ g (x : Matrix (Fin a) (Fin a) R), (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x → lam g = Multiplicative.ofAdd (φ (B * x).trace) := by
  intro R A _ _ _ a c hc φ hφ B
  exact ⟨CongChar.congChar hc φ hφ B, fun g x hx => CongChar.congChar_apply hc φ hφ B g x hx⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.not_isUnramifiedAt_of_sq_eq_neg_prime : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  first | exact @GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg | exact GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg | (intros; apply GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_weak_approx_unit_finite_place : ∀ (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℕ), ∃ y : E, y ≠ 0 ∧ Valued.v ((y : w.adicCompletion E) * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ ∀ v ∈ S, v ≠ w → v.valuation E (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.HkFin.exists_weak_approx_unit | exact GlobalTheory.HkFin.exists_weak_approx_unit | (intros; apply GlobalTheory.HkFin.exists_weak_approx_unit <;> assumption)
end
