module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle002
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedGroupLike
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle214
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle212
public import Mathlib.Tactic.Continuity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle213
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle216
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Unramified.Finite

@[expose] public section

section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_algHom_algebraicClosure_apply_eq_pow :
    ∀ (Ω : Type) [Field Ω] (K0 : Subfield Ω) (x : Ω), Transcendental K0 x → ∀ m : ℕ, 0 < m →
      ∃ τ : Ω →ₐ[K0] AlgebraicClosure Ω, τ x = algebraMap Ω (AlgebraicClosure Ω) x ^ m := by
  intro Ω _ K0 x hx m hm
  classical
  have h1 : AlgebraicIndepOn K0 id ({x} : Set Ω) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let i₀ : s := ⟨x, hxs rfl⟩
  have h2 := (algebraicIndependent_update_pow hs.1 i₀ hm).map'
    (f := IsScalarTower.toAlgHom K0 Ω (AlgebraicClosure Ω))
    (algebraMap Ω (AlgebraicClosure Ω)).injective
  obtain ⟨j, hj⟩ := GlobalTheory.GenericValue.exists_algHom_of_isTranscendenceBasis hs h2
  exact ⟨j, by simpa [i₀] using hj i₀⟩

end GlobalTheory
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_twisted_groupLike' : ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H] [Bialgebra K H] [Coalgebra.IsCocomm K H] [Module.Finite K H] (c : H ⊗[K] H), IsUnit c → c ⊗ₜ[K] (1 : H) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) c = (Algebra.TensorProduct.assoc K K K H H H).symm ((1 : H) ⊗ₜ[K] c * Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) c) → Algebra.TensorProduct.comm K H H c = c → ∃ u : H, u ≠ 0 ∧ c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u := by
  first | exact @GlobalTheory.exists_twisted_groupLike | exact GlobalTheory.exists_twisted_groupLike | (intros; apply GlobalTheory.exists_twisted_groupLike <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b c : B, b * c - 1 ∈ Ideal.span {f} → ∃ r : B, b - r ^ q ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed) | (exact GlobalTheory.exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed) | (intros; apply GlobalTheory.exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed  <;> assumption)
end

section

open GlobalTheory.EtC

open TensorProduct

namespace GlobalTheory

theorem isAlgClosed_fractionRing_atPrime_of_etale : ∀ (T E : Type) [CommRing T] [IsDomain T]
    [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime]
    [IsDomain (Localization.AtPrime P)],
    IsAlgClosed (FractionRing T) → IsAlgClosed (FractionRing (Localization.AtPrime P)) := by
  intro T E _ _ _ _ _ P _ _ hK
  haveI : Module.Flat T (Localization.AtPrime P) := Module.Flat.trans T E (Localization.AtPrime P)
  have hTEp : Function.Injective (algebraMap T (Localization.AtPrime P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    by_contra h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := (Localization.AtPrime P))
      (mem_nonZeroDivisors_of_ne_zero h0)
    apply one_ne_zero (α := (Localization.AtPrime P))
    apply hreg
    simp [Algebra.smul_def, ht]
  have hTL : Function.Injective (algebraMap T (FractionRing (Localization.AtPrime P))) := by
    rw [IsScalarTower.algebraMap_eq T (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]
    exact (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))).comp hTEp
  haveI : FaithfulSMul T (FractionRing (Localization.AtPrime P)) := (faithfulSMul_iff_algebraMap_injective T (FractionRing (Localization.AtPrime P))).2 hTL
  letI : Algebra (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.liftAlgebra T (FractionRing (Localization.AtPrime P))
  haveI : IsScalarTower T (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.isScalarTower_liftAlgebra T (FractionRing (Localization.AtPrime P))
  haveI : Module.Finite (FractionRing T) ((FractionRing T) ⊗[T] E) := Algebra.FormallyUnramified.finite_of_free (FractionRing T) ((FractionRing T) ⊗[T] E)
  let φ : (FractionRing T) ⊗[T] E →ₐ[(FractionRing T)] (FractionRing (Localization.AtPrime P)) := Algebra.TensorProduct.lift (Algebra.ofId (FractionRing T) (FractionRing (Localization.AtPrime P)))
    (IsScalarTower.toAlgHom T E (FractionRing (Localization.AtPrime P))) (fun _ _ => Commute.all _ _)
  have hE : ∀ e : E, IsIntegral (FractionRing T) (algebraMap E (FractionRing (Localization.AtPrime P)) e) := by
    intro e
    have h1 : IsIntegral (FractionRing T) ((1 : (FractionRing T)) ⊗ₜ[T] e) := Algebra.IsIntegral.isIntegral _
    have h2 := h1.map φ
    simpa [φ] using h2
  have hEp : ∀ x : (Localization.AtPrime P), algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) x ∈ algebraicClosure (FractionRing T) (FractionRing (Localization.AtPrime P)) := by
    intro x
    obtain ⟨⟨e, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have hs : algebraMap E (FractionRing (Localization.AtPrime P)) s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))).2
        (IsLocalization.map_units (Localization.AtPrime P) s).ne_zero
    have heq : algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (IsLocalization.mk' (Localization.AtPrime P) e s) =
        algebraMap E (FractionRing (Localization.AtPrime P)) e / algebraMap E (FractionRing (Localization.AtPrime P)) s := by
      rw [eq_div_iff hs, IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) e,
        IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (s : E), ← map_mul, IsLocalization.mk'_spec]
    simp only at heq ⊢
    rw [heq]
    exact div_mem (mem_algebraicClosure_iff.2 (hE e).isAlgebraic)
      (mem_algebraicClosure_iff.2 (hE s).isAlgebraic)
  have hL : (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))).IsIntegral := by
    intro z
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (Localization.AtPrime P) z
    exact (mem_algebraicClosure_iff.1 (div_mem (hEp x) (hEp y))).isIntegral
  haveI := hK
  exact IsAlgClosed.of_ringEquiv (FractionRing T) (FractionRing (Localization.AtPrime P))
    (RingEquiv.ofBijective (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))) (IsAlgClosed.ringHom_bijective_of_isIntegral _ hL))

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem exists_pow_eq_of_kaehler_D_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (K : Type) [Field K] [Algebra k K] (f : K), KaehlerDifferential.D k K f = 0 → ∃ h : K, h ^ p = f := by
  intro p hp k _ _ hk K _ _ f hf
  by_contra hne
  have hK : (p : K) = 0 := by
    have := congrArg (algebraMap k K) hk
    simpa using this
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 hK
  let F : Subfield K := (frobenius K p).fieldRange
  have hF : ∀ y : K, y ^ p ∈ F := fun y => ⟨y, by simp [frobenius_def]⟩
  have hfF : f ∉ F := by
    rintro ⟨h, hh⟩
    exact hne ⟨h, by simpa [frobenius_def] using hh⟩
  obtain ⟨L, hFL, hfL, htop⟩ := GlobalTheory.T.exists_maximal_subfield_missing_elem_expOne p K F hF f hfF
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_derivation_eq_one_of_pow_mem' p K L f hfL (hFL (hF f)) htop
  have hkL : ∀ a : k, algebraMap k K a ∈ L := by
    intro a
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a hp.out.pos
    rw [← hb, map_pow]
    exact hFL (hF _)
  have hD0 : ∀ a : k, D (algebraMap k K a) = 0 := fun a =>
    D.map_algebraMap (⟨_, hkL a⟩ : L)
  let D' : Derivation k K K := Derivation.mk'
    { toFun := D
      map_add' := fun x y => map_add D x y
      map_smul' := fun a x => by
        simp only [Algebra.smul_def, RingHom.id_apply, Derivation.leibniz, hD0, smul_eq_mul]
        simp }
    (fun a b => D.leibniz a b)
  have h1 : D' f = 1 := hD
  have h2 := D'.liftKaehlerDifferential_comp_D f
  rw [hf, map_zero, h1] at h2
  exact zero_ne_one h2

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.SplitSpread

open MvPolynomial

abbrev Mon (σ : Type) (D : ℕ) := {m : σ →₀ ℕ // m.degree ≤ D}

instance instFiniteMon (σ : Type) [Finite σ] (D : ℕ) : Finite (Mon σ D) :=
  (Finsupp.finite_of_degree_le (σ := σ) D).to_subtype

noncomputable instance instFintypeMon (σ : Type) [Finite σ] (D : ℕ) : Fintype (Mon σ D) :=
  Fintype.ofFinite _

abbrev Var (σ : Type) (D : ℕ) := (Bool × Mon σ D) ⊕ (Bool × σ) ⊕ Bool

theorem sum_eq_degree {σ : Type} (s : σ →₀ ℕ) : (s.sum fun _ e => e) = s.degree := rfl

theorem hom_eval {R S τ : Type} [CommSemiring R] [CommSemiring S] (h : R →+* S) (x : τ → R)
    (W : MvPolynomial τ R) : h (eval x W) = MvPolynomial.eval (h ∘ x) (MvPolynomial.map h W) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, RingHom.comp_id]

variable {σ : Type} [Finite σ] (A : Type) [CommRing A] (D : ℕ)

noncomputable def gen (b : Bool) : MvPolynomial σ (MvPolynomial (Var σ D) A) :=
  ∑ m : Mon σ D, monomial m.1 (X (Sum.inl (b, m)))

noncomputable def eqs (f g : MvPolynomial σ A) :
    ((σ →₀ ℕ) ⊕ Bool ⊕ Bool) → MvPolynomial (Var σ D) A
  | Sum.inl n => AddMonoidAlgebra.coeff (gen A D true * gen A D false - MvPolynomial.map C f) n
  | Sum.inr (Sum.inl b) => MvPolynomial.eval (fun i => X (Sum.inr (Sum.inl (b, i)))) (gen A D b)
  | Sum.inr (Sum.inr b) =>
      X (Sum.inr (Sum.inr b)) * MvPolynomial.eval (fun i => X (Sum.inr (Sum.inl (b, i)))) (MvPolynomial.map C g) - 1

variable {A D}

theorem map_gen {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k) (b : Bool) :
    MvPolynomial.map (eval₂Hom ψ z) (gen A D b) = ∑ m : Mon σ D, monomial m.1 (z (Sum.inl (b, m))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gen, map_sum, map_monomial]

theorem totalDegree_sum_le {k : Type} [CommRing k] (c : Mon σ D → k) :
    (∑ m : Mon σ D, monomial m.1 (c m)).totalDegree ≤ D := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
  exact (totalDegree_monomial_le _ _).trans m.2

theorem sum_coeff {k : Type} [CommRing k] (p : MvPolynomial σ k) (hp : p.totalDegree ≤ D) :
    ∑ m : Mon σ D, monomial m.1 (AddMonoidAlgebra.coeff p m.1) = p := by
  classical
  ext n
  simp only [coeff_sum, coeff_monomial]
  by_cases hn : n.degree ≤ D
  · rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · intro m _ hm
      rw [if_neg]
      intro h; exact hm (Subtype.ext h)
    · simp
  · rw [Finset.sum_eq_zero]
    · by_contra h
      exact hn ((sum_eq_degree n ▸ le_totalDegree (mem_support_iff.mpr (Ne.symm h))).trans hp)
    · intro m _
      rw [if_neg]
      rintro rfl; exact hn m.2

end GlobalTheory.SplitSpread

namespace GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] {A : Type} [CommRing A] {D : ℕ}

noncomputable def spec {k : Type} [CommRing k] (z : Var σ D → k) (b : Bool) : MvPolynomial σ k :=
  ∑ m : Mon σ D, monomial m.1 (z (Sum.inl (b, m)))

theorem eval_eqs_coeff {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (n : σ →₀ ℕ) :
    eval₂ ψ z (eqs A D f g (Sum.inl n)) = AddMonoidAlgebra.coeff (spec z true * spec z false - MvPolynomial.map ψ f) n := by
  rw [← coe_eval₂Hom]
  simp only [eqs]
  rw [← MvPolynomial.coeff_map, map_sub, map_mul, map_gen, map_gen, MvPolynomial.map_map,
    eval₂Hom_comp_C]
  rfl

theorem eval_eqs_point {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (b : Bool) :
    eval₂ ψ z (eqs A D f g (Sum.inr (Sum.inl b))) =
      MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i)))) (spec z b) := by
  rw [← coe_eval₂Hom]
  simp only [eqs]
  rw [hom_eval, map_gen]
  congr 2 <;> (ext i; simp)

theorem eval_eqs_inv {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (b : Bool) :
    eval₂ ψ z (eqs A D f g (Sum.inr (Sum.inr b))) =
      z (Sum.inr (Sum.inr b)) *
        MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i)))) (MvPolynomial.map ψ g) - 1 := by
  simp only [eqs, eval₂_sub, eval₂_mul, eval₂_X, eval₂_one]
  rw [← coe_eval₂Hom, hom_eval, MvPolynomial.map_map, eval₂Hom_comp_C]
  congr 4 <;> (ext i; simp)
end GlobalTheory.SplitSpread

namespace GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] {A : Type} [CommRing A]

def Bad (f g : MvPolynomial σ A) (D : ℕ) (k : Type) [Field k] (ψ : A →+* k) : Prop :=
  ∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧
    u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧
      MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧
      MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0

theorem bad_iff (f g : MvPolynomial σ A) (D : ℕ) (k : Type) [Field k] (ψ : A →+* k) :
    (∃ z : Var σ D → k, ∀ j, eval₂ ψ z (eqs A D f g j) = 0) ↔ Bad f g D k ψ := by
  constructor
  · rintro ⟨z, hz⟩
    have hinv : ∀ b, MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i))))
        (MvPolynomial.map ψ g) ≠ 0 := by
      intro b h0
      have := hz (Sum.inr (Sum.inr b))
      rw [eval_eqs_inv, h0] at this
      simp at this
    refine ⟨spec z true, spec z false, totalDegree_sum_le _, totalDegree_sum_le _, ?_,
      fun i => z (Sum.inr (Sum.inl (true, i))), fun i => z (Sum.inr (Sum.inl (false, i))),
      ?_, hinv true, ?_, hinv false⟩
    · ext n
      have := hz (Sum.inl n)
      rw [eval_eqs_coeff, MvPolynomial.coeff_sub, sub_eq_zero] at this
      exact this
    · have := hz (Sum.inr (Sum.inl true)); rwa [eval_eqs_point] at this
    · have := hz (Sum.inr (Sum.inl false)); rwa [eval_eqs_point] at this
  · rintro ⟨u, v, hu, hv, huv, P, Q, hPu, hPg, hQv, hQg⟩
    let z : Var σ D → k := Sum.elim (fun p => AddMonoidAlgebra.coeff (if p.1 then u else v) p.2.1)
      (Sum.elim (fun p => if p.1 then P p.2 else Q p.2)
        (fun b => (MvPolynomial.eval (if b then P else Q) (MvPolynomial.map ψ g))⁻¹))
    have hs : ∀ b, spec z b = if b then u else v := by
      intro b
      cases b
      · exact sum_coeff v hv
      · exact sum_coeff u hu
    refine ⟨z, ?_⟩
    rintro (n | b | b)
    · rw [eval_eqs_coeff, hs, hs]
      simp [huv]
    · rw [eval_eqs_point, hs]
      cases b <;> simpa [z]
    · rw [eval_eqs_inv]
      cases b
      · simp only [z, Sum.elim_inr, Bool.false_eq_true, if_false]
        exact sub_eq_zero.mpr (inv_mul_cancel₀ hQg)
      · simp only [z, Sum.elim_inr, if_true]
        exact sub_eq_zero.mpr (inv_mul_cancel₀ hPg)

end GlobalTheory.SplitSpread

theorem GlobalTheory.splitting_absence_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (D : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map φ f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map φ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map φ g) ≠ 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ (∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0) := by
  intro A _ σ _ f g D Ω _ _ φ hbad
  have h0 : ¬ ∃ z : GlobalTheory.SplitSpread.Var σ D → Ω, ∀ j,
      MvPolynomial.eval₂ φ z (GlobalTheory.SplitSpread.eqs A D f g j) = 0 := by
    rw [GlobalTheory.SplitSpread.bad_iff]; exact hbad
  obtain ⟨a, I, ha, hI, hk⟩ := GlobalTheory.T.no_common_zero_spreads_constructible_nbhd A _ _ (GlobalTheory.SplitSpread.eqs A D f g) Ω φ h0
  refine ⟨a, I, ha, hI, fun k _ ψ hψa hψI hb => hk k ψ hψa hψI ?_⟩
  exact (GlobalTheory.SplitSpread.bad_iff f g D k ψ).mpr hb
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GalSec

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

abbrev LCRing (k : ℕ) : Type := LocallyConstant (Fin k → (Ω ≃ₐ[K] Ω)) Ω

theorem isLocallyConstant_apply [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) (a : Ω) :
    IsLocallyConstant (fun g : Fin k → (Ω ≃ₐ[K] Ω) => g i a) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have hfd : FiniteDimensional K (IntermediateField.adjoin K {a}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  have hopen : IsOpen {σ : Ω ≃ₐ[K] Ω | (g₀ i)⁻¹ * σ ∈ (IntermediateField.adjoin K {a}).fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
  have hmem : ∀ᶠ g in nhds g₀, g i ∈ {σ : Ω ≃ₐ[K] Ω | (g₀ i)⁻¹ * σ ∈ (IntermediateField.adjoin K {a}).fixingSubgroup} :=
    ((continuous_apply i).tendsto g₀).eventually (hopen.mem_nhds (by simp [one_mem]))
  filter_upwards [hmem] with g hg
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a (IntermediateField.mem_adjoin_simple_self K a)
  have h2 := congrArg (g₀ i) h1
  simpa [AlgEquiv.mul_apply] using h2

def coord [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) : Ω →+* LCRing K Ω k where
  toFun a := ⟨fun g => g i a, isLocallyConstant_apply K Ω k i a⟩
  map_one' := LocallyConstant.ext fun g => by simp
  map_mul' a b := LocallyConstant.ext fun g => by simp
  map_zero' := LocallyConstant.ext fun g => by simp
  map_add' a b := LocallyConstant.ext fun g => by simp

@[simp] theorem coord_apply [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) (a : Ω) (g : Fin k → (Ω ≃ₐ[K] Ω)) :
    coord K Ω k i a g = g i a := rfl

def legHom [Algebra.IsAlgebraic K Ω] (k : ℕ) : Fin (k + 1) → (Ω →+* LCRing K Ω k) :=
  Fin.cases LocallyConstant.constRingHom (coord K Ω k)

def baseHom (k : ℕ) : K →+* LCRing K Ω k := LocallyConstant.constRingHom.comp (algebraMap K Ω)

theorem legHom_comp [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin (k + 1)) :
    (legHom K Ω k i).comp (algebraMap K Ω) = baseHom K Ω k := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · ext c g
    simp [legHom, baseHom]

def tailG (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) : Fin k → (Ω ≃ₐ[K] Ω) := fun i => (σ 0)⁻¹ * σ i.succ

def ptHom (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) : LCRing K Ω k →+* Ω :=
  ((σ 0 : Ω ≃ₐ[K] Ω) : Ω →+* Ω).comp (LocallyConstant.evalRingHom (tailG K Ω k σ))

theorem ptHom_legHom [Algebra.IsAlgebraic K Ω] (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) (i : Fin (k + 1)) :
    (ptHom K Ω k σ).comp (legHom K Ω k i) = ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · ext a; simp [ptHom, legHom]
  · ext a; simp [ptHom, legHom, tailG, AlgEquiv.mul_apply]

end GlobalTheory.EtC.GalSec

end
end

section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' : ∀ (k K B : Type) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B] (e : K ⊗[k] B), IsIdempotentElem e → e = 0 ∨ e = 1 := by
  first | exact @GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable | exact GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable | (intros; apply GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_primitive_monic_separable_specialization' : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℚ x → ∀ (J : Type) [Finite J] (e : J → K), ∃ (P : Polynomial (MvPolynomial (Fin D) ℚ)) (ψ : AdjoinRoot P →ₐ[ℚ] K) (g : K) (c : Fin D → ℚ), P.Monic ∧ Function.Injective ψ ∧ (∀ i, ψ (AdjoinRoot.of P (MvPolynomial.X i)) = x i) ∧ g ≠ 0 ∧ (∀ j, g * e j ∈ ψ.range) ∧ (P.map (MvPolynomial.eval c)).Separable := by
  first | exact @GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization | exact GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization | (intros; apply GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.normalisation_dvr_tensor_separable_finite : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra S D] [Module.Finite S D] [FaithfulSMul S D],
    Module.Finite D (integralClosure D (TensorProduct S D L)) := by
  first | exact @GlobalTheory.NormFin.main | exact GlobalTheory.NormFin.main | (intros; apply GlobalTheory.NormFin.main <;> assumption)
end
