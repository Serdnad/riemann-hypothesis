module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial DirectSum

noncomputable section

universe u

section QuotDecomposition

variable {ι R A : Type*} [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [Decomposition 𝒜] (I : Ideal A)

def quotPieces (n : ι) : Submodule R (A ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ R I).toLinearMap

omit [DecidableEq ι] [Decomposition 𝒜] in
theorem mk_mem_quotPieces {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I a ∈ quotPieces 𝒜 I n :=
  ⟨a, ha, rfl⟩

def quotPieceMap (n : ι) : 𝒜 n →+ quotPieces 𝒜 I n where
  toFun x := ⟨Ideal.Quotient.mk I x, mk_mem_quotPieces 𝒜 I x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def quotientDecomposition : A →+ ⨁ n, quotPieces 𝒜 I n :=
  (DirectSum.map (quotPieceMap 𝒜 I)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

variable {𝒜 I}

theorem quotientDecomposition_apply (a : A) : quotientDecomposition 𝒜 I a =
    DirectSum.map (quotPieceMap 𝒜 I) (DirectSum.decompose 𝒜 a) := rfl

theorem quotientDecomposition_of_mem_ideal (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) {a : A}
    (ha : a ∈ I) : quotientDecomposition 𝒜 I a = 0 := by
  ext n
  change Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a n : A) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI n a ha

omit [Decomposition 𝒜] in
theorem coe_comp_map_quotPieceMap :
    (DirectSum.coeAddMonoidHom (quotPieces 𝒜 I)).comp (DirectSum.map (quotPieceMap 𝒜 I)) =
      (Ideal.Quotient.mk I).toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝒜) := by
  ext n x
  simp [DirectSum.map_of, quotPieceMap]

theorem coe_quotientDecomposition (a : A) :
    DirectSum.coeAddMonoidHom (quotPieces 𝒜 I) (quotientDecomposition 𝒜 I a) = Ideal.Quotient.mk I a := by
  rw [quotientDecomposition_apply]
  have := congrArg (fun φ => φ (DirectSum.decompose 𝒜 a)) (coe_comp_map_quotPieceMap (𝒜 := 𝒜) (I := I))
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
  rw [this]
  exact congrArg (Ideal.Quotient.mk I) ((DirectSum.decompose 𝒜).symm_apply_apply a)

theorem quotientDecomposition_of_mem_piece {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    quotientDecomposition 𝒜 I a = DirectSum.of (fun n => quotPieces 𝒜 I n) n
      ⟨Ideal.Quotient.mk I a, mk_mem_quotPieces 𝒜 I ha⟩ := by
  rw [quotientDecomposition_apply, DirectSum.decompose_of_mem 𝒜 ha, DirectSum.map_of]
  rfl

def quotDecomp (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) :
    A ⧸ I →+ ⨁ n, quotPieces 𝒜 I n :=
  QuotientAddGroup.lift I.toAddSubgroup (quotientDecomposition 𝒜 I)
    (fun _ ha => AddMonoidHom.mem_ker.mpr (quotientDecomposition_of_mem_ideal hI ha))

@[instance_reducible]
def quotDecomposition (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) :
    Decomposition (quotPieces 𝒜 I) where
  decompose' := quotDecomp hI
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => exact coe_quotientDecomposition a
  right_inv d := by
    induction d using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of n q =>
      obtain ⟨q, a, ha, rfl⟩ := q
      rw [DirectSum.coeAddMonoidHom_of]
      exact quotientDecomposition_of_mem_piece ha
    | add d e hd he => rw [map_add (f := _), map_add (f := _), hd, he]

theorem quotPieces_isInternal (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) :
    IsInternal (quotPieces 𝒜 I) :=
  letI := quotDecomposition hI
  Decomposition.isInternal _

end QuotDecomposition

section PolyQuot

variable {S : Type u} [CommRing S] {N : ℕ}

theorem weight_one_int (d : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d = (d.degree : ℤ) := by
  rw [Finsupp.weight_apply]
  simp only [Finsupp.sum, nsmul_eq_mul, mul_one]
  change _ = ((∑ i ∈ d.support, d i : ℕ) : ℤ)
  push_cast
  rfl

theorem isHomogeneous_of_isWeightedHomogeneous_one {f : Poly S N} {n : ℕ}
    (hf : IsWeightedHomogeneous (fun _ => (1 : ℤ)) f (n : ℤ)) : f.IsHomogeneous n := by
  intro d hd
  have h1 := hf hd
  rw [weight_one_int] at h1
  have h2 : Finsupp.weight (1 : Fin (N + 1) → ℕ) d = d.degree := by
    rw [Finsupp.degree_eq_weight_one]; rfl
  rw [h2]
  exact_mod_cast h1

theorem weightedHomogeneousComponent_one_mem {p : Ideal (Poly S N)}
    (hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p) (c : ℤ) {f : Poly S N} (hf : f ∈ p) :
    weightedHomogeneousComponent (fun _ => (1 : ℤ)) c f ∈ p := by
  by_cases hc : 0 ≤ c
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hc
    have : weightedHomogeneousComponent (fun _ => (1 : ℤ)) (k : ℤ) f = homogeneousComponent k f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, weight_one_int]
      simp only [Nat.cast_inj]
    rw [this]
    exact hp f hf k
  · have : weightedHomogeneousComponent (fun _ => (1 : ℤ)) c f = 0 := by
      ext d
      rw [coeff_weightedHomogeneousComponent, weight_one_int, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      split_ifs with h
      · omega
      · rfl
    rw [this]
    exact p.zero_mem

def quotGraded (p : Ideal (Poly S N)) (hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p) :
    GradedPMod S N (Poly S N ⧸ p) where
  piece := quotPieces (weightedHomogeneousSubmodule S (fun _ : Fin (N + 1) => (1 : ℤ))) p
  isInternal := by
    classical
    let _ := weightedDecomposition S (fun _ : Fin (N + 1) => (1 : ℤ))
    refine quotPieces_isInternal fun n a ha => ?_
    have h := weightedDecomposition.decompose'_apply S (fun _ : Fin (N + 1) => (1 : ℤ)) a n
    change ((weightedDecomposition S (fun _ : Fin (N + 1) => (1 : ℤ))).decompose' a n :
      Poly S N) ∈ p
    rw [h]
    exact weightedHomogeneousComponent_one_mem hp n ha
  smul_mem d c q m hq hm := by
    obtain ⟨f, hf, rfl⟩ := hm
    refine ⟨q * f, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule, add_comm c (d : ℤ)]
      exact (isWeightedHomogeneous_int_of_isHomogeneous hq).mul hf
    · change Ideal.Quotient.mk p (q * f) = q • Ideal.Quotient.mk p f
      rfl

theorem mem_quotGraded_piece {p : Ideal (Poly S N)} {hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p}
    {c : ℤ} {m : Poly S N ⧸ p} :
    m ∈ (quotGraded p hp).piece c ↔ ∃ f : Poly S N,
      IsWeightedHomogeneous (fun _ => (1 : ℤ)) f c ∧ Ideal.Quotient.mk p f = m := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩

theorem finite_quot (p : Ideal (Poly S N)) : Module.Finite (Poly S N) (Poly S N ⧸ p) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ (Poly S N) p).toLinearMap
    Ideal.Quotient.mk_surjective

end PolyQuot

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace Domination

section Charts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}

theorem chartRing_eq_ampleBase {i : Fin (N + 1)} (hi : x i ≠ 0) :
    chartRing (S := S) (x := x) (singleChart hi) = ampleBase (S := S) x i := by
  apply le_antisymm
  · intro a ha
    have := (algebraMap S Ω).domain_nontrivial
    obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
    change s ∈ monos {i} at hs
    have hs' : s ∈ Submonoid.closure ({X i} : Set (Poly S N)) := by
      simpa [monos] using hs
    obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.mp hs'
    have hm : e = m := hse.inj_right (isHomogeneous_X_pow i m) (by
      rw [X_pow_eq_monomial, Ne, monomial_eq_zero]
      exact one_ne_zero)
    subst e
    rw [map_pow, aeval_X, ← aeval_div_of_isHomogeneous hf i, ampleBase,
      Algebra.adjoin_range_eq_range_aeval]
    exact ⟨f, rfl⟩
  · rw [ampleBase, Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    have hXi : (X i : Poly S N) ∈ monos {i} := X_mem_monos (Finset.mem_singleton_self i)
    exact ⟨X l, X i, 1, hXi, isHomogeneous_X S l, isHomogeneous_X S i, by simp⟩

theorem isNoetherianRing_chartRing [IsNoetherianRing S] {i : Fin (N + 1)} (hi : x i ≠ 0) :
    IsNoetherianRing (chartRing (S := S) (x := x) (singleChart hi)) := by
  classical
  have hfg : (chartRing (S := S) (x := x) (singleChart hi)).FG := by
    rw [chartRing_eq_ampleBase hi, ampleBase]
    refine ⟨Finset.univ.image fun l => x l / x i, ?_⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have : Algebra.FiniteType S (chartRing (S := S) (x := x) (singleChart hi)) :=
    ⟨(Subalgebra.fg_top _).mpr hfg⟩
  exact Algebra.FiniteType.isNoetherianRing S _

variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)



end Charts

section Clauses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}


end Clauses

end Domination

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def CechZerothCohomologySections.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubSystem S x E), x ≠ 0 → Nonempty (F.H 0 ≃ₗ[S] F.secs)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def GlobalFunctionsIntegral.Statement : Prop :=
  ∀ (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K] (N : ℕ) (y : Fin (N + 1) → K) (a : K),
    y ≠ 0 → (∀ (i : Fin (N + 1)) (hi : y i ≠ 0), a ∈ chartRing k y (singleChart hi)) → IsIntegral k a

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem SubSystem.twist_sub_eq_mul (F Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨y, hy, q, hq, by rw [smul_eq_mul, mul_comm]⟩
  · rintro ⟨y, hy, q, hq, rfl⟩
    exact ⟨q, hq, y, hy, by rw [smul_eq_mul, mul_comm]⟩

theorem twistMod_zero_eq_one (I : Chart x) : twistMod k x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

theorem SubSystem.pow_sub_eq_pow (Q : SubSystem k x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact twistMod_zero_eq_one I
  | succ n ih => rw [pow_succ, ← ih]; exact SubSystem.twist_sub_eq_mul _ _ I

end Lemmas

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}


variable (S x) in
def spanBundle (s : Ω) (hs : s ≠ 0) : LineBundle S x where
  sub I := Submodule.span (chartRing S x I) {s}
  mono I J h y hy := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact Submodule.mem_span_singleton.mpr ⟨chartIncl h a, rfl⟩
  mem_iff I J h y := by
    constructor
    · intro hy
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
      obtain ⟨a, ha, hab⟩ := exists_isUnit_mul_mem h b
      refine ⟨a, ha, Submodule.mem_span_singleton.mpr ⟨⟨_, hab⟩, ?_⟩⟩
      rw [chartRing_smul_def, chartRing_smul_def, smul_eq_mul, mul_assoc]
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      refine Submodule.mem_span_singleton.mpr ⟨(↑u⁻¹ : chartRing S x J) * chartIncl h c, ?_⟩
      rw [chartRing_smul_def, Subalgebra.coe_mul, mul_assoc]
      change (↑u⁻¹ : chartRing S x J).1 * ((c : Ω) * s) = y
      rw [← chartRing_smul_def c s, hc, smul_eq_mul, ← mul_assoc, hinv, one_mul]
  fg _ := Submodule.fg_span_singleton s
  invertible I := ⟨Submodule.span (chartRing S x I) {s⁻¹}, by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hs, ← Submodule.one_eq_span]⟩

variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def SubFamily.sup (F G : SubFamily S x E) : SubFamily S x E where
  sub I := F.sub I ⊔ G.sub I
  mono I J h y hy := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    exact Submodule.mem_sup.mpr ⟨a, F.mono I J h a ha, b, G.mono I J h b hb, rfl⟩
  mem_iff I J h y := by
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨u, hu, hua⟩ := (F.mem_iff I J h a).mp ha
      obtain ⟨v, hv, hvb⟩ := (G.mem_iff I J h b).mp hb
      refine ⟨u * v, by rw [map_mul]; exact hu.mul hv, ?_⟩
      have : ((u * v : chartRing S x I) : Ω) • (a + b) = v • ((u : Ω) • a) + u • ((v : Ω) • b) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, Subalgebra.coe_mul, smul_add,
          mul_comm (v : Ω) (u : Ω)]
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ v hua))
        (Submodule.mem_sup_right (Submodule.smul_mem _ u hvb))
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ : (a : Ω) • y ∈ F.sub J ⊔ G.sub J := by
        obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hay
        exact Submodule.mem_sup.mpr ⟨c, F.mono I J h c hc, d, G.mono I J h d hd, hcd⟩
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        rw [Subalgebra.smul_def, smul_smul, hinv, one_smul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def TwistSections.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (y : Fin (N + 1) → Ω), y ≠ 0 →
    ∀ᶠ n : ℕ in Filter.atTop, (twistSys S y (n : ℤ)).secs = (coordGraded S y).piece (n : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end
