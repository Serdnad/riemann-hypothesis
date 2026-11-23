module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle860
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
public import Development.AbelianVarietyTheory.Definitions.Foundations.TracePowApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingAdmissibleFacts
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle931
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle766
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle993
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

noncomputable section

namespace GlobalTheory.CapelliCoeffs

open Polynomial

def entry (O : Type) [CommRing O] (N : ℕ) (α : Equiv.Perm (Fin N)) (k : Fin N) :
    Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  C (FreeAlgebra.ι O (α k, k)) + if α k = k then X - C (((k : ℕ) : FreeAlgebra O (Fin N × Fin N))) else 0

def capPoly (O : Type) [CommRing O] (N : ℕ) : Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  ∑ α : Equiv.Perm (Fin N), (((Equiv.Perm.sign α : ℤˣ) : ℤ) : Polynomial (FreeAlgebra O (Fin N × Fin N))) *
    (List.ofFn (entry O N α)).prod

theorem ofFn_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] (ψ : M →+ M') : ∀ {m : ℕ} (g : Fin m → Module.End R M)
    (g' : Fin m → Module.End S M'), (∀ k x, ψ (g k x) = g' k (ψ x)) →
    ∀ x, ψ ((List.ofFn g).prod x) = (List.ofFn g').prod (ψ x)
  | 0, g, g', _, x => by simp
  | m + 1, g, g', h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h 0, ofFn_intertwine ψ (fun k => g k.succ) (fun k => g' k.succ) (fun k => h k.succ)]

theorem capDet_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] {n : ℕ} (ψ : M →+ M') (E : Fin n → Fin n → Module.End R M)
    (E' : Fin n → Fin n → Module.End S M') (h : ∀ i j x, ψ (E i j x) = E' i j (ψ x)) (u : ℤ) (x : M) :
    ψ (Formalism.BranchingDeterminantCap.capDet E u x) = Formalism.BranchingDeterminantCap.capDet E' u (ψ x) := by
  unfold Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  refine ofFn_intertwine ψ _ _ (fun k y => ?_) x
  simp only [Formalism.BranchingDeterminantCap.bmF, LinearMap.sub_apply, map_sub, h]
  split_ifs
  · simp [Module.End.intCast_apply, map_zsmul]
  · simp

theorem capDet_dualWeyl_domain (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ)
    (hν : Antitone ν) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν) (u : ℤ) :
    Formalism.BranchingDeterminantCap.capDet (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1) u f =
      ((∏ j : Fin N, (u + ((j : ℕ) : ℤ) - (ν j : ℤ)) : ℤ) : O) • f := by
  let K := FractionRing O
  let φ : O →+* K := algebraMap O K
  have hφ : Function.Injective φ := IsFractionRing.injective O K
  have hg := Formalism.GradedWeylDivisibility.dualWeylMap O K φ N N ν f hf
  have h1 := GlobalTheory.BrCompare.capDet_dualWeyl (K := K) hν u hg
  have e : (fun i j => GlobalTheory.Mem.Gelf.rowE K N N i j) = fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1 := by
    funext a b
    exact LinearMap.ext fun P => (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv K N N a b P).1
  rw [e] at h1
  have h2 := capDet_intertwine (MvPolynomial.map φ).toAddMonoidHom (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1)
    (fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1) (fun i j x => (Formalism.GradedWeylDivisibility.lclosedeq_rowDiv_map φ i j 1 x).symm) u f
  apply MvPolynomial.map_injective φ hφ
  have h3 := h2.trans h1
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h3
  rw [h3, Int.cast_smul_eq_zsmul K, Int.cast_smul_eq_zsmul O, map_zsmul]

theorem eval_capPoly (O : Type) [CommRing O] (N : ℕ) {M : Type} [AddCommGroup M] [Module O M]
    (Φ : FreeAlgebra O (Fin N × Fin N) →ₐ[O] Module.End O M) (v : ℤ) (L : ℕ)
    (hL : (capPoly O N).natDegree < L) :
    ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) =
      ((-1 : ℤ) ^ N) • Formalism.BranchingDeterminantCap.capDet (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) := by
  have hc : ∀ a : Module.End O M, Commute ((RingHom.id _) a) (v : Module.End O M) :=
    fun a => (Int.cast_commute v a).symm
  let ev := Polynomial.eval₂RingHom' (RingHom.id (Module.End O M)) (v : Module.End O M) hc
  let Ψ := Polynomial.mapRingHom (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
  have key : ev (Ψ (capPoly O N)) = ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) := by
    show eval₂ (RingHom.id _) (v : Module.End O M) (map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
      (capPoly O N)) = _
    rw [eval₂_eq_sum_range' _ (lt_of_le_of_lt natDegree_map_le hL)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, RingHom.id_apply, ← Int.cast_pow, zsmul_eq_mul']
    rfl
  rw [← key]
  unfold capPoly Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM

  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hev : ∀ p, ev p = p.eval₂ (RingHom.id _) (v : Module.End O M) := fun _ => rfl
  have hΨ : ∀ p, Ψ p = p.map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M) := fun _ => rfl
  have e : (List.ofFn fun k => ev (Ψ (entry O N α k))) =
      (List.ofFn fun k => Formalism.BranchingDeterminantCap.bmF (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) k (α k) (id k)).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
    funext k
    rw [hev, hΨ]
    simp only [Function.comp_apply, entry, Formalism.BranchingDeterminantCap.bmF, id]
    split_ifs
    · simp only [Polynomial.map_add (f := _), Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval₂_add,
        Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.id_apply, map_natCast, RingHom.coe_coe, Polynomial.map_natCast,
        Polynomial.eval₂_natCast]
      push_cast
      abel
    · simp
  rw [show (⇑ev ∘ ⇑Ψ ∘ entry O N α) = fun k => ev (Ψ (entry O N α k)) from rfl, e, List.prod_map_neg, List.length_ofFn, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  exact (Int.cast_commute _ _).left_comm _

theorem coeff_eq_of_int (P : Type) [CommRing P] [IsDomain P] [CharZero P] (L : ℕ) (a b : ℕ → P)
    (h : ∀ v : ℤ, ∑ i ∈ Finset.range L, (v : P) ^ i * a i = ∑ i ∈ Finset.range L, (v : P) ^ i * b i) :
    ∀ i < L, a i = b i := by
  intro i hi
  let Q : Polynomial P := ∑ j ∈ Finset.range L, monomial j (a j - b j)
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Int.cast_injective (α := P)))
    rintro _ ⟨v, rfl⟩
    have hv := h v
    simp only [Set.mem_setOf_eq, IsRoot, Q, eval_finsetSum, eval_monomial]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hv
    rw [← hv]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := congrArg (fun q : Polynomial P => q.coeff i) hQ
  simp only [Q, finsetSum_coeff, coeff_monomial, coeff_zero] at this
  simp only [Finsupp.single_apply] at this
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg hj) (fun h' => absurd (Finset.mem_range.2 hi) h'), if_pos rfl] at this
  exact sub_eq_zero.1 this

end GlobalTheory.CapelliCoeffs

namespace GlobalTheory.CapelliCoeffs

open Polynomial

theorem capelli_coeff_dualWeyl : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ),
    ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν →
      ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ,
        evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  intro O _ _ _ N
  refine ⟨fun k => (capPoly O N).coeff k, fun ν hν f hf k => ?_⟩
  set p : Polynomial ℤ := ∏ a : Fin N, (X + C (((ν a : ℤ) - (a : ℕ) : ℤ))) with hpdef
  set L := (capPoly O N).natDegree + N + 1 with hLdef
  have hp : p.natDegree ≤ N := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => (natDegree_X_add_C (((ν a : ℤ) - (a : ℕ) : ℤ))).le).trans ?_
    simp
  have hE : (fun a b => evalPol O N (FreeAlgebra.ι O (a, b))) = fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1 := by
    funext a b
    simp [evalPol]
  by_cases hk : k < L
  · refine coeff_eq_of_int (MvPolynomial (Fin N × Fin N) O) L
      (fun i => evalPol O N ((capPoly O N).coeff i) f) (fun i => ((p.coeff i : ℤ) : O) • f) (fun v => ?_) k hk
    have hA := eval_capPoly O N (evalPol O N) v L (by omega)
    rw [hE] at hA
    have hB := capDet_dualWeyl_domain O N ν hν f hf (-v)
    have e1 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * evalPol O N ((capPoly O N).coeff i) f =
        (∑ i ∈ Finset.range L, (v ^ i) • evalPol O N ((capPoly O N).coeff i)) f := by
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, ← Int.cast_pow, ← zsmul_eq_mul]
    have e2 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * (((p.coeff i : ℤ) : O) • f) =
        (p.eval v) • f := by
      rw [eval_eq_sum_range' (n := L) (by omega), Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Int.cast_pow, ← zsmul_eq_mul, Int.cast_smul_eq_zsmul, smul_smul, mul_comm]
    have e3 : p.eval v = (-1 : ℤ) ^ N * ∏ j : Fin N, (-v + ((j : ℕ) : ℤ) - (ν j : ℤ)) := by
      rw [hpdef, eval_prod]
      have : ((-1 : ℤ) ^ N) = ∏ _j : Fin N, (-1 : ℤ) := by simp
      rw [this, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [eval_add, eval_X, eval_C]
      ring
    rw [e1, e2, hA, LinearMap.smul_apply, hB, e3, Int.cast_smul_eq_zsmul, smul_smul]
  · have h1 : (capPoly O N).coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    show evalPol O N ((capPoly O N).coeff k) f = _
    rw [h1, h2, map_zero]
    simp

end GlobalTheory.CapelliCoeffs
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaTransfer

theorem spMap_comp_of {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_completion (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮.IsMaximal) :
    ∃ (T : Formalism.L2.Pj.CDVR) (a : 𝓞 K →+* T.V) (j : T.V →+* ℂ), j.comp a = σ.comp (algebraMap (𝓞 K) K) ∧
      ∀ x, a x ∈ IsLocalRing.maximalIdeal T.V ↔ x ∈ 𝔮 := by
  let la : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨𝔮, h𝔮.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔮 (RingOfIntegers.not_isField K)⟩
  obtain ⟨T, io, ho, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K la
  obtain ⟨em, hem⟩ := GlobalTheory.ComplexEmbedding.exists_embedding_fractionField K σ T hfin io
  have hv : ∀ x : K, Formalism.L2.Pj.valV T.V (io x) = la.valuation K x := fun x => by
    rw [GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho, pow_one]
  have hex : ∀ x : 𝓞 K, ∃ v : T.V, algebraMap T.V T.Fr v = io (algebraMap (𝓞 K) K x) := fun x =>
    GlobalTheory.PlaceCompletion.exists_algebraMap_eq_of_valV_le_one (by
      rw [hv]; exact la.valuation_le_one x)
  choose f hf using hex
  have hinj := IsFractionRing.injective T.V T.Fr
  refine ⟨T, { toFun := f
               map_one' := hinj (by rw [hf, map_one, map_one, map_one])
               map_mul' := fun x y => hinj (by rw [map_mul, hf, hf, hf, map_mul, map_mul])
               map_zero' := hinj (by rw [hf, map_zero, map_zero, map_zero])
               map_add' := fun x y => hinj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _), map_add (f := _)]) },
    em.comp (algebraMap T.V T.Fr), RingHom.ext fun x => ?_, fun x => ?_⟩
  · change em (algebraMap T.V T.Fr (f x)) = σ (algebraMap (𝓞 K) K x)
    rw [hf, ← hem]; rfl
  · change f x ∈ _ ↔ _
    rw [← GlobalTheory.PlaceCompletion.valV_algebraMap_lt_one_iff (K' := T.Fr), hf, hv]
    exact la.valuation_lt_one_iff_mem x

theorem pow_eq_one_iff {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (y : Over.mk (𝟙 S') ⟶ G') (z : Over.mk f ⟶ G)
    (e : z.left = y.left ≫ φ) (n : ℕ) : y ^ n = 1 ↔ z ^ n = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h (Over.mk (𝟙 S'))
  have key : ∀ {g : S' ⟶ S} (_ : g = f) (w : Over.mk g ⟶ G), w.left = z.left → (w ^ n = 1 ↔ z ^ n = 1) := by
    intro g hg w hw
    subst hg
    rw [Over.OverMorphism.ext hw]
  rw [← key (Category.id_comp f) (Φ y) ((hΦ y).trans e.symm), ← map_pow, MulEquiv.map_eq_one_iff]

noncomputable def restrict {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} (y : Over.mk (𝟙 S) ⟶ G) : Over.mk f ⟶ G :=
  (Over.homMk f (Category.comp_id f) : Over.mk f ⟶ Over.mk (𝟙 S)) ≫ y

theorem restrict_pow {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {y : Over.mk (𝟙 S) ⟶ G} {n : ℕ}
    (hy : y ^ n = 1) : restrict f y ^ n = 1 := by
  rw [restrict, ← MonObj.comp_pow, hy, MonObj.comp_one]

theorem exists_isGrpPullback_of_inertia : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (N : IntermediateField ℚ ℂ) [NumberField N] (P : Out.PolAV (Sp (𝓞 N))) (W : P.A ⟶ P.A) [IsMonHom W] (r s : 𝓞 N), IsPureBC P.A W r s → ∀ q : ℕ, q.Prime → ∀ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → r - s ∉ 𝔮 → ∀ τ : ℂ ≃+* ℂ, (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → ∀ (A : Over (Sp ℂ)) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ → ∃ io : A.left ⟶ A.left, IsGrpPullback A A (spMap (τ : ℂ →+* ℂ)) io ∧ ∀ n : ℕ, ¬ q ∣ n → ∀ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ P.A, y ^ n = 1 → ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → x ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left → x ≫ io = spMap (τ : ℂ →+* ℂ) ≫ x := by
  intro hFA hGM N _ P W _ r s hW q hq 𝔮 h𝔮 hq𝔮 hrs τ hτ A _ ψ hψ
  set i : 𝓞 N →+* ℂ := (algebraMap N ℂ).comp (algebraMap (𝓞 N) N) with hi
  have hinj : Function.Injective i := (algebraMap N ℂ).injective.comp (IsFractionRing.injective (𝓞 N) N)
  choose σ₀ hσ₀ hσ₁ using hτ
  have hσ : ∀ x, i (σ₀ x) = τ (i x) := hσ₀
  let σ : 𝓞 N →+* 𝓞 N :=
    { toFun := σ₀
      map_one' := hinj (by rw [hσ, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [map_mul, hσ, hσ, hσ, map_mul, map_mul])
      map_zero' := hinj (by rw [hσ, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [map_add (f := _), hσ, hσ, hσ, map_add (f := _), map_add (f := _)]) }
  obtain ⟨T, a, j, hj, ha⟩ := exists_completion N (algebraMap N ℂ) 𝔮 h𝔮
  let b : 𝓞 N →+* T.V := a.comp σ
  have hab : ∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T.V := fun x => by
    have := (ha _).2 (𝔮.neg_mem (hσ₁ x))
    rwa [neg_sub, map_sub] at this
  have hqT : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    have := (ha _).2 hq𝔮
    rwa [map_natCast] at this
  have hu : IsUnit (a (r - s)) := by
    by_contra h
    exact hrs ((ha _).1 h)
  obtain ⟨B, _, φ, hφ⟩ : ∃ (B : Over (Sp T.V)) (_ : GrpObj B) (φ : B.left ⟶ P.A.left),
      IsGrpPullback B P.A (spMap a) φ := ⟨_, inferInstance, _, isGrpPullback_pullback P.A (spMap a)⟩
  obtain ⟨φ', hφ', hred⟩ := GlobalTheory.T.exists_iso_baseChanges_of_congruent_maps_pureHodge hFA hGM (𝓞 N) P.A P.g P.isAb P.smoothDim W r s hW T.V T.cpl q hq hqT a b
    hab hu B φ hφ
  have ea : spMap j ≫ spMap a = spMap i := spMap_comp_of hj
  have eb : spMap j ≫ spMap b = spMap (τ : ℂ →+* ℂ) ≫ spMap i :=
    (spMap_comp_of (RingHom.ext fun x => (RingHom.congr_fun hj (σ x)).trans (hσ x))).trans
      (spMap_comp_of (f := i) (g := (τ : ℂ →+* ℂ)) rfl).symm
  have er : spMap (IsLocalRing.residue T.V) ≫ spMap a = spMap (IsLocalRing.residue T.V) ≫ spMap b :=
    (spMap_comp_of (RingHom.ext fun x => Ideal.Quotient.eq.2 (hab x))).trans
      (spMap_comp_of (f := b) (g := IsLocalRing.residue T.V) rfl).symm
  have w₁ : ψ ≫ P.A.hom = (A.hom ≫ spMap j) ≫ spMap a := by rw [Category.assoc, ea, hψ.1.w]
  obtain ⟨χ, hχ₁, hχ₂⟩ : ∃ χ : A.left ⟶ B.left, χ ≫ φ = ψ ∧ χ ≫ B.hom = A.hom ≫ spMap j :=
    ⟨hφ.1.lift _ _ w₁, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _⟩
  have hχ : IsGrpPullback A B (spMap j) χ := hφ.cancel (hψ.congr ea.symm hχ₁.symm) hχ₂
  have hc := (hχ.comp hφ').congr eb rfl
  have w₂ : (χ ≫ φ') ≫ P.A.hom = (A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap i := by rw [hc.1.w, Category.assoc]
  obtain ⟨io, hio₁, hio₂⟩ : ∃ io : A.left ⟶ A.left, io ≫ ψ = χ ≫ φ' ∧ io ≫ A.hom = A.hom ≫ spMap (τ : ℂ →+* ℂ) :=
    ⟨hψ.1.lift _ _ w₂, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  refine ⟨io, hψ.cancel (hc.congr rfl hio₁.symm) hio₂, fun n hn y hy x hx₁ hx₂ => ?_⟩
  have hnu : IsUnit (n : T.V) := by
    by_contra h
    have h' : (n : T.V) ∈ IsLocalRing.maximalIdeal T.V := h
    have hc : IsCoprime (q : T.V) (n : T.V) := by
      simpa using (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)).map (Int.castRingHom T.V)
    obtain ⟨u, v, huv⟩ := hc
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2
      (huv ▸ add_mem (Ideal.mul_mem_left _ u hqT) (Ideal.mul_mem_left _ v h')))
  have hyw : y.left ≫ P.A.hom = 𝟙 (Sp (𝓞 N)) := Over.w y
  have w₃ : (spMap a ≫ y.left) ≫ P.A.hom = 𝟙 (Sp T.V) ≫ spMap a := by
    rw [Category.assoc, hyw, Category.comp_id, Category.id_comp]
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : Sp T.V ⟶ B.left, t ≫ φ = spMap a ≫ y.left ∧ t ≫ B.hom = 𝟙 _ :=
    ⟨hφ.1.lift _ _ w₃, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _⟩
  let yT : Over.mk (𝟙 (Sp T.V)) ⟶ B := Over.homMk t ht₂
  have hyT : yT ^ n = 1 := (pow_eq_one_iff hφ yT (restrict (spMap a) y) ht₁.symm n).2 (restrict_pow _ hy)
  let z : Over.mk (spMap b) ⟶ P.A := Over.homMk (t ≫ φ') (by
    change (t ≫ φ') ≫ P.A.hom = spMap b
    rw [Category.assoc, hφ'.1.w, reassoc_of% ht₂])
  have hz : z ^ n = 1 := (pow_eq_one_iff hφ' yT z rfl n).1 hyT
  have hzy : z = restrict (spMap b) y := GlobalTheory.T.torsion_point_eq_of_residue_eq_invertible_order (𝓞 N) P T.V b n hnu z _ hz (restrict_pow _ hy) (by
    change spMap (IsLocalRing.residue T.V) ≫ t ≫ φ' = spMap (IsLocalRing.residue T.V) ≫ spMap b ≫ y.left
    rw [← Category.assoc, ← hred _ (by rw [Category.assoc, ht₂, Category.comp_id]), Category.assoc, ht₁,
      reassoc_of% er])
  have hzy' : t ≫ φ' = spMap b ≫ y.left := congrArg (fun u => u.left) hzy
  have hxχ : x ≫ χ = spMap j ≫ t := by
    refine hφ.1.hom_ext ?_ ?_
    · rw [Category.assoc, hχ₁, hx₂, Category.assoc, ht₁, reassoc_of% ea]
    · rw [Category.assoc, hχ₂, reassoc_of% hx₁, Category.assoc, ht₂, Category.comp_id]
  refine hψ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hio₁, reassoc_of% hxχ, hzy', reassoc_of% eb, Category.assoc, hx₂]
  · rw [Category.assoc, hio₂, reassoc_of% hx₁, Category.assoc, hx₁, Category.comp_id]

end GlobalTheory.InertiaTransfer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

def pairFun (φ : X' ⟶ X) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) : T ⥤ (Pair φ)ᵒᵖ where
  obj t := Opposite.op ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩
  map {t t'} a := (homOfLE (show (⟨((H.obj t').unop, (G.obj (K.obj t')).unop), le t'⟩ : Pair φ) ≤
      ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩ from
    ⟨leOfHom (H.map a).unop, leOfHom (G.map (K.map a)).unop⟩)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def pairTo {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (G : D ⥤ AffOp X) (H : T ⥤ AffOp X')
    (K : T ⥤ D) (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) :
    CoefMap (RingHom.id R') (OPair φ s') (H ⋙ OAff s') where
  G := pairFun φ G H K le
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

end GlobalTheory.PrimBasis

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

theorem pairTo_pairRes (φ : X' ⟶ X) (s' : X' ⟶ Sp R) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) (c : H2 (ext R₁ (OAff s'))) :
    (extMap R₁ (pairTo φ s' G H K le)).pull2 ((extMap R₁ (pairRes φ s')).pull2 c) =
      (extMap R₁ (CoefMap.restrict (OAff s') H)).pull2 c := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 H) (fun t b ↦ ?_) c
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem pairTo_pairPull {φ : X' ⟶ X} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} (w : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) (c : H2 (ext R₁ (OAff s))) :
    (extMap R₁ (pairTo φ s' G H K le)).pull2 ((extMap R₁ (pairPull w)).pull2 c) =
      (extMap R₁ (pullMap w G H K le)).pull2 ((extMap R₁ (CoefMap.restrict (OAff s) G)).pull2 c) := by
  rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
  refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 (K ⋙ G)) (fun t b ↦ ?_) c
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end GlobalTheory.PrimBasis

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

theorem pairTo_injective (φ : X' ⟶ X) (s' : X' ⟶ Sp R) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1)
    (hr : Function.Surjective (extMap R₁ (pairRes φ s')).pull2)
    (hH : Function.Injective (extMap R₁ (CoefMap.restrict (OAff s') H)).pull2) :
    Function.Injective (extMap R₁ (pairTo φ s' G H K le)).pull2 := by
  intro x y e
  obtain ⟨x, rfl⟩ := hr x
  obtain ⟨y, rfl⟩ := hr y
  rw [pairTo_pairRes, pairTo_pairRes] at e
  rw [hH e]

end GlobalTheory.PrimBasis


open GlobalTheory.PrimBasis in
theorem GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases : PrimitiveExtendedDegTwoVanish → ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] [Quiver.IsThin D] [Quiver.IsThin T] (G : D ⥤ AffOp A.left) (H : T ⥤ AffOp (A ⊗ A).left) (K₀ K₁ K₂ : T ⥤ D) (le₀ : ∀ t, (H.obj t).unop.1 ≤ (μ[A]).left ⁻¹ᵁ (G.obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ (fst A A).left ⁻¹ᵁ (G.obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ (snd A A).left ⁻¹ᵁ (G.obj (K₂.obj t)).unop.1), IsBasis G → IsBasis H → ∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ (G ⋙ OAff A.hom)), (extMap R₁ (pullMap (overW μ[A]) G H K₀ le₀)).pull2 c = (extMap R₁ (pullMap (overW (fst A A)) G H K₁ le₁)).pull2 c + (extMap R₁ (pullMap (overW (snd A A)) G H K₂ le₂)).pull2 c → c = 0 := by
  intro hP R R₁ _ _ _ q hq A _ g hA hg D T _ _ _ _ G H K₀ K₁ K₂ le₀ le₁ le₂ hGb hHb c hc
  have hG := (GlobalTheory.Obs.BasisExt.restrict_ext_bijective R R₁ A.left A.hom D G hGb.cover hGb.dir).2
  have hH := (GlobalTheory.Obs.BasisExt.restrict_ext_bijective R R₁ (A ⊗ A).left (A ⊗ A).hom T H hHb.cover hHb.dir).2
  have hr : ∀ φ : (A ⊗ A).left ⟶ A.left, Function.Bijective (extMap R₁ (pairRes φ (A ⊗ A).hom)).pull2 :=
    fun φ ↦ (GlobalTheory.T.cechPairRestrict_baseChange_bijective R R₁ A.left (A ⊗ A).left (A ⊗ A).hom φ).1.2
  obtain ⟨c', rfl⟩ := hG.2 c
  obtain ⟨c₁, hc₁⟩ := (hr (fst A A).left).2 ((extMap R₁ (pairPull (overW (fst A A)))).pull2 c')
  obtain ⟨c₂, hc₂⟩ := (hr (snd A A).left).2 ((extMap R₁ (pairPull (overW (snd A A)))).pull2 c')
  suffices h : c' = 0 by rw [h, map_zero]
  refine hP R R₁ q hq A g hA hg c' c₁ c₂ ?_ hc₁.symm hc₂.symm
  refine pairTo_injective R₁ _ _ G H K₀ le₀ (hr _).2 hH.1 ?_
  rw [pairTo_pairPull, pairTo_pairRes, map_add (f := _), hc, ← pairTo_pairPull R₁ (overW (fst A A)) G H K₁ le₁,
    ← pairTo_pairPull R₁ (overW (snd A A)) G H K₂ le₂, ← hc₁, ← hc₂, pairTo_pairRes, pairTo_pairRes]
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_polarizationCrystalForm_perfect_selfAnnihilating : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∃ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧ ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  first | exact @GlobalTheory.PolExists.polForm_exists | exact GlobalTheory.PolExists.polForm_exists | (intros; apply GlobalTheory.PolExists.polForm_exists <;> assumption)
end
