module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Smooth.Field
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.EtC

namespace GlobalTheory.LocalIndEtAIC

open Polynomial IsLocalRing

theorem lift_atComap {W O : Type} [CommRing W] [CommRing O] [IsLocalRing O] (v : W →+* O) :
    ∃ φ : Localization.AtPrime ((maximalIdeal O).comap v) →+* O,
      ∀ w, φ (algebraMap W _ w) = v w := by
  have hu : ∀ y : ((maximalIdeal O).comap v).primeCompl, IsUnit (v y) := fun y => by
    by_contra hy
    exact y.2 hy
  exact ⟨IsLocalization.lift hu, fun w => IsLocalization.lift_eq hu w⟩

theorem isDomain_aic_of_indEt : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O],
    IndEt T O → (∀ (E : Type) [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime],
      IsDomain (Localization.AtPrime P) ∧ AIC (Localization.AtPrime P)) → IsDomain O ∧ AIC O := by
  intro T O _ _ _ _ h hE
  have hdom : IsDomain O := by
    refine @NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩
    let I : Ideal (MvPolynomial (Fin 2) T) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    haveI : Algebra.FinitePresentation T (MvPolynomial (Fin 2) T ⧸ I) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
    let g : (MvPolynomial (Fin 2) T ⧸ I) →ₐ[T] O :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by
        intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        simp [hxy])
    obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
    let w : Fin 2 → W := fun i => u (Ideal.Quotient.mkₐ T I (MvPolynomial.X i))
    have hw : ∀ i, v (w i) = ![x, y] i := fun i => by
      have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ T I (MvPolynomial.X i))
      exact this.trans (MvPolynomial.aeval_X _ i)
    have h0 : w 0 * w 1 = 0 := by
      have : Ideal.Quotient.mkₐ T I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ T I (MvPolynomial.X 1) = 0 := by
        rw [← map_mul]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      simp only [w, ← map_mul, this, map_zero]
    obtain ⟨φ, hφ⟩ := lift_atComap (v : W →+* O)
    haveI := (hE W ((maximalIdeal O).comap (v : W →+* O))).1
    have hm : algebraMap W (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) (w 0) *
        algebraMap W _ (w 1) = 0 := by rw [← map_mul, h0, map_zero]
    rcases mul_eq_zero.mp hm with h1 | h1
    · left
      have e := hφ (w 0)
      rw [h1, map_zero] at e
      have := hw 0
      simp only [AlgHom.coe_toRingHom] at e
      rw [← e] at this
      simpa using this.symm
    · right
      have e := hφ (w 1)
      rw [h1, map_zero] at e
      have := hw 1
      simp only [AlgHom.coe_toRingHom] at e
      rw [← e] at this
      simpa using this.symm
  refine ⟨hdom, ?_⟩
  intro p hpm hdeg
  set n := p.natDegree with hn
  let g : MvPolynomial (Fin n) T →ₐ[T] O := MvPolynomial.aeval (fun i => p.coeff i)
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
  let c : Fin n → W := fun i => u (MvPolynomial.X i)
  have hc : ∀ i, v (c i) = p.coeff i := fun i => by
    have := DFunLike.congr_fun huv (MvPolynomial.X i)
    exact this.trans (MvPolynomial.aeval_X _ i)
  let p' : W[X] := X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp'm : p'.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hp' : p'.map (v : W →+* O) = p := by
    conv_rhs => rw [hpm.as_sum]

    simp only [p', Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C]
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
    simp [hc]
    rfl
  have hp'd : p'.natDegree = n := by
    have e1 := hp'm.natDegree_map (v : W →+* O)
    rw [hp'] at e1
    rw [← e1]
  obtain ⟨φ, hφ⟩ := lift_atComap (v : W →+* O)
  set L := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))
  haveI := (hE W ((maximalIdeal O).comap (v : W →+* O))).1
  have hL := (hE W ((maximalIdeal O).comap (v : W →+* O))).2
  have hmL : (p'.map (algebraMap W L)).Monic := hp'm.map _
  have hdL : 0 < (p'.map (algebraMap W L)).natDegree := by
    rw [hp'm.natDegree_map, hp'd]; exact hdeg
  obtain ⟨r, hr⟩ := hL _ hmL hdL
  refine ⟨φ r, ?_⟩
  have hcomp : φ.comp (algebraMap W L) = (v : W →+* O) := RingHom.ext hφ
  have hpL : p = (p'.map (algebraMap W L)).map φ := by rw [Polynomial.map_map, hcomp, hp']
  rw [hpL, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]

end GlobalTheory.LocalIndEtAIC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCElements

theorem chains_X_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) : IsZero (((chains R).obj E).X n) :=
  ((chainsN R).obj E).isZero_extend_X ComplexShape.embeddingDownNat n (fun i hi => by
    change -(i : ℤ) = n at hi; omega)

theorem res_X_isZero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) :=
  (injectiveResolution F).cocomplex.isZero_extend_X ComplexShape.embeddingUpNat n (fun i hi => by
    change (i : ℤ) = n at hi; omega)

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spcᵒᵖ) (n : ℤ), n < 0 → IsZero (((HC R F).obj E).X n)) ∧ ∃ cl : ∀ (E : Spc) (n : ℤ) (z : ((HC R F).obj (op E)).X n), ((HC R F).obj (op E)).d n (n + 1) z = 0 → H R E F n, (∀ E n x, ∃ z hz, cl E n z hz = x) ∧ (∀ E n z hz z' hz', cl E n z hz = cl E n z' hz' ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = z' + ((HC R F).obj (op E)).d (n - 1) n y) ∧ (∀ E n z hz, cl E n z hz = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = ((HC R F).obj (op E)).d (n - 1) n y) ∧ ∀ (E E' : Spc) (f : E ⟶ E') n z hz, ∃ h, pull R f F n (cl E' n z hz) = cl E n (((HC R F).map f.op).f n z) h := by
  intro R _ F
  have zero_iff : ∀ (E : Spc) (n : ℤ) (c : Cocycle ((chains R).obj E) (res R F) n),
      CohomologyClass.mk c = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), (show ((HC R F).obj (op E)).X n from c.1) = ((HC R F).obj (op E)).d (n - 1) n y := by
    intro E n c
    rw [CohomologyClass.mk_eq_zero_iff]
    constructor
    · rintro ⟨m, hm, β, hβ⟩
      obtain rfl : m = n - 1 := by omega
      exact ⟨β, hβ.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨n - 1, by omega, y, hy.symm⟩
  refine ⟨?_, fun E n z hz => CohomologyClass.mk (Cocycle.mk z (n + 1) rfl hz), ?_, ?_, ?_, ?_⟩
  · intro E n hn
    refine @AddCommGrpCat.isZero_of_subsingleton _ ⟨fun a b => ?_⟩
    change Cochain ((chains R).obj E.unop) (res R F) n at a b
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : 0 < p
    · exact (chains_X_isZero R E.unop p hp).eq_of_src _ _
    · exact (res_X_isZero R F q (by omega)).eq_of_tgt _ _
  · intro E n x
    obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c.1, c.2, rfl⟩
  · intro E n z hz z' hz'
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, zero_iff]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change z - z' = _ at hy
      rw [← hy]; abel
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change z - z' = _
      rw [hy]; abel
  · intro E n z hz
    exact zero_iff E n _
  · intro E E' f n z hz
    refine ⟨(zcomp (Cocycle.ofHom ((chains R).map f)) (Cocycle.mk z (n + 1) rfl hz) (zero_add n)).2, ?_⟩
    rfl

end GlobalTheory.EtC.HCElements
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanStep
variable {T : Type 1} [Category.{0} T]

abbrev altCx (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) : CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ F)

theorem alternatingCofaceComplexOfFunctor_d_zero_one (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (y : F.obj (X.obj (SimplexCategory.mk 0))) :
    (altCx X F).d 0 1 y = F.map (X.δ (n := 0) 0) y - F.map (X.δ (n := 0) 1) y := by
  have h0 : (altCx X F).d 0 1 = AlgebraicTopology.AlternatingCofaceMapComplex.objD (X ⋙ F) 0 :=
    CochainComplex.of_d (fun n ↦ (X ⋙ F).obj (SimplexCategory.mk n)) (AlgebraicTopology.AlternatingCofaceMapComplex.objD (X ⋙ F)) 0
  rw [h0]
  simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg, CosimplicialObject.δ]
  rfl

theorem altCx_nat (X : CosimplicialObject T) {F G : T ⥤ AddCommGrpCat.{1}} (φ : F ⟶ G) (n m : ℕ)
    (w : F.obj (X.obj (SimplexCategory.mk n))) :
    (altCx X G).d n m (φ.app _ w) = φ.app _ ((altCx X F).d n m w) := by
  have h := ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map (Functor.whiskerLeft X φ)).comm n m
  exact ConcreteCategory.congr_hom h w

theorem altCx_dd (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (y : F.obj (X.obj (SimplexCategory.mk 0))) :
    (altCx X F).d 1 2 ((altCx X F).d 0 1 y) = 0 :=
  ConcreteCategory.congr_hom ((altCx X F).d_comp_d 0 1 2) y

theorem altCx_exact1 (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (h : (altCx X F).ExactAt 1)
    (w : F.obj (X.obj (SimplexCategory.mk 1))) (hw : (altCx X F).d 1 2 w = 0) :
    ∃ v : F.obj (X.obj (SimplexCategory.mk 0)), (altCx X F).d 0 1 v = w := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp), ShortComplex.ab_exact_iff] at h
  exact h w hw

theorem aug_δ {U : T} {X : CosimplicialObject T} (a : (CosimplicialObject.const T).obj U ⟶ X) (j : Fin 2) :
    a.app (SimplexCategory.mk 0) ≫ X.δ j = a.app (SimplexCategory.mk 1) := by
  have h := a.naturality (SimplexCategory.δ j)
  simpa [CosimplicialObject.δ] using h.symm

theorem cartan_step : ∀ (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X) (Z M N : T ⥤ AddCommGrpCat.{1}) (i : Z ⟶ M) (d : M ⟶ N), (∀ V, Function.Injective (i.app V)) → (∀ V (y : M.obj V), d.app V y = 0 ↔ ∃ w, i.app V w = y) → WExact M a → WExact N a → ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ Z)).ExactAt 1 → ∀ (z : N.obj U) (y : M.obj (X.obj (SimplexCategory.mk (0)))), d.app _ y = N.map (a.app (SimplexCategory.mk (0))) z → ∃ x : M.obj U, d.app U x = z := by
  intro T _ U X a Z M N i d hi hd hM hN hZ z y hy
  have hu : d.app _ ((altCx X M).d 0 1 y) = 0 := by
    rw [alternatingCofaceComplexOfFunctor_d_zero_one, map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, hy,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← N.map_comp, ← N.map_comp,
      aug_δ a 0, aug_δ a 1, sub_self]
  obtain ⟨w, hw⟩ := (hd _ _).1 hu
  have hw2 : (altCx X Z).d 1 2 w = 0 := by
    have h1 : i.app _ ((altCx X Z).d 1 2 w) = 0 := by
      rw [← altCx_nat X i 1 2 w, hw, altCx_dd]
      rfl
    exact hi _ (h1.trans (map_zero _).symm)
  obtain ⟨v, hv⟩ := altCx_exact1 X Z hZ w hw2
  have hy' : M.map (X.δ (n := 0) 0) (y - i.app _ v) = M.map (X.δ (n := 0) 1) (y - i.app _ v) := by
    rw [← sub_eq_zero, map_sub, map_sub, sub_sub_sub_comm, ← alternatingCofaceComplexOfFunctor_d_zero_one, ← alternatingCofaceComplexOfFunctor_d_zero_one, altCx_nat X i 0 1, hv, hw]
    exact sub_self _
  obtain ⟨x, hx⟩ := hM.2.1 _ hy'
  refine ⟨x, hN.1 ?_⟩
  have e := ConcreteCategory.congr_hom (d.naturality (a.app (SimplexCategory.mk 0))) x
  simp only [ConcreteCategory.comp_apply] at e
  have e2 : d.app (X.obj (SimplexCategory.mk 0)) (y - i.app _ v) = N.map (a.app (SimplexCategory.mk 0)) z := by
    rw [map_sub, hy, (hd _ _).2 ⟨v, rfl⟩, sub_zero]
  rw [← hx] at e2
  exact e.symm.trans e2

end GlobalTheory.CartanStep
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactProd

theorem exactAt_of_prod {ι : Type} {c : ComplexShape ℕ} {K : HomologicalComplex AddCommGrpCat.{1} c}
    {L : ι → HomologicalComplex AddCommGrpCat.{1} c} (φ : ∀ i, K ⟶ L i)
    (hφ : ∀ n, Function.Bijective (fun (x : K.X n) (i : ι) => (φ i).f n x)) (p : ℕ)
    (hL : ∀ i, (L i).ExactAt p) : K.ExactAt p := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff]
  suffices key : ∀ z : K.X p, K.d p (c.next p) z = 0 → ∃ v : K.X (c.prev p), K.d (c.prev p) p v = z from key
  intro z hz
  have hcomm : ∀ i {q r : ℕ} (x : K.X q), (L i).d q r ((φ i).f q x) = (φ i).f r (K.d q r x) := by
    intro i q r x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (φ i).comm]
  have hw : ∀ i, ∃ w : (L i).X (c.prev p), (L i).d (c.prev p) p w = (φ i).f p z := by
    intro i
    have hex := hL i
    rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff] at hex
    refine hex ((φ i).f p z) ?_
    change (L i).d p (c.next p) ((φ i).f p z) = 0
    rw [hcomm, hz, map_zero]
  choose w hw using hw
  obtain ⟨v, hv⟩ := (hφ (c.prev p)).2 w
  refine ⟨v, ?_⟩
  apply (hφ p).1
  funext i
  change (φ i).f p (K.d (c.prev p) p v) = (φ i).f p z
  rw [← hcomm, ← hw i]
  exact congrArg _ (congrFun hv i)

theorem wexact_of_prod (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T)
    (a : (CosimplicialObject.const T).obj U ⟶ X) (ι : Type) (M : ι → T ⥤ AddCommGrpCat.{1})
    (N : T ⥤ AddCommGrpCat.{1}) (π : ∀ i, N ⟶ M i)
    (hπ : ∀ V, Function.Bijective (fun (x : N.obj V) (i : ι) => (π i).app V x))
    (hM : ∀ i, WExact (M i) a) : WExact N a := by
  have nat : ∀ i {P Q : T} (f : P ⟶ Q) (x : N.obj P), (π i).app Q (N.map f x) = (M i).map f ((π i).app P x) := by
    intro i P Q f x
    exact ConcreteCategory.congr_hom ((π i).naturality f) x
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply (hπ U).1
    funext i
    apply (hM i).1
    have h := congrArg ((π i).app _) hxy
    rw [nat, nat] at h
    exact h
  · intro y hy
    have hx : ∀ i, ∃ x : (M i).obj U, (M i).map (a.app (SimplexCategory.mk 0)) x = (π i).app _ y := by
      intro i
      refine (hM i).2.1 ((π i).app _ y) ?_
      rw [← nat, ← nat, hy]
    choose x hx using hx
    obtain ⟨x', hx'⟩ := (hπ U).2 x
    refine ⟨x', ?_⟩
    apply (hπ _).1
    funext i
    change (π i).app _ (N.map (a.app (SimplexCategory.mk 0)) x') = (π i).app _ y
    rw [nat, ← hx i]
    exact congrArg _ (congrFun hx' i)
  · intro n
    refine exactAt_of_prod (fun i => (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map
      (Functor.whiskerLeft X (π i))) (fun k => ?_) (n + 1) (fun i => (hM i).2.2 n)
    exact hπ (X.obj (SimplexCategory.mk k))

end GlobalTheory.EtC.WExactProd

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.HCTerms

variable (R : Type) [CommRing R]

theorem chainsXIso_inv_map {E E' : Spc} (f : E ⟶ E') (k : ℕ) :
    (chainsXIso R E k).inv ≫ ((chains R).map f).f (-(k : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E' k).inv := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl
  change (chainsXIso R E k).inv ≫ (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(k : ℤ)) = _
  rw [h]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem isZero_chains_X (E : Spc) (p : ℤ) (hp : 0 < p) : IsZero (((chains R).obj E).X p) := by
  apply HomologicalComplex.isZero_extend_X
  intro i h
  change -(i : ℤ) = p at h
  omega

def termEval (F : Shv R) (n : ℤ) (k : ℕ) :
    (HC R F ⋙ HomologicalComplex.eval _ _ n) ⟶ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op ⋙ (free R).op ⋙
      preadditiveYoneda.obj ((res R F).X (n - k)) where
  app E := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun β : Cochain ((chains R).obj E.unop) (res R F) n => (chainsXIso R E.unop k).inv ≫ β.v (-(k : ℤ)) (n - k) (by omega))
    (fun a b => by simp only [Cochain.add_v, Preadditive.comp_add]; rfl))
  naturality E E' f := by
    ext β
    revert β
    change ∀ β : Cochain ((chains R).obj E.unop) (res R F) n,
      (chainsXIso R E'.unop k).inv ≫ ((Cochain.ofHom ((chains R).map f.unop)).comp β (zero_add n)).v (-(k : ℤ)) (n - k) (by omega) =
      (free R).map (f.unop.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E.unop k).inv ≫ β.v (-(k : ℤ)) (n - k) (by omega)
    intro β
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainsXIso_inv_map, Category.assoc]

variable {R}

def blk {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k))
    (p q : ℤ) (m : ℕ) (h1 : p = -(m : ℤ)) (h2 : n - m = q) : ((chains R).obj E).X p ⟶ (res R F).X q :=
  (((chains R).obj E).XIsoOfEq h1).hom ≫ (chainsXIso R E m).hom ≫ g m ≫ ((res R F).XIsoOfEq h2).hom

theorem blk_eq {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k))
    (k m : ℕ) (hm : m = k) (h1 : -(k : ℤ) = -(m : ℤ)) (h2 : n - m = n - k) :
    blk g (-(k : ℤ)) (n - k) m h1 h2 = (chainsXIso R E k).hom ≫ g k := by
  subst hm
  simp [blk]

def ofFam {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k)) :
    Cochain ((chains R).obj E) (res R F) n :=
  Cochain.mk fun p q hpq => if hp : p ≤ 0 then blk g p q (-p).toNat (by omega) (by omega) else 0

theorem HC_X_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ), ∃ π : ∀ k : ℕ, (HC R F ⋙ HomologicalComplex.eval _ _ n) ⟶ ((evaluation _ PSh).obj (op (SimplexCategory.mk (k)))).op ⋙ (free R).op ⋙ preadditiveYoneda.obj ((res R F).X (n - k)), ∀ E : Spcᵒᵖ, Function.Bijective (fun (x : ((HC R F).obj E).X n) (k : ℕ) => (π k).app E x) := by
  intro R _ F n
  refine ⟨termEval R F n, fun E => ⟨fun x y hxy => ?_, fun g => ?_⟩⟩
  · revert x y
    change ∀ x y : Cochain ((chains R).obj E.unop) (res R F) n, _ → x = y
    intro x y hxy
    apply Cochain.ext
    intro p q hpq
    by_cases hp : 0 < p
    · exact (isZero_chains_X R E.unop p hp).eq_of_src _ _
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨p.natAbs, by omega⟩
      obtain rfl : q = n - k := by omega
      have h := congrFun hxy k
      change (chainsXIso R E.unop k).inv ≫ x.v (-(k : ℤ)) (n - k) _ = (chainsXIso R E.unop k).inv ≫ y.v (-(k : ℤ)) (n - k) _ at h
      exact (cancel_epi _).1 h
  · refine ⟨(ofFam (E := E.unop) g : Cochain ((chains R).obj E.unop) (res R F) n), funext fun k => ?_⟩
    change (chainsXIso R E.unop k).inv ≫ (ofFam g).v (-(k : ℤ)) (n - k) (by omega) = g k
    simp only [ofFam, Cochain.mk_v]
    rw [dite_eq_left (by omega), blk_eq g k _ (by omega)]
    erw [Iso.inv_hom_id_assoc]

end GlobalTheory.EtC.HCTerms
end
end

section

noncomputable section

open scoped Quaternion Topology

namespace GlobalTheory.QSA

def TraceOpen (R : Type) [CommRing R] [TopologicalSpace R] (a b : R) : Prop :=
  ∀ g : ℍ[R, a, b], nrm g = 1 → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g →
    ∃ O : Set R, IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t

def SqOpen (K : Type) [Monoid K] [TopologicalSpace K] : Prop :=
  ∀ V ∈ 𝓝 (1 : K), ∃ U ∈ 𝓝 (1 : K), ∀ r ∈ U, ∃ μ ∈ V, μ ^ 2 = r

end GlobalTheory.QSA
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct

theorem GlobalTheory.residueField_formallySmooth_of_isClosed :
    ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k)
      [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U),
      IsClosed ({x} : Set X) →
        (letI : Algebra k (X.presheaf.stalk x) :=
          ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
         Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
  intro k _ _ X f _ U x hxU _
  letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  have key : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hxU =
      (Sp k).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.germ_stalkMap f ⊤ x trivial]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have hS0 : ∀ p : PrimeSpectrum k, (StructureSheaf.toStalk k p).hom.EssFiniteType := by
    intro p
    have := StructureSheaf.IsLocalization.to_stalk k p
    have := Algebra.EssFiniteType.of_isLocalization (R := k)
      ((Spec.structureSheaf k).presheaf.stalk p) p.asIdeal.primeCompl
    exact RingHom.essFiniteType_algebraMap.mpr this
  have hS : (StructureSheaf.toStalk k (f x)).hom.EssFiniteType := hS0 (f x)
  have hT : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial =
      StructureSheaf.toStalk k (f x) := by
    rw [Scheme.ΓSpecIso_inv]
    exact AlgebraicGeometry.StructureSheaf.algebraMap_germ _ _ _
  have hφ : algebraMap k (X.presheaf.stalk x) =
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial) ≫
        f.stalkMap x).hom := by
    show ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)) = _
    rw [cstOn, ← CommRingCat.hom_comp, Category.assoc, Category.assoc, key]
  have hS' : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Sp k).presheaf.germ ⊤ (f x) trivial).hom.EssFiniteType := hT ▸ hS
  have hR : (IsLocalRing.residue (X.presheaf.stalk x)).FiniteType :=
    RingHom.FiniteType.of_surjective _ IsLocalRing.residue_surjective
  have hE : (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))).EssFiniteType := by
    have h : algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) =
        (IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap k (X.presheaf.stalk x)) := rfl
    rw [h, hφ, CommRingCat.hom_comp]
    exact (hS'.comp (LocallyOfFiniteType.stalkMap f x)).comp hR.essFiniteType
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    RingHom.essFiniteType_algebraMap.mp hE
  exact Algebra.FormallySmooth.of_perfectField
end
