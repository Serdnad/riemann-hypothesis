module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.QuasiFinite.Basic

@[expose] public section

section

open IsLocalRing Polynomial

namespace GlobalTheory

theorem etale_adjoinRoot_X_pow_sub_C : ∀ (R : Type) [CommRing R] (n : ℕ) (u : R), IsUnit (n : R) →
    IsUnit u → Algebra.Etale R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C u : Polynomial R)) := by
  intro R _ n u hn hu
  set f : R[X] := X ^ n - C u with hfdef
  have key : f.Monic ∧ IsUnit (AdjoinRoot.mk f (derivative f)) := by
    by_cases hn0 : n = 0
    · subst hn0
      have h01 : (0 : R) = 1 := isUnit_zero_iff.1 (by simpa using hn)
      have : Subsingleton R := subsingleton_of_zero_eq_one h01
      have : Subsingleton (AdjoinRoot f) := (AdjoinRoot.of f).codomain_trivial
      exact ⟨Subsingleton.elim _ _, isUnit_of_subsingleton _⟩
    have hm : f.Monic := monic_X_pow_sub_C _ hn0
    have h1 : AdjoinRoot.root f ^ n = algebraMap R _ u := by
      have := AdjoinRoot.eval₂_root f
      simpa [hfdef, sub_eq_zero] using this
    have hr : IsUnit (AdjoinRoot.root f) :=
      (isUnit_pow_iff hn0).1 (h1 ▸ hu.map _)
    refine ⟨hm, ?_⟩
    have e : AdjoinRoot.mk f (derivative f) = algebraMap R _ (n : R) * AdjoinRoot.root f ^ (n - 1) := by
      simp [hfdef, derivative_X_pow, AdjoinRoot.algebraMap_eq]
    rw [e]
    exact (hn.map _).mul (hr.pow _)
  obtain ⟨hm, h⟩ := key
  let P : StandardEtalePair R := ⟨f, hm, derivative f, 1, 0, 1, by simp⟩
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk f (derivative f))) _
      h).symm.restrictScalars R))

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory.EtaleDescent

open TensorProduct

theorem exists_etale_model_of_directed_union :
    ∀ (R : Type) [CommRing R] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      (Ri : ι → Subring R), Monotone Ri → (∀ x, ∃ i, x ∈ Ri i) →
      ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A],
        ∃ (i : ι) (Ai : Type) (_ : CommRing Ai) (_ : Algebra (Ri i) Ai),
          Algebra.Etale (Ri i) Ai ∧ Nonempty (TensorProduct (Ri i) R Ai ≃ₐ[R] A) := by
  intro R _ ι _ _ _ Ri hmono hcov A _ _ _
  obtain ⟨κ, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := R) (S := A)).mp
      inferInstance |>.out

  have hfin := P.finite_coeffs
  have hex : ∃ i, P.coeffs ⊆ (Ri i : Set R) := by
    classical
    choose j hj using hcov
    obtain ⟨i, hi⟩ := Finset.exists_le (hfin.toFinset.image j)
    refine ⟨i, fun x hx ↦ hmono (hi _ (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx))) (hj x)⟩
  obtain ⟨i, hi⟩ := hex
  letI : Algebra (Ri i) A := ((algebraMap R A).comp (algebraMap (Ri i) R)).toAlgebra
  haveI : IsScalarTower (Ri i) R A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (Ri i) := ⟨fun x hx ↦ ⟨⟨x, hi hx⟩, rfl⟩⟩
  let Q := P.ofHasCoeffs (Ri i)
  refine ⟨i, P.ModelOfHasCoeffs (Ri i), inferInstance, inferInstance, ?_,
    ⟨P.tensorModelOfHasCoeffsEquiv (Ri i)⟩⟩
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (Ri i) (P.ModelOfHasCoeffs (Ri i)) :=
    Q.isStandardSmoothOfRelativeDimension (by rw [← hP]; rfl)
  infer_instance

end GlobalTheory.EtaleDescent
end

section

open TensorProduct KaehlerDifferential

namespace GlobalTheory.AuxiliaryLemmaFirst

theorem main : ∀ (R R' B C B' K : Type) [inst : CommRing R] [inst_1 : CommRing R'] [inst_2 : CommRing B] [inst_3 : CommRing C] [inst_4 : CommRing B'] [inst_5 : Field K] [inst_6 : Algebra R R'] [inst_7 : Algebra R B] [inst_8 : Algebra R C] [inst_9 : Algebra R' C] [inst_10 : Algebra B C] [inst_11 : IsScalarTower R R' C] [inst_12 : IsScalarTower R B C] [Algebra.IsPushout R R' B C] [inst_14 : Algebra C B'] [inst_15 : Algebra R' B'] [IsScalarTower R' C B'] [Algebra.FormallyEtale C B'] [inst_18 : Algebra B' K] [inst_19 : Algebra B K], (∀ (x : B), (Algebra.algebraMap B K : B → K) x = (Algebra.algebraMap B' K : B' → K) ((Algebra.algebraMap C B' : C → B') ((Algebra.algebraMap B C : B → C) x))) → ∃ (e : TensorProduct B K Ω[B⁄R] ≃ₗ[K] TensorProduct B' K Ω[B'⁄R']), ∀ (x : B), (e : TensorProduct B K Ω[B⁄R] → TensorProduct B' K Ω[B'⁄R']) ((1 : K) ⊗ₜ[B] (KaehlerDifferential.D R B : B → Ω[B⁄R]) x) = (1 : K) ⊗ₜ[B'] (KaehlerDifferential.D R' B' : B' → Ω[B'⁄R']) ((Algebra.algebraMap C B' : C → B') ((Algebra.algebraMap B C : B → C) x)) := by
  intro R R' B C B' K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx
  letI : Algebra C K := ((algebraMap B' K).comp (algebraMap C B')).toAlgebra
  haveI : IsScalarTower C B' K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B C K := IsScalarTower.of_algebraMap_eq (fun x => hx x)
  let e1 := (AlgebraTensorModule.cancelBaseChange B C K K Ω[B⁄R]).symm
  let e2 := AlgebraTensorModule.congr (LinearEquiv.refl K K) (tensorKaehlerEquiv R R' B C)
  let e3 := (AlgebraTensorModule.cancelBaseChange C B' K K Ω[C⁄R']).symm
  let e4 := AlgebraTensorModule.congr (LinearEquiv.refl K K) (tensorKaehlerEquivOfFormallyEtale R' C B')
  refine ⟨e1 ≪≫ₗ e2 ≪≫ₗ e3 ≪≫ₗ e4, fun x => ?_⟩
  simp [e1, e2, e3, e4]

end GlobalTheory.AuxiliaryLemmaFirst
end

section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.EtaleHeightOne

theorem height_comap_le_one_of_goingDown {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.HasGoingDown A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height ≤ 1) :
    (Q.comap (algebraMap A B)).height ≤ 1 := by
  set p : Ideal A := Q.comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
  intro r hr hrp
  by_contra hcon
  have hr0 : r ≠ ⊥ := by
    rintro rfl
    simp at hcon
  haveI := hr
  obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp
  haveI := hP₁
  haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁
    (bot_lt_iff_ne_bot.mpr hr0)
  haveI := hP₀
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
  have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
  have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h2.trans hQ)
  exact absurd h3 (by decide)

theorem height_one_and_comap_eq_map_C : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (a : A), a ≠ 0 → algebraMap A (Localization.AtPrime Q) a ∈ P → P.height ≤ 1 →
    (P.comap (algebraMap A (Localization.AtPrime Q))).height = 1 ∧
      P.comap (algebraMap A[X] (Localization.AtPrime Q)) =
        (P.comap (algebraMap A (Localization.AtPrime Q))).map (Polynomial.C : A →+* A[X]) := by
  intro A _ _ _ _ E _ _ _ _ _ Q _ P _ a ha haP hP
  set R := Localization.AtPrime Q
  haveI : Module.Flat A[X] E := inferInstance
  haveI : Module.Flat A E := Module.Flat.trans A A[X] E
  haveI : Module.Flat E R := inferInstance
  haveI : Module.Flat A R := Module.Flat.trans A E R
  haveI : Module.Flat A[X] R := Module.Flat.trans A[X] E R
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : Algebra.HasGoingDown A[X] R := Algebra.HasGoingDown.of_flat
  set p := P.comap (algebraMap A R) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ P
  have hpne : p ≠ ⊥ := by
    intro h
    have : a ∈ p := haP
    rw [h, Ideal.mem_bot] at this
    exact ha this
  haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  have hp1 : 1 ≤ p.height := by
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hpne)
    simpa using this
  refine ⟨le_antisymm (height_comap_le_one_of_goingDown P hP) hp1, ?_⟩
  have htower : algebraMap A R = (algebraMap A[X] R).comp (Polynomial.C : A →+* A[X]) := by
    rw [IsScalarTower.algebraMap_eq A E R, IsScalarTower.algebraMap_eq A[X] E R,
      IsScalarTower.algebraMap_eq A A[X] E, ← Polynomial.algebraMap_eq]
    rfl
  set P' := P.comap (algebraMap A[X] R) with hP'
  haveI : P'.IsPrime := Ideal.comap_isPrime _ P
  haveI hCp : (p.map (Polynomial.C : A →+* A[X])).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hle : p.map (Polynomial.C : A →+* A[X]) ≤ P' := by
    rw [Ideal.map_le_iff_le_comap, hP', Ideal.comap_comap, ← htower]
  have hP'1 : P'.height ≤ 1 := height_comap_le_one_of_goingDown P hP
  by_contra hne
  have hlt : p.map (Polynomial.C : A →+* A[X]) < P' := lt_of_le_of_ne hle (Ne.symm hne)
  have hCne : p.map (Polynomial.C : A →+* A[X]) ≠ ⊥ := by
    intro h
    apply hpne
    rw [eq_bot_iff]
    intro x hx
    have : Polynomial.C x ∈ p.map (Polynomial.C : A →+* A[X]) := Ideal.mem_map_of_mem _ hx
    rw [h, Ideal.mem_bot, Polynomial.C_eq_zero] at this
    simp [this]
  haveI : (⊥ : Ideal A[X]).IsPrime := Ideal.isPrime_bot
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hCne)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h4 : (1 : ℕ∞) ≤ (p.map (Polynomial.C : A →+* A[X])).height := by simpa using h1
  have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h2.trans hP'1)
  exact absurd h3 (by decide)

end GlobalTheory.EtaleHeightOne
end
end

section

open IsLocalRing

namespace GlobalTheory

theorem etale_fractionField_of_etale_height_one :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A]
      [Algebra R A], ¬ IsField R →
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      Algebra.Etale (Localization.AtPrime (⊥ : Ideal R))
        (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) A) := by
  intro R A _ _ _ _ _ _ hR h

  have hm : maximalIdeal R ≠ ⊥ := fun hm => hR ((isField_iff_maximalIdeal_eq).mpr hm)
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨P, hPmin, -⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hxm)
  haveI hP : P.IsPrime := hPmin.1.1
  have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2
  have hPne : P ≠ ⊥ := fun e => hx0 (by simpa [e] using hxP)
  haveI : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have h1 : P.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin)
    (Order.one_le_iff_ne_zero.mpr (fun e => hPne (Ideal.height_eq_zero_iff_eq_bot.mp e)))
  haveI := h P h1
  set K := Localization.AtPrime (⊥ : Ideal R)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap R K y) := by
    intro y
    have hy : (y : R) ∈ (⊥ : Ideal R).primeCompl := by
      intro hb
      have hb' : (y : R) = 0 := Ideal.mem_bot.mp hb
      exact y.2 (by rw [hb']; exact P.zero_mem)
    exact IsLocalization.map_units K (⟨y, hy⟩ : (⊥ : Ideal R).primeCompl)
  letI : Algebra (Localization.AtPrime P) K :=
    (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) K :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change _ = IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit _
      rw [IsLocalization.lift_eq])
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P) K K A)

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem etale_localization_atPrime_of_height_one :
    ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [Algebra R A]
      (p : Ideal R) [p.IsPrime],
      (∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
        Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) A)) →
      ∀ (q : Ideal (Localization.AtPrime p)) [q.IsPrime], q.height = 1 →
        Algebra.Etale (Localization.AtPrime q)
          (TensorProduct (Localization.AtPrime p) (Localization.AtPrime q)
            (TensorProduct R (Localization.AtPrime p) A)) := by
  intro R A _ _ _ _ _ p _ H q _ hq
  set P : Ideal R := q.comap (algebraMap R (Localization.AtPrime p)) with hPdef
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.height = 1 := by
    rw [← hq, ← IsLocalization.height_under p.primeCompl q]
  haveI := H P hP
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) P :=
    IsLocalization.isLocalization_atPrime_localization_atPrime p.primeCompl q
  let e : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv P.primeCompl _ _
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime q) := e.toRingHom.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  haveI : Algebra.Etale (Localization.AtPrime q)
      (TensorProduct (Localization.AtPrime P) (Localization.AtPrime q)
        (TensorProduct R (Localization.AtPrime P) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  let e2 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

end GlobalTheory
end

section

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodEtale

def Hart (A R M : Type) [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ a : A, a ≠ 0 → ∀ m : M,
    (∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : M, algebraMap A R u • m = algebraMap A R a • m') →
    ∃ m' : M, m = algebraMap A R a • m'

def TorsionFreeOver (A R M : Type) [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M]
    [Module R M] : Prop :=
  ∀ a : A, a ≠ 0 → ∀ m : M, algebraMap A R a • m = 0 → m = 0

def EtaleLow (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] C)

end GlobalTheory.GoodEtale
end
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.EtaleSpreadReg

theorem isDedekindDomain_atPrime (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) [p.IsPrime] (hp : p.height ≤ 1) :
    IsDedekindDomain (Localization.AtPrime p) := by
  have hic : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hd : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p]
    exact_mod_cast hp
  have : Ring.DimensionLEOne (Localization.AtPrime p) :=
    ⟨fun {P} hP hPp => Ring.krullDimLE_one_iff_of_isPrime_bot.mp hd P hP hPp⟩
  exact {}

theorem isRegularLocalRing_polynomial_atPrime (A : Type*) [CommRing A] (Q₀ : Ideal A[X])
    [Q₀.IsPrime] [IsRegularRing (Localization.AtPrime (Q₀.under A))] :
    IsRegularLocalRing (Localization.AtPrime Q₀) := by
  set p : Ideal A := Q₀.under A with hpdef
  let Ap := Localization.AtPrime p
  letI : Algebra A[X] Ap[X] := Polynomial.algebra A Ap
  let M : Submonoid A[X] := Submonoid.map C p.primeCompl
  haveI : IsLocalization M Ap[X] := Polynomial.isLocalization p.primeCompl Ap
  have hdisj : Disjoint (M : Set A[X]) (Q₀ : Set A[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haQ
    exact ha haQ
  let Q' : Ideal Ap[X] := Q₀.map (algebraMap A[X] Ap[X])
  haveI hQ' : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M Ap[X] Q₀ inferInstance hdisj
  have hc : Q'.comap (algebraMap A[X] Ap[X]) = Q₀ :=
    IsLocalization.under_map_of_isPrime_disjoint M Ap[X] inferInstance hdisj
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime Q') Q'
  have e : (Q'.comap (algebraMap A[X] Ap[X])).primeCompl = Q₀.primeCompl := by
    ext x; simp only [Ideal.mem_primeCompl_iff, hc]
  have h2 : IsLocalization Q₀.primeCompl (Localization.AtPrime Q') := by
    rw [← e]; exact h
  have hreg : IsRegularLocalRing (Localization.AtPrime Q') := isRegularRing_iff.mp inferInstance Q'
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Q₀.primeCompl (Localization.AtPrime Q') (Localization.AtPrime Q₀)).toRingEquiv

theorem isRegularLocalRing_atPrime_of_etale (S T : Type*) [CommRing S] [IsNoetherianRing S]
    [CommRing T] [Algebra S T] [Algebra.Etale S T] (q : Ideal T) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.under S))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing S T
  let p : Ideal S := q.under S
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hun : Algebra.IsUnramifiedAt S q := inferInstance
  have hm := ((Algebra.isUnramifiedAt_iff_map_eq S p q).mp hun).2
  have hm' : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [← hm, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h1 := Ideal.spanFinrank_map_le_of_fg
    (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).fg_of_isNoetherianRing
  rw [hm'] at h1
  have h2 : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_self_add
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
  refine le_trans ?_ (WithBot.coe_le_coe.mpr h2)
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    ← hreg.spanFinrank_maximalIdeal]
  exact_mod_cast h1

theorem isRegularLocalRing_atPrime :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime] (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
    (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
    IsRegularLocalRing (Localization.AtPrime P) := by
  intro A _ _ _ _ EA _ _ _ _ _ QA _ P _ hP
  let Q : Ideal EA := P.comap (algebraMap EA (Localization.AtPrime QA))
  haveI hLoc : IsLocalization.AtPrime (Localization.AtPrime P) Q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization QA.primeCompl
      (Localization.AtPrime P) P
  have hpe : (Q.under (Polynomial A)).under A = P.comap (algebraMap A (Localization.AtPrime QA)) := by
    rw [Ideal.under_under]
    show Ideal.comap (algebraMap A EA) (Ideal.comap (algebraMap EA (Localization.AtPrime QA)) P) = _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  haveI : IsDedekindDomain (Localization.AtPrime ((Q.under (Polynomial A)).under A)) :=
    isDedekindDomain_atPrime A _ (hpe ▸ hP)
  have h0 := isRegularLocalRing_polynomial_atPrime A (Q.under (Polynomial A))
  have h1 := isRegularLocalRing_atPrime_of_etale (Polynomial A) EA Q h0
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) (Localization.AtPrime P)).toRingEquiv

end GlobalTheory.EtaleSpreadReg
end

section

namespace GlobalTheory

theorem eq_of_le_of_comap_eq_of_indEtale : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := by
  intro B O _ _ _ ⟨ι, _, _, _, Si, _, hcov, hloc⟩ p p' hp hp' hle hcomap
  by_contra hne
  obtain ⟨x, hx', hx⟩ : ∃ x, x ∈ p' ∧ x ∉ p := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hle h)
  obtain ⟨i, hi⟩ := hcov x
  obtain ⟨E, _, _, _, P, _, ⟨e⟩⟩ := hloc i
  haveI : Algebra.QuasiFinite B (Localization.AtPrime P) := inferInstance
  haveI : Algebra.QuasiFinite B (Si i) := (Algebra.QuasiFinite.iff_of_algEquiv e).mp inferInstance
  have key := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := B)
    (p.comap (algebraMap (Si i) O)) (p'.comap (algebraMap (Si i) O)) (Ideal.comap_mono hle)
    (by
      simp only [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hcomap)
  have h1 : (⟨x, hi⟩ : Si i) ∈ p'.comap (algebraMap (Si i) O) := hx'
  rw [← key] at h1
  exact hx h1

end GlobalTheory
end
