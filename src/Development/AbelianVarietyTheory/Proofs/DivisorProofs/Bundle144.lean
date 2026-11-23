module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.ConormalDer

theorem exists_derivation_cotangent (R B : Type) [CommRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] [Algebra.FormallySmooth R (ResidueField B)] :
    ∃ D : B →ₗ[R] CotangentSpace B, (∀ a b, D (a * b) = a • D b + b • D a) ∧
      ∀ t : maximalIdeal B, D t = (maximalIdeal B).toCotangent t := by
  set m := maximalIdeal B with hm
  let π : (B ⧸ m ^ 2) →ₐ[R] ResidueField B :=
    Ideal.Quotient.liftₐ (m ^ 2) (IsScalarTower.toAlgHom R B (ResidueField B)) fun a ha =>
      (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha)
  have hπ : ∀ a, π (Ideal.Quotient.mk _ a) = residue B a := fun _ => rfl
  have hsurj : Function.Surjective π := fun y => by
    obtain ⟨a, rfl⟩ := residue_surjective y
    exact ⟨_, hπ a⟩
  have hker : ∀ z, π z = 0 → z ∈ m.cotangentIdeal := fun z hz => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.mk_mem_cotangentIdeal.2 ((residue_eq_zero_iff a).1 hz)
  have hnil : IsNilpotent (RingHom.ker (π : (B ⧸ m ^ 2) →+* ResidueField B)) := by
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← m.cotangentIdeal_square]
    exact Ideal.pow_right_mono (fun z hz => hker z hz) 2
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R (ResidueField B)) π hsurj hnil
  have hs : ∀ y, π (s y) = y := fun y =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ y
  have hmem : ∀ a, Ideal.Quotient.mk _ a - s (residue B a) ∈ m.cotangentIdeal := fun a =>
    hker _ (by rw [map_sub, hs, hπ, sub_self])
  let D : B → CotangentSpace B := fun a => m.cotangentEquivIdeal.symm ⟨_, hmem a⟩
  have hD : ∀ a, m.cotangentToQuotientSquare (D a) = Ideal.Quotient.mk _ a - s (residue B a) :=
    fun a => by
      rw [← Ideal.cotangentEquivIdeal_apply]
      simp only [D, LinearEquiv.apply_symm_apply]
  have hinj := m.cotangentToQuotientSquare_injective
  have hsq : ∀ a b, (Ideal.Quotient.mk _ a - s (residue B a)) *
      (Ideal.Quotient.mk _ b - s (residue B b)) = 0 := fun a b => by
    have := Ideal.mul_mem_mul (hmem a) (hmem b)
    rwa [← pow_two, m.cotangentIdeal_square, Ideal.mem_bot] at this
  have hsm : ∀ (a : B) (z : B ⧸ m ^ 2), a • z = Ideal.Quotient.mk _ a * z := fun a z =>
    Algebra.smul_def a z
  have hmul : ∀ a b, D (a * b) = a • D b + b • D a := fun a b => by
    apply hinj
    rw [map_add (f := _), map_smul, map_smul, hD, hD, hD, hsm, hsm, map_mul, map_mul, map_mul]
    linear_combination (-1 : B ⧸ m ^ 2) * hsq a b
  have hR : ∀ c : R, D (algebraMap R B c) = 0 := fun c => by
    apply hinj
    rw [hD, map_zero, sub_eq_zero]
    exact (s.commutes c).symm
  refine ⟨⟨⟨D, fun a b => ?_⟩, fun c a => ?_⟩, hmul, fun t => ?_⟩
  · apply hinj
    rw [map_add (f := _), hD, hD, hD, map_add (f := _), map_add (f := _), map_add (f := _)]
    ring
  · show D (c • a) = c • D a
    rw [Algebra.smul_def, hmul, hR, smul_zero, add_zero, algebraMap_smul]
  · apply hinj
    show m.cotangentToQuotientSquare (D t) = _
    rw [hD, (residue_eq_zero_iff _).2 t.2, map_zero, sub_zero, Ideal.toCotangent_to_quotient_square]
    rfl

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem formallySmooth_residueField (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R]
    [CommRing B] [IsLocalRing B] [Algebra R B]
    (hu : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) :
    Algebra.FormallySmooth R (ResidueField B) := by
  let K := FractionRing R
  have hu' : ∀ c : nonZeroDivisors R, IsUnit (algebraMap R B c) := fun c =>
    hu c (nonZeroDivisors.ne_zero c.2)
  letI : Algebra K B := (IsLocalization.lift (M := nonZeroDivisors R) (S := K) hu').toAlgebra
  haveI : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq fun c =>
    (IsLocalization.lift_eq hu' c).symm
  haveI : IsScalarTower R K (ResidueField B) := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K B (ResidueField B), ← IsScalarTower.algebraMap_apply R K B,
      ← IsScalarTower.algebraMap_apply]
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing R
  haveI : Algebra.FormallySmooth K (ResidueField B) := formallySmooth_of_charZero K _
  haveI : Algebra.FormallyEtale R K := .of_isLocalization (nonZeroDivisors R)
  exact .comp R K (ResidueField B)

theorem exists_derivation_extending :
    ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by
  intro R B _ _ _ _ _ _ hu lam
  haveI := formallySmooth_residueField R B hu
  obtain ⟨D, hmul, hD⟩ := exists_derivation_cotangent R B
  have hsm : ∀ (a : B) (v : CotangentSpace B), lam (a • v) = a • lam v := fun a v => by
    rw [← algebraMap_smul (ResidueField B) a v, map_smul, algebraMap_smul]
  let L : B →ₗ[R] ResidueField B :=
    { toFun := fun a => lam (D a)
      map_add' := fun a b => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, map_smul, ← algebraMap_smul B c (D a), hsm, algebraMap_smul] }
  refine ⟨Derivation.mk' L fun a b => ?_, fun y hy => ?_⟩
  · change lam (D (a * b)) = a • lam (D b) + b • lam (D a)
    rw [hmul, map_add (f := _), hsm, hsm]
  · show lam (D y) = _
    exact congrArg lam (hD ⟨y, hy⟩)

end GlobalTheory.ConormalDer
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem annihilator_avoids_fibre_minimalPrimes
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (b : B)
    (hd : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q}))
    (u : PrimeSpectrum B) : ∃ g : B, g * b = 0 ∧ ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q := by
  classical
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) u
  let I₀ : Ideal B := p.asIdeal.map (algebraMap A B)
  let T : Set (Ideal B) := {Q | Q ∈ I₀.minimalPrimes ∧ Q.comap (algebraMap A B) = p.asIdeal}
  have hTfin : T.Finite := by
    let e := PrimeSpectrum.preimageOrderIsoFiber A B p
    haveI : IsNoetherianRing (p.asIdeal.Fiber B) :=
      Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
    have hM : {j : PrimeSpectrum (p.asIdeal.Fiber B) | j.asIdeal ∈ minimalPrimes (p.asIdeal.Fiber B)}.Finite :=
      (minimalPrimes.finite_of_isNoetherianRing _).preimage (fun x _ y _ h => PrimeSpectrum.ext h)
    refine (hM.image fun j => (e.symm j).1.asIdeal).subset ?_
    rintro Q ⟨hQmin, hQp⟩
    have hQprime : Q.IsPrime := hQmin.1.1
    let Q' : PrimeSpectrum B := ⟨Q, hQprime⟩
    have hQ'mem : Q' ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} := by
      show PrimeSpectrum.comap (algebraMap A B) Q' = p
      ext1; exact hQp
    obtain ⟨J, hJmin, hJle⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ (e ⟨Q', hQ'mem⟩).asIdeal)
    have hJprime : J.IsPrime := hJmin.1.1
    let j : PrimeSpectrum (p.asIdeal.Fiber B) := ⟨J, hJprime⟩
    refine ⟨j, hJmin, ?_⟩
    have hle : e.symm j ≤ ⟨Q', hQ'mem⟩ := by
      rw [← e.le_iff_le, e.apply_symm_apply]; exact hJle
    have hle' : (e.symm j).1.asIdeal ≤ Q := hle
    have hover : (e.symm j).1.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      congrArg PrimeSpectrum.asIdeal (e.symm j).2
    have hge : I₀ ≤ (e.symm j).1.asIdeal := by
      rw [Ideal.map_le_iff_le_comap, hover]
    exact le_antisymm hle' (hQmin.2 ⟨(e.symm j).1.isPrime, hge⟩ hle')
  obtain ⟨s, hs⟩ := hTfin.exists_finset_coe
  have hsT : ∀ i, i ∈ s ↔ i ∈ T := fun i => by rw [← hs]; rfl
  let K : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B B b)
  have hK : ∀ x, x ∈ K ↔ x * b = 0 := fun x => by
    simp [K, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have key : ∀ Q ∈ T, ¬ K ≤ Q := by
    intro Q hQ hKQ
    have hQprime : Q.IsPrime := hQ.1.1.1
    have hnot : ¬ (∏ Q'' ∈ s.erase Q, Q'') ≤ Q := by
      rw [hQprime.prod_le]
      rintro ⟨i, hi, hiQ⟩
      have hiT : i ∈ T := (hsT i).1 (Finset.mem_of_mem_erase hi)
      exact Finset.ne_of_mem_erase hi (le_antisymm hiQ (hQ.1.2 hiT.1.1 hiQ))
    obtain ⟨f, hfprod, hfQ⟩ := SetLike.not_le_iff_exists.1 hnot
    have hfo : ∀ Q'' ∈ T, Q'' ≠ Q → f ∈ Q'' := fun Q'' hQ'' hne =>
      (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_erase.2 ⟨hne, (hsT Q'').2 hQ''⟩))) hfprod
    let Qp : PrimeSpectrum B := ⟨Q, hQprime⟩
    have hcl := hd Qp
    rw [mem_closure_iff] at hcl
    obtain ⟨P, hPf, ⟨t, htP, htb⟩, hPfib⟩ :=
      hcl (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) (PrimeSpectrum.basicOpen f).isOpen hfQ
    have hPf' : f ∉ P.asIdeal := hPf
    have hPover : P.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      (congrArg PrimeSpectrum.asIdeal hPfib).trans hQ.2
    have hI₀P : I₀ ≤ P.asIdeal := by rw [Ideal.map_le_iff_le_comap, hPover]
    obtain ⟨Q', hQ'min, hQ'P⟩ := Ideal.exists_minimalPrimes_le hI₀P
    have hQ'T : Q' ∈ T := ⟨hQ'min, le_antisymm ((Ideal.comap_mono hQ'P).trans hPover.le)
      (Ideal.map_le_iff_le_comap.1 hQ'min.1.2)⟩
    by_cases hQQ : Q' = Q
    · subst hQQ
      exact htP (hQ'P (hKQ ((hK t).2 htb)))
    · exact hPf' (hQ'P (hfo Q' hQ'T hQQ))
  have hprime : ∀ i ∈ s, i ≠ ⊥ → i ≠ ⊥ → (id i : Ideal B).IsPrime := fun i hi _ _ =>
    ((hsT i).1 hi).1.1.1
  have hnot := mt (Ideal.subset_union_prime (f := id) (I := K) ⊥ ⊥ hprime).1 (by
    rintro ⟨i, hi, hKi⟩; exact key i ((hsT i).1 hi) hKi)
  rw [Set.not_subset] at hnot
  obtain ⟨g, hgK, hgU⟩ := hnot
  refine ⟨g, (hK g).1 hgK, fun Q hQ hQu hgQ => hgU ?_⟩
  have hQT : Q ∈ T := ⟨hQ, le_antisymm (Ideal.comap_mono hQu) (Ideal.map_le_iff_le_comap.1 hQ.1.2)⟩
  exact Set.mem_biUnion (show Q ∈ (↑s : Set (Ideal B)) from (hsT Q).2 hQT) hgQ

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preirreducibleSpace_primeSpectrum_tensor_localizationAway
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k]
    [Algebra A k] :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) →
      PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by
  intro hX
  letI : Algebra (k ⊗[A] B) (k ⊗[A] Localization.Away b) :=
    (Algebra.TensorProduct.map (AlgHom.id A k)
      (IsScalarTower.toAlgHom A B (Localization.Away b))).toAlgebra
  haveI : IsScalarTower k (k ⊗[A] B) (k ⊗[A] Localization.Away b) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right A k (Submonoid.powers b)
    (Localization.Away b) (by ext; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at hl
  haveI : IsLocalization.Away
      (Algebra.TensorProduct.includeRight (R := A) (A := k) b) (k ⊗[A] Localization.Away b) := hl
  exact (PrimeSpectrum.localization_away_isOpenEmbedding (k ⊗[A] Localization.Away b)
    (Algebra.TensorProduct.includeRight (R := A) (A := k) b)).preirreducibleSpace

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

def ultrafilterPrime {A : Type} [CommRing A] (U : Ultrafilter (PrimeSpectrum A)) :
    PrimeSpectrum A where
  asIdeal :=
    { carrier := {c | ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∈ t.asIdeal}
      add_mem' := fun {a b} ha hb => by
        have ha' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∈ t.asIdeal := ha
        have hb' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), b ∈ t.asIdeal := hb
        exact (ha'.and hb').mono fun t ht => t.asIdeal.add_mem ht.1 ht.2
      zero_mem' := Filter.Eventually.of_forall fun t => t.asIdeal.zero_mem
      smul_mem' := fun r a ha => by
        have ha' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∈ t.asIdeal := ha
        exact ha'.mono fun t ht => t.asIdeal.mul_mem_left r ht }
  isPrime :=
    { ne_top' := fun h => by
        have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), (1 : A) ∈ t.asIdeal :=
          (Ideal.eq_top_iff_one _).1 h
        obtain ⟨t, ht⟩ := h1.exists
        exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ht)
      mem_or_mem' := fun {a b} hab => by
        have h : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a * b ∈ t.asIdeal := hab
        exact Ultrafilter.eventually_or.1 (h.mono fun t ht => t.isPrime.mem_or_mem ht) }

theorem isOpen_of_stableUnderGeneralization_of_constructible_pieces :
    ∀ (A : Type) [CommRing A] (Z : Set (PrimeSpectrum A)), StableUnderGeneralization Z → (∀ p ∈ Z, ∃ (a : A) (I : Finset A), a ∉ p.asIdeal ∧ (∀ c ∈ I, c ∈ p.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → t ∈ Z) → IsOpen Z := by
  intro A _ Z hZ hpc
  rw [isOpen_iff_mem_nhds]
  intro p hp
  by_contra hn
  have hne : (nhds p ⊓ Filter.principal Zᶜ).NeBot := by
    rw [Filter.neBot_iff, Ne, Filter.inf_principal_eq_bot, compl_compl]
    exact hn
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (nhds p ⊓ Filter.principal Zᶜ)
  have hU1 : (U : Filter (PrimeSpectrum A)) ≤ nhds p := hU.trans inf_le_left
  have hU2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), t ∉ Z :=
    Filter.le_principal_iff.1 (hU.trans inf_le_right)
  have hle : ultrafilterPrime U ≤ p := by
    intro c hc
    by_contra hcp
    have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∈ t.asIdeal := hc
    have h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∉ t.asIdeal :=
      hU1 ((PrimeSpectrum.basicOpen c).isOpen.mem_nhds hcp)
    obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
    exact ht2 ht1
  have hq : ultrafilterPrime U ∈ Z :=
    hZ ((PrimeSpectrum.le_iff_specializes _ _).1 hle |> fun h => by simpa using h) hp
  obtain ⟨a, I, ha, hI, hsub⟩ := hpc _ hq
  have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∉ t.asIdeal :=
    Ultrafilter.eventually_not.2 ha
  have h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), ∀ c ∈ I, c ∈ t.asIdeal :=
    (Filter.eventually_all_finset I).2 fun c hc => hI c hc
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((h1.and h2).and hU2).exists
  exact ht3 (hsub t ht1 ht2)

end GlobalTheory
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isOpen_of_stableUnderGeneralization_of_locally_open_in_closure :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (U : Set (PrimeSpectrum B)),
      (∀ p q : PrimeSpectrum B, p ≤ q → q ∈ U → p ∈ U) →
      (∀ p ∈ U, ∃ g, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, p ≤ q → g ∉ q.asIdeal → q ∈ U) →
      IsOpen U := by
  intro B _ _ U hgen hloc
  classical
  set I := PrimeSpectrum.vanishingIdeal (Uᶜ) with hI
  have hIle : ∀ q : PrimeSpectrum B, q ∈ Uᶜ → I ≤ q.asIdeal := by
    intro q hq f hf
    exact (PrimeSpectrum.mem_vanishingIdeal _ f).1 hf q hq
  have key : ∀ x : PrimeSpectrum B, x.asIdeal ∈ I.minimalPrimes → x ∉ U := by
    intro x hx hxU
    obtain ⟨g, hg, hgU⟩ := hloc x hxU
    have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
    set S := hfin.toFinset.erase x.asIdeal with hS
    have hJ : ¬ S.inf id ≤ x.asIdeal := by
      intro h
      obtain ⟨P, hPS, hPx⟩ := (Ideal.IsPrime.inf_le' x.isPrime).1 h
      have hPm : P ∈ I.minimalPrimes := (Set.Finite.mem_toFinset hfin).1 (Finset.mem_of_mem_erase hPS)
      have hne : P ≠ x.asIdeal := Finset.ne_of_mem_erase hPS
      exact hne (le_antisymm hPx (hx.2 hPm.1 hPx))
    obtain ⟨c, hcJ, hcx⟩ := Set.not_subset.1 hJ
    have hgc : g * c ∈ I := by
      rw [hI, PrimeSpectrum.mem_vanishingIdeal]
      intro q hq
      obtain ⟨P, hPm, hPq⟩ := Ideal.exists_minimalPrimes_le (hIle q hq)
      by_cases hPx : P = x.asIdeal
      · by_cases hgq : g ∈ q.asIdeal
        · exact q.asIdeal.mul_mem_right c hgq
        · exact absurd (hgU q (show x.asIdeal ≤ q.asIdeal by rw [← hPx]; exact hPq) hgq) hq
      · have hPS : P ∈ S := Finset.mem_erase.2 ⟨hPx, (Set.Finite.mem_toFinset hfin).2 hPm⟩
        have : S.inf id ≤ P := Finset.inf_le (f := id) hPS
        exact q.asIdeal.mul_mem_left g (hPq (this hcJ))
    rcases x.isPrime.mem_or_mem (hx.1.2 hgc) with h | h
    · exact hg h
    · exact hcx h
  have hcl : IsClosed (Uᶜ) := by
    rw [← closure_subset_iff_isClosed, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    intro q hq
    have hIq : I ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hq
    obtain ⟨P, hPm, hPq⟩ := Ideal.exists_minimalPrimes_le hIq
    intro hqU
    exact key ⟨P, hPm.1.1⟩ hPm (hgen _ _ hPq hqU)
  exact isClosed_compl_iff.1 hcl

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem tensor_action_factors (k : Type) [Field k] (C O B : Type) [CommRing C] [Ring O] [Algebra C O]
    [Algebra C k] [Ring B] [Algebra k B] (e : (k ⊗[C] O) ≃ₐ[k] B) (X : Type) [AddCommGroup X]
    [Module k X] (σX : O →+* Module.End k X)
    (hσ : ∀ c, σX (algebraMap C O c) = algebraMap C k c • 1) :
    ∃ ρX : B →ₐ[k] Module.End k X, ∀ o, ρX (e (1 ⊗ₜ[C] o)) = σX o := by
  letI : Algebra C (Module.End k X) :=
    ((algebraMap k (Module.End k X)).comp (algebraMap C k)).toAlgebra'
      (fun c f => Algebra.commutes (algebraMap C k c) f)
  haveI : IsScalarTower C k (Module.End k X) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : O →ₐ[C] Module.End k X :=
    { σX with
      commutes' := fun c => by
        change σX (algebraMap C O c) = algebraMap k (Module.End k X) (algebraMap C k c)
        rw [hσ]; exact (Algebra.algebraMap_eq_smul_one _).symm }
  let F : (k ⊗[C] O) →ₐ[k] Module.End k X :=
    Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k X)) g
      (fun x y => Algebra.commutes x (g y))
  refine ⟨F.comp e.symm.toAlgHom, fun o => ?_⟩
  show F (e.symm (e (1 ⊗ₜ[C] o))) = σX o
  rw [e.symm_apply_apply]
  rw [show F (1 ⊗ₜ[C] o) = Algebra.ofId k (Module.End k X) 1 * g o from
    Algebra.TensorProduct.lift_tmul _ _ _ _ _, map_one, one_mul]
  rfl

end GlobalTheory
end

section

namespace GlobalTheory.TensorRingHomExtensionality

open scoped TensorProduct

theorem ringHom_ext_tensor {R S B C : Type} [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] (φ ψ : TensorProduct R S B →+* C)
    (h₁ : ∀ s : S, φ (s ⊗ₜ[R] (1 : B)) = ψ (s ⊗ₜ[R] (1 : B)))
    (h₂ : ∀ b : B, φ ((1 : S) ⊗ₜ[R] b) = ψ ((1 : S) ⊗ₜ[R] b)) : φ = ψ := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s b =>
    have h : s ⊗ₜ[R] b = (s ⊗ₜ[R] (1 : B)) * ((1 : S) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.TensorRingHomExtensionality
end
