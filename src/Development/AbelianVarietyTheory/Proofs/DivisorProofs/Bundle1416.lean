module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle670
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.TensorTower

theorem isFractionRing_of_injective {A F : Type} [CommRing A] [Field F] [Algebra A F]
    (hi : Function.Injective (algebraMap A F))
    (hs : ∀ z : F, ∃ x y : A, algebraMap A F y ≠ 0 ∧ z * algebraMap A F y = algebraMap A F x) :
    IsFractionRing A F := by
  haveI : IsDomain A := hi.isDomain (algebraMap A F)
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} e => ⟨1, by simp [hi e]⟩⟩
  · exact (map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero y.2) |>.isUnit
  · obtain ⟨x, y, hy, e⟩ := hs z
    exact ⟨⟨x, y, mem_nonZeroDivisors_of_ne_zero fun h => hy (by simp [h])⟩, e⟩

theorem isFractionRing_subring {K : Type} [Field K] (R : Subring K)
    (h : ∀ f : K, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ f * b = a) : IsFractionRing R K :=
  isFractionRing_of_injective Subtype.val_injective fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, e⟩

theorem exists_residue {κ : Type} [Field κ] [Algebra ℂ κ] (B : Subring κ)
    (hB : IsLocModel (algebraMap ℂ κ) B) (hr : RatRes (algebraMap ℂ κ) B) :
    ∃ ev : B →+* ℂ, ∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) ↔ ev b = a := by
  haveI := hB.isLocalRing
  let c0 : ℂ →+* B := (algebraMap ℂ κ).codRestrict B hB.const_mem
  let g : ℂ →+* IsLocalRing.ResidueField B := (IsLocalRing.residue B).comp c0
  have key : ∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) ↔
      IsLocalRing.residue B b = g a := fun b a => by
    rw [show (b : κ) - algebraMap ℂ κ a = ((b - c0 a : B) : κ) from rfl, nonUnit_iff,
      ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    show _ ↔ Ideal.Quotient.mk _ b = Ideal.Quotient.mk _ (c0 a)
    rw [Ideal.Quotient.eq]
  have hbij : Function.Bijective g := ⟨g.injective, fun y => by
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := hr b b.2
    exact ⟨a, ((key b a).1 ha).symm⟩⟩
  let e := RingEquiv.ofBijective g hbij
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue B), fun b a => ?_⟩
  rw [key]
  show _ ↔ e.symm _ = a
  rw [e.symm_apply_eq]
  rfl

theorem exists_isEtTower_tensor : ∀ {K κ L : Type} [Field K] [Field κ] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ) L] [IsScalarTower ℂ (K ⊗[ℂ] κ) L] [IsFractionRing (K ⊗[ℂ] κ) L]
    (R : Subring K) (B : Subring κ) (hB : IsLocModel (algebraMap ℂ κ) B) (r : ℕ) (τ : Fin r → B),
  IsLocModel (algebraMap ℂ K) R → IsIntegrallyClosed R → RatRes (algebraMap ℂ K) R →
  RatRes (algebraMap ℂ κ) B → (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) →
  (MvPolynomial.eval₂Hom ((algebraMap ℂ κ).codRestrict B hB.const_mem) τ).FormallyEtale →
  ∃ (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (j : B →+* T),
    IsEtTower (algebraMap ℂ K) R (algebraMap ℂ L) T ι ψ (fun i => j (τ i)) ∧
    (∀ a : R, (ι a : L) = algebraMap (K ⊗[ℂ] κ) L ((a : K) ⊗ₜ 1)) ∧
    (∀ b : B, (j b : L) = algebraMap (K ⊗[ℂ] κ) L (1 ⊗ₜ (b : κ))) ∧
    (∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) → ((ψ (j b) : R) : K) = algebraMap ℂ K a) ∧
    (∀ t : T, ∃ s s' : T, s ∈ Subring.closure (Set.range ι ∪ Set.range j) ∧
      s' ∈ Subring.closure (Set.range ι ∪ Set.range j) ∧ IsUnit (ψ s') ∧ (t : L) * s' = s) := by
  intro K κ L _ _ _ _ _ _ _ _ _ R B hB r τ hR hRn hRr hBr hm he
  haveI := hR.isLocalRing
  haveI := hB.isLocalRing
  letI iR : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R hR.const_mem).toAlgebra
  letI iB : Algebra ℂ B := ((algebraMap ℂ κ).codRestrict B hB.const_mem).toAlgebra
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ B κ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing R K := isFractionRing_subring R hR.frac
  haveI : IsFractionRing B κ := isFractionRing_subring B hB.frac
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.isFractionRing_tensor_of_fraction_fields (k := ℂ) (R := R) (B := B) (K := K) (κ := κ) (L := L)
  set f := (algebraMap (K ⊗[ℂ] κ) L).comp (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom ℂ R K) (IsScalarTower.toAlgHom ℂ B κ)).toRingHom with hf
  letI iA : Algebra (R ⊗[ℂ] B) L := f.toAlgebra
  haveI : IsFractionRing (R ⊗[ℂ] B) L := isFractionRing_of_injective hinj hsurj
  haveI : IsDomain (R ⊗[ℂ] B) := hinj.isDomain f
  haveI : Nontrivial (R ⊗[ℂ] B) := IsDomain.toNontrivial
  have hft : ∀ (a : R) (b : B), algebraMap (R ⊗[ℂ] B) L (a ⊗ₜ b) =
      algebraMap (K ⊗[ℂ] κ) L ((a : K) ⊗ₜ (b : κ)) := fun a b => rfl

  obtain ⟨ev, hev⟩ := exists_residue B hB hBr
  have hevc : ∀ a : ℂ, ev (algebraMap ℂ B a) = a := fun a =>
    (hev _ a).1 (by
      rw [show ((algebraMap ℂ B a : B) : κ) = algebraMap ℂ κ a from rfl, sub_self]
      exact nonUnit_zero B)
  let ev' : B →ₐ[ℂ] ℂ := { ev with commutes' := hevc }
  let φ : R ⊗[ℂ] B →ₐ[ℂ] R := Algebra.TensorProduct.lift (AlgHom.id ℂ R)
    ((Algebra.ofId ℂ R).comp ev') (fun _ _ => Commute.all _ _)
  have hφ : ∀ (a : R) (b : B), φ (a ⊗ₜ b) = a * algebraMap ℂ R (ev b) := fun a b => by
    simp [φ, ev']
  let q : Ideal (R ⊗[ℂ] B) := (IsLocalRing.maximalIdeal R).comap φ
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  have hq : q.primeCompl ≤ nonZeroDivisors (R ⊗[ℂ] B) := q.primeCompl_le_nonZeroDivisors
  let A : Subalgebra (R ⊗[ℂ] B) L := Localization.subalgebra.ofField L q.primeCompl hq
  haveI hA : IsLocalization q.primeCompl A := Localization.subalgebra.isLocalization_ofField L _ hq
  have hu : ∀ y : q.primeCompl, IsUnit (φ.toRingHom y) := fun y => by
    by_contra hy
    exact y.2 (show (y : R ⊗[ℂ] B) ∈ q from (IsLocalRing.mem_maximalIdeal _).2 hy)
  let ψ : A →+* R := IsLocalization.lift hu
  have hψ : ∀ x, ψ (algebraMap _ A x) = φ x := IsLocalization.lift_eq hu
  let a : R ⊗[ℂ] B →+* A := algebraMap _ A
  have ha : ∀ x, (a x : L) = algebraMap (R ⊗[ℂ] B) L x := fun x => rfl
  let ι : R →+* A := a.comp Algebra.TensorProduct.includeLeftRingHom
  let j : B →+* A := a.comp Algebra.TensorProduct.includeRight.toRingHom
  have hcL : ∀ z : ℂ, algebraMap (R ⊗[ℂ] B) L (algebraMap ℂ _ z) = algebraMap ℂ L z := fun z => by
    rw [Algebra.TensorProduct.algebraMap_apply, hft, IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ) L,
      Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hcl : ∀ x, a x ∈ Subring.closure (Set.range ι ∪ Set.range j) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have e : a (x ⊗ₜ y) = ι x * j y := by
        simp [ι, j, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [e]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨x, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨y, rfl⟩))
    | add x y hx hy => rw [map_add (f := _)]; exact Subring.add_mem _ hx hy
  have hmem : ∀ z : ℂ, algebraMap ℂ L z ∈ A.toSubring := fun z => by
    rw [← hcL]; exact A.algebraMap_mem _
  have hevτ : ∀ i, ev (τ i) = 0 := fun i => by
    refine (hev _ 0).1 ?_
    rw [map_zero, sub_zero]
    refine (nonUnit_iff (τ i)).2 fun hu => ?_
    have : τ i ∈ IsLocalRing.maximalIdeal B := by
      rw [hm]; exact Ideal.subset_span ⟨i, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).1 this hu
  refine ⟨A.toSubring, ι, ψ, j, ⟨hR, hRn, ⟨hmem, IsLocalization.AtPrime.isLocalRing A q, ?_, ?_⟩,
    fun z => ?_, fun x => ?_, fun i => ?_, ?_⟩, fun x => rfl, fun y => rfl, fun b z hbz => ?_,
    fun t => ?_⟩
  · have e : (algebraMap ℂ L).codRestrict A.toSubring hmem = a.comp (algebraMap ℂ (R ⊗[ℂ] B)) :=
      RingHom.ext fun z => Subtype.ext (hcL z).symm
    rw [e]
    haveI : Algebra.EssFiniteType ℂ R := RingHom.essFiniteType_algebraMap.1 hR.essFiniteType
    haveI : Algebra.EssFiniteType ℂ B := RingHom.essFiniteType_algebraMap.1 hB.essFiniteType
    haveI : Algebra.EssFiniteType ℂ (R ⊗[ℂ] B) := Algebra.EssFiniteType.comp ℂ R _
    have h1 : (algebraMap (R ⊗[ℂ] B) A).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization A q.primeCompl)
    have h2 : (algebraMap ℂ (R ⊗[ℂ] B)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
    exact h2.comp h1
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R ⊗[ℂ] B) z
    have hy' : algebraMap (R ⊗[ℂ] B) L y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    exact ⟨_, A.algebraMap_mem x, _, A.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩
  · exact (ha _).trans (hcL z)
  · show ψ (a (x ⊗ₜ 1)) = x
    rw [hψ, hφ, map_one, map_one, mul_one]
  · show ψ (a (1 ⊗ₜ τ i)) = 0
    rw [hψ, hφ, hevτ, map_zero, mul_zero]
  · have e : MvPolynomial.eval₂Hom ι (fun i => j (τ i)) =
        a.comp (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℂ] B)
          (fun i => (1 : R) ⊗ₜ[ℂ] τ i)) := by
      ext x <;> simp [ι, j]
    rw [e]
    have h1 : (algebraMap (R ⊗[ℂ] B) A).FormallyEtale :=
      RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization q.primeCompl)
    exact (GlobalTheory.T.formallyEtale_baseChange_eval_hom τ he).comp h1
  · show ((ψ (a (1 ⊗ₜ b)) : R) : K) = _
    rw [hψ, hφ, one_mul, (hev b z).1 hbz]
    rfl
  · obtain ⟨⟨x, y⟩, e⟩ := IsLocalization.surj q.primeCompl (S := A) t
    refine ⟨a x, a y, hcl x, hcl y, ?_, congrArg Subtype.val e⟩
    rw [hψ]; exact hu y

end GlobalTheory.FieldPair.TensorTower
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped TensorProduct

namespace GlobalTheory.GenFibClosure

theorem finite_of_finite_spec (K S : Type) [Field K] [CommRing S] [Algebra K S] [Algebra.FiniteType K S]
    [Finite (PrimeSpectrum S)] : Module.Finite K S := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := K)
  have : DiscreteTopology (PrimeSpectrum S) := JacobsonSpace.discreteTopology (Set.toFinite _)
  exact (Module.finite_iff_krullDimLE_zero K S).2
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.1 this).2

theorem isAlgebraic_of_injective {B S : Type} [CommRing B] [CommRing S] [Algebra ℚ S] [Module.Finite ℚ S]
    (f : B →+* S) (hf : Function.Injective f) : Algebra.IsAlgebraic ℤ B := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℤ S := Algebra.IsAlgebraic.trans ℤ ℚ S
  exact Algebra.IsAlgebraic.of_injective f.toIntAlgHom hf

theorem finiteType_of_surjective {A B : Type} [CommRing A] [CommRing B] [Algebra.FiniteType ℤ A]
    (f : A →+* B) (hf : Function.Surjective f) : Algebra.FiniteType ℤ B :=
  Algebra.FiniteType.of_surjective f.toIntAlgHom hf

theorem isAlgebraic_of_finite (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (h : {Q : PrimeSpectrum B | ∀ n : ℕ, n ≠ 0 → (n : B) ∉ Q.asIdeal}.Finite) : Algebra.IsAlgebraic ℤ B := by
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)
  let S := ℚ ⊗[ℤ] B
  letI : Algebra B S := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization M S := IsLocalization.tensorRight ℚ (nonZeroDivisors ℤ)
  have hinj := PrimeSpectrum.localization_comap_injective S M
  have hfin : Finite (PrimeSpectrum S) := by
    refine Set.finite_univ_iff.1 (Set.Finite.of_finite_image (h.subset ?_) hinj.injOn)
    rintro _ ⟨Q, -, rfl⟩ n hn hQ
    have h1 : (n : S) ∈ Q.asIdeal := by
      have := hQ
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at this
      exact this
    have h2 : IsUnit (n : S) := by
      have : IsUnit (n : ℚ) := (Nat.cast_ne_zero.2 hn).isUnit
      simpa using this.map (algebraMap ℚ S)
    exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 h2)
  have hf : Module.Finite ℚ S := finite_of_finite_spec ℚ S
  have hi : Function.Injective (algebraMap B S) := by
    refine IsLocalization.injective S (M := M) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by simpa using nonZeroDivisors.ne_zero hz)
  exact isAlgebraic_of_injective _ hi

theorem finite_primes_domain (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (h : {Q : PrimeSpectrum B | ∀ n : ℕ, n ≠ 0 → (n : B) ∉ Q.asIdeal}.Finite) (l : ℕ) (hl : l ≠ 0) :
    {Q : PrimeSpectrum B | (l : B) ∈ Q.asIdeal}.Finite := by
  have := isAlgebraic_of_finite B h
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  have hd := GlobalTheory.IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one B (RingHom.injective_int _)
  rw [trdeg_eq_zero] at hd
  have hd1 : Ring.KrullDimLE 1 B := by
    rw [Ring.krullDimLE_iff, hd]; simp
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B (Ideal.span {(l : B)})
  refine (hfin.preimage (f := PrimeSpectrum.asIdeal) fun _ _ _ _ e => PrimeSpectrum.ext e).subset ?_
  intro P hP
  refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hP⟩, fun Q hQ hQP => ?_⟩
  have hQ0 : Q ≠ ⊥ := fun e => by
    have := (Ideal.span_singleton_le_iff_mem _).1 hQ.2
    rw [e] at this
    exact Nat.cast_ne_zero.2 hl this
  have hm : Q.IsMaximal := Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hd1 Q hQ0 hQ.1
  exact (hm.eq_of_le P.isPrime.ne_top hQP).ge

theorem finite_primes (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] (P : PrimeSpectrum A)
    (hP : ∀ n : ℕ, n ≠ 0 → (n : A) ∉ P.asIdeal)
    (h : {Q : PrimeSpectrum A | P ≤ Q ∧ ∀ n : ℕ, n ≠ 0 → (n : A) ∉ Q.asIdeal}.Finite) (l : ℕ) (hl : l ≠ 0) :
    {Q : PrimeSpectrum A | P ≤ Q ∧ (l : A) ∈ Q.asIdeal}.Finite := by
  let π := Ideal.Quotient.mk P.asIdeal
  have hs : Function.Surjective π := Ideal.Quotient.mk_surjective
  have : CharZero (A ⧸ P.asIdeal) := @CharP.charP_to_charZero _ _ (by
    refine ⟨fun n => ⟨fun hn => ?_, fun hn => by rw [zero_dvd_iff.1 hn, Nat.cast_zero]⟩⟩
    by_contra hne
    refine hP n (fun e => hne (e ▸ dvd_rfl)) ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hn)
  have := finiteType_of_surjective π hs
  have hinj := PrimeSpectrum.comap_injective_of_surjective π hs
  have hr : Set.range (PrimeSpectrum.comap π) = PrimeSpectrum.zeroLocus (P.asIdeal : Set A) := by
    rw [range_comap_of_surjective _ π hs, Ideal.mk_ker]
  have hf := finite_primes_domain (A ⧸ P.asIdeal) ((h.preimage hinj.injOn).subset fun Q hQ => ⟨by
    have : PrimeSpectrum.comap π Q ∈ PrimeSpectrum.zeroLocus (P.asIdeal : Set A) := hr ▸ ⟨Q, rfl⟩
    exact this, fun n hn h1 => hQ n hn (by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at h1; exact h1)⟩) l hl
  refine (hf.image (PrimeSpectrum.comap π)).subset ?_
  rintro Q ⟨h1, h2⟩
  have : Q ∈ Set.range (PrimeSpectrum.comap π) := hr ▸ h1
  obtain ⟨Q, rfl⟩ := this
  refine ⟨Q, ?_, rfl⟩
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at h2
  exact h2

theorem natCast_eq_zero_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (Q : PrimeSpectrum Γ(X, U)) (n : ℕ) :
    (n : X.residueField (hU.fromSpec Q)) = 0 ↔ (n : Γ(X, U)) ∈ Q.asIdeal := by
  have hx : hU.fromSpec Q ∈ U := by
    have : hU.fromSpec Q ∈ Set.range hU.fromSpec := ⟨Q, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hb : hU.fromSpec Q ∈ X.basicOpen (n : Γ(X, U)) ↔ (n : Γ(X, U)) ∉ Q.asIdeal :=
    SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen _) Q
  rw [← map_natCast (X.evaluation U _ hx).hom n]
  exact (X.evaluation_eq_zero_iff_notMem_basicOpen _ hx _).trans (hb.not.trans not_not)

theorem finite_closure_inter_fib : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ W : Set X, IsClosed W → (W ∩ fib X 0).Finite → ∀ ℓ : ℕ, (closure (W ∩ fib X 0) ∩ fib X ℓ).Finite := by
  intro k _ X _ p D hX W hW hfin l
  have hsub : closure (W ∩ fib X 0) ⊆ W := closure_minimal Set.inter_subset_left hW
  rcases eq_or_ne l 0 with rfl | hl
  · exact hfin.subset (Set.inter_subset_inter_left _ hsub)
  have := hX.isNoetherian
  have hft : LocallyOfFiniteType (p ≫ spMap (Int.castRingHom k)) := by
    obtain ⟨N, j, _, hj⟩ := hX.isProjOver
    have := isProper_str k N
    have : IsProper p := hj ▸ inferInstance
    have : IsFinite (spMap (Int.castRingHom k)) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
    infer_instance
  have key (U : X.Opens) (hU : IsAffineOpen U) : (closure (W ∩ fib X 0) ∩ fib X l ∩ U).Finite := by
    have : Algebra.FiniteType ℤ Γ(X, U) := by
      set t := p ≫ spMap (Int.castRingHom k)
      have e : (t.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom =
        algebraMap ℤ Γ(X, U) := RingHom.ext_int _ _
      rw [← RingHom.finiteType_algebraMap, ← e, RingHom.finiteType_respectsIso.cancel_left_isIso]
      exact HasRingHomProperty.appLE @LocallyOfFiniteType t hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    have hemb := hU.fromSpec.isOpenEmbedding
    have h0 (Q : PrimeSpectrum Γ(X, U)) :
        hU.fromSpec Q ∈ fib X 0 ↔ ∀ n : ℕ, n ≠ 0 → (n : Γ(X, U)) ∉ Q.asIdeal := by
      change ringChar _ = 0 ↔ _
      simp only [← natCast_eq_zero_iff hU, ringChar.spec]
      refine ⟨fun h n hn => by rw [h, zero_dvd_iff]; exact hn, fun h => ?_⟩
      by_contra hne
      exact h _ hne dvd_rfl
    have hS : (hU.fromSpec ⁻¹' (W ∩ fib X 0)).Finite := hfin.preimage hemb.injective.injOn
    have hT := hS.biUnion (t := fun P : PrimeSpectrum Γ(X, U) =>
        {Q : PrimeSpectrum Γ(X, U) | P ≤ Q ∧ (l : Γ(X, U)) ∈ Q.asIdeal}) fun P hP =>
      finite_primes _ P ((h0 P).1 hP.2) (hS.subset fun Q hQ => ⟨hW.stableUnderSpecialization
        (((PrimeSpectrum.le_iff_specializes P Q).1 hQ.1).map hemb.continuous) hP.1, (h0 Q).2 hQ.2⟩) l hl
    refine (hT.image hU.fromSpec).subset ?_
    rintro y ⟨⟨hy, hyl⟩, hyU⟩
    have : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hyU
    obtain ⟨Q, rfl⟩ := this
    refine ⟨Q, ?_, rfl⟩
    have h1 : Q ∈ closure (hU.fromSpec ⁻¹' (W ∩ fib X 0)) := by
      rw [← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]; exact hy
    rw [← Set.biUnion_of_singleton (hU.fromSpec ⁻¹' (W ∩ fib X 0)), hS.closure_biUnion] at h1
    obtain ⟨P, hP, h1⟩ := Set.mem_iUnion₂.1 h1
    refine Set.mem_iUnion₂.2 ⟨P, hP, (PrimeSpectrum.le_iff_specializes P Q).2 (specializes_iff_mem_closure.2 h1), ?_⟩
    exact (natCast_eq_zero_iff hU Q l).1 ((ringChar.spec _ _).2 (dvd_of_eq hyl))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.2)
    fun x _ => by
      obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩
  refine (s.finite_toSet.biUnion fun U _ => key U.1 U.2).subset fun y hy => ?_
  obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  exact Set.mem_iUnion₂.2 ⟨U, hU, hy, hyU⟩

end GlobalTheory.GenFibClosure
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.Denom

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem exists_sec_tens {L M : LB Y} (hL : L.IsLB) (hM : M.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (u : M.Sec) (hu : genericPoint Y ∈ nonzeroLocus u)
    (hE : (divOfRatSec hL hr + divOfSec hM u hu).Eff) :
    ∃ (t : (tens L M).Sec) (ht : genericPoint Y ∈ nonzeroLocus t), ∀ i j, genericPoint Y ∈ L.U i →
      genericPoint Y ∈ M.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j := by
  have P := (presents_divOfRatSec hL hr).tens (presents_divOfRatSec hM (isRatSec_ratOfSec u hu))
  obtain ⟨t, ht⟩ := P.exists_rat_eq (f := 1) (CartierDiv.mem_sections.2 fun x => hE x)
  have hη : genericPoint Y ∈ nonzeroLocus t :=
    (P.generatesAt_rat_iff t).1 (ht ▸ CartierDiv.generatesAt_genericPoint _ one_ne_zero)
  refine ⟨t, hη, fun i j hi hj => Units.ext ?_⟩
  have e := P.rat_mul t (i, j) ⟨hi, hj⟩
  rw [ht, one_mul] at e
  rw [val_ratOfSec (show genericPoint Y ∈ (tens L M).U (i, j) from ⟨hi, hj⟩), ← e]

theorem gen_mem_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m) := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  have hj : genericPoint Y ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  refine (mem_nonzeroLocus_iff _ _ hj).2 ((unitAt_fnOf_iff hj hj _).1 (unitAt_genericPoint ?_))
  show fnOf _ hj (resG Y _ (t.f i) ^ m) ≠ 0
  rw [map_pow, fnOf_resG]
  exact pow_ne_zero _ (fnOf_sec_ne_zero ht hi)

theorem divOfSec_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) (hm : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m)) :
    divOfSec (isLB_lbPow hL m) (Cartier.secPow t m) hm = m • divOfSec hL t ht := by
  refine CartierDiv.ext_of_isEqn fun x => ?_
  obtain ⟨i, hi⟩ := exists_chart hL x
  have hj : x ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  have e : ratOfSec (Cartier.secPow t m) hm (fun _ => i) = ratOfSec t ht i ^ m := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj)]
    show fnOf _ (gen_mem hj) (resG Y _ (t.f i) ^ m) = _
    rw [map_pow, fnOf_resG]
  refine ⟨ratOfSec t ht i ^ m, ?_,
    ((presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i x hi).nsmul m⟩
  rw [← e]
  exact (presents_divOfRatSec (isLB_lbPow hL m) (isRatSec_ratOfSec _ hm)).isEqn _ x hj

theorem exists_open_regularAt {L : LB Y} (hL : L.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) :
    ∃ W : Y.Opens, genericPoint Y ∈ W ∧ ∀ x ∈ W, (divOfRatSec hL hr).RegularAt x 1 := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  obtain ⟨U, hU, a, ha⟩ := (regAt_genericPoint (r i : Y.functionField)).exists_fnOf
  refine ⟨L.U i ⊓ U, ⟨hi, hU⟩, fun x hx => ?_⟩
  refine ((presents_divOfRatSec hL hr).isEqn i x hx.1).regularAt_iff.2 ?_
  rw [one_mul, ← ha]
  exact regAt_fnOf hx.2 _ a

end GlobalTheory.MixHt.Denom


open GlobalTheory.MixHt.Denom in
theorem GlobalTheory.MixHt.exists_common_denom : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ (N : HermLB q) (r r' : N.B.ι → Y.functionFieldˣ), IsRatSec N.B r →
    IsRatSec N.B r' → ∃ (A : HermLB q) (u : A.B.Sec) (t t' : (N.tens A).B.Sec)
    (hu : genericPoint Y ∈ nonzeroLocus u) (ht : genericPoint Y ∈ nonzeroLocus t)
    (ht' : genericPoint Y ∈ nonzeroLocus t'), ∀ (i : N.B.ι) (j : A.B.ι), genericPoint Y ∈ N.B.U i →
    genericPoint Y ∈ A.B.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j ∧
      ratOfSec t' ht' (i, j) = r' i * ratOfSec u hu j := by
  intro k _ Y _ q hq N r r' hr hr'
  obtain ⟨n₀, j, hj, hjq⟩ := hq.isProjOver
  let H₀ : HermLB (PSpace.str k n₀) :=
    .fs _ (isAmple_projective_O_one k n₀).isLB (ProjSpace.coord k n₀)
      (ProjSpace.iSup_nonzeroLocus_coord k n₀) (fun _ => 1) (fun _ => by simp)
      (fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩)
  let H : HermLB q := H₀.pull j hjq
  have hH : IsAmpleLB H.B := (isAmple_projective_O_one k n₀).pull_of_isClosedImmersion j
  haveI := hH.compactSpace
  obtain ⟨W, hW, hWr⟩ := exists_open_regularAt N.isLB hr
  obtain ⟨W', hW', hWr'⟩ := exists_open_regularAt N.isLB hr'
  obtain ⟨n, -, t, ht, hle, -⟩ :=
    hH.exists_affine_le (x := genericPoint Y) (U := W ⊓ W') ⟨hW, hW'⟩
  have hL := isLB_lbPow H.isLB n
  obtain ⟨N₁, h₁⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr x (hle hx).1
  obtain ⟨N₂, h₂⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr' x (hle hx).2
  have hu := gen_mem_secPow hL t ht (max N₁ N₂)
  have hD := divOfSec_secPow hL t ht (max N₁ N₂) hu
  obtain ⟨s, hs, e⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₁ _ (le_max_left _ _))
  obtain ⟨s', hs', e'⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr' (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₂ _ (le_max_right _ _))
  exact ⟨(H.pow n).pow (max N₁ N₂), Cartier.secPow t (max N₁ N₂), s, s', hu, hs, hs',
    fun i j hi hj => ⟨e i j hi hj, e' i j hi hj⟩⟩
end
end
