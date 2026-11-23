module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Smooth.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

section

open IntermediateField

namespace GlobalTheory

theorem fixedField_ker_toPerm_finite_isGalois_finrank_dvd (Ω K : Type) [Field Ω] [Field K]
    [Algebra Ω K] [IsAlgClosure Ω K] [CharZero Ω] (n : ℕ)
    (φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin n)) :
    FiniteDimensional Ω (IntermediateField.fixedField φ.ker) ∧
      IsGalois Ω (IntermediateField.fixedField φ.ker) ∧
      Module.finrank Ω (IntermediateField.fixedField φ.ker) ∣ n.factorial := by
  haveI : Algebra.IsAlgebraic Ω K := IsAlgClosure.isAlgebraic
  haveI : Normal Ω K := IsAlgClosure.normal Ω K
  haveI : IsGalois Ω K := ⟨⟩
  set E : IntermediateField Ω K := fixedField φ.ker with hE
  have hHF : φ.ker ≤ E.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hker : φ.ker.index ∣ n.factorial := by
    rw [Subgroup.index_ker]
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [Nat.card_perm, Nat.card_fin] at h
  have hF : E.fixingSubgroup.index ∣ n.factorial :=
    (Subgroup.index_dvd_of_le hHF).trans hker
  haveI : E.fixingSubgroup.FiniteIndex :=
    ⟨fun h => (Nat.factorial_pos n).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hF))⟩
  have hopen : IsOpen (E.fixingSubgroup : Set (K ≃ₐ[Ω] K)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (InfiniteGalois.fixingSubgroup_isClosed E)
  haveI hfin : FiniteDimensional Ω E := (InfiniteGalois.isOpen_iff_finite E).1 hopen
  have hnorm : E.fixingSubgroup.Normal := by
    constructor
    intro σ hσ g
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hx' : g⁻¹ x ∈ E := by
      rw [hE, IntermediateField.mem_fixedField_iff] at hx ⊢
      intro h hh
      have hc : g * h * g⁻¹ ∈ φ.ker := (MonoidHom.normal_ker φ).conj_mem h hh g
      have := hx _ hc
      calc h (g⁻¹ x) = g⁻¹ ((g * h * g⁻¹) x) := by simp [AlgEquiv.mul_apply]
        _ = g⁻¹ x := by rw [this]
    have h2 := hσ _ hx'
    simp only [AlgEquiv.mul_apply]
    change g (σ (g⁻¹ x)) = x
    rw [h2]
    exact g.apply_symm_apply x
  haveI hgal : IsGalois Ω E := (InfiniteGalois.normal_iff_isGalois E).1 hnorm
  refine ⟨hfin, hgal, ?_⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  exact hF

end GlobalTheory
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.AbsIntClosedLocal

theorem exists_root_sub_mem_of_eval_mem (T : Type) [CommRing T] [IsLocalRing T] [IsDomain T]
    (hroot : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    ∀ (n : ℕ) (f : T[X]), f.Monic → f.natDegree = n → ∀ a₀ : T, f.eval a₀ ∈ maximalIdeal T →
      ∃ a : T, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal T := by
  intro n
  induction n with
  | zero =>
    intro f hf hdeg a₀ hmem
    have : f = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
      have := hf.coeff_natDegree
      rw [hdeg] at this
      rw [this, map_one]
    rw [this, eval_one] at hmem
    exact absurd ((Ideal.eq_top_iff_one _).2 hmem) (maximalIdeal.isMaximal T).ne_top
  | succ n ih =>
    intro f hf hdeg a₀ hmem
    obtain ⟨r, hr⟩ := hroot f hf (by omega)
    have hrr : f.IsRoot r := hr
    have hdiv := (mul_divByMonic_eq_iff_isRoot (p := f) (a := r)).2 hrr
    set g := f /ₘ (X - C r) with hg
    have hgm : g.Monic := (monic_X_sub_C r).of_mul_monic_left (by rw [hdiv]; exact hf)
    have hgdeg : g.natDegree = n := by
      have := natDegree_divByMonic f (monic_X_sub_C r)
      rw [natDegree_X_sub_C] at this
      rw [hg, this, hdeg]; omega
    have hev : f.eval a₀ = (a₀ - r) * g.eval a₀ := by
      conv_lhs => rw [← hdiv]
      simp [eval_mul]
    rw [hev] at hmem
    rcases (maximalIdeal.isMaximal T).isPrime.mem_or_mem hmem with h | h
    · refine ⟨r, hrr, ?_⟩
      have := (maximalIdeal T).neg_mem h
      simpa using this
    · obtain ⟨a, ha, ha'⟩ := ih g hgm hgdeg a₀ h
      refine ⟨a, ?_, ha'⟩
      rw [← hdiv]
      simp [IsRoot, eval_mul, ha.eq_zero]

theorem henselian_isAlgClosed_pow_surj :
    ∀ (T : Type) [CommRing T] [IsLocalRing T], (IsDomain T ∧ ∀ f : Polynomial T, f.Monic →
      0 < f.natDegree → ∃ x : T, f.eval x = 0) →
      HenselianLocalRing T ∧ IsAlgClosed (ResidueField T) ∧
        ∀ (n : ℕ) (u : Tˣ), 0 < n → ∃ v : Tˣ, v ^ n = u := by
  intro T _ _ ⟨hdom, hroot⟩
  refine ⟨⟨fun f hf a₀ h₁ _ => exists_root_sub_mem_of_eval_mem T hroot _ f hf rfl a₀ h₁⟩, ?_, ?_⟩
  · refine IsAlgClosed.of_exists_root _ (fun p hpm hpirr => ?_)
    have hl : p ∈ lifts (residue T) := (mem_lifts p).2 (map_surjective _ residue_surjective p)
    obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hpm
    obtain ⟨x, hx⟩ := hroot q hqm (by rw [hqd]; exact hpirr.natDegree_pos)
    refine ⟨residue T x, ?_⟩
    rw [← hq, eval_map, eval₂_hom, hx, map_zero]
  · intro n u hn
    obtain ⟨x, hx⟩ := hroot (X ^ n - C (u : T)) (monic_X_pow_sub_C _ hn.ne')
      (by rw [natDegree_X_pow_sub_C _]; exact hn)
    have hxn : x ^ n = (u : T) := by
      simp only [eval_sub, eval_pow, eval_X, eval_C] at hx
      exact sub_eq_zero.1 hx
    have hxu : IsUnit x := (isUnit_pow_iff hn.ne').1 (hxn ▸ u.isUnit)
    refine ⟨hxu.unit, Units.ext ?_⟩
    simp [hxn]

end GlobalTheory.AbsIntClosedLocal
end

section

open Matrix

namespace GlobalTheory

theorem range_idempotent_projective {A : Type} [CommRing A] (n : ℕ) (P : Matrix (Fin n) (Fin n) A)
    (hP : P * P = P) : Module.Projective A (LinearMap.range P.mulVecLin) := by
  refine Module.Projective.of_split (LinearMap.range P.mulVecLin).subtype P.mulVecLin.rangeRestrict ?_
  ext ⟨v, w, rfl⟩ j
  simp [Matrix.mulVec_mulVec, hP]

theorem exists_rank_ideal_of_idempotent : ∀ (A : Type) [CommRing A] (I : Type) [Fintype I] (n : ℕ) (P : I → Matrix (Fin n) (Fin n) A),
    (∀ i, P i * P i = P i) → ∀ (m : ℕ), ∃ x : A, ∀ (T : Type) [CommRing T] (f : A →+* T),
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : I),
          Module.rankAtStalk (LinearMap.range (P i).mulVecLin)
            (⟨RingHom.ker (h.comp f), RingHom.ker_isPrime _⟩ : PrimeSpectrum A) = m) ↔ f x = 0) := by
  intro A _ I _ n P hP m
  let V : Set (PrimeSpectrum A) :=
    ⋂ i, {q | Module.rankAtStalk (LinearMap.range (P i).mulVecLin) q = m}
  have hV : IsClopen V := by
    refine isClopen_iInter_of_finite fun i => ?_
    have := range_idempotent_projective n (P i) (hP i)
    have := Module.finitePresentation_of_projective A (LinearMap.range (P i).mulVecLin)
    exact (Module.isLocallyConstant_rankAtStalk (R := A)
      (M := LinearMap.range (P i).mulVecLin)).isClopen_fiber m
  obtain ⟨e, x, hmul, hadd, hVe⟩ := PrimeSpectrum.isClopen_iff_mul_add.mp hV
  refine ⟨x, fun T _ f => ?_⟩
  have hmem : ∀ q : PrimeSpectrum A, q ∈ V ↔ e ∉ q.asIdeal := by
    intro q; rw [hVe]; rfl
  have hmem' : ∀ q : PrimeSpectrum A, q ∈ V ↔ ∀ i, Module.rankAtStalk (LinearMap.range (P i).mulVecLin) q = m := by
    intro q; simp [V]
  constructor
  · intro H
    have hxx : f x * f x = f x := by
      have : x * x = x := by
        have h1 : x = x * (e + x) := by rw [hadd, mul_one]
        calc x * x = x * (e + x) - x * e := by ring
          _ = x := by rw [← h1, mul_comm x e, hmul, sub_zero]
      rw [← map_mul, this]
    have hnil : IsNilpotent (f x) := by
      rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
      intro (Q : Ideal T) hQ
      haveI : Q.IsPrime := hQ
      let k := AlgebraicClosure (FractionRing (T ⧸ Q))
      let h : T →+* k := (algebraMap (FractionRing (T ⧸ Q)) k).comp
        ((algebraMap (T ⧸ Q) (FractionRing (T ⧸ Q))).comp (Ideal.Quotient.mk Q))
      have hker : RingHom.ker h = Q := by
        ext t
        simp only [h, RingHom.mem_ker, RingHom.comp_apply]
        rw [map_eq_zero_iff _ (algebraMap (FractionRing (T ⧸ Q)) k).injective,
          IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      have hq := (hmem _).mp ((hmem' _).mpr (H k h))
      have : e * x ∈ RingHom.ker (h.comp f) := by rw [hmul]; exact Ideal.zero_mem _
      rcases (RingHom.ker_isPrime (h.comp f)).mem_or_mem this with he | hx
      · exact absurd he hq
      · rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hker] at hx
        exact hx
    obtain ⟨N, hN⟩ := hnil
    have : ∀ j : ℕ, f x ^ (j + 1) = f x := by
      intro j; induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, ih, hxx]
    rcases N with _ | N
    · simp at hN; exact (subsingleton_of_zero_eq_one hN.symm).elim _ _
    · rw [this] at hN; exact hN
  · intro hx k _ _ h i
    refine ((hmem' _).mp ?_) i
    rw [hmem]
    show e ∉ RingHom.ker (h.comp f)
    rw [RingHom.mem_ker, RingHom.comp_apply]
    have : f e = 1 := by
      have := congrArg f hadd
      rw [map_add (f := _), hx, add_zero, map_one] at this; exact this
    rw [this, map_one]; exact one_ne_zero

end GlobalTheory
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem kerCotangentToTensor_injective_of_formallySmooth (k R F : Type*) [CommRing k] [CommRing R]
    [CommRing F] [Algebra k R] [Algebra k F] [Algebra R F] [IsScalarTower k R F]
    [Algebra.FormallySmooth k F] (hs : Function.Surjective (algebraMap R F)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R F) := by
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom k R F).kerSquareLift :=
    fun x ↦ by
      obtain ⟨y, rfl⟩ := hs x
      exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hnil : RingHom.ker (IsScalarTower.toAlgHom k R F).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) hs).symm
    ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k F) _ hsurj ⟨2, hnil⟩⟩
  exact Function.LeftInverse.injective (g := l) fun x ↦ congr($hl x)

theorem mem_sq_localization_of_pderiv_mem :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by
  intro Λ _ _ _ σ _ Q _ hQ x hx hd
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  let R := Localization.AtPrime Q
  let F := ResidueField R
  let k := FractionRing Λ
  have hunit : ∀ a : nonZeroDivisors Λ, IsUnit (algebraMap Λ R a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply Λ (MvPolynomial σ Λ) R]
    exact IsLocalization.map_units R (M := Q.primeCompl)
      ⟨MvPolynomial.C a.1, fun h => nonZeroDivisors.coe_ne_zero a (hQ _ h)⟩
  letI : Algebra k R := (IsLocalization.lift (M := nonZeroDivisors Λ) (S := k) hunit).toAlgebra
  haveI : IsScalarTower Λ k R := IsScalarTower.of_algebraMap_eq
    (fun a => (IsLocalization.lift_eq (M := nonZeroDivisors Λ) (S := k) hunit a).symm)
  letI : Algebra k F := ((algebraMap R F).comp (algebraMap k R)).toAlgebra
  haveI : IsScalarTower k R F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Λ k F := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [IsScalarTower.algebraMap_apply Λ R F, IsScalarTower.algebraMap_apply Λ k R]; rfl)
  haveI : Algebra.EssFiniteType (MvPolynomial σ Λ) R := .of_isLocalization R Q.primeCompl
  haveI : Algebra.EssFiniteType Λ R := .comp Λ (MvPolynomial σ Λ) R
  haveI : Algebra.EssFiniteType R F := .of_surjective (Algebra.ofId R F) residue_surjective
  haveI : Algebra.EssFiniteType Λ F := .comp Λ R F
  haveI : Algebra.EssFiniteType k F := Algebra.EssFiniteType.of_comp Λ k F
  haveI : Algebra.FormallySmooth k F := Algebra.FormallySmooth.of_perfectField
  haveI : Algebra.FormallySmooth Λ k := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors Λ)
  haveI : Algebra.FormallySmooth Λ F := Algebra.FormallySmooth.comp Λ k F
  have hinj := kerCotangentToTensor_injective_of_formallySmooth Λ R F (residue_surjective)
  have hker : RingHom.ker (algebraMap R F) = maximalIdeal R := ker_residue
  have hmem : ∀ p ∈ Q, algebraMap (MvPolynomial σ Λ) R p ∈ RingHom.ker (algebraMap R F) := by
    intro p hp
    rw [hker]; exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R Q p).mpr hp
  have hym := hmem x hx
  have hD : KaehlerDifferential.D Λ (MvPolynomial σ Λ) x =
      ∑ s, MvPolynomial.pderiv s x • KaehlerDifferential.D Λ (MvPolynomial σ Λ) (MvPolynomial.X s) := by
    conv_lhs => rw [← (KaehlerDifferential.mvPolynomialBasis Λ σ).sum_repr (KaehlerDifferential.D Λ _ x)]
    simp [KaehlerDifferential.mvPolynomialBasis_repr_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  have h0 : KaehlerDifferential.kerCotangentToTensor Λ R F
      ((RingHom.ker (algebraMap R F)).toCotangent ⟨_, hym⟩) = 0 := by
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]

    rw [← KaehlerDifferential.map_D Λ Λ (MvPolynomial σ Λ) R, hD, map_sum, tmul_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [LinearMap.map_smul_of_tower, ← algebraMap_smul R, ← smul_tmul, Algebra.smul_def, mul_one,
      RingHom.mem_ker.mp (hmem _ (hd s)), zero_tmul]
  have h2 : algebraMap (MvPolynomial σ Λ) R x ∈ RingHom.ker (algebraMap R F) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp (hinj (h0.trans (map_zero _).symm))
  rw [hker, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow] at h2
  obtain ⟨m, hm, hmx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl) (S := R) _ _).mp h2
  exact ⟨m, hm, hmx⟩

end GlobalTheory
end
