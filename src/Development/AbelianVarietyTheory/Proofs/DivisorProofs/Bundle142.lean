module

public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationRing
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
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.RamGalDVR

theorem isSeparable_of_natCast_finrank_ne_zero' {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  refine ⟨fun x => ?_⟩
  have hint : IsIntegral F x := IsIntegral.of_finite F x
  have hdvd := minpoly.degree_dvd hint
  show (minpoly F x).Separable
  rw [Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
  intro hd
  set n := (minpoly F x).natDegree with hn
  have hpos : 0 < n := minpoly.natDegree_pos hint
  have hc := congrArg (fun p : Polynomial F => p.coeff (n - 1)) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc
  rw [Nat.sub_add_cancel hpos] at hc
  have hlead : (minpoly F x).coeff n = 1 := minpoly.monic hint
  rw [hlead, one_mul] at hc
  have hn0 : (n : F) = 0 := by
    have : ((n - 1 : ℕ) : F) + 1 = ((n - 1 + 1 : ℕ) : F) := by push_cast; ring
    rw [this, Nat.sub_add_cancel hpos] at hc
    exact hc
  obtain ⟨c, hc'⟩ := hdvd
  exact h (by rw [hc', Nat.cast_mul, hn0, zero_mul])

theorem isSeparable_of_isField {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    [Module.Finite F E] (hF : IsField F) (hE : IsField E)
    (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  letI := hF.toField
  letI := hE.toField
  exact @isSeparable_of_natCast_finrank_ne_zero' F E _ _ ‹Algebra F E› ‹Module.Finite F E› h

theorem ramGal : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field K] [Algebra S K]
    [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [IsGalois K L] (q : ℕ), 0 < q → IsUnit (q : S) →
    Module.finrank K L ∣ q →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) ∧
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ q _ hq hdeg
  set B := integralClosure S L
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : Module.Finite S B := IsIntegralClosure.finite S K L B
  have : IsGaloisGroup (L ≃ₐ[K] L) S B := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have hinj : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have : FaithfulSMul S B :=
    (faithfulSMul_iff_algebraMap_injective S _).2 (fun a b h => hinj (congrArg Subtype.val h))
  have : Module.Flat S B :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (maximalIdeal S) B (L ≃ₐ[K] L)
  rw [IsGalois.card_aut_eq_finrank] at hfund
  have hef : Ideal.ramificationIdxIn (maximalIdeal S) B * Ideal.inertiaDegIn (maximalIdeal S) B ∣ q :=
    (Dvd.intro_left _ hfund).trans hdeg
  have hlies : ∀ P : Ideal B, P.IsMaximal → P.LiesOver (maximalIdeal S) := by
    intro P hP
    refine ⟨?_⟩
    have : (P.under S).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
    exact (IsLocalRing.eq_maximalIdeal this).symm
  refine ⟨fun P hP => ?_, fun P hP _ => ?_⟩
  · have := hlies P hP
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal S) P (L ≃ₐ[K] L)]
    exact (Dvd.intro _ rfl).trans hef
  · have := hP
    have : (maximalIdeal S).IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
    have hf : Module.finrank (S ⧸ maximalIdeal S) (B ⧸ P) ∣ q := by
      rw [← Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal S) P,
        ← Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal S) P (L ≃ₐ[K] L)]
      exact (Dvd.intro_left _ rfl).trans hef
    have : Module.Finite S (B ⧸ P) := inferInstance
    have : Module.Finite (S ⧸ maximalIdeal S) (B ⧸ P) :=
      Module.Finite.of_restrictScalars_finite S _ _
    refine isSeparable_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance)
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hP) ?_
    obtain ⟨c, hc⟩ := hf
    intro h0
    have hu : IsUnit ((q : S) : S ⧸ maximalIdeal S) := hq.map (Ideal.Quotient.mk _)
    rw [map_natCast, hc, Nat.cast_mul, h0, zero_mul] at hu
    exact not_isUnit_zero hu

end GlobalTheory.RamGalDVR
end

section

open IsLocalRing

namespace GlobalTheory

theorem pi_eq_pow_ramificationIdx_mul_unit
    (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D]
    (P : Ideal (integralClosure S L)) [P.IsMaximal] :
    Irreducible π → algebraMap S (integralClosure S L) π ∈ P →
      ∃ ϖ : Localization.AtPrime P, Irreducible ϖ ∧ ∃ u : (Localization.AtPrime P)ˣ,
        algebraMap S (Localization.AtPrime P) π = ϖ ^ P.ramificationIdx S * (u : Localization.AtPrime P) := by
  intro hπ hπP
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hO0 : algebraMap S (integralClosure S L) π ≠ 0 := by
    intro h
    have h2 : algebraMap (integralClosure S L) L (algebraMap S (integralClosure S L) π) = 0 := by rw [h, map_zero]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S K L] at h2
    rw [map_eq_zero_iff _ (algebraMap K L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective S K)] at h2
    exact hπ0 h2
  have hPbot : P ≠ ⊥ := fun h => hO0 (by rw [h] at hπP; simpa using hπP)
  haveI hA : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure S L) hPbot (Localization.AtPrime P)
  have hinj : Function.Injective (algebraMap (integralClosure S L) (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have hx0 : algebraMap S (Localization.AtPrime P) π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply S (integralClosure S L) (Localization.AtPrime P)]
    exact fun h => hO0 (hinj (by rw [h, map_zero]))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ

  have hunder : P.under S = Ideal.span {π} := by
    have hmem : π ∈ P.under S := by simpa [Ideal.under] using hπP
    have hne : P.under S ≠ ⊥ := fun h => hπ0 (by rw [h] at hmem; simpa using hmem)
    have hmax : (P.under S).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
    rw [IsLocalRing.eq_maximalIdeal hmax, hπ.maximalIdeal_eq]
  have hram : P.ramificationIdx S = n := by
    rw [Ideal.ramificationIdx_def, hunder, Ideal.map_span, Set.image_singleton, hn,
      Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
      ENat.toNat_natCast]
  refine ⟨ϖ, hϖ, u, ?_⟩
  rw [hram, hn, mul_comm]

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

theorem exists_ringHom_lift_of_formallySmooth {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    (φ : R →+* A) (hφ : φ.FormallySmooth) (ψ : R →+* C) (I : Ideal C) (hI : IsNilpotent I)
    (g : A →+* C ⧸ I) (hg : g.comp φ = (Ideal.Quotient.mk I).comp ψ) :
    ∃ F : A →+* C, (∀ x, Ideal.Quotient.mk I (F x) = g x) ∧ ∀ r, F (φ r) = ψ r := by
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  haveI : Algebra.FormallySmooth R A := hφ
  let g' : A →ₐ[R] C ⧸ I :=
    { g with
      commutes' := fun r => by
        have := congrArg (· r) hg
        exact this }
  refine ⟨(Algebra.FormallySmooth.lift I hI g').toRingHom, fun x => ?_, fun r => ?_⟩
  · exact Algebra.FormallySmooth.mk_lift I hI g' x
  · have := (Algebra.FormallySmooth.lift I hI g').commutes r
    simpa [RingHom.algebraMap_toAlgebra] using this

def powModP (p : ℕ) (hp : p.Prime) (B : Type) [CommRing B] :
    B →+* B ⧸ Ideal.span {(p : B)} where
  toFun z := Ideal.Quotient.mk _ (z ^ p)
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]
  map_zero' := by simp [zero_pow hp.ne_zero]
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
    rw [hr, map_add (f := _), map_add (f := _)]
    have : Ideal.Quotient.mk (Ideal.span {(p : B)}) ((p : B) * x * y * r) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, mul_assoc, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [this, add_zero]

theorem frob_lift_etale_chart :
    ∀ (p : ℕ) [Fact p.Prime] {n : ℕ} {B : Type} [CommRing B]
      (φ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B), φ.Etale →
      ∃ F : B →+* B, (∀ z, ∃ w, F z = z ^ p + p * w) ∧
        ∀ l, F (φ (MvPolynomial.X l)) = φ (MvPolynomial.X l) ^ p := by
  intro p hpf n B _ φ hφ
  have hp : p.Prime := hpf.out
  set I : Ideal B := Ideal.span {(p : B)} with hIdef
  have hp2 : ((p : B)) ^ 2 = 0 := by
    have : ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) = 0 := by
      rw [← map_natCast (MvPolynomial.C (σ := Fin n)), ZMod.natCast_self, map_zero]
    calc ((p : B)) ^ 2 = φ ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) := by
          rw [map_natCast]; push_cast; rfl
      _ = 0 := by rw [this, map_zero]
  have hI : IsNilpotent I := by
    refine ⟨2, ?_⟩
    rw [hIdef, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.zero_eq_bot]
  have hsm : φ.FormallySmooth := by
    letI := φ.toAlgebra
    haveI : Algebra.Etale _ B := hφ
    show Algebra.FormallySmooth _ B
    infer_instance
  let ψ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B :=
    φ.comp (MvPolynomial.expand p).toRingHom
  have hg : (powModP p hp B).comp φ = (Ideal.Quotient.mk I).comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact congrArg (· r) (Subsingleton.elim ((((powModP p hp B).comp φ)).comp MvPolynomial.C)
        (((Ideal.Quotient.mk I).comp ψ).comp MvPolynomial.C))
    · intro i
      simp [ψ, powModP, I]
  obtain ⟨F, hF1, hF2⟩ := exists_ringHom_lift_of_formallySmooth φ hsm ψ I hI (powModP p hp B) hg
  refine ⟨F, fun z => ?_, fun l => ?_⟩
  · have h1 := hF1 z
    have : F z - z ^ p ∈ I := by
      rw [← Ideal.Quotient.eq]
      exact h1
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨w, by rw [mul_comm]; linear_combination -hw⟩
  · rw [hF2]
    simp [ψ]

end GlobalTheory.DI
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open TensorProduct

namespace GlobalTheory.TorStep

theorem mul_tensor_injective : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B]
    [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂),
    Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ →
    RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ →
    a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := by
  intro P R₂ B B₂ _ _ _ _ _ K₁ f₂ a₂ c₂ hf hc hcomp hker hK hflat
  letI := a₂.toAlgebra
  haveI : Module.Flat R₂ B₂ := hflat
  have hc' : ∀ p : P, c₂ (algebraMap P B p) = a₂ (f₂ p) := fun p => by
    simpa using congrArg (fun g : P →+* B₂ => g p) hcomp
  have hsmulB : ∀ (p : P) (b : B), c₂ (p • b) = f₂ p • c₂ b := fun p b => by
    rw [Algebra.smul_def, map_mul, hc', Algebra.smul_def, RingHom.algebraMap_toAlgebra]

  have hzero : ∀ x : P, x ∈ K₁ → f₂ x = 0 → x = 0 := fun x h1 h2 => by
    have : x ∈ K₁ ⊓ RingHom.ker f₂ := ⟨h1, h2⟩
    rw [hK] at this
    simpa using this

  have L0 : ∀ x : B, x ∈ RingHom.ker c₂ → ∀ k : K₁, (k ⊗ₜ[P] x : K₁ ⊗[P] B) = 0 := by
    intro x hx
    rw [hker, Ideal.map] at hx
    suffices H : ∀ (k : K₁) (y : B), (k ⊗ₜ[P] (y * x) : K₁ ⊗[P] B) = 0 by
      intro k; simpa using H k 1
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨κ, hκ, rfl⟩ := hz
      intro k y
      have e1 : y * algebraMap P B κ = κ • y := by rw [Algebra.smul_def, mul_comm]
      rw [e1, ← smul_tmul]
      have e2 : κ • k = 0 := by
        apply Subtype.ext
        apply hzero
        · exact (κ • k).2
        · simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
          rw [RingHom.mem_ker.mp hκ, zero_mul]
      rw [e2, zero_tmul]
    | zero => intro k y; rw [mul_zero, tmul_zero]
    | add u v _ _ hu hv => intro k y; rw [mul_add, tmul_add, hu, hv, add_zero]
    | smul b u _ hu => intro k y; rw [smul_eq_mul, ← mul_assoc]; exact hu k (y * b)
  have L1 : ∀ (k : K₁) (x y : B), c₂ x = c₂ y → (k ⊗ₜ[P] x : K₁ ⊗[P] B) = k ⊗ₜ[P] y := by
    intro k x y h
    rw [← sub_eq_zero, ← tmul_sub]
    exact L0 _ (by rw [RingHom.mem_ker, map_sub, h, sub_self]) k
  let s := Function.surjInv hc
  have hs : ∀ β, c₂ (s β) = β := Function.surjInv_eq hc
  let J₂ : Ideal R₂ := K₁.map f₂
  let ej : K₁ → J₂ := fun k => ⟨f₂ k, Ideal.mem_map_of_mem f₂ k.2⟩
  have hpre : ∀ j : J₂, ∃ k : P, k ∈ K₁ ∧ f₂ k = j := fun j =>
    (Ideal.mem_map_iff_of_surjective f₂ hf).mp j.2
  let einv : J₂ → K₁ := fun j => ⟨Classical.choose (hpre j), (Classical.choose_spec (hpre j)).1⟩
  have hE' : ∀ j : J₂, f₂ (einv j) = j := fun j => (Classical.choose_spec (hpre j)).2
  have hE : ∀ (k : K₁) (j : J₂), f₂ k = j → einv j = k := by
    intro k j h
    apply Subtype.ext
    rw [← sub_eq_zero]
    apply hzero
    · exact (einv j - k).2
    · rw [map_sub, hE', h, sub_self]

  let ψ0 : K₁ →+ B →+ J₂ ⊗[R₂] B₂ :=
    AddMonoidHom.mk' (fun k => AddMonoidHom.mk' (fun b => ej k ⊗ₜ[R₂] c₂ b)
      (fun b b' => by rw [map_add (f := _), tmul_add]))
      (fun k k' => by
        ext b
        have : ej (k + k') = ej k + ej k' := Subtype.ext (by simp [ej])
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, this, add_tmul])
  let ψ : K₁ ⊗[P] B →+ J₂ ⊗[R₂] B₂ := liftAddHom ψ0 (by
    intro p k b
    simp only [ψ0, AddMonoidHom.mk'_apply]
    have : ej (p • k) = f₂ p • ej k := Subtype.ext (by simp [ej])
    rw [this, hsmulB, smul_tmul])

  let χ0 : J₂ →+ B₂ →+ K₁ ⊗[P] B :=
    AddMonoidHom.mk' (fun j => AddMonoidHom.mk' (fun β => einv j ⊗ₜ[P] s β)
      (fun β β' => by rw [← tmul_add]; exact L1 _ _ _ (by rw [map_add (f := _), hs, hs, hs])))
      (fun j j' => by
        ext β
        have : einv (j + j') = einv j + einv j' :=
          hE _ _ (by rw [Submodule.coe_add, map_add (f := _), hE', hE', Submodule.coe_add])
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, this, add_tmul])
  let χ : J₂ ⊗[R₂] B₂ →+ K₁ ⊗[P] B := liftAddHom χ0 (by
    intro r j β
    simp only [χ0, AddMonoidHom.mk'_apply]
    obtain ⟨p, rfl⟩ := hf r
    have e1 : einv (f₂ p • j) = p • einv j :=
      hE _ _ (by simp [hE'])
    rw [e1, smul_tmul]
    exact L1 _ _ _ (by rw [hsmulB, hs, hs]))
  have hχψ : ∀ t, χ (ψ t) = t := by
    intro t
    induction t with
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
    | tmul k b =>
      simp only [ψ, χ, liftAddHom_tmul, ψ0, χ0, AddMonoidHom.mk'_apply]
      rw [hE k (ej k) rfl]
      exact L1 _ _ _ (hs _)

  let ν : J₂ ⊗[R₂] B₂ →ₗ[R₂] B₂ :=
    (TensorProduct.lid R₂ B₂).toLinearMap ∘ₗ J₂.subtype.rTensor B₂
  have hν : Function.Injective ν :=
    (TensorProduct.lid R₂ B₂).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ J₂.injective_subtype)
  set μ := TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype) with hμ
  have key : ∀ t, ν (ψ t) = c₂ (μ t) := by
    intro t
    induction t with
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _), map_add (f := _)]
    | tmul k b =>
      simp only [ψ, liftAddHom_tmul, ψ0, AddMonoidHom.mk'_apply, ν, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul, hμ, TensorProduct.lift.tmul, LinearMap.coe_comp,
        LinearMap.lsmul_apply]
      rw [hsmulB]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have h1 : ψ t = 0 := hν (by rw [key, ht, map_zero, map_zero])
  rw [← hχψ t, h1, map_zero]

end GlobalTheory.TorStep
end

section

open NumberField

namespace GlobalTheory

theorem isPrimitiveRoot_map_of_isUnit_order' {o K : Type} [CommRing o] [IsDomain o] [CommRing K] [IsDomain K]
    (φ : o →+* K) {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) :
    IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

theorem valuationRing_rootOfUnity_lift_reduce : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω]
    [Algebra U Ω] [IsFractionRing U Ω] [Field k] (h : U →+* k) (n : ℕ), IsUnit (n : U) → ∀ ζ : Ωˣ, ζ ^ n = 1 →
    ∃! z : Uˣ, algebraMap U Ω z = ζ ∧ (IsPrimitiveRoot ζ n → IsPrimitiveRoot (Units.map (h : U →* k) z) n) := by
  intro U Ω k _ _ _ _ _ _ _ h n hn ζ hζ
  have hinj : Function.Injective (algebraMap U Ω) := IsFractionRing.injective U Ω
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hn
    · exact h0

  have unitOf : ∀ a : U, (algebraMap U Ω a) ^ n = 1 → IsUnit a := by
    intro a ha
    have : a ^ n = 1 := hinj (by rw [map_pow, ha, map_one])
    exact IsUnit.of_mul_eq_one (a ^ (n - 1)) (by rw [← pow_succ', Nat.sub_add_cancel hn0, this])
  have hex : ∃ z : Uˣ, algebraMap U Ω z = ζ := by
    rcases (ValuationRing.iff_isInteger_or_isInteger U Ω).1 inferInstance (ζ : Ω) with ⟨a, ha⟩ | ⟨b, hb⟩
    · have hu := unitOf a (by rw [ha, ← Units.val_pow_eq_pow_val, hζ, Units.val_one])
      exact ⟨hu.unit, by simpa using ha⟩
    · have hb' : (algebraMap U Ω b) ^ n = 1 := by
        rw [hb, ← Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_pow, hζ, inv_one, Units.val_one]
      have hu := unitOf b hb'
      refine ⟨hu.unit⁻¹, ?_⟩
      have : algebraMap U Ω (hu.unit : U) = (ζ : Ω)⁻¹ := by simpa using hb
      have key : algebraMap U Ω (hu.unit : U) * algebraMap U Ω ((hu.unit⁻¹ : Uˣ) : U) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [this, inv_mul_eq_one₀ ζ.ne_zero] at key
      exact key.symm
  obtain ⟨z, hz⟩ := hex
  refine ⟨z, ⟨hz, fun hp => ?_⟩, fun w ⟨hw, _⟩ => Units.ext (hinj (by rw [hw, hz]))⟩
  have hpz : IsPrimitiveRoot (z : U) n := by
    rw [← IsPrimitiveRoot.map_iff_of_injective hinj, hz]
    exact IsPrimitiveRoot.coe_units_iff.2 hp
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact isPrimitiveRoot_map_of_isUnit_order' h hn0 hpz hn

end GlobalTheory
end

section

namespace GlobalTheory.RingHomTensorExtensionality

theorem ringHom_ext_tensor {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] {g h : TensorProduct R A B →+* C}
    (ha : ∀ a : A, g (a ⊗ₜ[R] (1 : B)) = h (a ⊗ₜ[R] (1 : B)))
    (hb : ∀ b : B, g ((1 : A) ⊗ₜ[R] b) = h ((1 : A) ⊗ₜ[R] b)) : g = h := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    have e : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, ha, hb]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.RingHomTensorExtensionality
end
