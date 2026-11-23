module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.LocalSubring
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
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Unramified.Field
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isRegularRing_tensor_of_fibre_localRings :
    ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K]
      [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q →
      (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) →
      (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q →
        IsRegularLocalRing (Localization.AtPrime n ⧸
          (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) →
      IsRegularRing (T ⊗[S] K) := by
  intro S T K _ _ _ _ _ _ Q hQ hfrac hreg
  haveI : Q.IsPrime := hQ ▸ RingHom.ker_isPrime (algebraMap S K)
  let φ : Q.ResidueField →ₐ[S] K := Ideal.ResidueField.liftₐ Q (Algebra.ofId S K) hQ.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hQ ▸ h0))
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, b, hb, hy⟩ := hfrac y
    have hb0 : algebraMap S K b ≠ 0 := fun h0 => hb (hQ ▸ h0)
    refine ⟨algebraMap S Q.ResidueField a * (algebraMap S Q.ResidueField b)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, AlgHom.commutes, AlgHom.commutes]
    rw [← hy, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  let e : Q.ResidueField ≃ₐ[S] K := AlgEquiv.ofBijective φ ⟨φ.toRingHom.injective, hsurj⟩
  let E : Q.Fiber T ≃ₐ[S] T ⊗[S] K :=
    (Algebra.TensorProduct.congr e AlgEquiv.refl).trans (Algebra.TensorProduct.comm S K T)
  haveI : IsNoetherianRing (Q.Fiber T) := by
    letI : Algebra T (Q.Fiber T) := Algebra.TensorProduct.rightAlgebra
    let Sp := Localization (Algebra.algebraMapSubmonoid T Q.primeCompl)
    haveI : IsNoetherianRing Sp :=
      IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid T Q.primeCompl) Sp inferInstance
    exact isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivAux₁ Q (S := T)).toRingEquiv.symm
  haveI : IsRegularRing (Q.Fiber T) := by
    rw [isRegularRing_iff]
    intro q hq
    let n : Ideal T := q.comap (Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T)
    haveI : n.IsPrime := Ideal.comap_isPrime _ _
    have hn : n.comap (algebraMap S T) = Q := by
      change Ideal.comap (algebraMap S T) (Ideal.comap
        ((Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T) : T →+* Q.Fiber T) q) = Q
      rw [Ideal.comap_comap, AlgHom.comp_algebraMap]
      exact (Ideal.over_def q Q).symm
    haveI := hreg n hn
    exact IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ Q q).toRingEquiv.symm
  exact IsRegularRing.of_ringEquiv E.toRingEquiv

end GlobalTheory
end

section

namespace GlobalTheory

theorem isReduced_of_smooth_over_field (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] : IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  by_contra h0
  obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal (Ideal.span {a}).annihilator fun h =>
    h0 ((one_smul A a).symm.trans ((Submodule.mem_annihilator_span_singleton a 1).1 (h ▸ Submodule.mem_top)))
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let P := MvPolynomial (Fin n) K
  have : IsReduced (TensorProduct P (FractionRing P) (Localization.Away f)) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing P) _
  have : IsReduced (Localization.Away f) := isReduced_of_injective _
    (Algebra.TensorProduct.includeRight_injective (A := FractionRing P) (IsFractionRing.injective P _))
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) a).1
    (ha.map (algebraMap A (Localization.Away f))).eq_zero
  exact hf (hp.isPrime.mem_of_pow_mem N (hI ((Submodule.mem_annihilator_span_singleton a _).2 hN)))

end GlobalTheory
end

section

namespace GlobalTheory

theorem idempotent_algHom_ker_fg {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (e : A →ₐ[R] A) (he : ∀ x, e (e x) = e x) :
    (RingHom.ker e.rangeRestrict.toRingHom).FG := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  refine ⟨s.image (fun x => x - e x), ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨x, _, rfl⟩
    change e.rangeRestrict (x - e x) = 0
    apply Subtype.ext
    simp [he]
  · intro b hb
    have hb' : e b = 0 := by
      have := congrArg Subtype.val (show e.rangeRestrict b = 0 from hb)
      simpa using this
    have key : ∀ y : A, y - e y ∈ Ideal.span ((fun x => x - e x) '' (s : Set A)) := by
      intro y
      have hy : y ∈ Algebra.adjoin R (s : Set A) := by rw [hs]; exact Algebra.mem_top
      induction hy using Algebra.adjoin_induction with
      | mem x hx => exact Ideal.subset_span ⟨x, hx, rfl⟩
      | algebraMap r => simp
      | add x y _ _ hx hy =>
        have h : x + y - e (x + y) = (x - e x) + (y - e y) := by rw [map_add (f := _)]; ring
        rw [h]; exact Ideal.add_mem _ hx hy
      | mul x y _ _ hx hy =>
        have h : x * y - e (x * y) = x * (y - e y) + e y * (x - e x) := by rw [map_mul]; ring
        rw [h]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hx)
    simpa [hb'] using key b

theorem smooth_range_of_idempotent : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by
  intro R A _ _ _ _ e he
  have hq : ∀ b : e.range, e.rangeRestrict (b : A) = b := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    simp [he]
  have hsurj : Function.Surjective e.rangeRestrict := fun b => ⟨b, hq b⟩
  refine { formallySmooth := ?_, finitePresentation := ?_ }
  · refine Algebra.FormallySmooth.of_split e.rangeRestrict
      ((Ideal.Quotient.mkₐ R _).comp e.range.val) ?_
    ext b
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_id, id_eq,
      Subalgebra.coe_val]
    rw [AlgHom.kerSquareLift_mk, hq]
  · exact Algebra.FinitePresentation.of_surjective hsurj (idempotent_algHom_ker_fg e he)

end GlobalTheory
end

section

namespace GlobalTheory

open Module

theorem localizedModule_map_injective_of_surjective_of_rankAtStalk
    {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q]
    (r : ℕ) (P : PrimeSpectrum R) (hP : Module.rankAtStalk Q P = r) (φ : (Fin r → R) →ₗ[R] Q)
    (hs : Function.Surjective (LocalizedModule.map P.asIdeal.primeCompl φ)) :
    Function.Injective (LocalizedModule.map P.asIdeal.primeCompl φ) := by
  haveI : Nontrivial R := nontrivial_of_ne (0 : R) 1 fun h =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h ▸ P.asIdeal.zero_mem))
  haveI : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl Q) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl (Fin r → R)) := Module.free_of_flat_of_isLocalRing
  have h1 : Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl (Fin r → R)) = r := by
    have := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := Fin r → R)) P
    rw [Module.finrank_fin_fun] at this
    exact this
  have h2 : Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl Q) = r := hP
  let e := LinearEquiv.ofFinrankEq _ _ (h1.trans h2.symm)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap _ e.injective hs

theorem exists_smul_mem_range_of_surjective_localizedModule_map
    {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] (P : Ideal R) [P.IsPrime] (φ : M →ₗ[R] Q)
    (hs : Function.Surjective (LocalizedModule.map P.primeCompl φ)) :
    ∃ f ∉ P, ∀ q : Q, f • q ∈ LinearMap.range φ := by
  have key : ∀ g : Q, ∃ a ∈ P.primeCompl, a • g ∈ LinearMap.range φ := by
    intro g
    obtain ⟨y, hy⟩ := hs (LocalizedModule.mk g 1)
    induction y using LocalizedModule.induction_on with
    | h x t =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨u, hu⟩ := hy
      refine ⟨(u : R) * t, P.primeCompl.mul_mem u.2 t.2, ⟨(u : R) • x, ?_⟩⟩
      rw [map_smul, mul_smul]
      simpa [Submonoid.smul_def] using hu
  classical
  choose a ha hga using key
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := Q)
  refine ⟨∏ g ∈ s, a g, fun h => ?_, ?_⟩
  · exact (Submonoid.prod_mem P.primeCompl fun g _ => ha g) h
  · have hle : Submodule.span R (s : Set Q) ≤
        (LinearMap.range φ).comap (LinearMap.lsmul R Q (∏ g ∈ s, a g)) := by
      rw [Submodule.span_le]
      intro g hg
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
      rw [← Finset.prod_erase_mul s a hg, mul_smul]
      exact Submodule.smul_mem _ _ (hga g)
    intro q
    have := hle (hs ▸ Submodule.mem_top : q ∈ Submodule.span R (s : Set Q))
    simpa using this

theorem localizedModule_map_surjective_of_smul_mem_range
    {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (S : Submonoid R) (φ : M →ₗ[R] Q) (f : R) (hf : f ∈ S)
    (h : ∀ q : Q, f • q ∈ LinearMap.range φ) :
    Function.Surjective (LocalizedModule.map S φ) := by
  intro y
  induction y using LocalizedModule.induction_on with
  | h q s =>
    obtain ⟨x, hx⟩ := h q
    refine ⟨LocalizedModule.mk x (⟨f, hf⟩ * s), ?_⟩
    rw [LocalizedModule.map_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    rw [hx]
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    exact smul_comm _ _ _

theorem exists_pow_smul_eq_zero_of_localizedModule_map_injective
    {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (φ : M →ₗ[R] Q) (f : R)
    (h : ∀ (P : Ideal R) [P.IsPrime], f ∉ P →
      Function.Injective (LocalizedModule.map P.primeCompl φ))
    (k : M) (hk : φ k = 0) : ∃ n : ℕ, f ^ n • k = 0 := by
  by_contra hne
  push_neg at hne
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M k)
  have hd : Disjoint (I : Set R) (Submonoid.powers f : Set R) := by
    rw [Set.disjoint_left]
    rintro a ha ⟨n, rfl⟩
    exact hne n (by simpa [I] using ha)
  obtain ⟨P, hP, hIP, hPd⟩ := Ideal.exists_le_prime_disjoint I _ hd
  have hfP : f ∉ P := fun hf => Set.disjoint_left.1 hPd hf (Submonoid.mem_powers f)
  have h0 : LocalizedModule.map P.primeCompl φ (LocalizedModule.mk k 1) =
      LocalizedModule.map P.primeCompl φ 0 := by
    rw [LocalizedModule.map_mk, hk, LocalizedModule.zero_mk, map_zero]
  have h1 := h P hfP h0
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
  obtain ⟨u, hu⟩ := h1
  have hu' : (u : R) ∈ I := by
    simpa [I, Submonoid.smul_def] using hu
  exact u.2 (hIP hu')

theorem exists_embedding_bijective_localizedModule_map_of_rankAtStalk :
    ∀ (R Q : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q]
      (N r : ℕ) (b : Fin N → Q), Submodule.span R (Set.range b) = ⊤ →
      (∀ P : PrimeSpectrum R, Module.rankAtStalk Q P = r) → ∀ P₀ : PrimeSpectrum R,
      ∃ (σ : Fin r ↪ Fin N) (f : R), f ∉ P₀.asIdeal ∧
        Function.Bijective (LocalizedModule.map (Submonoid.powers f)
          (Fintype.linearCombination R (b ∘ σ))) := by
  intro R Q _ _ _ _ _ N r b hspan hrank P₀
  let p := P₀.asIdeal
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl Q) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation (Localization.AtPrime p) (LocalizedModule p.primeCompl Q) :=
    Module.finitePresentation_of_projective _ _
  let v : Fin N → LocalizedModule p.primeCompl Q := fun i => LocalizedModule.mk (b i) 1
  have hv : Submodule.span (Localization.AtPrime p) (Set.range v) = ⊤ := by
    have hle : Submodule.span R (Set.range b) ≤
        ((Submodule.span (Localization.AtPrime p) (Set.range v)).restrictScalars R).comap
          (LocalizedModule.mkLinearMap p.primeCompl Q) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [eq_top_iff]
    rintro y -
    induction y using LocalizedModule.induction_on with
    | h q s =>
      have hq : LocalizedModule.mk q 1 ∈ Submodule.span (Localization.AtPrime p) (Set.range v) :=
        hle (hspan ▸ Submodule.mem_top)
      have : LocalizedModule.mk q s =
          (Localization.mk 1 s : Localization.AtPrime p) • LocalizedModule.mk q 1 := by
        rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ hq
  obtain ⟨κ, a, bs, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  haveI : Finite κ := Module.Finite.finite_basis bs
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    rw [← hrank P₀, Module.rankAtStalk, Module.finrank_eq_card_basis bs]
  have ha : Function.Injective a := fun i j hij => bs.injective (by rw [hb, hb, hij])
  let eqv : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let σ : Fin r ↪ Fin N := eqv.toEmbedding.trans ⟨a, ha⟩
  let φ : (Fin r → R) →ₗ[R] Q := Fintype.linearCombination R (b ∘ σ)
  have hs0 : Function.Surjective (LocalizedModule.map p.primeCompl φ) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← bs.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨LocalizedModule.mk (Pi.single (eqv.symm j) 1) 1, ?_⟩
    rw [LocalizedModule.map_mk, hb]
    simp [φ, σ, v]
  obtain ⟨f, hf, hfr⟩ := exists_smul_mem_range_of_surjective_localizedModule_map p φ hs0
  refine ⟨σ, f, hf, ?_,
    localizedModule_map_surjective_of_smul_mem_range _ φ f (Submonoid.mem_powers f) hfr⟩
  have hloc : ∀ (P : Ideal R) [P.IsPrime], f ∉ P →
      Function.Injective (LocalizedModule.map P.primeCompl φ) := by
    intro P hP hfP
    exact localizedModule_map_injective_of_surjective_of_rankAtStalk r ⟨P, hP⟩ (hrank ⟨P, hP⟩) φ
      (localizedModule_map_surjective_of_smul_mem_range _ φ f hfP hfr)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  induction y using LocalizedModule.induction_on with
  | h x s =>
    rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hy
    obtain ⟨u, hu⟩ := hy
    have hk : φ ((u : R) • (s : R) • x) = 0 := by
      simpa [Submonoid.smul_def, map_smul] using hu
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_localizedModule_map_injective φ f hloc _ hk
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨f ^ n, n, rfl⟩ * u, ?_⟩
    simp only [Submonoid.smul_def, smul_zero, Submonoid.coe_mul, mul_smul]
    exact hn

end GlobalTheory
end

section

namespace GlobalTheory


open Module in
theorem bijective_linearCombination_of_rankAtStalk :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (r : ℕ),
      (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) → ∀ s : Fin r → M,
      Module.support R (M ⧸ Submodule.span R (Set.range s)) = ∅ →
      Function.Bijective (Fintype.linearCombination R s) := by
  intro R M _ _ _ _ _ r hr s hs
  have hspan : Submodule.span R (Set.range s) = ⊤ := by
    have : Subsingleton (M ⧸ Submodule.span R (Set.range s)) := Module.support_eq_empty_iff.1 hs
    exact Submodule.Quotient.subsingleton_iff.1 this
  refine ⟨?_, ?_⟩
  · rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    refine LinearIndependent.of_isLocalized_maximal (fun P _ => Localization.AtPrime P)
      (fun P _ => LocalizedModule P.primeCompl M) (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M)
      s fun P hP => ?_
    have hfree : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
      Module.free_of_flat_of_isLocalRing
    have hrk : Module.finrank (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = r :=
      hr ⟨P, hP.isPrime⟩
    have hsp : Submodule.span (Localization.AtPrime P)
        (Set.range (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) = ⊤ := by
      rw [Set.range_comp]
      exact span_eq_top_of_isLocalizedModule (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl M) hspan
    have hsurj : Function.Surjective (Fintype.linearCombination (Localization.AtPrime P)
        (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hsp]
    let b := Module.finBasisOfFinrankEq (Localization.AtPrime P) (LocalizedModule P.primeCompl M) hrk
    have hinj := OrzechProperty.injective_of_surjective_endomorphism
      (b.equivFun.toLinearMap ∘ₗ Fintype.linearCombination (Localization.AtPrime P)
        (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) (b.equivFun.surjective.comp hsurj)
    rw [linearIndependent_iff_injective_fintypeLinearCombination]
    exact Function.Injective.of_comp (f := ⇑b.equivFun) hinj
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem range_comap_includeRight_field :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : Type) [Field k] [Algebra A k],
    Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom) = {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A k)} := by
  intro A B _ _ _ k _ _
  ext r
  constructor
  · rintro ⟨q, rfl⟩
    show Ideal.comap (algebraMap A B) (Ideal.comap _ q.asIdeal) = _
    rw [Ideal.comap_comap, ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
      ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ q.asIdeal),
      ← RingHom.ker_eq_comap_bot]
  · intro hr
    change Ideal.comap (algebraMap A B) r.asIdeal = RingHom.ker (algebraMap A k) at hr
    set f := algebraMap A k with hf
    let I := RingHom.ker f
    let K := r.asIdeal.ResidueField
    let g : A →+* K := (algebraMap B K).comp (algebraMap A B)
    have hg : RingHom.ker g = I := by
      change RingHom.ker ((algebraMap B K).comp (algebraMap A B)) = RingHom.ker f
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField, hr]
    have hIg : ∀ a ∈ I, g a = 0 := fun a ha => by rw [← RingHom.mem_ker, hg]; exact ha
    let ι₁ : A ⧸ I →+* k := RingHom.kerLift f
    let ι₂ : A ⧸ I →+* K := Ideal.Quotient.lift I g hIg
    have inj₁ : Function.Injective ι₁ := RingHom.kerLift_injective f
    have inj₂ : Function.Injective ι₂ := RingHom.lift_injective_of_ker_le_ideal I hIg hg.le
    letI : Algebra (A ⧸ I) k := ι₁.toAlgebra
    letI : Algebra (A ⧸ I) K := ι₂.toAlgebra
    haveI : Nontrivial (k ⊗[A ⧸ I] K) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain (A ⧸ I) k K inj₁ inj₂
    haveI : SMulCommClass (A ⧸ I) A k := ⟨fun x a y => by
      simp only [Algebra.smul_def]; ring⟩
    let α : k →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.includeLeft
    let β : B →ₐ[A] k ⊗[A ⧸ I] K :=
      { ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) with
        commutes' := fun a => by
          change (1 : k) ⊗ₜ[A ⧸ I] (algebraMap (A ⧸ I) K (Ideal.Quotient.mk I a)) = _
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := K),
            ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
          rfl }
    let φ : k ⊗[A] B →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.lift α β (fun _ _ => Commute.all _ _)
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[A ⧸ I] K)
    refine ⟨PrimeSpectrum.comap φ.toRingHom ⟨m, hm.isPrime⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.comap φ.toRingHom m) = r.asIdeal
    have hcomp : φ.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom =
        ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) := by
      ext b
      simp [φ, α, β, Algebra.TensorProduct.lift_tmul]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ m),
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end GlobalTheory
end

section

namespace GlobalTheory.IntegralInValuationSubring

theorem mem_valuationSubring_of_isIntegral {Ω : Type} [Field Ω] {R : Type} [CommRing R]
    [Algebra R Ω] (A : ValuationSubring Ω) (h : ∀ r : R, algebraMap R Ω r ∈ A) {b : Ω}
    (hb : IsIntegral R b) : b ∈ A := by
  let f : R →+* A := (algebraMap R Ω).codRestrict A h
  letI : Algebra R A := f.toAlgebra
  haveI : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hA : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 hA
  rw [← hy]
  exact y.2

end GlobalTheory.IntegralInValuationSubring
end
