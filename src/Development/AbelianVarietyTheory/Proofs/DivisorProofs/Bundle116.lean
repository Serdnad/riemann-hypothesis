module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
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
public import Mathlib.FieldTheory.FinTrdeg
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

namespace GlobalTheory

theorem finite_away_of_isAlgebraic_of_finiteType : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Module.Finite A' B' := by
  intro A B _ _ _ _ hft halg
  obtain ⟨s, hs⟩ := hft.out
  choose y hy hint using fun b : B =>
    (Algebra.IsAlgebraic.isAlgebraic (R := A) b).exists_integral_multiple
  refine ⟨∏ b ∈ s, y b, Finset.prod_ne_zero_iff.mpr fun b _ => hy b, ?_⟩
  intro c A' B' _ _ _ _ _ _ _ _ hA' hB'
  set a := ∏ b ∈ s, y b with ha
  haveI hBB : Algebra.FiniteType B B' :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (algebraMap A B (a * c))) B'
  haveI : Algebra.FiniteType A B' := Algebra.FiniteType.trans hft hBB
  haveI : Algebra.FiniteType A' B' := .of_restrictScalars_finiteType A A' B'
  have hu : IsUnit (algebraMap A A' (a * c)) := IsLocalization.Away.algebraMap_isUnit (a * c)
  have hunit : ∀ (r : A) (m : ℕ), r ∣ (a * c) ^ m → ∃ r' : A', algebraMap A' B' r' * algebraMap A B' r = 1 := by
    intro r m hr
    obtain ⟨u, hu'⟩ := isUnit_of_dvd_unit (map_dvd (algebraMap A A') hr) (by rw [map_pow]; exact hu.pow m)
    refine ⟨↑u⁻¹, ?_⟩
    rw [IsScalarTower.algebraMap_apply A A' B', ← hu', ← map_mul, Units.inv_mul, map_one]
  haveI : Algebra.IsIntegral A' B' := by
    let S : Subalgebra A B :=
      ((integralClosure A' B').restrictScalars A).comap (IsScalarTower.toAlgHom A B B')
    have hS : Algebra.adjoin A (s : Set B) ≤ S := by
      rw [Algebra.adjoin_le_iff]
      intro b hb
      have h1 : IsIntegral A' (algebraMap B B' (y b • b)) :=
        ((hint b).map (IsScalarTower.toAlgHom A B B')).tower_top
      obtain ⟨r', hr'⟩ := hunit (y b) 1 (by rw [pow_one]; exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hb) c)
      show IsIntegral A' (algebraMap B B' b)
      have : algebraMap B B' b = algebraMap A' B' r' * algebraMap B B' (y b • b) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← mul_assoc, hr', one_mul]
      rw [this]
      exact isIntegral_algebraMap.mul h1
    rw [hs] at hS
    constructor
    intro x
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hx⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap A B (a * c))) x
    have hb : IsIntegral A' (algebraMap B B' b) := hS (Algebra.mem_top (x := b))
    obtain ⟨r', hr'⟩ := hunit ((a * c) ^ n) n dvd_rfl
    refine IsIntegral.of_mul_unit (y := algebraMap B B' (algebraMap A B (a * c) ^ n)) (r := r') ?_ ?_
    · rw [← map_pow, ← IsScalarTower.algebraMap_apply]; exact hr'
    · have hx' : x * algebraMap B B' (algebraMap A B (a * c) ^ n) = algebraMap B B' b := hx
      rw [hx']; exact hb
  exact Algebra.IsIntegral.finite

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField

namespace GlobalTheory

theorem eq_maximalIdeal_of_trdeg_le (F A : Type) [Field F] [CommRing A] [IsDomain A]
    [IsLocalRing A] [Algebra F A] (hA : Algebra.EssFiniteType F A) (p : Ideal A)
    (hp : p.IsPrime)
    (htr : Algebra.trdeg F (FractionRing (A ⧸ p)) ≤ Algebra.trdeg F (ResidueField A)) :
    p = maximalIdeal A := by
  classical
  by_contra hne
  have hle : p ≤ maximalIdeal A := le_maximalIdeal hp.ne_top
  obtain ⟨a, ham, hap⟩ : ∃ a ∈ maximalIdeal A, a ∉ p := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hle h)
  haveI := hA
  haveI : Algebra.EssFiniteType F (ResidueField A) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom F A (ResidueField A))
      (IsLocalRing.residue_surjective)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (ResidueField A)
  haveI : Finite s := finite_of_isTranscendenceBasis hs
  let f : A ⧸ p →ₐ[F] ResidueField A :=
    Ideal.Quotient.liftₐ p (IsScalarTower.toAlgHom F A (ResidueField A)) (fun x hx => by
      simpa [IsLocalRing.residue_eq_zero_iff] using hle hx)
  have hfmk : ∀ x : A, f (Ideal.Quotient.mk p x) = IsLocalRing.residue A x := fun x => rfl
  choose y hy using fun i : s => IsLocalRing.residue_surjective (R := A) i.1
  let z : s → A ⧸ p := fun i => Ideal.Quotient.mk p (y i)
  have hfz : f ∘ z = ((↑) : s → ResidueField A) := by
    funext i
    simp only [Function.comp_apply, z, hfmk, hy]
  have hz : AlgebraicIndependent F z := by
    have h1 := hs.1
    rw [← hfz] at h1
    exact h1.of_comp f
  set b : A ⧸ p := Ideal.Quotient.mk p a with hbdef
  have hb0 : b ≠ 0 := by
    rw [hbdef, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hap
  have hbk : b ∈ RingHom.ker f.toRingHom := by
    rw [RingHom.mem_ker]
    change f (Ideal.Quotient.mk p a) = 0
    rw [hfmk, IsLocalRing.residue_eq_zero_iff]
    exact ham
  have hinj := algebraicIndependent_iff_injective_aeval.mp hs.1
  have htrans : Transcendental (Algebra.adjoin F (Set.range z)) b := by
    intro halg
    apply Ideal.comap_ne_bot_of_algebraic_mem hb0 hbk halg
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker] at hc
    have hc2 : (c : A ⧸ p) ∈ (MvPolynomial.aeval (R := F) z).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact c.2
    obtain ⟨g, hg⟩ := hc2
    have h0 : MvPolynomial.aeval ((↑) : s → ResidueField A) g = 0 := by
      rw [← hfz]
      change MvPolynomial.aeval (fun i => f (z i)) g = 0
      rw [← MvPolynomial.comp_aeval_apply]
      change f ((MvPolynomial.aeval z).toRingHom g) = 0
      rw [hg]
      exact hc
    have hg0 : g = 0 := hinj (by rw [h0, map_zero])
    rw [Ideal.mem_bot]
    apply Subtype.ext
    rw [← hg, hg0, map_zero]
    rfl
  have hopt : AlgebraicIndependent F (fun o : Option s => o.elim b z) :=
    AlgebraicIndependent.option_iff.mpr ⟨hz, htrans⟩
  have hopt' := hopt.map' (f := IsScalarTower.toAlgHom F (A ⧸ p) (FractionRing (A ⧸ p)))
    (IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p)))
  have hc1 := hopt'.cardinalMk_le_trdeg
  rw [← hs.cardinalMk_eq_trdeg] at htr
  have hle2 : Cardinal.mk (Option s) ≤ Cardinal.mk s := hc1.trans htr
  obtain ⟨e⟩ := Cardinal.le_def _ _ |>.mp hle2
  haveI := Fintype.ofFinite s
  have := Fintype.card_le_of_embedding e
  rw [Fintype.card_option] at this
  omega

end GlobalTheory
end

section

set_option autoImplicit false

open scoped TensorProduct
open KaehlerDifferential

namespace GlobalTheory.BertiniAlg

theorem linearIndependent_D_of_algebraicIndependent (k κ : Type) [Field k] [CharZero k] [Field κ]
    [Algebra k κ] [Algebra.EssFiniteType k κ] {σ : Type} (t : σ → κ)
    (ht : AlgebraicIndependent k t) :
    LinearIndependent κ (fun s => KaehlerDifferential.D k κ (t s)) := by
  let P := MvPolynomial σ k
  let φ : P →ₐ[k] κ := MvPolynomial.aeval t
  have hφ : Function.Injective φ := ht
  algebraize [φ.toRingHom]
  have : IsScalarTower k P κ := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let K := FractionRing P
  have hinj : Function.Injective (algebraMap P κ) := hφ
  let : Algebra K κ := (IsFractionRing.lift (K := K) hinj).toAlgebra
  have : IsScalarTower P K κ := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (K := K) hinj a).symm
  have : IsScalarTower k K κ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k P K, ← IsScalarTower.algebraMap_apply P K κ,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.EssFiniteType K κ := .of_comp k K κ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : Algebra.FormallySmooth K κ := Algebra.FormallySmooth.of_perfectField
  have : Algebra.FormallyEtale P K := .of_isLocalization (nonZeroDivisors P)
  have : Algebra.FormallySmooth P κ := .comp P K κ
  have hH : Subsingleton (Algebra.H1Cotangent P κ) := Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinjm : Function.Injective (mapBaseChange k P κ) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k P κ x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  let b := (mvPolynomialBasis k σ).baseChange κ
  have h := b.linearIndependent.map' (mapBaseChange k P κ) (LinearMap.ker_eq_bot.2 hinjm)
  have hX (s : σ) : algebraMap P κ (MvPolynomial.X s) = t s := MvPolynomial.aeval_X t s
  have e : (fun s => KaehlerDifferential.D k κ (t s)) = mapBaseChange k P κ ∘ b := by
    funext s
    simp only [Function.comp_apply, b, Module.Basis.baseChange_apply, mvPolynomialBasis_apply]
    erw [mapBaseChange_tmul, one_smul, map_D, hX]
  rw [e]
  exact h

end GlobalTheory.BertiniAlg
end

section

namespace GlobalTheory.LiftDeriv

theorem krullDimLE_and_isLocalRing_quotient {P : Type} [CommRing P] (Q S : Ideal P) [hQ : Q.IsMaximal]
    (n : ℕ) (h1 : Q ^ (n + 1) ≤ S) (h2 : S ≤ Q) :
    Ring.KrullDimLE 0 (P ⧸ S) ∧ IsLocalRing (P ⧸ S) := by
  have hSt : S ≠ ⊤ := fun h => hQ.ne_top (top_le_iff.1 (h ▸ h2))
  have : Nontrivial (P ⧸ S) := Ideal.Quotient.nontrivial_iff.2 hSt
  have key : ∀ M : Ideal (P ⧸ S), M.IsPrime → M = Q.map (Ideal.Quotient.mk S) := by
    intro M hM
    have hc : (M.comap (Ideal.Quotient.mk S)).IsPrime := Ideal.comap_isPrime _ _
    have h3 : Q ≤ M.comap (Ideal.Quotient.mk S) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (h1 ha)]
      exact M.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M).symm.trans
      (congrArg _ (hQ.eq_of_le hc.ne_top h3).symm)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (P ⧸ S)
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (P ⧸ S)).out 2 1 rfl rfl).mp
    ⟨M, hM.isPrime, fun M' hM' => (key M' hM').trans (key M hM.isPrime).symm⟩

theorem exists_derivation_extending : ∀ (A P R K : Type) [CommRing A] [CommRing P] [IsNoetherianRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], Function.Surjective (algebraMap P R) → Function.Surjective (algebraMap R K) → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (algebraMap A R) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (algebraMap A R) = β) → ∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i := by
  intro A P R K _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf hg hlift ℓ
  have hPK : algebraMap P K = (algebraMap R K).comp (algebraMap P R) := IsScalarTower.algebraMap_eq P R K
  have hQm : (RingHom.ker (algebraMap P K)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (by rw [hPK]; exact hg.comp hf)
  have hIQ : RingHom.ker (algebraMap P R) ≤ RingHom.ker (algebraMap P K) := fun x hx => by
    rw [RingHom.mem_ker] at hx ⊢
    rw [hPK, RingHom.comp_apply, hx, map_zero]
  generalize hI : RingHom.ker (algebraMap P R) = I at ℓ hIQ
  generalize hQ : RingHom.ker (algebraMap P K) = Q at hQm hIQ
  let J : Ideal P := Submodule.map I.subtype (LinearMap.ker ℓ)
  have hJI : J ≤ I := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hJ : ∀ (i i' : P) (hi : i ∈ I) (hi' : i' ∈ I), i' - i ∈ J → ℓ ⟨i, hi⟩ = ℓ ⟨i', hi'⟩ := by
    intro i i' hi hi' h
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 h
    have e : x = ⟨i', hi'⟩ - ⟨i, hi⟩ := Subtype.ext (by simpa using hxe)
    rw [LinearMap.mem_ker, e, map_sub, sub_eq_zero] at hx
    exact hx.symm
  have hQIJ : Q * I ≤ J := by
    refine Ideal.mul_le.2 fun q hq i hi => ?_
    refine Submodule.mem_map.2 ⟨⟨q * i, I.mul_mem_left q hi⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker]
    have e : (⟨q * i, I.mul_mem_left q hi⟩ : I) = q • ⟨i, hi⟩ := rfl
    rw [e, map_smul, Algebra.smul_def]
    have hq0 : algebraMap P K q = 0 := by rw [← RingHom.mem_ker, hQ]; exact hq
    rw [hq0, zero_mul]
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul Q (I : Submodule P P)
  have hAR : Q ^ (k + 1) ⊓ I ≤ J := by
    have h := hk (k + 1) (Nat.le_succ k)
    rw [Nat.add_sub_cancel_left, pow_one] at h
    have e : (Q ^ (k + 1) • ⊤ : Submodule P P) = Q ^ (k + 1) := by rw [smul_eq_mul, Ideal.mul_top]
    rw [e] at h
    rw [h]
    exact le_trans (Submodule.smul_mono le_rfl inf_le_right) hQIJ

  let S : Ideal P := J ⊔ Q ^ (k + 1)
  let T : Ideal P := I ⊔ Q ^ (k + 1)
  have hST : S ≤ T := sup_le_sup_right hJI _
  have hSQ : S ≤ Q := sup_le (hJI.trans hIQ) (Ideal.pow_le_self (Nat.succ_ne_zero k))
  obtain ⟨hdim, hloc⟩ := krullDimLE_and_isLocalRing_quotient Q S k le_sup_right hSQ
  haveI : IsArtinianRing (P ⧸ S) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let π : P ⧸ S →+* P ⧸ T := Ideal.Quotient.factor hST
  have hπmk : ∀ x, π (Ideal.Quotient.mk S x) = Ideal.Quotient.mk T x := fun x => rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, hπmk x⟩
  have hTT : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ S := by
    intro x hx y hy
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨i', hi', z', hz', rfl⟩ := Submodule.mem_sup.1 hy
    have e : (i + z) * (i' + z') = i * i' + (i * z' + z * (i' + z')) := by ring
    rw [e]
    refine S.add_mem (Ideal.mem_sup_left (hQIJ (Ideal.mul_mem_mul (hIQ hi) hi'))) (Ideal.mem_sup_right ?_)
    exact (Q ^ (k + 1)).add_mem (Ideal.mul_mem_left _ _ hz') (Ideal.mul_mem_right _ _ hz)
  have hsq : RingHom.ker π ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun c hc d hd => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [RingHom.mem_ker, hπmk, Ideal.Quotient.eq_zero_iff_mem] at hc hd
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hTT x hc y hd
  let β : A →+* P ⧸ S := (Ideal.Quotient.mk S).comp (algebraMap A P)
  have hIT : RingHom.ker (algebraMap P R) ≤ T := hI ▸ le_sup_left
  let e := RingHom.quotientKerEquivOfSurjective hf
  let L : P ⧸ RingHom.ker (algebraMap P R) →+* P ⧸ T :=
    Ideal.Quotient.lift (RingHom.ker (algebraMap P R)) (Ideal.Quotient.mk T)
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hIT ha))
  let φ₀ : R →+* P ⧸ T := L.comp e.symm.toRingHom
  have hφ₀ : ∀ a, φ₀ (algebraMap P R a) = Ideal.Quotient.mk T a := by
    intro a
    have h1 : e.symm (algebraMap P R a) = Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]; rfl
    change L (e.symm (algebraMap P R a)) = _
    rw [h1, Ideal.Quotient.lift_mk]
  have hcomp : φ₀.comp (algebraMap A R) = π.comp β := by
    ext r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A P R r, hφ₀]
    rfl
  obtain ⟨φ, hφπ, hφA⟩ := hlift (P ⧸ S) (P ⧸ T) π hπs hsq β φ₀ hcomp

  let δ : P → P ⧸ S := fun a => Ideal.Quotient.mk S a - φ (algebraMap P R a)
  have hδ : ∀ a, δ a ∈ RingHom.ker π := by
    intro a
    rw [RingHom.mem_ker]
    show π (Ideal.Quotient.mk S a - φ (algebraMap P R a)) = 0
    rw [map_sub, hπmk, ← RingHom.comp_apply, hφπ, hφ₀, sub_self]
  have hδadd : ∀ a b, δ (a + b) = δ a + δ b := by
    intro a b
    show Ideal.Quotient.mk S (a + b) - φ (algebraMap P R (a + b)) = _
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]
    show _ = (Ideal.Quotient.mk S a - φ (algebraMap P R a)) + (Ideal.Quotient.mk S b - φ (algebraMap P R b))
    ring
  have hδmul : ∀ a b, δ (a * b) = Ideal.Quotient.mk S a * δ b + Ideal.Quotient.mk S b * δ a := by
    intro a b
    have h0 : δ a * δ b = 0 := by
      have : δ a * δ b ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul (hδ a) (hδ b)
      rw [hsq] at this
      exact (Ideal.mem_bot.1 this)
    change (Ideal.Quotient.mk S a - φ (algebraMap P R a)) * (Ideal.Quotient.mk S b - φ (algebraMap P R b)) = 0 at h0
    show Ideal.Quotient.mk S (a * b) - φ (algebraMap P R (a * b)) =
      Ideal.Quotient.mk S a * (Ideal.Quotient.mk S b - φ (algebraMap P R b)) +
        Ideal.Quotient.mk S b * (Ideal.Quotient.mk S a - φ (algebraMap P R a))
    rw [map_mul, map_mul, map_mul]
    linear_combination -h0

  let Rl : P ⧸ S → K → Prop := fun c v => ∃ (i : P) (hi : i ∈ I), ∃ z ∈ Q ^ (k + 1),
    Ideal.Quotient.mk S (i + z) = c ∧ ℓ ⟨i, hi⟩ = v
  have huniq : ∀ c v v', Rl c v → Rl c v' → v = v' := by
    rintro c v v' ⟨i, hi, z, hz, rfl, rfl⟩ ⟨i', hi', z', hz', he, rfl⟩
    rw [Ideal.Quotient.eq] at he
    obtain ⟨j, hj, w, hw, hjw⟩ := Submodule.mem_sup.1 he
    have hmem : i' - i - j ∈ Q ^ (k + 1) ⊓ I := by
      refine ⟨?_, (I.sub_mem (I.sub_mem hi' hi) (hJI hj))⟩
      have e1 : i' - i - j = w + z - z' := by linear_combination -hjw
      rw [e1]
      exact (Q ^ (k + 1)).sub_mem ((Q ^ (k + 1)).add_mem hw hz) hz'
    have h2 : i' - i ∈ J := by
      have := J.add_mem (hAR hmem) hj
      rwa [sub_add_cancel] at this
    exact hJ i i' hi hi' h2
  have hex : ∀ c : P ⧸ S, π c = 0 → ∃ v, Rl c v := by
    intro c hc
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hπmk, Ideal.Quotient.eq_zero_iff_mem] at hc
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.1 hc
    exact ⟨_, i, hi, z, hz, rfl, rfl⟩
  have hRadd : ∀ c c' v v', Rl c v → Rl c' v' → Rl (c + c') (v + v') := by
    rintro c c' v v' ⟨i, hi, z, hz, rfl, rfl⟩ ⟨i', hi', z', hz', rfl, rfl⟩
    refine ⟨i + i', I.add_mem hi hi', z + z', (Q ^ (k + 1)).add_mem hz hz', ?_, ?_⟩
    · rw [← map_add (f := _)]; congr 1; ring
    · rw [← map_add (f := _)]; rfl
  have hRsmul : ∀ c v (p : P), Rl c v → Rl (Ideal.Quotient.mk S p * c) (p • v) := by
    rintro c v p ⟨i, hi, z, hz, rfl, rfl⟩
    refine ⟨p * i, I.mul_mem_left p hi, p * z, Ideal.mul_mem_left _ p hz, ?_, ?_⟩
    · rw [← map_mul]; congr 1; ring
    · rw [← map_smul]; rfl
  have hR0 : Rl 0 0 := ⟨0, I.zero_mem, 0, (Q ^ (k + 1)).zero_mem, by simp, map_zero ℓ⟩
  have hRI : ∀ i (hi : i ∈ I), Rl (Ideal.Quotient.mk S i) (ℓ ⟨i, hi⟩) :=
    fun i hi => ⟨i, hi, 0, (Q ^ (k + 1)).zero_mem, by rw [add_zero], rfl⟩
  let D0 : P → K := fun a => Classical.choose (hex (δ a) (hδ a))
  have hD0 : ∀ a v, Rl (δ a) v → D0 a = v := fun a v h =>
    huniq _ _ _ (Classical.choose_spec (hex (δ a) (hδ a))) h
  have hspec : ∀ a, Rl (δ a) (D0 a) := fun a => Classical.choose_spec (hex (δ a) (hδ a))
  have hDadd : ∀ a b, D0 (a + b) = D0 a + D0 b := fun a b =>
    hD0 _ _ (by rw [hδadd]; exact hRadd _ _ _ _ (hspec a) (hspec b))
  have hDmul : ∀ a b, D0 (a * b) = a • D0 b + b • D0 a := fun a b =>
    hD0 _ _ (by rw [hδmul]; exact hRadd _ _ _ _ (hRsmul _ _ a (hspec b)) (hRsmul _ _ b (hspec a)))
  have hDA : ∀ r : A, D0 (algebraMap A P r) = 0 := by
    intro r
    refine hD0 _ _ ?_
    have : δ (algebraMap A P r) = 0 := by
      show Ideal.Quotient.mk S (algebraMap A P r) - φ (algebraMap P R (algebraMap A P r)) = 0
      rw [← IsScalarTower.algebraMap_apply A P R r, ← RingHom.comp_apply φ, hφA, sub_eq_zero]
      rfl
    rw [this]; exact hR0
  let Dl : P →ₗ[A] K :=
    { toFun := D0
      map_add' := hDadd
      map_smul' := fun r a => by
        rw [Algebra.smul_def, hDmul, hDA, smul_zero, add_zero, RingHom.id_apply, algebraMap_smul] }
  refine ⟨Derivation.mk' Dl hDmul, fun ⟨i, hi⟩ => ?_⟩
  show D0 i = ℓ ⟨i, hi⟩
  refine hD0 _ _ ?_
  have : δ i = Ideal.Quotient.mk S i := by
    show Ideal.Quotient.mk S i - φ (algebraMap P R i) = _
    have hi0 : algebraMap P R i = 0 := by rw [← RingHom.mem_ker, hI]; exact hi
    rw [hi0, map_zero, sub_zero]
  rw [this]; exact hRI i hi

end GlobalTheory.LiftDeriv
end

section

namespace GlobalTheory

theorem finite_maximal_ideals_containing (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) : {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite := by
  have hI : Ideal.span {f} ≠ (0 : Ideal B) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hf
  have hfin := Ideal.finite_factors hI
  apply (hfin.image (fun v : IsDedekindDomain.HeightOneSpectrum B => v.asIdeal)).subset
  rintro P ⟨hmax, hfP⟩
  have hne : P ≠ ⊥ := by
    rintro rfl
    exact hf ((Submodule.mem_bot B).mp hfP)
  refine ⟨⟨P, hmax.isPrime, hne⟩, ?_, rfl⟩
  show P ∣ Ideal.span {f}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hfP

theorem finite_maximal_ideals_containing' : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B),
    f ≠ 0 → {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite :=
  fun B _ _ f hf => finite_maximal_ideals_containing B f hf

end GlobalTheory
end
