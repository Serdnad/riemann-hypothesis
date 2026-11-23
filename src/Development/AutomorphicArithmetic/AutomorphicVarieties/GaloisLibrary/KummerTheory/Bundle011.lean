module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle002
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClProd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle008
public import Mathlib.Topology.LocallyConstant.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle009
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
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem reflTw_empty {K : Type} [Field K] [NumberField K] {c d : ClassGroup (𝓞 K)}
    (h : (QuotientGroup.mk c : ClS (∅ : Set (HeightOneSpectrum (𝓞 K)))) = QuotientGroup.mk d) : c = d := by
  rw [QuotientGroup.eq] at h
  have e : clSub (∅ : Set (HeightOneSpectrum (𝓞 K))) = ⊥ := by simp [clSub]
  rw [e, Subgroup.mem_bot] at h
  exact inv_mul_eq_one.1 h

private theorem reflTw_one {K : Type} [Field K] [NumberField K] (n : ℕ) : radCl n (1 : Kˣ) = 1 := by
  simp [radCl, ordv_one]

private theorem reflTw_pow {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) {a : Kˣ}
    (ha : a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n) (m : ℕ) : radCl n (a ^ m) = radCl n a ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, reflTw_one]
  | succ m ih =>
    rw [pow_succ, pow_succ, ← ih]
    apply reflTw_empty
    rw [QuotientGroup.mk_mul]
    exact (radClMul K ∅ n hn).1 _ (pow_mem ha m) _ ha

private theorem reflTw_pow_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) {a : Kˣ}
    (ha : a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n) : radCl n a ^ n = 1 := by
  apply reflTw_empty
  rw [QuotientGroup.mk_pow, QuotientGroup.mk_one]
  exact (radClMul K ∅ n hn).2.1 _ ha

private theorem reflTw_dvd (n : ℕ) [NeZero n] : n ∣ (-1 : ZMod n).val + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  simp

private theorem reflTw_radPow {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {U : Subgroup (G F Ω)} {n : ℕ} [NeZero n]
    {ζ β : Ω} (hζ : ζ ^ n = 1) {φ : U → ZMod n} (h : ∀ u : U, u.1 β = ζ ^ (φ u).val * β) (m : ZMod n) (u : U) :
    u.1 (β ^ m.val) = ζ ^ (m * φ u).val * β ^ m.val := by
  rw [map_pow, h, mul_pow, ← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hζ, mul_comm m.val]

private theorem reflTw_key {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {K : Type}
    [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) {φ : galOf F K Ω → ZMod n} {β : Ω} {a : Kˣ}
    (hβ : IsRad (algebraMap K Ω ζ) (galOf F K Ω) φ β) (ha : β ^ n = algebraMap K Ω a)
    {τ : K ≃+* K} {σ : Ω ≃+* Ω} (hl : IsLift τ σ) (k s : ZMod n)
    (hk : σ (algebraMap K Ω ζ) = algebraMap K Ω ζ ^ k.val)
    (hs : ∀ u u' : galOf F K Ω, (∀ x, u'.1 (σ x) = σ (u.1 x)) → φ u = s * φ u') :
    ∃ c : Kˣ, Units.map τ.toMonoidHom a = a ^ (k * s).val * c ^ n := by
  have hz : algebraMap K Ω ζ ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h1 : IsRad (algebraMap K Ω ζ) (galOf F K Ω) (fun u => k * s * φ u) (σ β) := by
    refine radConj F Ω _ n _ β σ k φ _ hz hk hβ fun u' => ?_
    have hK : ∀ x : K, ((σ.trans u'.1.toRingEquiv).trans σ.symm) (algebraMap K Ω x) = algebraMap K Ω x := fun x => by
      show σ.symm (u'.1 (σ (algebraMap K Ω x))) = _
      rw [hl x, u'.2, ← hl x, σ.symm_apply_apply]
    let u : galOf F K Ω := ⟨AlgEquiv.ofRingEquiv (f := (σ.trans u'.1.toRingEquiv).trans σ.symm) fun x => by
      rw [IsScalarTower.algebraMap_apply F K Ω, hK], hK⟩
    have hu : ∀ x, u'.1 (σ x) = σ (u.1 x) := fun x => (σ.apply_symm_apply _).symm
    exact ⟨u, hu, by rw [hs u u' hu, mul_assoc]⟩
  have h2 : IsRad (algebraMap K Ω ζ) (galOf F K Ω) (fun u => k * s * φ u) (β ^ (k * s).val) :=
    ⟨pow_ne_zero _ hβ.1, reflTw_radPow hz hβ.2 _⟩
  obtain ⟨c, hc⟩ := (radXDual F Ω K _ n 1 ζ rfl hζ).2 _ _ _ h2 h1
  refine ⟨c, Units.ext ((algebraMap K Ω).injective ?_)⟩
  show algebraMap K Ω (τ a) = _
  rw [← hl, ← ha, map_pow, hc, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_pow,
    map_pow, ← ha]
  ring

theorem UpperTheory.V.Kum.reflTw :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K] (χ ψ : G F Ω →* (ZMod n)ˣ) (φ : U → ZMod n) (β : Ω) (a : Kˣ), U = galOf F K Ω → IsPrimitiveRoot ζ n → (∀ g : G F Ω, g (algebraMap K Ω ζ) = (algebraMap K Ω ζ) ^ (χ g : ZMod n).val) → φ ∈ EqHom N U (scalRep (ZMod n) ψ) → IsRad (algebraMap K Ω ζ) U φ β → β ^ n = algebraMap K Ω a →
    radCl n a ∈ ClTw K n (χ * ψ⁻¹) ∧ ∀ (τ : K ≃+* K) (σ : Ω ≃+* Ω), IsLift τ σ → τ ζ = ζ⁻¹ → φ ∈ conjCond U σ ((1 : ZMod n) • (LinearMap.id : ZMod n →ₗ[ZMod n] ZMod n)) → a * Units.map τ.toMonoidHom a ∈ powK K n ∧ radCl n a ∈ ClMinus τ := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ _ χ ψ φ β a hU hζ hχ hφ hβ ha
  subst hU
  have hn : n ≠ 0 := NeZero.ne n
  have hS : a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n := by
    obtain ⟨β₀, a₀, h₀, ha₀, hS₀⟩ := (radXDual F Ω K _ n N ζ rfl hζ).1 φ hφ.1
    obtain ⟨c, hc⟩ := (radXDual F Ω K _ n N ζ rfl hζ).2 _ _ _ h₀ hβ
    have e : a = a₀ * c ^ n := Units.ext ((algebraMap K Ω).injective (by
      rw [← ha, hc, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, ← ha₀]; ring))
    rw [e]
    refine mul_mem hS₀ fun v _ => ?_
    refine ⟨ordv v c, ?_⟩
    simp [ordv]
  have h1 := reflTw_pow_eq hn hS
  have hmap : ∀ (τ : K ≃+* K) (m : ℕ) (c : Kˣ), Units.map τ.toMonoidHom a = a ^ m * c ^ n →
      clMap τ (radCl n a) = radCl n a ^ m := fun τ m c h => by
    rw [radClMap, h, (radClMul K ∅ n hn).2.2, reflTw_pow hn hS]
  refine ⟨⟨h1, fun g τ hl => ?_⟩, fun τ σ hl hτ hc => ?_⟩
  · have hg : φ ∈ conjCond (galOf F K Ω) g.toRingEquiv (scalRep (ZMod n) ψ g) := (Submodule.mem_iInf _).1 hφ.2 g
    obtain ⟨c, hc⟩ := reflTw_key hζ hβ ha hl (χ g) ((ψ g)⁻¹ : (ZMod n)ˣ) (hχ g) fun u u' h => by
      rw [hg u u' h, scalRep_apply]
      simp
    refine hmap τ _ c ?_
    rw [hc]
    simp
  · obtain ⟨j, hj⟩ := reflTw_dvd n
    have hk : σ (algebraMap K Ω ζ) = algebraMap K Ω ζ ^ (-1 : ZMod n).val := by
      rw [hl, hτ, ← map_pow]
      congr 1
      refine inv_eq_of_mul_eq_one_left ?_
      rw [← pow_succ, hj, pow_mul, hζ.pow_eq_one, one_pow]
    obtain ⟨c, hc⟩ := reflTw_key hζ hβ ha hl (-1) 1 hk fun u u' h => by
      rw [hc u u' h]
      simp
    rw [mul_one] at hc
    refine ⟨⟨a ^ j * c, ?_⟩, ?_⟩
    · rw [hc, ← mul_assoc, ← pow_succ', hj, powMonoidHom_apply, mul_pow, ← pow_mul, mul_comm j]
    · show clMap τ (radCl n a) * radCl n a = 1
      rw [hmap τ _ c hc, ← pow_succ, hj, pow_mul, h1, one_pow]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem card_parity_sign_length_of_eq {A B : Type} [Group A] [CommGroup B] (E P : Subgroup B) (j : A →* B ⧸ P)
    (hj : Function.Injective j) (hE : ∀ x, ∃ b ∈ E ⊔ P, j x = QuotientGroup.mk b) :
    Nat.card A ∣ Nat.card (E ⧸ P.subgroupOf E) := by
  let f : E →* B ⧸ P := (QuotientGroup.mk' P).comp E.subtype
  have hk : f.ker = P.subgroupOf E := by
    ext x
    simp [f, Subgroup.mem_subgroupOf]
  have h1 : Nat.card (E ⧸ P.subgroupOf E) = Nat.card f.range := by
    rw [← hk]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hm : ∀ x, j x ∈ f.range := by
    intro x
    obtain ⟨b, hb, h⟩ := hE x
    obtain ⟨e, he, p, hp, rfl⟩ := Subgroup.mem_sup.1 hb
    refine ⟨⟨e, he⟩, ?_⟩
    rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p).2 hp, mul_one]
    rfl
  rw [h1]
  exact Subgroup.card_dvd_of_injective (j.codRestrict f.range hm)
    fun x y h => hj (congrArg Subtype.val h)

private theorem pow_val_add {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] {ζ : Ω} (hζ : ζ ^ n = 1) (x y : ZMod n) :
    ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) n, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem UpperTheory.V.Kum.reflMap :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K), U = galOf F K Ω → IsPrimitiveRoot ζ n → ∃ κ : XDual N U (ZMod n) (ZMod n) →+ Additive (ClassGroup (𝓞 K)),
    (∀ (φ : XDual N U (ZMod n) (ZMod n)) (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1 β → β ^ n = algebraMap K Ω a → κ φ = Additive.ofMul (radCl n a)) ∧
    Nat.card κ.ker ∣ Nat.card ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K ⧸ (powK K n).subgroupOf ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K)) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ hU hζ
  obtain ⟨hex, huniq⟩ := radXDual F Ω K U n N ζ hU hζ
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨hmul, -, hpow⟩ := radClMul K (∅ : Set (HeightOneSpectrum (𝓞 K))) n hn
  have hker : ∀ a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n,
      radCl n a = 1 → a ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ powK K n := by
    intro a ha h
    have hf : {v : HeightOneSpectrum (𝓞 K) | ordv v a / n ≠ 0}.Finite :=
      ((clProd K).2.2.1 a).subset fun v hv hv0 => hv (by simp [hv0])
    set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (ordv v a / n) with hI
    have hI0 : I ≠ 0 := by
      rw [hI]
      refine finprod_induction (fun J => J ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
      exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
    have hc : ∀ v, FractionalIdeal.count K v I = ordv v a / n := fun v =>
      FractionalIdeal.count_finprod K v _ (by simpa [Filter.eventually_cofinite] using hf)
    have h3 : ClassGroup.mk K (Units.mk0 I hI0) = 1 := by
      rw [(clProd K).1, ← h]
      exact finprod_congr fun v => by rw [Units.val_mk0, hc]
    obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h3)
    rw [Units.val_mk0] at hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hI0 (by rw [hb, FractionalIdeal.spanSingleton_zero])
    let b' : Kˣ := Units.mk0 b hb0
    have hb' : ∀ v, ordv v b' = ordv v a / n := fun v => by
      rw [← (clProd K).2.1, Units.val_mk0, ← hb, hc]
    refine Subgroup.mem_sup.2 ⟨a * (b' ^ n)⁻¹, ?_, b' ^ n, ⟨b', rfl⟩, by simp⟩
    have hunit : ∀ (u : Kˣ), u ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).unit K ↔
        ∀ v ∉ (∅ : Set (HeightOneSpectrum (𝓞 K))), ordv v u = 0 := by
      intro u
      change (∀ v ∉ (∅ : Set (HeightOneSpectrum (𝓞 K))), v.valuation K (u : K) = 1) ↔ _
      refine forall₂_congr fun v _ => ?_
      rw [← HeightOneSpectrum.valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj, ordv, neg_eq_zero, toAdd_eq_zero]
    apply (hunit _).2
    intro v hv
    rw [ordv_mul, ordv_inv]
    have hp : ordv v (b' ^ n) = n * ordv v b' := by simp [ordv]
    rw [hp, hb', Int.mul_ediv_cancel' (ha v hv), add_neg_cancel]
  have hbot : clSub (∅ : Set (HeightOneSpectrum (𝓞 K))) = ⊥ := by simp [clSub]
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  have hex' : ∀ φ : XDual N U (ZMod n) (ZMod n), ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1 β ∧
      β ^ n = algebraMap K Ω a ∧ a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n := fun φ => hex φ.1 φ.2
  choose β a hrad hβ hsel using hex'
  have hwd : ∀ (φ : XDual N U (ZMod n) (ZMod n)) (β' : Ω) (a' : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1 β' →
      β' ^ n = algebraMap K Ω a' → ∃ c : Kˣ, a' = a φ * c ^ n := by
    intro φ β' a' h1 h2
    obtain ⟨c, hc⟩ := huniq φ.1 (β φ) β' (hrad φ) h1
    refine ⟨c, Units.ext ((algebraMap K Ω).injective ?_)⟩
    rw [← h2, hc, mul_pow, hβ]
    simp [mul_comm]
  have hadd : ∀ φ ψ : XDual N U (ZMod n) (ZMod n), ∃ c : Kˣ, a φ * a ψ = a (φ + ψ) * c ^ n := by
    intro φ ψ
    refine hwd (φ + ψ) (β φ * β ψ) _ ⟨mul_ne_zero (hrad φ).1 (hrad ψ).1, fun u => ?_⟩ ?_
    · rw [map_mul, (hrad φ).2 u, (hrad ψ).2 u]
      change _ = algebraMap K Ω ζ ^ (φ.1 u + ψ.1 u).val * _
      rw [pow_val_add hζ'.pow_eq_one]
      ring
    · rw [mul_pow, hβ, hβ]
      simp
  have hmul' : ∀ φ ψ : XDual N U (ZMod n) (ZMod n), radCl n (a (φ + ψ)) = radCl n (a φ) * radCl n (a ψ) := by
    intro φ ψ
    obtain ⟨c, hc⟩ := hadd φ ψ
    have h := hmul _ (hsel φ) _ (hsel ψ)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, hbot, Subgroup.mem_bot, inv_mul_eq_one, hc, hpow] at h
    exact h
  let κ : XDual N U (ZMod n) (ZMod n) →+ Additive (ClassGroup (𝓞 K)) :=
    AddMonoidHom.mk' (fun φ => Additive.ofMul (radCl n (a φ))) fun φ ψ => by rw [hmul']; rfl
  have hκ : ∀ φ, κ φ = Additive.ofMul (radCl n (a φ)) := fun _ => rfl
  refine ⟨κ, fun φ β' a' h1 h2 => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := hwd φ β' a' h1 h2
    rw [hκ, hpow]
  · let j : Multiplicative κ.ker →* Kˣ ⧸ powK K n :=
      MonoidHom.mk' (fun x => QuotientGroup.mk (a (Multiplicative.toAdd x).1)) fun x y => by
        obtain ⟨c, hc⟩ := hadd (Multiplicative.toAdd x).1 (Multiplicative.toAdd y).1
        have hc1 : (QuotientGroup.mk (c ^ n) : Kˣ ⧸ powK K n) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨c, rfl⟩
        rw [← QuotientGroup.mk_mul, hc, QuotientGroup.mk_mul, hc1, mul_one]
        rfl
    have hj : ∀ x, j x = QuotientGroup.mk (a (Multiplicative.toAdd x).1) := fun _ => rfl
    refine card_parity_sign_length_of_eq (A := Multiplicative κ.ker) _ _ j ?_ ?_
    · rw [injective_iff_map_eq_one]
      intro x hx
      rw [hj, QuotientGroup.eq_one_iff] at hx
      obtain ⟨c, hc⟩ := hx
      set φ := (Multiplicative.toAdd x).1 with hφ
      have hc' : c ^ n = a φ := hc
      have hc0 : algebraMap K Ω c ≠ 0 := by simp
      have h1 : (β φ / algebraMap K Ω c) ^ n = 1 := by
        rw [div_pow, hβ, ← hc', Units.val_pow_eq_pow_val, map_pow, div_self (pow_ne_zero _ hc0)]
      obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
      have h2 : β φ = algebraMap K Ω (ζ ^ i * c) := by
        rw [map_mul, map_pow, hi, div_mul_cancel₀ _ hc0]
      have h0 : φ = 0 := by
        refine Subtype.ext (funext fun u => ?_)
        have hu : u.1 ∈ galOf F K Ω := hU ▸ u.2
        have h3 : u.1 (β φ) = β φ := by rw [h2]; exact hu _
        rw [(hrad φ).2 u, mul_eq_right₀ (hrad φ).1] at h3
        have h4 := hζ'.dvd_of_pow_eq_one _ h3
        exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt h4 (ZMod.val_lt _))
      exact Multiplicative.toAdd.injective (Subtype.ext h0)
    · intro x
      refine ⟨_, hker _ (hsel (Multiplicative.toAdd x).1) ?_, hj x⟩
      exact (Multiplicative.toAdd x).2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exists_valuationSubring_isPlaceOver (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ A : ValuationSubring Ω, IsPlaceOver A v := by
  let f : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective (𝓞 K) K)
  let e : 𝓞 K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let I : Ideal f.range := v.asIdeal.map e
  have hI : I ≠ ⊤ := by
    haveI : (v.asIdeal.map e).IsPrime := Ideal.map_isPrime_of_equiv e
    exact Ideal.IsPrime.ne_top this
  obtain ⟨V, hRV, hV⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hlt : ∀ y ∈ v.asIdeal, V.valuation (f y) < 1 := by
    intro y hy
    have h1 : f y ∈ V.nonunits := hV ⟨e y, Ideal.mem_map_of_mem e hy, rfl⟩
    exact (ValuationSubring.mem_nonunits_iff V).1 h1
  have hle : ∀ y : 𝓞 K, V.valuation (f y) ≤ 1 := by
    intro y
    exact (ValuationSubring.valuation_le_one_iff V _).2 (hRV (RingHom.mem_range_self f y))
  refine ⟨V, fun x => ⟨fun hx => ?_, fun hx => hlt x hx⟩⟩
  by_contra hxv
  obtain ⟨r, y, hy, hry⟩ := v.isMaximal.exists_inv hxv
  have h2 : V.valuation (f (r * x)) < 1 := by
    rw [map_mul, Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle r)) hx
  have h3 : V.valuation (f (r * x + y)) < 1 := by
    rw [map_add (f := _)]
    exact Valuation.map_add_lt _ h2 (hlt y hy)
  rw [hry, map_one, Valuation.map_one] at h3
  exact lt_irrefl _ h3

private theorem finite_above_of_ne_zero (K : Type) [Field K] [NumberField K] (N : ℕ) (hN : N ≠ 0) :
    (Above K N).Finite := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.2 hv

theorem UpperTheory.V.Kum.finChar :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n N : ℕ) (ζ : K), n ≠ 0 → N ≠ 0 → IsPrimitiveRoot ζ n → {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0}.Finite := by
  intro K Ω _ _ _ _ _ n N ζ hn hN hζ
  haveI : NeZero n := ⟨hn⟩
  let ζΩ := algebraMap K Ω ζ
  have hζΩ : IsPrimitiveRoot ζΩ n := hζ.map_of_injective (algebraMap K Ω).injective
  have hfix : ∀ (g : G K Ω) (x : K), g (algebraMap K Ω x) = algebraMap K Ω x :=
    fun g x => AlgEquiv.commutes g x
  have hη : ∀ g : G K Ω, g ζΩ = ζΩ ^ ((fun _ => (1 : ZMod n)) g).val := by
    intro g
    rw [hfix g ζ]
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]
    · have hn1 : n = 1 := by omega
      subst hn1
      have : ζΩ = 1 := IsPrimitiveRoot.one_right_iff.1 hζΩ
      show ζΩ = ζΩ ^ _
      rw [this, one_pow]
  have key : ∀ φ ∈ {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0},
      ∃ β : Ω, ∃ a : Kˣ, a ∈ SelK (Above K N) n ∧ β ^ n = algebraMap K Ω a ∧
        ∀ g : G K Ω, g β = ζΩ ^ (φ g).val * β := by
    rintro φ ⟨hlc, hadd, hine⟩
    obtain ⟨β, a, hβ, hg⟩ := radExists K Ω n ζΩ (fun _ => 1) φ hζΩ hη hlc
      (fun g h => by rw [hadd, one_mul])
    refine ⟨β, a, ?_, hβ, hg⟩
    intro v hv
    obtain ⟨A, hA⟩ := exists_valuationSubring_isPlaceOver K Ω v
    have hnot : ¬ A.valuation (N : Ω) < 1 := fun h => hv (((placeDict K Ω).2.2.2 A v N hA).1 h)
    exact dvdOfIne K Ω n A v β a hA hβ
      (fun g hg' => by rw [hg, hine A hnot g hg', ZMod.val_zero, pow_zero, one_mul])
  choose! β a ha hβ hg using key
  haveI hQ : Finite (↥(SelK (Above K N) n) ⧸ (powK K n).subgroupOf (SelK (Above K N) n)) := by
    apply Nat.finite_of_card_ne_zero
    rw [cardSel K _ n hn, cardSUnit K _ n (finite_above_of_ne_zero K N hN)]
    have h1 : Nat.card ↥(rootsOfUnity n K) ≠ 0 := Nat.card_pos.ne'
    have h2 : Nat.card {c : ClS (Above K N) // c ^ n = 1} ≠ 0 := by
      haveI : Nonempty {c : ClS (Above K N) // c ^ n = 1} := ⟨⟨1, one_pow _⟩⟩
      exact Nat.card_pos.ne'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn) h1) h2
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective (β := ↥(SelK (Above K N) n) ⧸ (powK K n).subgroupOf (SelK (Above K N) n))
    (fun φ => QuotientGroup.mk ⟨a φ.1, ha φ.1 φ.2⟩) ?_
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ h
  simp only at h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hc
  have hcu : a φ * c ^ n = a ψ := by rw [hc, mul_inv_cancel_left]
  have hne : ∀ θ ∈ _, β θ ≠ 0 := fun θ hθ h0 => by
    have := hβ θ hθ
    rw [h0, zero_pow hn] at this
    exact (Units.ne_zero (a θ)) ((algebraMap K Ω).injective (this.symm.trans (map_zero _).symm))
  refine Subtype.ext (funext fun g => ?_)
  have hφ0 := hne φ hφ
  have hcΩ : algebraMap K Ω (c : K) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact c.ne_zero
  set ω := β ψ / (β φ * algebraMap K Ω (c : K)) with hωdef
  have hωn : ω ^ n = 1 := by
    rw [hωdef, div_pow, mul_pow, hβ ψ hψ, hβ φ hφ, ← map_pow, ← map_mul, ← hcu]
    push_cast
    exact div_self (by simp)
  obtain ⟨i, -, hi⟩ := hζΩ.eq_pow_of_pow_eq_one hωn
  have hψeq : β ψ = ω * (β φ * algebraMap K Ω (c : K)) := by
    rw [hωdef, div_mul_cancel₀ _ (mul_ne_zero hφ0 hcΩ)]
  have hgω : g ω = ω := by
    rw [← hi, map_pow]
    exact congrArg (· ^ i) (hfix g ζ)
  have hω0 : ω ≠ 0 := by
    rw [← hi]
    exact pow_ne_zero _ (hζΩ.ne_zero hn)
  have e1 := hg ψ hψ g
  rw [hψeq, map_mul, map_mul, hgω, hg φ hφ g, hfix] at e1
  have e2 : ζΩ ^ (φ g).val = ζΩ ^ (ψ g).val := by
    have h3 := mul_ne_zero hω0 (mul_ne_zero hφ0 hcΩ)
    apply mul_right_cancel₀ h3
    linear_combination e1
  exact ZMod.val_injective _ (hζΩ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e2)
end
