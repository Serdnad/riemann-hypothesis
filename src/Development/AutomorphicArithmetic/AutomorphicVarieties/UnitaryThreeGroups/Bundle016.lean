module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle057
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle008
import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ShaInjGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem isCM (K : Type) [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) (h' : IsTotallyComplex K) :
    IsCMField K := by
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := h }
  exact IsCMField.ofCMExtension ℚ K

private theorem exists_w (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk10.exists_w K hp

private theorem cop_norm {K : Type} [Field K] [NumberField K] {p N : ℕ} (hp : p.Prime) (hN : ¬ p ∣ N)
    {w : HeightOneSpectrum (𝓞 K)} (hw : (p : 𝓞 K) ∈ w.asIdeal) : (normV w).Coprime N := by
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [Ideal.absNorm_span_natCast] at h
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] at *
  exact Nat.Coprime.coprime_dvd_left h (((Nat.Prime.coprime_iff_not_dvd hp).2 hN).pow_left _)

private theorem frob_val {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [hl : Fact l.Prime] {p N : ℕ} [NeZero N] (hp : p.Prime) (hN : ¬ p ∣ N) (hlp : l ≠ p)
    {w : HeightOneSpectrum (𝓞 K)} (hw : (p : 𝓞 K) ∈ w.asIdeal) {B : ValuationSubring Ω} (hB : IsPlaceOver B w)
    {σ : G K Ω} (hσ : IsFrob B (normV w) σ) :
    ((Chr.cls ℚ Ω N (galEmb ℚ K Ω σ) : (ZMod N)ˣ) : ZMod N) = normV w ∧
      ((cycZ ℚ Ω l (galEmb ℚ K Ω σ) : ℤ_[l]ˣ) : ℤ_[l]) = normV w := by
  obtain ⟨-, -, -, hcop, -, -, hpow, -⟩ := ML.placeBasic Ω
  have hp' : ML.Over B p := by
    have := (hB p).2 hw
    simpa using this
  constructor
  · have hφ : IsFrob (F := ℚ) B (normV w) (galEmb ℚ K Ω σ) :=
      ⟨Subgroup.mem_comap.1 (((galEmbFam ℚ K Ω l).1 B).1.ge hσ.1), hσ.2⟩
    have h := hpow B _ N _ hφ (hcop B p N ((Nat.Prime.coprime_iff_not_dvd hp).2 hN) hp')
    rw [(Chr.clsFacts ℚ Ω N).2.2.1 _ (ZMod.unitOfCoprime _ (cop_norm hp hN hw)) fun ζ hζ => ?_, ZMod.coe_unitOfCoprime]
    rw [h ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]
  · refine cycZ_of_isFrob (F := K) (fun h => ?_) hB hσ
    refine hcop B p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hp' ?_
    have := (hB l).2 h
    simpa using this

private theorem vl_bound {l : ℕ} [hl : Fact l.Prime] {ι : Type} {κ : Type} [Fintype ι] (X : ι → Finset κ)
    (f : ι → κ → PadicAlgCl l) (NN : ℤ) (h0 : NN ≠ 0) (hf : ∀ o, ∀ ρ ∈ X o, f o ρ ≠ 0)
    (h : ‖((NN : ℤ) : PadicAlgCl l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖f o ρ‖) :
    ∑ o, ∑ ρ ∈ X o, vl l (f o ρ) ≤ padicValInt l NN := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have e1 : ‖((NN : ℤ) : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l NN : ℝ)) := by
    rw [← map_intCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends,
      Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast h0), Padic.valuation_intCast, ← Real.rpow_intCast]
    simp
  have h2 := Real.logb_le_logb_of_le hl1 (by rw [e1]; positivity) h
  rw [e1, Real.logb_rpow (by positivity) hl1.ne', Real.logb_prod _ _ fun o _ =>
    Finset.prod_ne_zero_iff.2 fun ρ hρ => norm_ne_zero_iff.2 (hf o ρ hρ),
    Finset.sum_congr rfl fun o _ => Real.logb_prod _ _ fun ρ hρ => norm_ne_zero_iff.2 (hf o ρ hρ)] at h2
  simp only [vl, Finset.sum_neg_distrib]
  linarith

private theorem ker_comp {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') (hf : Function.Injective f)
    (ψ : DirichletCharacter O N) : (ψ.ringHomComp f).toUnitHom.ker = ψ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, MulChar.ringHomComp_apply, Units.val_one]
  exact map_eq_one_iff f hf

private theorem card_orb {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    Nat.card {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} ≤ Nat.totient H.index := by
  by_cases h : ∃ χ : DirichletCharacter ℂ N, χ.toUnitHom.ker = H
  · obtain ⟨χ, rfl⟩ := h
    obtain ⟨h1, -, -, h2⟩ := orbFacts ℂ N χ
    rw [h1, ← h2]
    exact le_rfl
  · haveI : IsEmpty {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} := ⟨fun x => h ⟨x.1, x.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

private theorem t_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] (c : Coef l)
    {N : ℕ} [NeZero N] (e q : ℕ) (ψ : DirichletCharacter c.O N) (ι : Qbar l ≃+* ℂ) (g : G ℚ Ω)
    (h1 : ((Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N) = q) (h2 : ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = q) :
    ι.symm (Af.eis3 q e (ι (algebraMap c.O (PadicAlgCl l) (ψ q)))⁻¹) =
      algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g⁻¹ : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g⁻¹)⁻¹ : c.Oˣ) : c.O)) := by
  have e1 : ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : c.Oˣ) : c.O) = (q : c.O) ^ e * ψ q := by
    simp [Chr.Psi, Chr.dirG, chiO, h1, h2]
  rw [map_inv (Chr.Psi l e (Chr.dirG ℚ Ω ψ)), inv_inv, map_add (f := _), map_add (f := _), map_one, map_units_inv, e1]
  simp [Af.eis3, mul_comm]

private theorem comp_inj {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') (hf : Function.Injective f)
    {ψ ψ' : DirichletCharacter O N} (h : ψ.ringHomComp f = ψ'.ringHomComp f) : ψ = ψ' :=
  MulChar.ext' fun a => hf (by rw [← MulChar.ringHomComp_apply, h, MulChar.ringHomComp_apply])

private theorem orb_equiv {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) (f : c.O →+* ℂ)
    (hf : Function.Injective f) {ψ₀ : DirichletCharacter c.O N} (h₀ : ψ₀ ∈ orb c H) :
    ∃ E : orb c H ≃ {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H}, ∀ ψ, (E ψ).1 = ψ.1.ringHomComp f := by
  refine ⟨Equiv.ofBijective (fun ψ => ⟨ψ.1.ringHomComp f, (ker_comp f hf _).trans ((mem_orb c).1 ψ.2)⟩) ⟨?_, ?_⟩,
    fun _ => rfl⟩
  · intro a b h
    exact Subtype.ext (comp_inj f hf (congrArg Subtype.val h))
  · rintro ⟨χ, hχ⟩
    have h1 := (ker_comp f hf ψ₀).trans ((mem_orb c).1 h₀)
    obtain ⟨j, -, hj⟩ := ((orbFacts ℂ N (ψ₀.ringHomComp f)).2.2.1 χ).1 (hχ.trans h1.symm)
    rw [MulChar.ringHomComp_pow] at hj
    refine ⟨⟨ψ₀ ^ j, (mem_orb c).2 ?_⟩, Subtype.ext hj.symm⟩
    rw [← ker_comp f hf, ← hj, hχ]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem twist_triv {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    (D : Dat Ω K c e ψ) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {C : Type} [Group C]
    (φ : G K Ω →* C) (hφ : (cycBar K Ω l).ker ≤ φ.ker) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A → φ s ≠ 1 → D.ΨQ (galEmb ℚ K Ω s) ^ m = 1) (g : G K Ω) :
    φ g = 1 := by
  have hl : l.Prime := Fact.out
  have hI : Ine (F := ℚ) A ≤ (galEmb ℚ K Ω).range := by
    rw [range_galEmb, ← D.η_ker]
    exact ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).1
  have hsur : ∀ u : ℤ_[l]ˣ, ∃ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A ∧ cycZ K Ω l s = u := fun u => by
    obtain ⟨σ, hσ, hu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
    obtain ⟨s, rfl⟩ := hI hσ
    exact ⟨s, hσ, hu⟩
  by_contra hg
  obtain ⟨s, hs, hsg⟩ := hsur (cycZ K Ω l g)
  have hs1 : φ s ≠ 1 := by
    intro h1
    have : φ (g * s⁻¹) = 1 := hφ (by
      rw [MonoidHom.mem_ker, cycBar, MonoidHom.comp_apply, map_mul, map_inv, hsg, mul_inv_cancel, map_one])
    rw [map_mul, map_inv, h1, inv_one, mul_one] at this
    exact hg this
  have hu : IsUnit ((1 + l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  obtain ⟨t, ht, htu⟩ := hsur hu.unit
  have ht1 : D.ΨQ (galEmb ℚ K Ω t) ^ m = 1 := by
    by_cases h1 : φ t = 1
    · have h2 := h (s * t) (by rw [map_mul]; exact mul_mem hs ht) (by rwa [map_mul, h1, mul_one])
      rwa [map_mul, map_mul, mul_pow, h s hs hs1, one_mul] at h2
    · exact h t ht h1
  have hn : Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ = 1 := by
    rw [Chr.dirG, MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]
  have hc : (chiO ℚ Ω l c.O (galEmb ℚ K Ω t) : c.O) = ((1 + l : ℕ) : c.O) := by
    have : cycZ ℚ Ω l (galEmb ℚ K Ω t) = hu.unit := htu
    rw [chiO, MonoidHom.comp_apply, this]
    simp
  have h3 : ((D.Ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : c.Oˣ) : c.O) = ((1 + l : ℕ) : c.O) ^ (e * Nat.card (ZMod N)ˣ) := by
    rw [Dat.Ψ, Chr.Psi, MonoidHom.mul_apply, mul_pow, hn, mul_one, zpow_natCast, MonoidHom.pow_apply, ← pow_mul,
      Units.val_pow_eq_pow_val, hc]
  have h4 : ((D.ΨQ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ) := by
    have := congrArg (algebraMap c.O (PadicAlgCl l)) h3
    rw [map_pow, map_natCast] at this
    rw [← this, Dat.ΨQ, MonoidHom.comp_apply, ← map_pow]
    rfl
  have h5 : ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1 := by
    rw [pow_mul, ← h4, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, ht1, one_pow, Units.val_one]
  have h6 : (1 + l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1 := by exact_mod_cast h5
  have he := D.gd.e_pos
  have hN : 0 < Nat.card (ZMod N)ˣ := Nat.card_pos
  rcases Nat.pow_eq_one.1 h6 with h7 | h7
  · exact hl.ne_zero (by omega)
  · exact (mul_ne_zero (mul_ne_zero (by omega) hN.ne') hm) h7
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem place_uniq {l : ℕ} (hl : l.Prime) (v w : HeightOneSpectrum (𝓞 ℚ)) (hv : (l : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : (l : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have key : ∀ u : HeightOneSpectrum (𝓞 ℚ), (l : 𝓞 ℚ) ∈ u.asIdeal →
      Ideal.span {(l : ℤ)} = u.asIdeal.map (e : 𝓞 ℚ →+* ℤ) := by
    intro u hu
    apply hmax.eq_of_le
    · rw [Ideal.map_comap_of_equiv]
      exact Ideal.comap_ne_top _ u.isPrime.ne_top
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hel : e (l : 𝓞 ℚ) = (l : ℤ) := map_natCast e l
      rw [← hel]
      exact Ideal.mem_map_of_mem _ hu
  apply HeightOneSpectrum.ext
  rw [← Ideal.map_of_equiv (I := v.asIdeal) e, ← Ideal.map_of_equiv (I := w.asIdeal) e, ← key v hv, ← key w hw]

theorem UpperTheory.exists_finite_place_set_factoring_through_GS :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
          {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
          ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S) (η' : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* ℤˣ) (Ψ' : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* c.Oˣ),
            ContainsAbove S l ∧ (∀ v, IsPlaceOver (A v) v.1) ∧ D.ι.range = Dec (F := ℚ) (A v₀) ∧ (∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀) ∧
            η'.comp (toGS Ω _) = D.η ∧ Ψ'.comp (toGS Ω _) = D.Ψ := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  classical
  have hlp : l.Prime := Fact.out
  haveI : IsScalarTower ℚ K Ω := inferInstance
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have hηopen : IsOpen (D.η.ker : Set (G ℚ Ω)) := by
    rw [D.η_ker]
    let b := Module.finBasis ℚ K
    have heq : (galOf ℚ K Ω : Set (G ℚ Ω)) = ⋂ i, {σ : G ℚ Ω | σ (algebraMap K Ω (b i)) = algebraMap K Ω (b i)} := by
      ext σ
      simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe, mem_galOf]
      refine ⟨fun h i => h _, fun h x => ?_⟩
      have h' := b.ext (f₁ := σ.toLinearMap ∘ₗ (IsScalarTower.toAlgHom ℚ K Ω).toLinearMap)
        (f₂ := (IsScalarTower.toAlgHom ℚ K Ω).toLinearMap) h
      exact LinearMap.congr_fun h' x
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_setOf_apply (F := ℚ) _ (fun t => t = algebraMap K Ω (b i))
  obtain ⟨⟨T, hT⟩, -⟩ := ramFinite ℚ ℚ K Ω
  have hlN0 : ((l * N : ℕ) : 𝓞 ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hlp.ne_zero (NeZero.ne N))
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((l * N : ℕ) : 𝓞 ℚ)}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := T ∪ hfin.toFinset
  have hmemS : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply Finset.mem_union_right
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
  have hcast : ∀ n : ℕ, algebraMap ℚ Ω (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := fun n => by simp
  have hlv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v hv
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hv
  have hNv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v hv
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ hv
  obtain ⟨A₀, hA₀l, hA₀dec, -⟩ := dat_loc D
  have hA₀top : A₀ ≠ ⊤ := by
    intro h
    exact ((places ℚ Ω l A₀).2.1 h).2 hA₀l
  obtain ⟨v₀, hv₀⟩ := (places ℚ Ω l A₀).1 hA₀top
  have hlv₀ : ((l : ℕ) : 𝓞 ℚ) ∈ v₀.asIdeal := by
    rw [← hv₀, hcast]
    exact hA₀l
  have hv₀S : v₀ ∈ S := hmemS v₀ (hlv v₀ hlv₀)
  let v₀' : S := ⟨v₀, hv₀S⟩
  let A : S → ValuationSubring Ω := fun v =>
    if v.1 = v₀ then A₀ else Classical.choose (exists_isPlaceOver Ω v.1)
  let H : Subgroup (G ℚ Ω) := (cycZ ℚ Ω l).ker ⊓ (Chr.cls ℚ Ω N).ker ⊓ D.η.ker
  have hHclosed : IsClosed (H : Set (G ℚ Ω)) := by
    simp only [H, Subgroup.coe_inf]
    refine (IsClosed.inter ?_ ?_).inter ?_
    · rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage (contTw ℚ Ω l).1
    · exact Subgroup.isClosed_of_isOpen _ (Chr.clsFacts ℚ Ω N).1
    · exact Subgroup.isClosed_of_isOpen _ hηopen
  have hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ H := by
    apply Subgroup.topologicalClosure_minimal _ _ hHclosed
    apply Subgroup.normalClosure_le_normal
    simp only [Set.iUnion_subset_iff]
    intro v hv B hB g hg
    have hg' : g ∈ Ine (F := ℚ) B := hg
    have hvS : v ∉ S := hv
    have hvT : v ∉ T := fun h => hvS (Finset.mem_union_left _ h)
    have hlB : ¬ B.valuation (l : Ω) < 1 := by
      intro h
      rw [← hcast] at h
      exact hvS (hmemS v (hlv v ((hB _).mp h)))
    have hNB : ¬ B.valuation (N : Ω) < 1 := by
      intro h
      rw [← hcast] at h
      exact hvS (hmemS v (hNv v ((hB _).mp h)))
    refine ⟨⟨(places ℚ Ω l B).2.2.2 hlB hg', (Chr.clsFacts ℚ Ω N).2.2.2.2 B hNB hg'⟩, ?_⟩
    show g ∈ D.η.ker
    rw [D.η_ker]
    exact hT v hvT B hB ⟨by rw [galOf_self]; trivial, hg'⟩
  have hηk : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ D.η.ker := hNS.trans inf_le_right
  have hΨk : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ D.Ψ.ker := by
    intro g hg
    have hH := hNS hg
    have h1 : cycZ ℚ Ω l g = 1 := hH.1.1
    have h2 : Chr.cls ℚ Ω N g = 1 := hH.1.2
    rw [MonoidHom.mem_ker]
    simp [Dat.Ψ, Chr.Psi, chiO, Chr.dirG, h1, h2]
  refine ⟨S, A, v₀', QuotientGroup.lift _ D.η hηk, QuotientGroup.lift _ D.Ψ hΨk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact hmemS v (hlv v hv)
  · intro v
    by_cases h : v.1 = v₀
    · simp only [A, if_pos h]
      rw [h]
      exact hv₀
    · simp only [A, if_neg h]
      exact Classical.choose_spec (exists_isPlaceOver Ω v.1)
  · simp only [A, v₀', if_pos rfl]
    exact hA₀dec
  · intro v
    constructor
    · intro hv
      exact Subtype.ext (place_uniq hlp _ _ hv hlv₀)
    · rintro rfl
      exact hlv₀
  · ext g
    rfl
  · ext g
    rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem cycMod_cc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {σ : G ℚ Ω}
    (h : IsConjOm σ.toRingEquiv) : cycMod ℚ Ω l 1 σ = -1 := by
  obtain ⟨j, hj⟩ := h
  have hlp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hlp.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hζl : ζ ^ l = 1 := hζ.pow_eq_one
  have hσζ : σ.toRingEquiv ζ = ζ⁻¹ := by
    apply j.injective
    rw [hj, map_inv₀]
    have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (n := l)
      (by rw [← map_pow, hζl, map_one]) hlp.ne_zero
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ (n := 1) (by rw [pow_one]; exact hζl)
  have hval : ((cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) =
      PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv).val := rfl
  set a : ZMod (l ^ 1) := PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv).val with ha
  haveI : NeZero (l ^ 1) := ⟨by simp [hlp.ne_zero]⟩
  have hlt : a.val < l := by simpa using ZMod.val_lt a
  have hinv : ζ⁻¹ = ζ ^ (l - 1) := by
    rw [eq_comm, inv_eq_of_mul_eq_one_right]
    rw [← pow_succ', Nat.sub_add_cancel hlp.one_le, hζl]
  have hav : a.val = l - 1 := by
    apply hζ.pow_inj hlt (Nat.sub_lt hlp.pos one_pos)
    rw [← hspec, hσζ, hinv]
  apply Units.ext
  rw [hval, ← ZMod.natCast_zmod_val a, hav, Units.val_neg, Units.val_one, eq_neg_iff_add_eq_zero]
  have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    simp
  rw [← h0, ← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hlp.one_le]

theorem UpperTheory.exists_galois_cyclotomic_neg_one_trivial_on_eta_psi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
          {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
          ∃ g : G ℚ Ω, D.η g = 1 ∧ barChar c.O D.Ψ g = 1 ∧ cycMod ℚ Ω l 1 g = -1 := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  obtain ⟨-, hηcc, hΨcc, -⟩ := dat_facts D
  have hcyc_cc : cycMod ℚ Ω l 1 D.cc = -1 := by
    apply cycMod_cc l
    obtain ⟨φ, hφ⟩ := D.conj
    exact ⟨φ, hφ⟩
  have hgd := D.gd.eta
  rw [← D.η_ker] at hgd
  obtain ⟨h, hmem, hnot⟩ := SetLike.not_le_iff_exists.mp hgd
  obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.mp hmem
  rw [MonoidHom.mem_ker] at hh1 hh2 hnot
  have hηh : D.η h = -1 := (Int.units_eq_one_or _).resolve_left hnot
  obtain ⟨⟨w, hw, -⟩, hall⟩ := omT Ω l c
  have hwk : w.ker = (cycMod ℚ Ω l 1).ker := (hall w hw).1
  have hwh : w h = 1 := by
    rw [← MonoidHom.mem_ker, hwk, MonoidHom.mem_ker]
    exact hh1
  obtain ⟨b, -, -, hcong⟩ := (psiBar Ω l c w hw N ψ).1
  have hΨh : barChar c.O D.Ψ h = 1 := by
    have hm := hcong e h
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hwh, hh2, one_pow, mul_one, Units.val_one] at hm
    apply Units.ext
    show (residue c.O) ((D.Ψ h : (c.O)ˣ) : c.O) = ((1 : (ResidueField c.O)ˣ) : ResidueField c.O)
    rw [Units.val_one, ← map_one (residue c.O), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hm
  refine ⟨D.cc * h, ?_, ?_, ?_⟩
  · rw [map_mul, hηcc, hηh]
    rfl
  · rw [map_mul, hΨh, mul_one]
    simp only [barChar, MonoidHom.coe_comp, Function.comp_apply, hΨcc, map_one]
  · rw [map_mul, hcyc_cc, hh1, mul_one]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

abbrev UpperTheory.V.U3.CocVal {O : Type} [CommRing O] (a : O) : Type := Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {a})

private theorem shaInj_loc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) :
    D.ι.range ∈ shaFam ℚ Ω (l * N) ∧ ∃ s', IsUnit ((D.Ψ (D.ι s') : c.O) ^ 2 - 1) := by
  obtain ⟨A, hA, hD, hIn, -⟩ := dat_loc D
  obtain ⟨s, hs, hsu⟩ := ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).2
  rw [← hIn] at hs
  obtain ⟨s', -, hs'⟩ := Subgroup.mem_map.1 hs
  refine ⟨?_, s', by rw [hs']; exact hsu⟩
  rw [hD]
  exact Chr.shaFam_mono (dvd_mul_right l N) (Or.inl ⟨A, hA, rfl⟩)

private theorem shaInj_away {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) :
    ∀ g ∈ D.Kill, ∃ D' ∈ shaFam ℚ Ω (l * N), g ∈ D' := by
  rintro g ⟨A', -, hg', -⟩
  exact ⟨_, Or.inr ⟨A', rfl⟩, hg'⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.V.U3.sha_inj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (g₁ : G ℚ Ω), D.Marked g₁ → ∀ b : c.O, b ≠ 0 → ∃ a : c.O, a ≠ 0 ∧
      ∃ γ : Submodule.torsionBy c.O (ShaU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) (l * N) ⊤) b →+ (G ℚ Ω → CocVal a),
        Function.Injective γ ∧ ∀ x, γ x ∈ shaCoc D.η D.Ψ D.Kill D.ι D.cc g₁ a := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D g₁ hM b hb
  exact ⟨b, hb, sha_inj_gen (O := c.O) e (l * N) (Chr.dirG ℚ Ω ψ) D.η D.Kill D.ι D.cc g₁ b hb hM
    (dat_facts D).2.2.2.2.2.2.1 (dat_facts D).2.2.2.2.2.1 (shaInj_away D) (shaInj_loc D).1 _
    (shaInj_loc D).2.choose_spec⟩
end
