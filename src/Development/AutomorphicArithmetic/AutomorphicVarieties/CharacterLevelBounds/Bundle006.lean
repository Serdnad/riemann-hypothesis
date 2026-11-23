module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigSign
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem aux {O W M : Type} [CommRing O] [IsDomain O] [Group W] [AddCommGroup M] [Module O M] {N : ℕ} [NeZero N]
    (H : Subgroup (ZMod N)ˣ) [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))]
    (π : Representation O W M) (cl : W →* (ZMod N)ˣ) (hcl : Function.Surjective cl)
    (hker : ∀ g, cl g ∈ H → ∀ x, π g x = x) (h2 : IsUnit (2 : O)) (s : ℕ) (c : W) (hcc : cl c = -1)
    (T : Finset (DirichletCharacter O N)) (hT : evenSet O H s ⊆ ↑T) :
    Module.length O (Module.End.eigenspace (π c) ((-1 : O) ^ s)) ≤
      ∑ χ ∈ T, Module.length O (eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) M)
        ((χ.toUnitHom.comp cl).comp (⊤ : Subgroup W).subtype)) := by
  classical
  let _ : Fintype (((ZMod N)ˣ ⧸ H) →* Oˣ) := Fintype.ofFinite _
  let p : W →* (ZMod N)ˣ ⧸ H := (QuotientGroup.mk' H).comp cl
  have hp : Function.Surjective p := (QuotientGroup.mk'_surjective H).comp hcl
  have hpc : p c = QuotientGroup.mk' H (-1) := by
    show QuotientGroup.mk' H (cl c) = _
    rw [hcc]
  let f : (((ZMod N)ˣ ⧸ H) →* Oˣ) → DirichletCharacter O N := fun ψ =>
    MulChar.ofUnitHom (ψ.comp (QuotientGroup.mk' H))
  have hf : ∀ ψ, (f ψ).toUnitHom = ψ.comp (QuotientGroup.mk' H) := fun ψ =>
    MulChar.equivToUnitHom.apply_symm_apply _
  have finj : Function.Injective f := fun ψ ψ' h => by
    have h' : ψ.comp (QuotientGroup.mk' H) = ψ'.comp (QuotientGroup.mk' H) := by rw [← hf, ← hf, h]
    exact (MonoidHom.cancel_right (QuotientGroup.mk'_surjective H)).1 h'
  have key := lenEigSign O W ((ZMod N)ˣ ⧸ H) M π p hp
    (fun g hg x => hker g ((QuotientGroup.eq_one_iff _).1 hg) x) h2 c ((-1) ^ s)
    (by rw [hpc, ← map_mul]; simp) (by rw [← mul_pow]; simp)
    (Finset.univ.filter fun ψ => ψ (p c) = (-1) ^ s) (fun ψ h => by simpa using h)
  have hs : (((-1 : Oˣ) ^ s : Oˣ) : O) = (-1) ^ s := by simp
  rw [hs] at key
  refine key.trans ?_
  have hE : ∀ ψ : ((ZMod N)ˣ ⧸ H) →* Oˣ, eig π (ψ.comp p) =
      eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) M)
        (((f ψ).toUnitHom.comp cl).comp (⊤ : Subgroup W).subtype) := by
    intro ψ
    ext x
    rw [mem_eig, mem_eig, hf]
    exact ⟨fun h g => h g.1, fun h g => h ⟨g, trivial⟩⟩
  rw [Finset.sum_congr rfl fun ψ _ => congrArg (fun S : Submodule O M => Module.length O S) (hE ψ),
    ← Finset.sum_image (f := fun χ : DirichletCharacter O N => Module.length O
      (eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) M)
        ((χ.toUnitHom.comp cl).comp (⊤ : Subgroup W).subtype))) finj.injOn]
  refine Finset.sum_le_sum_of_subset fun χ hχ => ?_
  obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.1 hχ
  have hψ' := (Finset.mem_filter.1 hψ).2
  refine hT ⟨fun u hu => ?_, ?_⟩
  · rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).2 hu, map_one]
  · have : f ψ (((-1 : (ZMod N)ˣ)) : ZMod N) = (((f ψ).toUnitHom (-1) : Oˣ) : O) := (MulChar.coe_toUnitHom _ _).symm
    rw [hf, MonoidHom.comp_apply, ← hpc, hψ', hs] at this
    simpa using this

theorem UpperTheory.V.Chr.signLe :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))], l ≠ 2 → ∀ (e s : ℕ) (c : G ℚ Ω), IsConjOm c.toRingEquiv →
          ∀ T : Finset (DirichletCharacter O N), evenSet O H s ⊆ ↑T →
          Module.length O (Module.End.eigenspace (shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H) c) ((-1 : O) ^ s)) ≤
            ∑ χ ∈ T, eigL l e (levH ℚ Ω H) (dirG ℚ Ω χ) := by
  intro Ω _ _ _ N _ H l hl O _ _ _ _ _ _ hl2 e s c hc T hT
  have h2 : IsUnit (2 : O) := by
    have := (dvrFacts l O).2.2.2.2.2.2.2.2 2 fun h =>
      hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h)
    simpa using this
  have hker : ∀ g, cls ℚ Ω N g ∈ H → ∀ x, shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H) g x = x :=
    fun g hg x => selRep_of_mem _ (levH ℚ Ω H) _ (g := g) (Subgroup.mem_comap.2 hg) x
  exact aux H (shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H)) (cls ℚ Ω N) (clsOnto Ω N).1
    hker h2 s c ((clsFacts ℚ Ω N).2.2.2.1 c hc) T hT
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.H0_local_card_bounded_of_cls_ker_le_ker :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N : ℕ) [NeZero N] (e : ℕ) (ψ : G ℚ Ω →* Oˣ), e ≠ 0 → (cls ℚ Ω N).ker ≤ ψ.ker →
          (∀ (A : ValuationSubring Ω) (U : Subgroup (G ℚ Ω)), A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ U →
            h0 l e ψ U ≤ (LDataCardLeFinrank.nuBound l N e : ℕ∞) * eO l O) ∧ h0 l e ψ ⊤ ≤ (LDataCardLeFinrank.nuBound l N e : ℕ∞) * eO l O := by
  intro Ω _ _ _ l hl O _ _ _ _ _ N _ e ψ he hψ
  have key : ∀ (A : ValuationSubring Ω) (U : Subgroup (G ℚ Ω)), A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ U →
      h0 l e ψ U ≤ (LDataCardLeFinrank.nuBound l N e : ℕ∞) * eO l O := by
    intro A U hA hU
    have h1 := (h0Nu ℚ Ω l O e ψ U).1 (Ine (F := ℚ) A ⊓ (cls ℚ Ω N).ker) (inf_le_left.trans hU)
    have h2 := (h0Nu ℚ Ω l O e ψ (Ine (F := ℚ) A ⊓ (cls ℚ Ω N).ker)).2 (inf_le_right.trans hψ)
    have h3 := LDataCardLeFinrank.nuLeBound l N e _ ((clsOnto Ω N).2 l A hA) he
    exact h1.trans (h2.trans (mul_le_mul_left h3 _))
  obtain ⟨A, hA⟩ := (placesQ Ω).1 l hl.out
  exact ⟨key, key A ⊤ hA le_top⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem not_both {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p l : ℕ} (h : Nat.Coprime p l)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (l : Ω) < 1 := by
  intro hl
  have hg : ((Nat.gcd p l : ℕ) : ℤ) = (p : ℤ) * Nat.gcdA p l + (l : ℤ) * Nat.gcdB p l := Nat.gcd_eq_gcd_ab p l
  rw [h.gcd_eq_one, Nat.cast_one] at hg
  have hΩ : (1 : Ω) = (p : Ω) * ((Nat.gcdA p l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB p l : ℤ) : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hg
    push_cast at this
    exact this
  have hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => A.valuation_le_one ⟨(z : Ω), intCast_mem A z⟩
  have h1 : A.valuation ((p : Ω) * ((Nat.gcdA p l : ℤ) : Ω)) < 1 := by
    rw [Valuation.map_mul]
    calc A.valuation (p : Ω) * A.valuation ((Nat.gcdA p l : ℤ) : Ω) ≤ A.valuation (p : Ω) * 1 := by
          gcongr
          exact hint _
      _ < 1 := by rw [mul_one]; exact hp
  have h2 : A.valuation ((l : Ω) * ((Nat.gcdB p l : ℤ) : Ω)) < 1 := by
    rw [Valuation.map_mul]
    calc A.valuation (l : Ω) * A.valuation ((Nat.gcdB p l : ℤ) : Ω) ≤ A.valuation (l : Ω) * 1 := by
          gcongr
          exact hint _
      _ < 1 := by rw [mul_one]; exact hl
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [← hΩ, Valuation.map_one] at h3
  exact lt_irrefl _ h3

theorem UpperTheory.V.Chr.locUnr :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e n : ℕ) (ψ : G ℚ Ω →* Oˣ), e ≠ 0 → n ≠ 0 → IsOpen (ψ.ker : Set (G ℚ Ω)) → ψ ^ n = 1 →
          ∀ (p : ℕ) (A : ValuationSubring Ω), p.Prime → p ≠ l → A.valuation (p : Ω) < 1 →
          ∀ (U' U : Subgroup (G ℚ Ω)) (h : U' ≤ U), U' = Ine (F := ℚ) A → U = Dec (F := ℚ) A →
          Module.length O (LinearMap.ker (resU (rho l e ψ) h)) ≤ (n.factorization l : ℕ∞) * eO l O ∧
            (U' ≤ ψ.ker → Function.Injective (resU (rho l e ψ) h)) := by
  intro Ω _ _ _ l _ O _ _ _ _ _ e n ψ he hn hopen hpow p A hp hpl hAp U' U h hU' hU
  subst hU' hU
  obtain ⟨hnorm, _, γ, hγ, hcl, hcyc⟩ := decCyc Ω p A hp hAp
  haveI := hnorm
  obtain ⟨_, hζ, heOtop, hchar⟩ := rootVal l O n hn
  haveI := hchar
  have hlprime : l.Prime := Fact.out
  have hlA : ¬ A.valuation (l : Ω) < 1 := not_both A ((Nat.coprime_primes hp hlprime).2 hpl) hAp
  have hIneCyc : Ine (F := ℚ) A ≤ (cycZ ℚ Ω l).ker := (places ℚ Ω l A).2.2.2 hlA
  have hcont : ContAction (rho l e ψ) := by
    have hk : IsOpen ((ψ⁻¹).ker : Set (G ℚ Ω)) := by
      have hkk : (ψ⁻¹).ker = ψ.ker := by
        ext g
        simp [MonoidHom.mem_ker]
      rw [hkk]
      exact hopen
    exact (contTw ℚ Ω l).2.2 O ψ⁻¹ (-(e : ℤ)) hk
  have hK := kerResCyc O (G ℚ Ω) (QO l O) (rho l e ψ) hcont (Ine (F := ℚ) A) (Dec (F := ℚ) A) h γ hγ hcl
  have hact : ∀ g m, rho l e ψ g m = (((ψ g)⁻¹ * (chiO ℚ Ω l O g) ^ (-(e : ℤ)) : Oˣ) : O) • m := by
    intro g m
    rw [rho, twist₂, scalRep_apply]
    rfl
  have hchiIne : ∀ g ∈ Ine (F := ℚ) A, chiO ℚ Ω l O g = 1 := by
    intro g hg
    have h1 : cycZ ℚ Ω l g = 1 := hIneCyc hg
    simp [chiO, h1]
  have hchiγ : ((chiO ℚ Ω l O γ : Oˣ) : O) = (p : O) := by
    have h1 := hcyc l hpl.symm
    show algebraMap ℤ_[l] O ((cycZ ℚ Ω l γ : ℤ_[l]ˣ) : ℤ_[l]) = (p : O)
    rw [h1]
    exact map_natCast (algebraMap ℤ_[l] O) p
  have hψn : ∀ g, (ψ g) ^ n = 1 := by
    intro g
    have := congrArg (fun f => f g) hpow
    simpa using this
  have hinj : Ine (F := ℚ) A ≤ ψ.ker → Function.Injective (resU (rho l e ψ) h) := by
    intro hker
    apply hK.2
    intro m _
    set c : Oˣ := (ψ γ)⁻¹ * (chiO ℚ Ω l O γ) ^ (-(e : ℤ)) with hcdef
    have hc1 : (c : O) - 1 ≠ 0 := by
      intro h0
      have hcU : c = 1 := Units.ext (sub_eq_zero.mp h0)
      have h2 : c ^ n = 1 := by rw [hcU, one_pow]
      have key : (chiO ℚ Ω l O γ) ^ (e * n) = (c ^ n)⁻¹ := by
        rw [hcdef, mul_pow, inv_pow, hψn γ, inv_one, one_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
          ← zpow_neg]
        congr 1
        push_cast
        ring
      rw [h2, inv_one] at key
      have hv := congrArg (fun u : Oˣ => (u : O)) key
      simp only [Units.val_pow_eq_pow_val, hchiγ, Units.val_one] at hv
      have hv' : ((p ^ (e * n) : ℕ) : O) = ((1 : ℕ) : O) := by push_cast; exact hv
      have hnat := Nat.cast_injective hv'
      exact absurd hnat (Nat.one_lt_pow (Nat.mul_ne_zero he hn) hp.one_lt).ne'
    obtain ⟨m', hm'⟩ := (qoFacts l O).2.2.1 ((c : O) - 1) hc1 m
    refine ⟨m', ?_, ?_⟩
    · rw [H0U, mem_riemannRochSpace_iff_regularAt_everywhere]
      intro g
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hact, hchiIne g g.2, hker g.2]
      simp
    · rw [hact, ← hm', sub_smul, one_smul]
  refine ⟨?_, hinj⟩
  by_cases hker : Ine (F := ℚ) A ≤ ψ.ker
  · have hbot : LinearMap.ker (resU (rho l e ψ) h) = ⊥ := LinearMap.ker_eq_bot.mpr (hinj hker)
    rw [hbot]
    simp
  · obtain ⟨g, hg, hgk⟩ := SetLike.not_le_iff_exists.mp hker
    set ζ : O := (((ψ g)⁻¹ : Oˣ) : O) with hζdef
    have hζn : ζ ^ n = 1 := by
      rw [hζdef, ← Units.val_pow_eq_pow_val, inv_pow, hψn g, inv_one, Units.val_one]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      apply hgk
      rw [MonoidHom.mem_ker]
      have : ((ψ g)⁻¹ : Oˣ) = 1 := Units.ext h1
      exact inv_eq_one.mp this
    have hsub : H0U (rho l e ψ) (Ine (F := ℚ) A) ≤ ((ζ - 1) • LinearMap.id : QO l O →ₗ[O] QO l O).ker := by
      intro m hm
      rw [H0U, mem_riemannRochSpace_iff_regularAt_everywhere] at hm
      have h1 := hm ⟨g, hg⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hact, hchiIne g hg] at h1
      simp only [one_zpow, mul_one] at h1
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, sub_smul, one_smul, hζdef, h1, sub_self]
    have hbound : Module.length O (H0U (rho l e ψ) (Ine (F := ℚ) A)) ≤ (n.factorization l : ℕ∞) * eO l O := by
      refine (Module.length_le_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)).trans ?_
      rw [(qoFacts l O).2.2.2]
      exact hζ ζ hζn hζ1
    have hfin : Module.length O (H0U (rho l e ψ) (Ine (F := ℚ) A)) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.coe_ne_top _) heOtop) hbound
    have hmono : H0U (rho l e ψ) (Dec (F := ℚ) A) ≤ H0U (rho l e ψ) (Ine (F := ℚ) A) := by
      intro m hm
      rw [H0U, mem_riemannRochSpace_iff_regularAt_everywhere] at hm ⊢
      intro g
      exact hm ⟨g, h g.2⟩
    exact (hK.1 hfin).trans ((Module.length_le_of_injective (Submodule.inclusion hmono)
      (Submodule.inclusion_injective hmono)).trans hbound)
end
