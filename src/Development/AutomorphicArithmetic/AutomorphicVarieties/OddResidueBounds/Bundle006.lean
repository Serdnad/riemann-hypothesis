module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.unrSel :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], (∃ ζ : E, IsPrimitiveRoot ζ l) → ∃ f : UnrHom E Ω l → SelK (Above E l) l ⧸ (powK E l).subgroupOf (SelK (Above E l) l), Function.Injective f := by
  intro E Ω _ _ _ _ _ l _ hζE
  obtain ⟨ζ₀, hζ₀⟩ := hζE
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Fact (1 < l) := ⟨(Fact.out : l.Prime).one_lt⟩
  have hζ : IsPrimitiveRoot (algebraMap E Ω ζ₀) l := hζ₀.map_of_injective (algebraMap E Ω).injective
  have hgζ : ∀ g : G E Ω, g (algebraMap E Ω ζ₀) = algebraMap E Ω ζ₀ := fun g => g.commutes ζ₀
  have hdata : ∀ φ : UnrHom E Ω l, ∃ β : Ω, ∃ a : Eˣ, β ^ l = algebraMap E Ω a ∧
      ∀ g : G E Ω, g β = algebraMap E Ω ζ₀ ^ (φ.1 g).val * β := by
    intro φ
    obtain ⟨hlc, hadd, -⟩ := φ.2
    exact radExists E Ω l (algebraMap E Ω ζ₀) (fun _ => 1) φ.1 hζ
      (fun g => by rw [hgζ, ZMod.val_one, pow_one]) hlc (fun g h => by rw [hadd, one_mul])
  choose β a hβa hgβ using hdata
  have hsel : ∀ φ, a φ ∈ SelK (Above E l) l := by
    intro φ
    show ∀ v ∉ Above E l, _
    intro v hv
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    refine dvdOfIne E Ω l A v (β φ) (a φ) hA (hβa φ) ?_
    intro g hg
    have hnot : ¬ A.valuation (l : Ω) < 1 := by
      intro h
      apply hv
      have hp := hA (l : 𝓞 E)
      have he : algebraMap E Ω (((l : 𝓞 E) : E)) = (l : Ω) := by simp
      exact hp.mp (he ▸ h)
    have h0 : φ.1 g = 0 := φ.2.2.2 A hnot g hg
    rw [hgβ, h0, ZMod.val_zero, pow_zero, one_mul]
  refine ⟨fun φ => QuotientGroup.mk ⟨a φ, hsel φ⟩, fun φ ψ hfe => ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfe
  obtain ⟨c, hc⟩ := hfe
  have hc' : a ψ = a φ * c ^ l := by
    have h : c ^ l = (a φ)⁻¹ * a ψ := by simpa using hc
    rw [h, mul_inv_cancel_left]
  have hβne : ∀ φ, β φ ≠ 0 := by
    intro φ h
    have h' := hβa φ
    rw [h, zero_pow (NeZero.ne l)] at h'
    exact (a φ).ne_zero ((map_eq_zero_iff _ (algebraMap E Ω).injective).mp h'.symm)
  have hcΩ : algebraMap E Ω (c : E) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E Ω).injective).mpr c.ne_zero
  apply Subtype.ext
  funext g
  have hγl : (β ψ / (β φ * algebraMap E Ω c)) ^ l = 1 := by
    rw [div_pow, mul_pow, hβa ψ, hβa φ, ← map_pow, ← map_mul, hc', Units.val_mul, Units.val_pow_eq_pow_val]
    exact div_self ((map_ne_zero_iff _ (algebraMap E Ω).injective).mpr
      (mul_ne_zero (a φ).ne_zero (pow_ne_zero _ c.ne_zero)))
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hγl
  have hgγ : g (β ψ / (β φ * algebraMap E Ω c)) = β ψ / (β φ * algebraMap E Ω c) := by
    rw [← hi, map_pow, hgζ]
  have hγ0 : β ψ / (β φ * algebraMap E Ω c) ≠ 0 := div_ne_zero (hβne ψ) (mul_ne_zero (hβne φ) hcΩ)
  have hgγ' : g (β ψ / (β φ * algebraMap E Ω c)) =
      algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val *
        (β ψ / (β φ * algebraMap E Ω c)) := by
    rw [map_div₀, map_mul, hgβ, hgβ, AlgEquiv.commutes, mul_assoc, mul_div_mul_comm]
  have hζb : algebraMap E Ω ζ₀ ^ (φ.1 g).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne l))
  have hq : algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val = 1 := by
    apply mul_right_cancel₀ hγ0
    rw [one_mul, ← hgγ', hgγ]
  have hpow := ((div_eq_one_iff_eq hζb).mp hq).symm
  exact ZMod.val_injective l (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem pow_tot_mem (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (N : ℕ) [NeZero N] (g : G E Ω) : g ^ N.totient ∈ fixMu E Ω N := by
  obtain ⟨b, hb⟩ := (liftEx E Ω N).2 g.toRingEquiv
  intro x hx
  have h : ∀ k : ℕ, (g ^ k) x = x ^ ((b : ZMod N).val ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, pow_succ', pow_mul]
      congr 1
      exact hb x hx
  rw [h, pow_eq_pow_mod _ hx, (Nat.ModEq.pow_totient (ZMod.val_coe_unit_coprime b) : _ % N = 1 % N),
    ← pow_eq_pow_mod _ hx, pow_one]

theorem UpperTheory.V.Odd.totKill :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (N : ℕ) [NeZero N], e ≠ 0 → Procyc E Ω l → ∀ x : H1 (qzTw D e), (∀ u : Uinf E Ω l, u.1 ∈ fixMu E Ω N → resInf D e x u = 0) → N.totient • x = 0 := by
  intro E Ω _ _ _ _ _ l _ D e N _ he hP x hx
  have hadd : ∀ a b : Uinf E Ω l, resInf D e x (a * b) = resInf D e x a + resInf D e x b := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hchi : ∀ g : G E Ω, D.chi (toGS Ω _ g) = cycZ E Ω l g := fun g => DFunLike.congr_fun D.hchi g
    have htriv : ∀ g : G E Ω, cycZ E Ω l g = 1 → ∀ m, qzTw D e (toGS Ω _ g) m = m := fun g hg m => by
      rw [qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul]
    have hz : ∀ a b, z.1 (a * b) = z.1 a + qzTw D e a (z.1 b) := z.2.2
    intro a b
    rw [resInf_mk, resInf_mk, resInf_mk, Subgroup.coe_mul, map_mul, hz, htriv _ a.2.2]
  have hpow : ∀ (u : Uinf E Ω l) (k : ℕ), resInf D e x (u ^ k) = k • resInf D e x u := by
    intro u k
    induction k with
    | zero =>
      have := hadd 1 1
      rw [one_mul] at this
      rw [pow_zero, zero_smul]
      exact left_eq_add.1 this
    | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]
  apply resInfInj E Ω l D e he hP
  rw [map_nsmul, map_zero]
  funext u
  rw [Pi.smul_apply, ← hpow]
  exact hx _ (by rw [Subgroup.coe_pow]; exact pow_tot_mem E Ω N u.1)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.actFacts :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → Function.Surjective ρ ∧ IsAbelianGalois ℚ E ∧ Nat.card (Gq ρ) = Module.finrank ℚ E ∧ ρ.ker.index = Module.finrank ℚ E ∧ ∀ (M : ℕ) [NeZero M] (h : N ∣ M), IsCycAct Ω M (ρ.comp (ZMod.unitsMap h)) := by
  intro E Ω _ _ _ _ _ N _ ρ hρ
  obtain ⟨_, hb⟩ := liftEx E Ω N
  have inj := (algebraMap E Ω).injective
  have hsurj : Function.Surjective ρ := by
    intro τ
    obtain ⟨σ, hσ⟩ := exists_isLift (Ω := Ω) τ.toRingEquiv
    obtain ⟨b, hbσ⟩ := hb σ
    refine ⟨b, ?_⟩
    ext x
    apply inj
    have h1 := hρ b σ hbσ x
    have h2 := hσ x
    simpa using h1.symm.trans h2
  haveI hc : CharZero Ω := charZero_of_injective_algebraMap inj
  haveI : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have key : ∀ φ : E →ₐ[ℚ] Ω, ∃ σ : Ω ≃+* Ω, ∀ x : E, σ (algebraMap E Ω x) = φ x := by
    intro φ
    refine ⟨((Algebra.IsAlgebraic.algEquivEquivAlgHom ℚ Ω).symm (φ.liftNormal Ω)).toRingEquiv,
      fun x => ?_⟩
    change φ.liftNormal Ω (algebraMap E Ω x) = φ x
    simpa only [Algebra.algebraMap_self_apply] using φ.liftNormal_commutes Ω x
  let f : Gal(E/ℚ) → (E →ₐ[ℚ] Ω) := fun g => (IsScalarTower.toAlgHom ℚ E Ω).comp g.toAlgHom
  have hf : Function.Surjective f := by
    intro φ
    obtain ⟨σ, hσ⟩ := key φ
    obtain ⟨b, hbσ⟩ := hb σ
    refine ⟨ρ b, ?_⟩
    ext x
    have h1 := hρ b σ hbσ x
    rw [← hσ x, h1]
    rfl
  have hcard : Nat.card Gal(E/ℚ) = Module.finrank ℚ E := by
    apply le_antisymm
    · rw [Nat.card_eq_fintype_card]
      exact AlgEquiv.card_le
    · calc Module.finrank ℚ E = Nat.card (E →ₐ[ℚ] Ω) := by
            rw [Nat.card_eq_fintype_card, AlgHom.card]
        _ ≤ Nat.card Gal(E/ℚ) := Nat.card_le_card_of_surjective f hf
  haveI : IsGalois ℚ E := IsGalois.of_card_aut_eq_finrank ℚ E hcard
  have hq : Nat.card (Gq ρ) = Module.finrank ℚ E := by
    rw [← hcard]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj).toEquiv
  refine ⟨hsurj, ?_, hq, hq, ?_⟩
  · exact
      { is_comm := ⟨fun x y => by
          obtain ⟨a, rfl⟩ := hsurj x
          obtain ⟨c, rfl⟩ := hsurj y
          rw [← map_mul, ← map_mul, mul_comm]⟩ }
  · intro M _ h b σ hσ
    apply hρ
    intro x hx
    have hxM : x ^ M = 1 := by
      obtain ⟨k, rfl⟩ := h
      rw [pow_mul, hx, one_pow]
    rw [hσ x hxM, ZMod.unitsMap_val]
    have e : (ZMod.cast (b : ZMod M) : ZMod N).val = (b : ZMod M).val % N := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (b : ZMod M)]
      rw [ZMod.cast_natCast h, ZMod.val_natCast]
    rw [e]
    conv_lhs => rw [← Nat.div_add_mod (b : ZMod M).val N]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
end
