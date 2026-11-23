module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle007
public import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem prime_p (l : ℕ) [hl : Fact l.Prime] : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have e : Rat.ringOfIntegersEquiv.symm (l : ℤ) = ((l : ℕ) : 𝓞 ℚ) := by simp
  rw [← e]
  exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv.symm : ℤ ≃* 𝓞 ℚ)).mpr h

private theorem exists_move {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A A' : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (hA' : A'.valuation ((l : ℕ) : Ω) < 1) :
    ∃ g : G ℚ Ω, ∀ x, g x ∈ A ↔ x ∈ A' := by
  have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)
  have key : ∀ B : ValuationSubring Ω, B.valuation ((l : ℕ) : Ω) < 1 →
      ∀ n : ℤ, B.valuation (n : Ω) < 1 ↔ (l : ℤ) ∣ n := by
    intro B hB n
    have hle : ∀ m : ℤ, B.valuation (m : Ω) ≤ 1 := by
      intro m
      have := B.valuation_le_one (m : B)
      simpa using this
    have hB' : B.valuation ((l : ℤ) : Ω) < 1 := by simpa using hB
    constructor
    · intro hn
      by_contra hd
      obtain ⟨a, b, hab⟩ := hpr.irreducible.coprime_iff_not_dvd.mpr hd
      have h1 : B.valuation ((a : Ω) * (l : ℤ)) < 1 := by
        rw [map_mul]
        calc B.valuation (a : Ω) * B.valuation ((l : ℤ) : Ω) ≤ 1 * B.valuation ((l : ℤ) : Ω) :=
              mul_le_mul_left (hle a) _
          _ < 1 := by rwa [one_mul]
      have h2 : B.valuation ((b : Ω) * n) < 1 := by
        rw [map_mul]
        calc B.valuation (b : Ω) * B.valuation (n : Ω) ≤ 1 * B.valuation (n : Ω) :=
              mul_le_mul_left (hle b) _
          _ < 1 := by rwa [one_mul]
      have h3 := Valuation.map_add_lt _ h1 h2
      have e : ((a : Ω) * (l : ℤ) + (b : Ω) * n) = 1 := by
        exact_mod_cast congrArg (fun z : ℤ => (z : Ω)) hab
      rw [e, map_one] at h3
      exact lt_irrefl _ h3
    · rintro ⟨m, rfl⟩
      rw [Int.cast_mul, map_mul]
      calc B.valuation ((l : ℤ) : Ω) * B.valuation (m : Ω) ≤ B.valuation ((l : ℤ) : Ω) * 1 :=
            mul_le_mul_right (hle m) _
        _ < 1 := by rwa [mul_one]
  have hne : ((l : ℕ) : 𝓞 ℚ) ≠ 0 := (prime_p l).ne_zero
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨Ideal.span {((l : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime hne).mpr (prime_p l),
      by simpa [Ideal.span_singleton_eq_bot] using hne⟩
  have hpl : ∀ B : ValuationSubring Ω, B.valuation ((l : ℕ) : Ω) < 1 → IsPlaceOver B v := by
    intro B hB x
    have hx : algebraMap ℚ Ω (x : ℚ) = ((Rat.ringOfIntegersEquiv x : ℤ) : Ω) := by
      rw [← map_intCast (algebraMap ℚ Ω), Rat.ringOfIntegersEquiv_apply_coe]
    rw [hx, key B hB]
    change _ ↔ x ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)}
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast]
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hpl A' hA') (hpl A hA)
  refine ⟨σ, fun x => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem UpperTheory.V.Ws.Rq.placeMove :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] (p : ℕ), p.Prime →
      ∀ A A' : ValuationSubring Ω, A.valuation (p : Ω) < 1 → A'.valuation (p : Ω) < 1 → ∃ g : G ℚ Ω, (∀ x, g x ∈ A ↔ x ∈ A') ∧
        (∀ s ∈ Dec (F := F) A, g⁻¹ * resQ F s * g ∈ Dec (F := ℚ) A') ∧ ∀ s ∈ Ine (F := F) A, g⁻¹ * resQ F s * g ∈ Ine (F := ℚ) A' := by
  intro Ω _ _ _ F _ p hp A A' hA hA'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_move p A A' hA hA'
  have hL : UpperTheory.V.IsLift (RingEquiv.refl ℚ) (g : Ω ≃+* Ω) := fun x => by simp
  have hc : ∀ t : G ℚ Ω, UpperTheory.V.conjGal hL t = g⁻¹ * t * g := by
    intro t
    ext x
    rw [UpperTheory.V.conjGal_apply]
    rfl
  have hsm : ∀ s : G F Ω, resQ F s • A = s • A := by
    intro s
    ext x
    simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  refine ⟨g, hg, fun s hs => ?_, fun s hs => ?_⟩
  · rw [← hc]
    apply UpperTheory.V.conjGal_mem_Dec hL hg
    rw [mem_Dec] at hs ⊢
    rw [hsm, hs]
  · rw [← hc]
    apply UpperTheory.V.conjGal_mem_Ine hL hg
    rw [mem_Ine] at hs ⊢
    obtain ⟨h1, h2⟩ := hs
    refine ⟨?_, h2⟩
    rw [MulAction.mem_stabilizer_iff] at h1 ⊢
    rw [hsm, h1]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rq.killQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Ok →
      ∀ (pr : Bool) (g0 : G ℚ Ω) (M : Type) [Monoid M] (r : G ℚ Ω →* M), (∀ g ∈ (frQ D pr g0).N, r g = 1) →
        ∀ g ∈ (T.fr ∅).N, r (resQ T.F g) = 1 := by
  intro Ω _ _ _ l _ c D hD T hT pr g0 M _ r hr g hg
  obtain ⟨A, hA, hI, hb⟩ := hg
  have hIQ : resQ T.F g ∈ Ine (F := ℚ) A := hI
  have hl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
  by_cases hw : Raw.Away D.T A
  · exact hr _ (Or.inl ⟨A, hw, hIQ, hb⟩)
  · have hw' : ∃ p ∈ D.T, A.valuation (p : Ω) < 1 := by
      by_contra h
      exact hw fun p hp hv => h ⟨p, hp, hv⟩
    obtain ⟨p, hp, hv⟩ := hw'
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact absurd hv hl
    have hpS : p ∈ D.S := by
      unfold Raw.Sb at hp
      exact Finset.mem_of_mem_filter _ hp
    have hpp : p.Prime := hD.S_prime p hpS
    obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 p A (D.pl p) hpp hv (hD.pl_over p hpp)
    have hψ : D.ψ (resQ T.F g) = 1 :=
      hT.kb A (fun q hq => by rw [Finset.mem_singleton.1 hq]; exact hl) g hI hb
    have hk : u⁻¹ * resQ T.F g * u ∈ D.ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, hψ, mul_one, ← map_mul, inv_mul_cancel, map_one]
    have h1 : r (u⁻¹ * resQ T.F g * u) = 1 := hr _ (Or.inr ⟨p, hp, hu _ hIQ, hk⟩)
    have h2 : resQ T.F g = u * (u⁻¹ * resQ T.F g * u) * u⁻¹ := by group
    rw [h2, map_mul, map_mul, h1, mul_one, ← map_mul, mul_inv_cancel, map_one]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem mu_pow {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommGroup M] {l : ℕ}
    (f : Γ →* M) (hf : IsClosed (f.ker : Set Γ)) {H : Subgroup Γ} {s : Γ} (hs : s ∈ muOf l H) :
    ∃ a : ℕ, f s ^ l ^ a = 1 := by
  obtain ⟨-, a, ha⟩ := hs
  refine ⟨a, ?_⟩
  have hle : ⁅H, H⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Commute.all _ _
  have hmem := Subgroup.topologicalClosure_minimal _ hle hf ha
  rwa [MonoidHom.mem_ker, map_pow] at hmem

private theorem one_of {M : Type} [Monoid M] {x : M} {l a m : ℕ} (h : l.Coprime m) (h1 : x ^ l ^ a = 1)
    (h2 : x ^ m = 1) : x = 1 := by
  have hc : Nat.Coprime (l ^ a) m := Nat.Coprime.pow_left a h
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one hc, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem UpperTheory.V.Ws.Rq.muPs :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Ok →
      ∀ H : Subgroup (G T.F Ω), ∀ s ∈ muOf l H, ∀ i, D.ps i (resQ T.F s) = 1 := by
  intro Ω _ _ _ l _ c D hD T hT H s hs i
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) T.F⟩
  have hcont : Continuous (resQ T.F) := (galEmbTop ℚ T.F Ω).1.continuous
  have hlp : l.Prime := Fact.out
  have gen : ∀ (χ : G ℚ Ω →* (c.O)ˣ) (m : ℕ), l.Coprime m →
      IsClosed ((χ.comp (resQ T.F)).ker : Set (G T.F Ω)) → χ (resQ T.F s) ^ m = 1 → χ (resQ T.F s) = 1 := by
    intro χ m hm hcl h2
    obtain ⟨a, ha⟩ := mu_pow (χ.comp (resQ T.F)) hcl hs
    exact one_of hm ha h2
  have closedOfOpen : ∀ χ : G ℚ Ω →* (c.O)ˣ, IsOpen (χ.ker : Set (G ℚ Ω)) →
      IsClosed ((χ.comp (resQ T.F)).ker : Set (G T.F Ω)) := by
    intro χ ho
    have hc : IsClosed (χ.ker : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen _ ho
    rw [← MonoidHom.comap_ker]
    exact hc.preimage hcont
  have hcyc : cycZ T.F Ω l s = 1 := by
    have hcl : IsClosed ((cycZ T.F Ω l).ker : Set (G T.F Ω)) :=
      isClosed_singleton.preimage (continuous_cycZ T.F Ω l)
    obtain ⟨a, ha⟩ := mu_pow (cycZ T.F Ω l) hcl hs
    have htor : cycZ T.F Ω l s ^ GroundTheory.Global.Cyclotomic.torsionExponent l = 1 :=
      (GroundTheory.Global.Cyclotomic.mem_torsion_iff l _).1
        ((CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ a, pow_pos hlp.pos a, ha⟩))
    have hcop : l.Coprime (GroundTheory.Global.Cyclotomic.torsionExponent l) := by
      simp only [GroundTheory.Global.Cyclotomic.torsionExponent, hD.l_odd, if_false]
      exact Nat.coprime_of_lt_prime (Nat.sub_pos_of_lt hlp.one_lt).ne' (Nat.sub_lt hlp.pos one_pos) hlp
    exact one_of hcop ha htor
  have hchi : chiO ℚ Ω l c.O (resQ T.F s) = 1 := by
    have e : cycZ ℚ Ω l (resQ T.F s) = cycZ T.F Ω l s := rfl
    simp only [chiO, MonoidHom.comp_apply]
    rw [e, hcyc, map_one]
  obtain ⟨m, hm, hkc⟩ := hT.kc
  have hψ : D.ψ (resQ T.F s) = 1 := gen D.ψ m hm (closedOfOpen _ hD.psi_open) (hkc s hcyc)
  obtain ⟨m', hm', hξm⟩ := hD.xi_ord
  have hξ : D.ξ (resQ T.F s) = 1 :=
    gen D.ξ m' hm' (closedOfOpen _ hD.xi_open) (by rw [← MonoidHom.pow_apply, hξm, MonoidHom.one_apply])
  have hom : D.om (resQ T.F s) = 1 := by
    have hb := hD.om_bar (resQ T.F s)
    have hb' : residue c.O ↑(D.om (resQ T.F s)) = residue c.O ↑(1 : (c.O)ˣ) := by
      have e1 : Raw.bar D.om (resQ T.F s) = residue c.O ↑(D.om (resQ T.F s)) := rfl
      have e2 : Raw.bar (chiO ℚ Ω l c.O) (resQ T.F s) = residue c.O ↑(chiO ℚ Ω l c.O (resQ T.F s)) := rfl
      rw [← e1, hb, e2, hchi]
    apply (congrFacts Ω l c).2.2.2.1 _ 1 (l - 1)
    · exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hlp.one_lt) (Nat.sub_lt hlp.pos one_pos)
    · rw [← MonoidHom.pow_apply, hD.om_pow, MonoidHom.one_apply]
    · exact one_pow _
    · rw [← residue_eq_zero_iff, map_sub, hb', sub_self]
  have hal : D.al (resQ T.F s) = 1 := by
    simp only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, hchi, hom, hξ, inv_one, mul_one]
  have hPsi : D.Psi (resQ T.F s) = 1 := by
    simp only [Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.zpow_apply,
      hψ, hchi, one_pow, one_zpow, mul_one]
  have hth : D.th (resQ T.F s) = 1 := by
    simp only [Raw.th, Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, hchi, hom, hξ, hPsi, inv_one, mul_one]
  fin_cases i
  · exact hth
  · exact hPsi
  · exact hal
  · rfl
end
