module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle006
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GlobalEulerCharacteristicRationalsOddPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoContLev
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDecNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle007
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoScal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle006
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
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle006

@[expose] public section

local instance (priority := 2000) fieldAlgebraIsTorsionFreeForLevelCohomology (K Ω : Type)
    [Field K] [Field Ω] [Algebra K Ω] : Module.IsTorsionFree K Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.unrOf :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (k : Type) [Field k] (γ : G ℚ Ω →* kˣ) (K : Subgroup (G ℚ Ω)) [K.Normal], K ≤ γ.ker → ∀ (SP : Set (HeightOneSpectrum (𝓞 ℚ))) (T : Finset ℕ) (z : GS Ω SP → k), (∀ g h, z (toGS Ω SP (g * h)) = z (toGS Ω SP g) + (γ g : k) * z (toGS Ω SP h)) → (∀ v ∈ SP, (∃ p ∈ T, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) ∨ ∃ A, IsPlaceOver A v ∧ ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z (toGS Ω SP g) = 0) → ∀ A : ValuationSubring Ω, (∀ p ∈ T, ¬ A.valuation (p : Ω) < 1) → ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z (toGS Ω SP g) = 0 := by
  intro Ω _ _ _ k _ γ K hKn hK SP T z hz hS A hA g hg hgK
  have h1 : z (toGS Ω SP 1) = 0 := by
    have e := hz 1 1
    rw [mul_one, map_one γ, Units.val_one, one_mul] at e
    linear_combination (-1 : k) * e
  obtain ⟨hTop, hPl, -, hAb⟩ := UpperTheory.V.Kum.placeDict ℚ Ω
  by_cases hAT : A = ⊤
  · subst hAT
    rw [hTop, Subgroup.mem_bot] at hg
    subst hg
    exact h1
  obtain ⟨v, hv⟩ := hPl A hAT
  by_cases hvS : v ∈ SP
  · rcases hS v hvS with ⟨p, hpT, hp⟩ | ⟨A', hA', hz0⟩
    · exact absurd ((hAb A v p hv).mpr hp) (hA p hpT)
    · obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA' hv
      subst hσ
      have hc : σ⁻¹ * g * σ ∈ Ine (F := ℚ) A' := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hg
      have hcK : σ⁻¹ * g * σ ∈ K := by
        have e := hKn.conj_mem g hgK σ⁻¹
        simpa only [inv_inv] using e
      have e0 := hz0 _ hc hcK
      have e1 := hz g σ
      have e2 := hz σ (σ⁻¹ * g * σ)
      have hγ : γ g = 1 := hK hgK
      have hm : σ * (σ⁻¹ * g * σ) = g * σ := by group
      rw [hγ, Units.val_one, one_mul] at e1
      rw [hm, e0, mul_zero, add_zero] at e2
      linear_combination e2 - e1
  · have hN : g ∈ NS Ω SP := by
      unfold NS
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hvS, A, hv, hg⟩
    have e : toGS Ω SP g = toGS Ω SP 1 := by
      rw [map_one]
      exact (QuotientGroup.eq_one_iff g).mpr hN
    rw [e]
    exact h1
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.globEuler :
    GlobalFiniteness → GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → ∀ σ : G ℚ Ω, IsCC σ → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
  intro hF hE Ω _ inst _ l _ hl S hS k _ _ _ M _ _ _ _ _ ρ hρ σ hσ
  have hc : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hM : Finite M := Module.finite_of_finite k
  exact UpperTheory.global_euler_characteristic_rationals_odd_prime hF hE Ω l hl k M S ρ hS hρ σ hσ
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem arith (l n : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (hn : 0 < n) (hnd : ¬ l ∣ n) :
    0 < orderOf (l : ZMod (Nat.lcm 4 n)) ∧ Nat.lcm 4 n ∣ l ^ orderOf (l : ZMod (Nat.lcm 4 n)) - 1 := by
  have hm0 : Nat.lcm 4 n ≠ 0 := Nat.lcm_ne_zero (by norm_num) hn.ne'
  haveI : NeZero (Nat.lcm 4 n) := ⟨hm0⟩
  have h2 : Nat.Coprime l 2 := (Nat.coprime_primes hl Nat.prime_two).mpr hl2
  have h4 : Nat.Coprime l 4 := by
    have e := Nat.Coprime.pow_right 2 h2
    norm_num at e
    exact e
  have hn' : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hnd
  have hc : Nat.Coprime l (Nat.lcm 4 n) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul 4 n) (Nat.Coprime.mul_right h4 hn')
  have hue : ((ZMod.unitOfCoprime l hc : (ZMod (Nat.lcm 4 n))ˣ) : ZMod (Nat.lcm 4 n)) = (l : ZMod (Nat.lcm 4 n)) :=
    ZMod.coe_unitOfCoprime l hc
  have hord : orderOf (l : ZMod (Nat.lcm 4 n)) = orderOf (ZMod.unitOfCoprime l hc) := by
    rw [← hue, orderOf_units]
  refine ⟨by rw [hord]; exact orderOf_pos _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hl.pos), Nat.cast_pow,
    pow_orderOf_eq_one, Nat.cast_one, sub_self]

theorem UpperTheory.V.X.th1Facts :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N) (l : ℕ), l.Prime → l ≠ 2 → ψ = psi2 ψ * th1 l ψ * kap l ψ ∧ (∃ s, kap l ψ ^ l ^ s = 1) ∧ Odd (th1 l ψ ^ 2).conductor ∧ 0 < f0 l ψ ∧ 4 ∣ l ^ f0 l ψ - 1 ∧ th1 l ψ ^ (l ^ f0 l ψ - 1) = 1 ∧ l - 1 ∣ l ^ f0 l ψ - 1 := by
  intro O _ _ N _ ψ l hl hl2
  obtain ⟨-, hmul, hone, hinv, hpow, hidem, -, -⟩ := compAlg O N 2 Nat.prime_two
  have hfin : 0 < orderOf ψ := orderOf_pos ψ
  obtain ⟨hoK, -, hndvd, -, -, -, -⟩ := partOrd _ l hl ψ hfin
  have hkapOrd : orderOf (kap l ψ) = l ^ (orderOf ψ).factorization l := hoK
  have hc2k : comp 2 (kap l ψ) = 1 := by
    obtain ⟨k, hk⟩ := (compOrd O N (kap l ψ) 2 Nat.prime_two).2.1
    have hd : orderOf (comp 2 (kap l ψ)) ∣ orderOf (kap l ψ) := (hidem (kap l ψ)).2.1
    rw [hk, hkapOrd] at hd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ l ^ (orderOf ψ).factorization l := dvd_trans (dvd_pow_self 2 hk0) hd
      have e := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).mp (Nat.prime_two.dvd_of_dvd_pow h2)
      exact hl2 e.symm
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hψ : th0 l ψ * kap l ψ = ψ := dirichletPrimeToLPart_mul_lPowerPart l ψ
  have hc2 : comp 2 ψ = comp 2 (th0 l ψ) := by
    conv_lhs => rw [← hψ]
    rw [hmul, hc2k, mul_one]
  have hth1c : comp 2 (th1 l ψ) = 1 := by
    show comp 2 (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) = 1
    rw [hmul, hinv, (hidem _).1, mul_inv_cancel]
  have hth1pow : th1 l ψ ^ orderOf (th0 l ψ) = 1 := by
    show (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) ^ orderOf (th0 l ψ) = 1
    rw [mul_pow, inv_pow, ← hpow, pow_orderOf_eq_one, hone, inv_one, mul_one]
  have hdvd1 : orderOf (th1 l ψ) ∣ orderOf (th0 l ψ) := orderOf_dvd_of_pow_eq_one hth1pow
  have hnd1 : ¬ l ∣ orderOf (th1 l ψ) := fun h => hndvd (dvd_trans h hdvd1)
  have hpos1 : 0 < orderOf (th1 l ψ) := orderOf_pos _
  obtain ⟨hf0, hdiv⟩ := arith l (orderOf (th1 l ψ)) hl hl2 hpos1 hnd1
  have hf : f0 l ψ = orderOf ((l : ZMod (Nat.lcm 4 (orderOf (th1 l ψ))))) := rfl
  refine ⟨?_, ⟨(orderOf ψ).factorization l, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show ψ = comp 2 ψ * (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) * kap l ψ
    rw [hc2, mul_comm (comp 2 (th0 l ψ)) (th0 l ψ * _), inv_mul_cancel_right]
    exact hψ.symm
  · rw [← hkapOrd]
    exact pow_orderOf_eq_one _
  · have h1 : comp 2 (th1 l ψ ^ 2) = 1 := by
      rw [hpow, hth1c, one_pow]
    have h := ((compCond O N (th1 l ψ ^ 2) 2 Nat.prime_two).2.1).mp h1
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  · rw [hf]
    exact hf0
  · rw [hf]
    exact dvd_trans (Nat.dvd_lcm_left 4 _) hdiv
  · rw [hf]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (Nat.dvd_lcm_right 4 _) hdiv)
  · have e := Nat.sub_dvd_pow_sub_pow l 1 (f0 l ψ)
    rwa [one_pow] at e
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private def lkRepZ {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M] (N : ℕ) [Module (ZMod N) M]
    (ρ : Representation O Γ M) : Representation (ZMod N) Γ M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap N
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul, Module.End.mul_apply]

theorem UpperTheory.V.X.So.locKill :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ n : ℤ, n ≠ 0 → n ≠ 1 → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ((l : ℕ) : 𝓞 k) ∉ v.asIdeal → ∃ B : ℕ, ∀ (a : O) (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation O (Dec (F := k) A) M), IsLev a ((ψ * chiO k Ω l O ^ n).comp (Dec (F := k) A).subtype) ρ → Finite (H1 ρ) ∧ Nat.card (H1 ρ) ≤ B := by
  intro hFin hTate hEul k Ω _ _ _ _ _ l _ O _ _ _ _ _ ψ hψ n hn0 hn1 v A hA hl
  obtain ⟨g₁, hg₁D, hg₁⟩ := So.decNe k Ω l O ψ hψ n hn0 v A hA
  have hψ' : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
    have hk : (ψ⁻¹).ker = ψ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hk]
    exact hψ
  obtain ⟨g₂, hg₂D, hg₂⟩ :=
    So.decNe k Ω l O ψ⁻¹ hψ' (1 - n) (sub_ne_zero.mpr (Ne.symm hn1)) v A hA
  set d₁ : O := (((ψ * chiO k Ω l O ^ n) g₁ : Oˣ) : O) - 1 with hd₁
  set d₂ : O := (((ψ⁻¹ * chiO k Ω l O ^ (1 - n)) g₂ : Oˣ) : O) - 1 with hd₂
  have hd₁0 : d₁ ≠ 0 := by
    intro h
    apply hg₁
    apply Units.ext
    simpa [hd₁, sub_eq_zero] using h
  have hd₂0 : d₂ ≠ 0 := by
    intro h
    apply hg₂
    apply Units.ext
    simpa [hd₂, sub_eq_zero] using h
  obtain ⟨hM0fin, ⟨r₀, -, hr₀k⟩, -⟩ :=
    So.levFacts l O d₂ hd₂0 (O ⧸ Ideal.span {d₂}) ⟨LinearEquiv.refl O _⟩
  haveI := hM0fin
  haveI : NeZero (l ^ r₀) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Module (ZMod (l ^ r₀)) (O ⧸ Ideal.span {d₂}) := AddCommGroup.zmodModule hr₀k
  obtain ⟨ι₀, -, hι₀rng, -⟩ :=
    So.dualEmb l O d₂ hd₂0 r₀ (O ⧸ Ideal.span {d₂}) ⟨LinearEquiv.refl O _⟩
  haveI hTfin : Finite (TDual (ZMod (l ^ r₀)) (O ⧸ Ideal.span {d₂})) := by
    unfold TDual Module.Dual
    exact Finite.of_injective
      (fun f : (O ⧸ Ideal.span {d₂}) →ₗ[ZMod (l ^ r₀)] ZMod (l ^ r₀) => (f : (O ⧸ Ideal.span {d₂}) → ZMod (l ^ r₀)))
      (fun f g h => LinearMap.ext (congrFun h))
  refine ⟨Nat.card (O ⧸ Ideal.span {d₁}) *
    Nat.card (TDual (ZMod (l ^ r₀)) (O ⧸ Ideal.span {d₂})), ?_⟩
  intro a M _ _ _ _ ρ hρ
  obtain ⟨hMfin, ⟨r, hr, hrk⟩, hMt⟩ := So.levFacts l O a hρ.ne M hρ.cyc
  haveI := hMfin
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule hrk
  set ρZ := lkRepZ (l ^ r) ρ with hρZ
  have hρZapp : ∀ g m, ρZ g m = ρ g m := fun g m => rfl
  let ρG : Representation O (G k Ω) M :=
    (Module.toModuleEnd O (S := O) M).toMonoidHom.comp
      ((Units.coeHom O).comp (ψ * chiO k Ω l O ^ n))
  have hρG : IsLev a (ψ * chiO k Ω l O ^ n) ρG := ⟨hρ.ne, hρ.cyc, fun g m => rfl⟩
  have hcG := So.contLev k Ω l O ψ n hψ a M ρG hρG
  have hcZ : ReciprocityTheory.Gal.ContAction ρZ := by
    have hf : (fun p : Dec (F := k) A × M => ρZ p.1 p.2) =
        (fun p : G k Ω × M => ρG p.1 p.2) ∘ (fun p : Dec (F := k) A × M => ((p.1 : G k Ω), p.2)) := by
      funext p
      rw [hρZapp, hρ.act]
      rfl
    unfold ReciprocityTheory.Gal.ContAction
    rw [hf]
    exact hcG.comp (continuous_subtype_val.prodMap continuous_id)
  let τ : Representation (ZMod (l ^ r)) (Dec (F := k) A) (TDual (ZMod (l ^ r)) M) :=
    { toFun := fun g => ((cycMod k Ω l r (g : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • (ρZ g⁻¹).dualMap
      map_one' := by
        refine LinearMap.ext fun φ => LinearMap.ext fun m => ?_
        show ((cycMod k Ω l r ((1 : Dec (F := k) A) : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
          φ (ρZ 1⁻¹ m) = φ m
        simp
      map_mul' := by
        intro g h
        refine LinearMap.ext fun φ => LinearMap.ext fun m => ?_
        show ((cycMod k Ω l r ((g * h : Dec (F := k) A) : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
            φ (ρZ (g * h)⁻¹ m) =
          ((cycMod k Ω l r (g : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
            (((cycMod k Ω l r (h : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * φ (ρZ h⁻¹ (ρZ g⁻¹ m)))
        rw [mul_inv_rev, map_mul, Module.End.mul_apply, Subgroup.coe_mul, map_mul, Units.val_mul, mul_assoc] }
  have hτ : ∀ (g : Dec (F := k) A) (φ : TDual (ZMod (l ^ r)) M) (m : M),
      τ g φ m = ((cycMod k Ω l r (g : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * φ (ρZ g⁻¹ m) :=
    fun g φ m => rfl
  have hEq := (hEul k Ω l r M A ρZ v hr hA hcZ).2 hl
  obtain ⟨hH1f, -, hH2⟩ := So.locCard hFin hTate k Ω l r hr v A hA M ρZ hcZ τ hτ
  have hB1 : Nat.card (H0 ρZ) ≤ Nat.card (O ⧸ Ideal.span {d₁}) := by
    have hmem : ∀ x : H0 ρZ, d₁ • (x : M) = 0 := by
      intro x
      have hx := (Representation.mem_invariants ρZ (x : M)).mp x.2 ⟨g₁, hg₁D⟩
      rw [hρZapp, hρ.act] at hx
      rw [hd₁, sub_smul, one_smul, sub_eq_zero]
      exact hx
    refine le_trans ?_ (hMt d₁ hd₁0)
    refine Nat.card_le_card_of_injective (fun x => ⟨(x : M), hmem x⟩) ?_
    intro x y h
    exact Subtype.ext (congrArg (fun z : {m : M // d₁ • m = 0} => (z : M)) h)
  have hB2 : Nat.card (H0 τ) ≤ Nat.card (TDual (ZMod (l ^ r₀)) (O ⧸ Ideal.span {d₂})) := by
    obtain ⟨ι, hιinj, -, hιact⟩ := So.dualEmb l O a hρ.ne r M hρ.cyc
    have hu : (algebraMap ℤ_[l] O) ((cycZ k Ω l g₂ : ℤ_[l]ˣ) : ℤ_[l]) *
        (((ψ * chiO k Ω l O ^ n) g₂⁻¹ : Oˣ) : O) =
        (((ψ⁻¹ * chiO k Ω l O ^ (1 - n)) g₂ : Oˣ) : O) := by
      have hc : (algebraMap ℤ_[l] O) ((cycZ k Ω l g₂ : ℤ_[l]ˣ) : ℤ_[l]) =
          ((chiO k Ω l O g₂ : Oˣ) : O) := rfl
      rw [hc, ← Units.val_mul]
      congr 1
      simp only [map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply, zpow_sub,
        zpow_one, mul_inv, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hmem : ∀ φ : H0 τ, ι (φ : TDual (ZMod (l ^ r)) M) ∈ Set.range ι₀ := by
      intro φ
      rw [← hι₀rng]
      have hinv := (Representation.mem_invariants τ (φ : TDual (ZMod (l ^ r)) M)).mp φ.2 ⟨g₂, hg₂D⟩
      have key := hιact ((cycZ k Ω l g₂ : ℤ_[l]ˣ) : ℤ_[l]) (((ψ * chiO k Ω l O ^ n) g₂⁻¹ : Oˣ) : O)
        (φ : TDual (ZMod (l ^ r)) M) (τ ⟨g₂, hg₂D⟩ φ) (fun m => by
          rw [hτ, hρZapp, hρ.act]
          rfl)
      rw [hinv, hu] at key
      rw [hd₂, sub_smul, one_smul, ← key, sub_self]
    refine Nat.card_le_card_of_injective (fun φ => Classical.choose (hmem φ)) ?_
    intro φ₁ φ₂ h
    have h1 := Classical.choose_spec (hmem φ₁)
    have h2 := Classical.choose_spec (hmem φ₂)
    apply Subtype.ext
    apply hιinj
    rw [← h1, ← h2]
    exact congrArg ι₀ h
  obtain ⟨-, ⟨e1⟩, -⟩ := So.scal O (ZMod (l ^ r)) (Dec (F := k) A) M ρ ρZ (fun g m => rfl)
  haveI := hH1f
  refine ⟨Finite.of_equiv _ e1.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e1.toEquiv, hEq, hH2]
  exact Nat.mul_le_mul hB1 hB2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem ps_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (i : Fin 4) (g : G ℚ Ω) : D.ps i g = D.al g ^ lamW i * D.Psi g ^ muW i := by
  fin_cases i <;> simp [Raw.ps, Raw.th, lamW, muW]

private theorem rbar_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (g : G ℚ Ω) : D.rbar g = Matrix.diagonal fun i => residue c.O (D.ps i g : c.O) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Raw.rbar, Raw.r0, mapRep, diagRep]
  · simp [Raw.rbar, Raw.r0, mapRep, diagRep, Matrix.diagonal_apply, h]

theorem UpperTheory.V.X.spAct :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (rb : D.Gam →* M4 (ResidueField c.O)), rb.comp (toGS Ω D.SP) = D.rbar → ∀ (h : (form c.O).Normalises rb) (j : ℤ × ℤ) (g : G ℚ Ω) (Y : (form c.O).gw (ResidueField c.O) j), Alg.FormData.adRep h j (toGS Ω D.SP g) Y = Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) g • Y := by
  intro Ω _ _ _ l _ c D rb hrb h j g Y
  apply Subtype.ext
  show rb (toGS Ω D.SP g) * (Y : Matrix (Fin 4) (Fin 4) (ResidueField c.O)) * rb (toGS Ω D.SP g)⁻¹ = _
  rw [← map_inv, ← MonoidHom.comp_apply rb, ← MonoidHom.comp_apply rb, hrb, rbar_eq, rbar_eq]
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Submodule.coe_smul, Matrix.smul_apply, smul_eq_mul]
  by_cases hab : w4 a - w4 b = j
  · have key : D.ps a g * D.ps b g⁻¹ = (D.al ^ j.1 * D.Psi ^ j.2) g := by
      subst hab
      rw [map_inv, ps_eq, ps_eq, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.zpow_apply]
      simp only [w4, Prod.fst_sub, Prod.snd_sub, zpow_sub, div_eq_mul_inv, mul_inv]
      ac_rfl
    rw [Raw.bar, ← key, Units.val_mul, map_mul]
    ring
  · have hz : (Y : Matrix (Fin 4) (Fin 4) (ResidueField c.O)) a b = 0 := (Submodule.mem_inf.1 Y.2).2 a b hab
    simp [hz]
end
