module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle002
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle057
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.StatementLoc
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.dirVal :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (g : G ℚ Ω), ∃ a : ℤ, IsCoprime a M ∧ ∀ (N : ℕ) [NeZero N], N ∣ M → ∀ (O : Type) [CommRing O] (χ : DirichletCharacter O N), (Chr.dirG ℚ Ω χ g : O) = χ a := by
  intro Ω _ _ _ M _ g
  refine ⟨(((Chr.cls ℚ Ω M g : (ZMod M)ˣ) : ZMod M).val : ℕ), ?_, fun N _ h O _ χ => ?_⟩
  · exact Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime _)
  · have h1 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω M).2.1 N h) g
    have h2 : ((Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N) = ((((Chr.cls ℚ Ω M g : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod N) := by
      rw [← h1, MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.natCast_val]
    rw [Int.cast_natCast, ← h2]
    exact MulChar.coe_toUnitHom χ _
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.decZhat :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ), p.Prime → ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∃ φ : Dec (F := ℚ) A, ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧ ∀ n : ℕ, 0 < n → ∃ d : Dec (F := ℚ) A →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ (Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A), d s = 1) ∧ d φ = Multiplicative.ofAdd 1 := by
  intro Ω _ _ _ p hp A hA
  have : Fact p.Prime := ⟨hp⟩
  have hP := UpperTheory.V.Base.places ℚ Ω p A
  obtain ⟨v, hv⟩ := hP.1 fun h => (hP.2.1 h).2 hA
  obtain ⟨φ, -, hClosure, hFiniteQuotients⟩ := UpperTheory.V.GC.decZhat ℚ Ω v A hv
  exact ⟨φ, hClosure, hFiniteQuotients⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.dualEmb :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module O M] [Module (ZMod (l ^ r)) M], Nonempty (M ≃ₗ[O] (O ⧸ Ideal.span {a})) → ∃ ι : ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M →+ QO l O, Function.Injective ι ∧ (∀ w, a • w = 0 ↔ w ∈ Set.range ι) ∧ ∀ (y : ℤ_[l]) (x : O) (φ φ' : ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M), (∀ m, φ' m = PadicInt.toZModPow r y * φ (x • m)) → ι φ' = (algebraMap ℤ_[l] O y * x) • ι φ := by
  intro l _ O _ _ _ _ _ a ha r M _ _ _ hM
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨φ₀, hker, hsurj⟩ := UpperTheory.V.X.So.dualGen l O a ha r M hM
  obtain ⟨w, hw⟩ := (UpperTheory.V.ML.qoCyc l O).2.1 a ha
  choose c hc using hsurj
  have key : ∀ x x' : O, (∀ m : M, φ₀ (x • m) = φ₀ (x' • m)) → x • w = x' • w := by
    intro x x' h
    have hd : a ∣ x - x' := (hker _).1 (fun m => by rw [sub_smul, map_sub, h, sub_self])
    have h0 := (hw (x - x')).2 hd
    rwa [sub_smul, sub_eq_zero] at h0
  have kill : ∀ (s : O) (n : M), ((l : O) ^ r * s) • n = 0 := by
    intro s n
    rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)),
      ZMod.natCast_self, zero_smul]
  have scal : ∀ (y : ℤ_[l]) (n : M),
      φ₀ (algebraMap ℤ_[l] O y • n) = PadicInt.toZModPow r y * φ₀ n := by
    intro y n
    have hmem : y - ((PadicInt.toZModPow r y).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    obtain ⟨t, ht⟩ := hmem
    have hy : y = ((PadicInt.toZModPow r y).val : ℤ_[l]) + (l : ℤ_[l]) ^ r * t := by
      rw [← ht]; ring
    conv_lhs => rw [hy]
    rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_smul, kill, add_zero,
      Nat.cast_smul_eq_nsmul O, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  refine ⟨{ toFun := fun φ => c φ • w, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
  · show c 0 • w = 0
    rw [← zero_smul O w]
    apply key
    intro m
    rw [← hc, zero_smul, map_zero]
    rfl
  · intro φ ψ
    show c (φ + ψ) • w = c φ • w + c ψ • w
    rw [← add_smul]
    apply key
    intro m
    have e1 := hc (φ + ψ) m
    have e2 := hc φ m
    have e3 := hc ψ m
    rw [add_smul, map_add (f := _), ← e1, ← e2, ← e3]
    exact TDual.add_apply φ ψ m
  · rw [injective_iff_map_eq_zero]
    intro φ hφ
    change c φ • w = 0 at hφ
    have hd := (hw _).1 hφ
    apply LinearMap.ext
    intro m
    rw [hc φ m, (hker _).2 hd m]
    rfl
  · intro v
    constructor
    · intro hv
      obtain ⟨y, rfl⟩ := (UpperTheory.V.ML.qoCyc l O).2.2.1 a w ha hw v hv
      refine ⟨(φ₀.toAddMonoidHom.comp (DistribSMul.toAddMonoidHom M y)).toZModLinearMap (l ^ r), ?_⟩
      show c _ • w = y • w
      apply key
      intro m
      rw [← hc]
      rfl
    · rintro ⟨φ, rfl⟩
      show a • (c φ • w) = 0
      rw [smul_smul]
      exact (hw _).2 (dvd_mul_right a _)
  · intro y x φ φ' h
    show c φ' • w = (algebraMap ℤ_[l] O y * x) • (c φ • w)
    rw [smul_smul]
    apply key
    intro m
    have e1 := hc φ' m
    have e2 := hc φ (x • m)
    rw [← e1]
    refine (h m).trans ((congrArg (fun z => PadicInt.toZModPow r y * z) e2).trans ?_)
    rw [smul_smul,
      show algebraMap ℤ_[l] O y * x * c φ = algebraMap ℤ_[l] O y * (c φ * x) by ring,
      mul_smul (algebraMap ℤ_[l] O y), scal]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.omDir :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ ω : DirichletCharacter c.O l, ω ^ (l - 1) = 1 ∧ IsOmT c (Chr.dirG ℚ Ω ω) := by
  intro Ω _ _ _ l hl c
  obtain ⟨⟨w, hw, -⟩, h⟩ := omT Ω l c
  have hk := (h w hw).2.1
  have hs : Function.Surjective (Chr.cls ℚ Ω l) := (Chr.clsOnto Ω l).1
  let f : (ZMod l)ˣ →* c.Oˣ := (Chr.cls ℚ Ω l).liftOfSurjective hs ⟨w, hk.ge⟩
  have hf : f.comp (Chr.cls ℚ Ω l) = w := MonoidHom.ext fun σ => MonoidHom.liftOfRightInverse_comp_apply _ _
    (Function.rightInverse_surjInv hs) ⟨w, hk.ge⟩ σ
  refine ⟨MulChar.ofUnitHom f, ?_, ?_⟩
  · rw [← ZMod.card_units l]
    exact MulChar.pow_card_eq_one _
  · have e : Chr.dirG ℚ Ω (MulChar.ofUnitHom f : DirichletCharacter c.O l) = w := by
      rw [← hf, Chr.dirG]
      simp
    rw [e]
    exact hw
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

namespace UpperTheory.V.X.GaloisIndexPlaces

private theorem prime_p {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact h

private noncomputable def vQ (l : ℕ) (hl : l.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_p hl).ne_zero).mpr (prime_p hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_p hl).ne_zero

private theorem mem_vQ (l : ℕ) (hl : l.Prime) : ((l : ℕ) : 𝓞 ℚ) ∈ (vQ l hl).asIdeal :=
  Ideal.mem_span_singleton_self _

private theorem eq_vQ (l : ℕ) (hl : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (h : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    vQ l hl = v := by
  apply HeightOneSpectrum.ext
  have hle : (vQ l hl).asIdeal ≤ v.asIdeal := by
    show Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h
  exact (vQ l hl).isMaximal.eq_of_le v.isPrime.ne_top hle

private theorem vQ_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : vQ p hp = vQ q hq) : p = q := by
  have h1 : ((p : ℕ) : 𝓞 ℚ) ∈ (vQ q hq).asIdeal := h ▸ mem_vQ p hp
  have h2 : ((q : ℕ) : 𝓞 ℚ) ∣ ((p : ℕ) : 𝓞 ℚ) := Ideal.mem_span_singleton.1 h1
  have h3 := map_dvd Rat.ringOfIntegersEquiv h2
  simp only [map_natCast] at h3
  exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 h3)).symm

private theorem isPlaceOver_vQ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) (hl : l.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l hl) := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨hne, htop, hab, -⟩ := UpperTheory.V.Base.places ℚ Ω l A
  have hAT : A ≠ ⊤ := by
    intro hT
    exact (htop hT).2 hA
  obtain ⟨v, hv⟩ := hne hAT
  have hlv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (hab v hv).mp hA
  rw [eq_vQ l hl v hlv]
  exact hv

end UpperTheory.V.X.GaloisIndexPlaces

open UpperTheory.V.X.GaloisIndexPlaces in
theorem UpperTheory.V.X.galIdx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (e : T ⊕ Q ≃ S), SP = S ∧ (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) ∧ (∀ v : T, IsPlaceOver (pl v) (e (.inl v)).1) ∧ ∀ q : Q, IsPlaceOver (pl q) (e (.inr q)).1 := by
  classical
  intro Ω _ _ _ l SP T Q v0 pl K hD
  have hex : ∃ f : ℕ → HeightOneSpectrum (𝓞 ℚ), ∀ (p : ℕ) (hp : Nat.Prime p), f p = vQ p hp :=
    ⟨fun p => if hp : Nat.Prime p then vQ p hp else vQ 2 Nat.prime_two, fun p hp => dif_pos hp⟩
  obtain ⟨f, hf⟩ := hex
  have hpr : ∀ p, p ∈ T ∨ p ∈ Q → p.Prime := hD.prime
  have hmemS : ∀ p, p ∈ T ∨ p ∈ Q → f p ∈ (T ∪ Q).image f := by
    intro p hp
    exact Finset.mem_image_of_mem f (Finset.mem_union.mpr hp)
  have hfinj : ∀ p q, (p ∈ T ∨ p ∈ Q) → (q ∈ T ∨ q ∈ Q) → f p = f q → p = q := by
    intro p q hp hq he
    rw [hf p (hpr p hp), hf q (hpr q hq)] at he
    exact vQ_inj _ _ he
  let g : T ⊕ Q → (T ∪ Q).image f := fun x => match x with
    | .inl p => ⟨f p, hmemS p (Or.inl p.2)⟩
    | .inr q => ⟨f q, hmemS q (Or.inr q.2)⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) he <;> simp only [g, Subtype.mk.injEq] at he
      · have := hfinj a b (Or.inl ha) (Or.inl hb) he
        subst this
        rfl
      · have := hfinj a b (Or.inl ha) (Or.inr hb) he
        subst this
        exact absurd hb (Finset.disjoint_left.mp hD.disj ha)
      · have := hfinj a b (Or.inr ha) (Or.inl hb) he
        subst this
        exact absurd ha (Finset.disjoint_left.mp hD.disj hb)
      · have := hfinj a b (Or.inr ha) (Or.inr hb) he
        subst this
        rfl
    · rintro ⟨s, hs⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ⟨.inl ⟨p, hp⟩, rfl⟩
      · exact ⟨.inr ⟨p, hp⟩, rfl⟩
  refine ⟨(T ∪ Q).image f, Equiv.ofBijective g hg, ?_, ?_, ?_, ?_⟩
  · ext v
    rw [hD.mem v, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, hpv⟩
      refine ⟨p, Finset.mem_union.mpr hp, ?_⟩
      rw [hf p (hpr p hp)]
      exact eq_vQ p _ v hpv
    · rintro ⟨p, hp, rfl⟩
      have hp' := Finset.mem_union.mp hp
      refine ⟨p, hp', ?_⟩
      rw [hf p (hpr p hp')]
      exact mem_vQ p _
  · intro v hv
    have hl : l ∈ T ∨ l ∈ Q := Or.inl hD.l_mem
    have : f l = v := by
      rw [hf l (hpr l hl)]
      exact eq_vQ l _ v hv
    rw [← this]
    exact hmemS l hl
  · intro p
    have hp : (p : ℕ) ∈ T ∨ (p : ℕ) ∈ Q := Or.inl p.2
    show IsPlaceOver (pl p) (f p)
    rw [hf p (hpr p hp)]
    exact isPlaceOver_vQ p _ (pl p) (hD.isOver p hp)
  · intro q
    have hq : (q : ℕ) ∈ T ∨ (q : ℕ) ∈ Q := Or.inr q.2
    show IsPlaceOver (pl q) (f q)
    rw [hf q (hpr q hq)]
    exact isPlaceOver_vQ q _ (pl q) (hD.isOver q hq)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem not_dvd_index_ker {H k ι : Type} [Group H] [Field k] [Finite k] [Fintype ι] {l : ℕ} [hl : Fact l.Prime]
    (h0 : (l : k) = 0) (φ : H →* (ι → kˣ)) : ¬ l ∣ φ.ker.index := by
  classical
  haveI := Fintype.ofFinite k
  intro hd
  rw [Subgroup.index_ker] at hd
  have h1 : Nat.card φ.range ∣ Nat.card (ι → kˣ) := Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (ι → kˣ) = (Fintype.card k - 1) ^ Fintype.card ι := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_units]
  have hc : ringChar k = l := by
    rcases (Nat.dvd_prime hl.out).1 (ringChar.dvd h0) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  haveI : CharP k l := by
    rw [← hc]
    exact ringChar.charP k
  obtain ⟨n, -, hn⟩ := FiniteField.card k l
  have hq : l ∣ Fintype.card k := by
    rw [hn]
    exact dvd_pow_self _ (PNat.ne_zero n)
  have hpos : 0 < Fintype.card k := Fintype.card_pos
  have h3 : l ∣ Fintype.card k - 1 := hl.out.dvd_of_dvd_pow (h2 ▸ dvd_trans hd h1)
  have h6 : Fintype.card k - 1 + 1 = Fintype.card k := by omega
  rw [← h6] at hq
  have h4 : l ∣ 1 := (Nat.dvd_add_right h3).1 hq
  exact hl.out.one_lt.ne' (Nat.dvd_one.1 h4)

theorem UpperTheory.V.X.spKer :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.rbar.ker.Normal ∧ ¬ l ∣ D.rbar.ker.index ∧ ∀ (j : ℤ × ℤ), ∀ g ∈ D.rbar.ker, Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) g = 1 := by
  intro Ω _ _ _ l _ c D
  classical
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, hfin, hl, -⟩ := abelian₂.dvr_finite l c.O
  have key : ∀ g, D.rbar g = 1 ↔ ∀ i, residue c.O ↑(D.ps i g) = 1 := by
    intro g
    have e : D.rbar g = Matrix.diagonal fun i => residue c.O ↑(D.ps i g) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [Raw.rbar, Raw.r0, mapRep, diagRep]
      · simp [Raw.rbar, Raw.r0, mapRep, diagRep, Matrix.diagonal_apply, h]
    rw [e, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
  let φ : G ℚ Ω →* (Fin 4 → (ResidueField c.O)ˣ) :=
    Pi.monoidHom fun i => (Units.map (residue c.O : c.O →* ResidueField c.O)).comp (D.ps i)
  have hφ : ∀ g, φ g = 1 ↔ ∀ i, residue c.O ↑(D.ps i g) = 1 := by
    intro g
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    rw [Pi.one_apply, Units.ext_iff]
    exact Iff.rfl
  have hker : D.rbar.ker = φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, key, hφ]
  have h0 : ((l : ℕ) : ResidueField c.O) = 0 := by
    have h := (IsLocalRing.residue_eq_zero_iff _).2 hl
    simpa using h
  refine ⟨by rw [hker]; infer_instance, by rw [hker]; exact not_dvd_index_ker h0 φ, ?_⟩
  intro j g hg
  have hk := (key g).1 hg
  have a1 : Units.map (residue c.O : c.O →* ResidueField c.O) (D.Psi g) = 1 := by
    ext
    simpa [Raw.ps] using hk 1
  have a2 : Units.map (residue c.O : c.O →* ResidueField c.O) (D.al g) = 1 := by
    ext
    simpa [Raw.ps] using hk 2
  have hu : Units.map (residue c.O : c.O →* ResidueField c.O) ((D.al ^ j.1 * D.Psi ^ j.2) g) = 1 := by
    simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow, a1, a2, one_zpow, mul_one]
  exact congrArg Units.val hu
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

theorem UpperTheory.V.X.hQuad :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ), l.Prime → 5 ≤ l → Module.finrank ℚ K = 2 → discr K = l → classNumber K < l := by
  intro K _ _ l hl h5 hn hd
  have h := GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have habs : |((discr K : ℤ) : ℝ)| = (l : ℝ) := by
    rw [hd]
    push_cast
    exact abs_of_pos hl0
  rw [hn, habs, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  have hx0 : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hl0
  have h5r : (5 : ℝ) ≤ l := by exact_mod_cast h5
  have hx1 : Real.sqrt (l : ℝ) ≠ 1 := by
    intro h1
    have hs := Real.sq_sqrt hl0.le
    rw [h1] at hs
    linarith
  have hlog := Real.log_lt_sub_one_of_pos hx0 hx1
  have hsq : Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) = l := Real.mul_self_sqrt hl0.le
  have hlt : (classNumber K : ℝ) < l := by
    calc (classNumber K : ℝ) ≤ Real.sqrt (l : ℝ) * (1 + Real.log (Real.sqrt (l : ℝ))) := h
      _ < Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) := by
        apply mul_lt_mul_of_pos_left _ hx0
        linarith
      _ = l := hsq
  exact_mod_cast hlt
end
