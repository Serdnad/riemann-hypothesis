module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.IndexNormal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Pointwise

private theorem cyc_ine (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  show cyclotomicCharacter Ω l σ.toRingEquiv = 1
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one
  have hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, not_lt]
    exact one_le_pow₀ (not_lt.1 hA)
  have h1 : Chr.cls ℚ Ω (l ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ
  have h2 := Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one
  rw [h1] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hspec.symm.trans h2)
  rw [ZMod.val_injective _ h3]
  simp

private theorem ine_iff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F]
    (A : ValuationSubring Ω) (g : G F Ω) : g ∈ Ine (F := F) A ↔ resQ F g ∈ Ine (F := ℚ) A := Iff.rfl

private theorem mix_one {k : Type} [Field k] (h : (2 : k) ≠ 0) (γ : kˣ) : mix γ 1 1 = (1 : M4 k) := by
  have e : (2 : k)⁻¹ * (1 + 1) = 1 := by rw [one_add_one_eq_two, inv_mul_cancel₀ h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mix, e]

private theorem diag_one {Γ k : Type} [Group Γ] [Field k] {r : Γ →* GL (Fin 2) k} {H : Subgroup Γ} {x : Γ →* kˣ}
    (h : IsDiagOn r H ![1, x]) {s : Γ} (hs : s ∈ H) (hx : x s = 1) : r s = 1 := by
  obtain ⟨g, hg⟩ := h
  have h1 : g * r s * g⁻¹ = 1 := by
    apply Units.ext
    rw [hg s hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hx]
  simpa [mul_inv_eq_one] using h1

private theorem sqrt_one {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : (Qbar l)ˣ} (h : d ^ 2 = 1) (hc : Cong d 1) : d = 1 := by
  have h1 : (d : Qbar l) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  rcases sq_eq_one_iff.1 h1 with h2 | h2
  · exact Units.ext h2
  · exfalso
    have h3 : ‖(2 : Qbar l)‖ < 1 := by
      have h4 : ‖(d : Qbar l) - 1‖ < 1 := hc
      rw [h2, show (-1 - 1 : Qbar l) = -2 by ring, norm_neg] at h4
      exact h4
    have h5 : ‖((2 : ℕ) : ℚ_[l])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hl
    have h6 : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by rw [map_natCast, Nat.cast_ofNat]
    rw [h6, norm_algebraMap', h5] at h3
    exact lt_irrefl _ h3

theorem UpperTheory.induced_representation_constituent_vanishing :
    UpperTheory.V.Sd.S2.IndKill := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H g hg
  obtain ⟨A, hA, hgI, hrb⟩ := hg
  have hAl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
  have hsI : resQ T.F g ∈ Ine (F := ℚ) A := (ine_iff _ _ _).1 hgI
  have hψ : D.ψ (resQ T.F g) = 1 :=
    H.hyp.ok.kb A (fun p hp => by rw [Finset.mem_singleton.1 hp]; exact hAl) g hgI hrb
  have hk : resQ T.F g ∈ k₀.fixingSubgroup := (H.hyp.ps g).1 (H.hyp.two.unr A g hgI)
  have hδ2 := H.δ_sq g
  have hδ1 := H.δ_one g
  show (tw (R.comp (resQ T.F)) δ g).val = 1
  rw [tw_val, MonoidHom.comp_apply]
  generalize resQ T.F g = s at *
  have hz : cycZ ℚ Ω l s = 1 := cyc_ine Ω l A hAl hsI
  have hbar : cycBar ℚ Ω l s = 1 := by simp [cycBar, hz]
  have hchi : chiO ℚ Ω l c.O s = 1 := by simp [chiO, hz]
  have hom : D.om s = 1 := (H.chars.om s).2 (by rw [hbar]; simp [Cong])
  have hal : D.al s = D.ξ s := by simp [Raw.al, hchi, hom]
  have hξ : D.ξ s = 1 := by
    refine H.chars.xi s ?_
    have h1 : residue c.O (D.ξ s : c.O) = 1 := by
      have h2 := congrFun (congrFun hrb 2) 2
      rw [← hal]
      simpa [Raw.rbar, Raw.r0, mapRep, GradeZeroInterpolatingElement.diagRep, Raw.ps] using h2
    have h3 : (D.ξ s : c.O) - 1 ∈ maximalIdeal c.O := by
      rw [← residue_eq_zero_iff, map_sub, h1, map_one, sub_self]
    have h4 := (UpperTheory.V.Fr.sc_norm l c _).2.1 h3
    rw [Subalgebra.coe_sub, Subalgebra.coe_one] at h4
    unfold Cong
    rw [Units.val_one]
    exact h4
  have hth : D.th s = 1 := by simp [Raw.th, Raw.Psi, Chr.Psi, hal, hξ, hchi, hψ]
  have hup : up D.ξ s = 1 := by simp [up, hξ]
  have hδ : δ g = 1 := by
    refine sqrt_one H.hyp.good.l_odd ?_ hδ1
    simpa [hbar, hup, H.hyp.φ_in s hk, up, hth, hξ] using hδ2
  obtain ⟨h, rfl⟩ : s ∈ (resQ k₀).range := ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => hk ⟨x.1, x.2⟩, rfl⟩
  have hN : (resQ k₀).range.Normal := Subgroup.normal_of_index_eq_two H.mix.index
  set t₀ := resQ T.F T.g0 with ht₀
  obtain ⟨h', hh'⟩ : t₀⁻¹ * resQ k₀ h * t₀ ∈ (resQ k₀).range := hN.conj_mem' _ ⟨h, rfl⟩ t₀
  have r1 : r h = 1 := diag_one (H.dat.away A hAl) ((ine_iff _ _ _).2 hsI) hup
  obtain ⟨c1, c2, -⟩ := UpperTheory.V.Two.ineConj ℚ Ω t₀
  have hAA : t₀ • (t₀⁻¹ • A) = A := smul_inv_smul _ _
  have r2 : r h' = 1 := by
    refine diag_one (H.dat.away (t₀⁻¹ • A) fun h0 => hAl ?_) ((ine_iff _ _ _).2 ?_) ?_
    · rw [← hAA]; exact (c2 _ l).2 h0
    · rw [hh']; exact c1 _ _ (hAA.symm ▸ hsI)
    · rw [MonoidHom.comp_apply, hh', map_mul, map_mul, hup, mul_one, ← map_mul, inv_mul_cancel, map_one]
  rw [H.mix.on h h' hh', r1, r2, hδ, Units.val_one, Units.val_one, one_smul]
  exact mix_one H.mix.two _
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Pointwise

private theorem two_primes {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    {w w' : HeightOneSpectrum (𝓞 K)} (hne : w ≠ w') (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) (hw' : ((p : ℕ) : 𝓞 K) ∈ w'.asIdeal) :
    Ideal.absNorm w.asIdeal = p ∧ Ideal.span {((p : ℕ) : 𝓞 K)} = w.asIdeal * w'.asIdeal := by
  have hco : IsCoprime w.asIdeal w'.asIdeal := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact w.isMaximal.coprime_of_ne w'.isMaximal fun h => hne (HeightOneSpectrum.ext h)
  have hd : w.asIdeal * w'.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 K)} :=
    hco.mul_dvd (Ideal.dvd_span_singleton.2 hw) (Ideal.dvd_span_singleton.2 hw')
  obtain ⟨J, hJ⟩ := hd
  have hn : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
  have e := congrArg Ideal.absNorm hJ
  rw [hn, map_mul, map_mul] at e
  have a1 := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have a2 := NumberField.HeightOneSpectrum.one_lt_absNorm w'
  generalize Ideal.absNorm w.asIdeal = a at *
  generalize Ideal.absNorm w'.asIdeal = b at *
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (show a ∣ p ^ 2 from ⟨b * Ideal.absNorm J, by rw [e, mul_assoc]⟩)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (show b ∣ p ^ 2 from ⟨p ^ i * Ideal.absNorm J, by rw [e]; ring⟩)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (show Ideal.absNorm J ∣ p ^ 2 from ⟨p ^ i * p ^ j, by rw [e]; ring⟩)
  rw [hk, ← pow_add, ← pow_add] at e
  have e2 := Nat.pow_right_injective hp.two_le e
  have i0 : i ≠ 0 := by rintro rfl; simp at a1
  have j0 : j ≠ 0 := by rintro rfl; simp at a2
  have i1 : i = 1 := by omega
  have k0 : k = 0 := by omega
  rw [k0, pow_zero, Ideal.absNorm_eq_one_iff] at hk
  refine ⟨by rw [i1, pow_one], ?_⟩
  rw [hJ, hk, Ideal.mul_top]

private theorem only_two {K : Type} [Field K] [NumberField K] {I : Ideal (𝓞 K)}
    {w w' u : HeightOneSpectrum (𝓞 K)} (h : I = w.asIdeal * w'.asIdeal) (hu : I ≤ u.asIdeal) : u = w ∨ u = w' := by
  rw [h] at hu
  rcases u.isPrime.mul_le.1 hu with h1 | h1
  · exact Or.inl (HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h1).symm)
  · exact Or.inr (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le u.isPrime.ne_top h1).symm)

theorem UpperTheory.quadratic_field_split_prime_two_places :
    UpperTheory.V.Sd.S2.QuadSplit := by
  intro Ω _ _ _ k₀ _ h2 p hp hs
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure k₀ Ω := ⟨inferInstance, inferInstance⟩
  have key : ∀ A A' : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ g : G ℚ Ω, g ∉ k₀.fixingSubgroup →
      (∀ y, g y ∈ A ↔ y ∈ A') → ∃ w w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal ∧
        IsPlaceOver A w ∧ IsPlaceOver A' w' := by
    intro A A' hA g hg hAA
    have hA' : A'.valuation (p : Ω) < 1 := by
      rw [valuation_lt_one_iff'] at hA ⊢
      rw [← hAA, ← hAA, map_inv₀, map_natCast]
      exact hA
    obtain ⟨a1, a2, a3, -⟩ := places k₀ Ω p A
    obtain ⟨b1, b2, b3, -⟩ := places k₀ Ω p A'
    obtain ⟨v, hv⟩ := a1 fun h => (a2 h).2 hA
    obtain ⟨u, hu⟩ := b1 fun h => (b2 h).2 hA'
    refine ⟨v, u, ?_, (a3 v hv).1 hA, (b3 u hu).1 hA', hv, hu⟩
    rintro rfl
    obtain ⟨h, hh⟩ := exists_smul_eq_of_isPlaceOver hv hu
    have hm : g * galEmb ℚ k₀ Ω h ∈ Dec (F := ℚ) A := by
      have e : g • A' = A := by
        ext y
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hAA]
        exact iff_of_eq (congrArg (· ∈ A) (g.apply_symm_apply y))
      show (g * galEmb ℚ k₀ Ω h) • A = A
      rw [mul_smul, show galEmb ℚ k₀ Ω h • A = A' from hh, e]
    have hk : galEmb ℚ k₀ Ω h ∈ k₀.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => h.commutes ⟨x, hx⟩
    exact hg ((Subgroup.mul_mem_cancel_right _ hk).1 (hs A hA hm))
  obtain ⟨g, hg⟩ : ∃ g : G ℚ Ω, g ∉ k₀.fixingSubgroup := by
    by_contra hc
    push Not at hc
    haveI : IsGalois ℚ Ω := {}
    have e : k₀ = ⊥ := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup k₀, (Subgroup.eq_top_iff' _).2 hc, InfiniteGalois.fixedField_bot]
    rw [IntermediateField.finrank_eq_one_iff.2 e] at h2
    omega
  have other : ∀ w : Pl k₀, ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal → ∃ w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal := by
    intro w hw
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨v, u, hne, hv, hu, h1, -⟩ := key A (A.comap g.toRingEquiv.toRingHom)
      (((places k₀ Ω p A).2.2.1 w hA).2 hw) g hg fun _ => Iff.rfl
    have e : v = w := HeightOneSpectrum.ext (Ideal.ext fun x => (h1 x).symm.trans (hA x))
    exact ⟨u, e ▸ hne, hu⟩
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨w', hne, hw'⟩ := other w hw
    obtain ⟨h1, h3⟩ := two_primes h2 hp hne hw hw'
    refine ⟨h1, fun h => hne ?_⟩
    rw [← Ideal.dvd_span_singleton, h3, sq, mul_dvd_mul_iff_left w.ne_bot, Ideal.dvd_iff_le] at h
    exact HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top h).symm
  · obtain ⟨w, hw⟩ : ∃ w : Pl k₀, ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal := by
      have hn : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 k₀)}) = p ^ 2 := by
        rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
      have ht : Ideal.span {((p : ℕ) : 𝓞 k₀)} ≠ ⊤ := fun h => by
        rw [Ideal.absNorm_eq_one_iff.2 h] at hn
        exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne hn
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ ht
      have hpM := (Ideal.span_singleton_le_iff_mem _).1 hle
      refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hpM⟩
      rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hpM
      exact hp.ne_zero hpM
    obtain ⟨w', hne, hw'⟩ := other w hw
    obtain ⟨-, h3⟩ := two_primes h2 hp hne hw hw'
    refine ⟨w, w', hne, hw, hw', fun A A' hA g hg hAA => ?_⟩
    obtain ⟨v, u, hvu, hv, hu, h1, h4⟩ := key A A' hA g hg hAA
    rcases only_two h3 ((Ideal.span_singleton_le_iff_mem _).2 hv) with rfl | rfl <;>
      rcases only_two h3 ((Ideal.span_singleton_le_iff_mem _).2 hu) with rfl | rfl
    exacts [absurd rfl hvu, Or.inl ⟨h1, h4⟩, Or.inr ⟨h1, h4⟩, absurd rfl hvu]
end
