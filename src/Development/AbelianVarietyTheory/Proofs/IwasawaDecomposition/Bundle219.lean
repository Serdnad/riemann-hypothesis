module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosed
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle001
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedResEta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle207
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsOfThetaDatumInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepParametersPartitionExtendedByZeros
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem hspace_gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) :
    W.gram.det ≠ 0 := by
  apply GlobalTheory.RecDict.det_gram_ne_zero <;> assumption

theorem cmData_isCMExt_and_gram_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), IsCMExt F E cm.sig ∧ ∀ W : HSpace E, IsHermND cm.sig W.gram := by
  intro F E _ _ _ _ _ _ cm
  refine ⟨⟨cm.totReal, cm.cmUnram.1, cm.deg2, fun τ x => cm.cmUnram.2.1 τ x⟩, fun W => ⟨fun i j => ?_, hspace_gram_det_ne_zero W⟩⟩
  exact W.herm.eq (W.frame j) (W.frame i)

end GlobalTheory.Mem.Vol
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j] (T : TopologicalSpace.Closeds X), ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → j (genericPoint Y) ∉ T → ∃ D : CartierDiv Y, D.Eff ∧ (∀ y, y ∈ D.supp ↔ j y ∈ T) ∧ ∀ (y : Y) (g : Y.functionFieldˣ), D.IsEqn y g → ∀ (f : Y.functionField) (n : ℕ), RegAt y f → RegAt y (f ^ n / g) → RegAt y (f / g) := by
  first | exact @GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv | exact GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv | (intros; apply GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.DeltaZero

theorem exists_char_of_dvd {G : Type} [Group G] [IsCyclic G] {m : ℕ} (hm : m ≠ 0) (h : m ∣ Nat.card G) :
    ∃ θ : G →* ℂˣ, ∀ n : ℕ, θ ^ n = 1 ↔ m ∣ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hζ := Complex.isPrimitiveRoot_exp m hm
  have hζ' := hζ.isUnit_unit hm
  set ζ : ℂˣ := (hζ.isUnit hm).unit
  have ho : orderOf ζ ∣ orderOf g := by
    rw [← hζ'.eq_orderOf, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact h
  refine ⟨monoidHomOfForallMemZpowers hg ho, fun n => ?_⟩
  rw [MonoidHom.eq_iff_eq_on_generator hg, MonoidHom.pow_apply, monoidHomOfForallMemZpowers_apply_gen,
    MonoidHom.one_apply]
  exact hζ'.pow_eq_one_iff_dvd n

theorem exists_place_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ Q : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ Q.asIdeal := by
  have hne : Ideal.span {((p : ℕ) : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 : IsUnit (algebraMap ℤ (𝓞 K) (p : ℤ)) := by simpa using hu
    have h2 : IsUnit (p : ℤ) := isUnit_of_map_unit _ _ h1
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((p : ℕ) : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))

private theorem exists_residue_read {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (ω : (ZMod p)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, (∀ (a : ℕ) (ha : a.Coprime p) (b : (𝓞 L ⧸ w.asIdeal)ˣ),
        (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) → θ b = ω (ZMod.unitOfCoprime a ha)) ∧
      ∀ n : ℕ, θ ^ n = 1 ↔ ω ^ n = 1 := by
  have hc : Nat.card (𝓞 L ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  let _ : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  let ρ : ZMod p ≃+* (𝓞 L ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])
  refine ⟨ω.comp (Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p)), fun a ha b hb => ?_, fun n => ?_⟩
  · rw [MonoidHom.comp_apply]
    congr 1
    ext
    simp [hb]
  · constructor
    · intro h
      ext u
      have := congrArg (fun f => f (Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) u)) h
      simp only [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply] at this
      have e : Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p) (Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) u) = u := by
        ext; simp
      rw [e] at this
      simp [MonoidHom.pow_apply, this]
    · intro h
      refine MonoidHom.ext fun u => ?_
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, h, MonoidHom.one_apply,
        MonoidHom.one_apply]


open Classical in
theorem delta_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → p % 15 = 1 → _root_.GlobalTheory.Mem.Chr.SplitsC H.E p → _root_.Formalism.L2.Host.DeltaExists (H := H) p := by
  intro R H p hp h15 hs
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hsp := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs
  obtain ⟨Q, hQ⟩ := exists_place_over H.K hp
  have : Fact p.Prime := ⟨hp⟩
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  obtain ⟨ω, hω⟩ := exists_char_of_dvd (G := (ZMod p)ˣ) (m := 15) (by norm_num)
    (by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]; omega)
  have hθ : ∀ w : HeightOneSpectrum (𝓞 H.E), ∃ θ : (𝓞 H.E ⧸ w.asIdeal)ˣ →* ℂˣ,
      (_root_.Formalism.L2.Host.OverP H p w → ∀ (a : ℕ) (ha : a.Coprime p) (b : (𝓞 H.E ⧸ w.asIdeal)ˣ),
        (b : 𝓞 H.E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E) → θ b = ω (ZMod.unitOfCoprime a ha)) ∧
      (_root_.Formalism.L2.Host.OverP H p w → ∀ n : ℕ, θ ^ n = 1 ↔ 15 ∣ n) := by
    intro w
    by_cases h : _root_.Formalism.L2.Host.OverP H p w
    · obtain ⟨θ, h1, h2⟩ := exists_residue_read w hp (hsp w h).1 ω
      exact ⟨θ, fun _ => h1, fun _ n => (h2 n).trans (hω n)⟩
    · exact ⟨1, fun h' => absurd h' h, fun h' => absurd h' h⟩
  choose θ hθ1 hθ2 using hθ
  let S : Finset (HeightOneSpectrum (𝓞 H.E)) := _root_.Formalism.L2.Host.aboveF (L := H.E) H.K Q
  have hS : ∀ w, w ∈ S ↔ w.under (𝓞 H.K) = Q := fun w => by
    simp only [S, _root_.Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset]
    rfl
  have hov : ∀ w ∈ S, _root_.Formalism.L2.Host.OverP H p w := fun w hw => by
    have h1 := hQ
    rw [← (hS w).1 hw] at h1
    have h2 : algebraMap (𝓞 H.K) (𝓞 H.E) ((p : ℕ) : 𝓞 H.K) ∈ w.asIdeal := h1
    rwa [map_natCast] at h2
  have hres := UpperTheory.prod_residue_char_norm_one_unit_eq_one H.K H.E p hp Q S hS (fun w hw => ⟨(hsp w (hov w hw)).1, (hsp w (hov w hw)).2.1⟩) ω θ
    (by
      intro w hw a ha
      have hu : IsUnit (Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E)) := by
        obtain ⟨s, t, hst⟩ : IsCoprime ((a : ℕ) : 𝓞 H.E) ((p : ℕ) : 𝓞 H.E) := Nat.Coprime.cast ha
        have h0 : Ideal.Quotient.mk w.asIdeal ((p : ℕ) : 𝓞 H.E) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hov w hw)
        have h1 := congrArg (Ideal.Quotient.mk w.asIdeal) hst
        rw [map_add (f := _), map_mul, map_mul, h0, mul_zero, add_zero, map_one] at h1
        exact IsUnit.of_mul_eq_one_right _ h1
      exact ⟨hu.unit, hu.unit_spec, hθ1 w (hov w hw) a ha _ hu.unit_spec⟩)
  obtain ⟨χ, -, ht, hi, htame, hunr, -, hord⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (_root_.Formalism.L2.Host.embPsi H) hcm (fun _ => 0) S θ
    (by
      intro w hw w' hcj hw'
      rw [hce] at hcj
      exact ((hsp w (hov w hw)).2.2.2 Q hQ w' hcj).2.1 ((hS w).1 hw) ((hS w').1 hw'))
    (by
      intro ζ hζ
      have h1 := hres ζ (H.der.norm_mu _ hζ)
      have h2 : ∏ w ∈ S, ((θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1 := by
        rw [← Units.coe_prod]
        exact congrArg Units.val h1 |>.trans Units.val_one
      rw [h2]
      simp)
  refine ⟨χ, GlobalTheory.T.heckeChar_finiteOrder_of_trivial_at_infinity H.E χ fun k => ?_, ht, htame, fun v hv => hunr v (fun h => hv (hov v h)) ?_,
    fun v hv n => ?_⟩
  · apply Units.ext
    rw [hi k]
    simp
  · intro w hw hcj
    rw [hce] at hcj
    exact hv ((hsp w (hov w hw)).2.2.2 Q hQ v hcj).1
  · by_cases h : v ∈ S
    · exact (hord v h n).1.trans (hθ2 v hv n)
    · obtain ⟨w, hw, -⟩ := existsUnique_conjPl c.toRingEquiv.symm v
      have hcj : ConjPl c.toRingEquiv w v := fun x => by
        have := hw (c.toRingEquiv x)
        rw [RingEquiv.symm_apply_apply] at this
        exact this.symm
      have hwo : _root_.Formalism.L2.Host.OverP H p w := by
        refine ((conjPl_iff_mem _ w v).1 hcj _ _ ?_).2 hv
        simp
      have hwS : w ∈ S := (hS w).2
        (((hsp w hwo).2.2.2 Q hQ v (hce ▸ hcj)).2.2 fun e => h ((hS v).2 e))
      exact ((hord w hwS n).2 v hcj).trans (hθ2 w hwo n)

end GlobalTheory.Mem.DeltaZero
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.exists_heckeChar_trivOn_realSubfield_infinityType : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), _root_.GlobalTheory.Mem.Chr.CMData F c φ → ∀ (e : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ0 : ∀ v : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), (∀ w ∈ S, ∀ w', ConjPl c.toRingEquiv w w' → w' ∉ S) → (∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) → (∏ i, φ i ((ζ : 𝓞 L) : L) ^ (-e i)) * ∏ w ∈ S, ((θ0 w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1) → ∃ χ : _root_.Formalism.L2.Host.HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => -2 * e i) ∧ (∀ v, χ.TameAt v) ∧ (∀ v, v ∉ S → (∀ w ∈ S, ¬ ConjPl c.toRingEquiv w v) → χ.UnrAt v) ∧ (∀ w ∈ S, ∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ w.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y → χ.locK w k = θ0 w b) ∧ (∀ w ∈ S, ∀ n : ℕ, ((∀ x, _root_.Formalism.L2.Host.IsUnitAt w x → χ.loc w x ^ n = 1) ↔ θ0 w ^ n = 1) ∧ ∀ w', ConjPl c.toRingEquiv w w' → ((∀ x, _root_.Formalism.L2.Host.IsUnitAt w' x → χ.loc w' x ^ n = 1) ↔ θ0 w ^ n = 1)) := by
  first | exact @GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | exact GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | (intros; apply GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.exists_unramified_resEta_alt : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), _root_.GlobalTheory.Mem.Chr.CMData F c φ → (∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), _root_.Formalism.L2.Host.ordF P (_root_.Formalism.L2.Host.upF F k) = _root_.Formalism.L2.Host.ordF (P.under (𝓞 F)) k) → (∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), _root_.Formalism.L2.Host.etaFin (L := L) F v a) * ∏ w : InfinitePlace F, _root_.Formalism.L2.Host.etaInf F w a = 1) → ∀ (n : I → ℤ), (∀ i, Odd (n i)) → (∀ ζ : L, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ∃ δ : Lˣ, (δ : L) = ζ * c (δ : L) ∧ (∀ P : HeightOneSpectrum (𝓞 L), (_root_.Formalism.L2.Host.aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (_root_.Formalism.L2.Host.ordF P δ)) ∧ ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) → ∃ χ : _root_.Formalism.L2.Host.HChar L, χ.IsUnitary ∧ (∀ v, χ.UnrAt v) ∧ χ.ResEta F ∧ χ.HasInf φ n := by
  first | exact @GlobalTheory.Mem.EtaExt.exists_unramified_resEta | exact GlobalTheory.Mem.EtaExt.exists_unramified_resEta | (intros; apply GlobalTheory.Mem.EtaExt.exists_unramified_resEta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_oscillatorRepresentation_unitaryCover : ∀ (P Q : ℕ) (T0 : GrpData P Q) (F : Fock (Ix P Q)), ∃ Om : T0.G →* (F.H →L[ℂ] F.H), IsOsc T0 F Om := by
  first | exact @GlobalTheory.OscGauss.exists_isOsc | exact GlobalTheory.OscGauss.exists_isOsc | (intros; apply GlobalTheory.OscGauss.exists_isOsc <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem interNum_one_lbPow_of_curve {κ : Type} [Field κ] {C : Scheme.{0}} [Algebra κ Γ(C, ⊤)]
    [IsProper (strHom κ (X := C))] {H N : LB C} (hH : IsAmpleLB H) (hd : topologicalKrullDim C = 1)
    (hN : N.IsLB) (n : ℕ) :
    interNum κ (structureModule C) ![lbPow N n] = n * interNum κ (structureModule C) ![N] := by
  induction n with
  | zero =>
    rw [interNum_eq_zero_of_cls_eq_zero κ _ (isLB_vecOne (isLB_lbPow hN 0)) 0
      ((cls_lbPow hN 0 _).trans (zero_nsmul _))]
    simp
  | succ n ih =>
    rw [interNum_one_of_cls_eq_add hH hd (isLB_lbPow hN (n + 1)) (isLB_lbPow hN n) hN
      (by
        calc
          _ = (n + 1) • cls N hN := cls_lbPow hN (n + 1) _
          _ = n • cls N hN + cls N hN := succ_nsmul _ _
          _ = _ := by rw [cls_lbPow hN n _]), ih]
    push_cast
    ring

theorem nefFib_pow_iff : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0})
    (p : X ⟶ Sp k), IsProjOver p → ∀ (L : HermLB p) (m : ℕ), 0 < m →
      (ArInt.NefFib (L.pow m) ↔ ArInt.NefFib L) := by
  intro k _ _ X p hp L m hm
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
      [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 →
      topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
    intro Z i _ _ κ _ _ _ hd
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
    have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    have hAZ := hA.pull_of_isClosedImmersion i
    have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
    have e1 : topSelfIntersection κ ((L.pow m).B.pull i) 1 =
        interNum κ (structureModule Z) ![lbPow (L.B.pull i) m] :=
      interNum_congr_cls κ _ (fun _ => LB.isLB_pull (L.pow m).isLB i)
        (isLB_vecOne (isLB_lbPow hN m)) fun j => by
          fin_cases j
          exact (cls_pull (L.pow m).isLB i _).trans
            ((congrArg (pull i) (cls_lbPow L.isLB m (L.pow m).isLB)).trans
              ((map_nsmul (pull i) m _).trans (cls_lbPow hN m _).symm))
    have e2 : topSelfIntersection κ (L.B.pull i) 1 = interNum κ (structureModule Z) ![L.B.pull i] := by
      rw [topSelf_def]
      congr 1
      funext j
      fin_cases j
      rfl
    rw [e1, e2]
    exact interNum_one_lbPow_of_curve hAZ hd hN m
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  constructor
  · intro h Z i _ _ κ _ _ _ hd
    have h' := h Z i κ hd
    rw [key Z i κ hd] at h'
    exact (mul_nonneg_iff_of_pos_left hm').1 h'
  · intro h Z i _ _ κ _ _ _ hd
    rw [key Z i κ hd]
    exact mul_nonneg hm'.le (h Z i κ hd)

end GlobalTheory.ArInt
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem nefFib_of_primeField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : HermLB p),
    (∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (q : ℕ) [Fact q.Prime]
      [Algebra (ZMod q) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1) →
    ArInt.NefFib L := by
  intro k _ X p L h Z i _ _ κ _ _ _ hdim
  haveI : Fintype κ := Fintype.ofFinite κ
  haveI hq : Fact (ringChar κ).Prime := ⟨CharP.char_is_prime κ (ringChar κ)⟩
  letI : Algebra (ZMod (ringChar κ)) κ := ZMod.algebra κ (ringChar κ)
  letI : Algebra (ZMod (ringChar κ)) Γ(Z, ⊤) :=
    ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod (ringChar κ)) κ)).toAlgebra
  haveI : IsScalarTower (ZMod (ringChar κ)) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := h Z i (ringChar κ) hdim
  have e := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod (ringChar κ)) κ Z (structureModule Z) (fun _ : Fin 1 => L.B.pull i)
  rw [topSelf_def] at h1 ⊢
  rw [e] at h1
  haveI : Module.Finite (ZMod (ringChar κ)) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod (ringChar κ)) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h1

end GlobalTheory.ArInt
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ProjFin

theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

theorem finrank_app_eq_residueDegree {Z Z' : Scheme.{0}} [IsIntegral Z] [IsIntegral Z']
    (f : Z' ⟶ Z) [IsFinite f] (h : f (genericPoint Z') = genericPoint Z) {U : Z.Opens}
    (hU : IsAffineOpen U) (hxU : f (genericPoint Z') ∈ U) :
    letI := (f.app U).hom.toAlgebra
    Module.finrank Γ(Z, U) Γ(Z', f ⁻¹ᵁ U) = f.residueDegree (genericPoint Z') := by
  letI := (f.app U).hom.toAlgebra
  letI := (Z.evaluation U _ hxU).hom.toAlgebra
  letI : Algebra Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z')) :=
    (Z'.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (f.app U ≫ Z'.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z')) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.evaluation_naturality f _ hxU).hom).symm
  haveI := isFractionRing_evaluation Z hU h hxU
  haveI := isFractionRing_evaluation Z' (hU.preimage f) rfl hxU
  exact (IsFractionRing.finrank_eq Γ(Z, U) (Z.residueField (f (genericPoint Z')))
    Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z'))).symm

theorem genRank_eq_finrank_sections {X : Scheme.{0}} [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (hx : genericPoint X ∈ U) :
    VB.genRank F = Module.finrank Γ(X, U) Γ(F, U) := by
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  have key (y : U) : Module.finrank (X.presheaf.stalk (y : X)) (F.presheaf.stalk (y : X) :) =
      Module.finrank Γ(X, U) Γ(F, U) := by
    have := hU.isLocalization_stalk y
    have := QCoh.isLocalizedModule_germLinear F hU y
    have hp := (hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors
    rw [IsLocalization.finrank_eq _ _ hp, IsLocalizedModule.finrank_eq _ (QCoh.germLinear F y) hp]
  exact key ⟨_, hx⟩

theorem isFiniteQC_pushforward_structureModule {Z Z' : Scheme.{0}} (f : Z' ⟶ Z) [IsFinite f] :
    QCoh.IsFiniteQC ((Scheme.Modules.pushforward f).obj (structureModule Z')) :=
  ⟨inferInstance, fun _ hV => QCoh.finite_sections_pushforward f _ hV
    (hF := QCoh.finite_sections (structureModule Z') (hV.preimage f))⟩

theorem genRank_pushforward {Z Z' : Scheme.{0}} [IsIntegral Z] [IsIntegral Z'] (f : Z' ⟶ Z)
    [IsFinite f] (h : f (genericPoint Z') = genericPoint Z) :
    VB.genRank ((Scheme.Modules.pushforward f).obj (structureModule Z')) =
      f.residueDegree (genericPoint Z') := by
  obtain ⟨U, hU, hxU⟩ := QCoh.exists_affine_mem (genericPoint Z)
  have hx' : f (genericPoint Z') ∈ U := h ▸ hxU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have h1 : VB.genRank ((Scheme.Modules.pushforward f).obj (structureModule Z')) =
      Module.finrank Γ(Z, U) Γ((Scheme.Modules.pushforward f).obj (structureModule Z'), U) :=
    genRank_eq_finrank_sections _ hU hxU
  letI := (f.app U).hom.toAlgebra
  let e : Γ((Scheme.Modules.pushforward f).obj (structureModule Z'), U) ≃ₗ[Γ(Z, U)]
      Γ(Z', f ⁻¹ᵁ U) :=
    { toFun := fun s => s
      invFun := fun s => s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [h1, e.finrank_eq, finrank_app_eq_residueDegree f h hU hx']

theorem interNumOn_eq_residueDegree_mul : ∀ (κ : Type) [Field κ] (Z Z' : Scheme.{0}) [IsIntegral Z]
    [IsIntegral Z'] [Algebra κ Γ(Z, ⊤)] (f : Z' ⟶ Z) [IsFinite f], IsProjOver (strHom κ (X := Z)) →
    topologicalKrullDim Z = 1 → f (genericPoint Z') = genericPoint Z → ∀ N : LB Z, N.IsLB →
    interNumOn κ f ![N] = (f.residueDegree (genericPoint Z') : ℤ) *
      interNum κ (structureModule Z) ![N] := by
  intro κ _ Z Z' _ _ _ f _ hP hd hg N hN
  haveI := isFiniteQC_pushforward_structureModule f
  rw [interNumOn_def, GlobalTheory.T.intersectionNumber_eq_genericRank_mul_projCurve κ Z hP hd _ N hN, genRank_pushforward f hg]

end GlobalTheory.ProjFin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockVectorsOfThetaDatum_injective : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → IsVacVec ψ θ M M' f → Function.Injective (ptOf ψ θ M M' f) := by
  first | exact @GlobalTheory.FockInj.ptOf_injective | exact GlobalTheory.FockInj.ptOf_injective | (intros; apply GlobalTheory.FockInj.ptOf_injective <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastStep_parameters_partition_extended_by_zeros : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau) (n N : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool) (lam' : Fin N → ℝ) (ε' : Fin N → Bool), (k : ℕ) + 1 = D.R.m → n = D.R.r + k * D.R.t → N = n + D.R.t → IsEnum (parB (Ptw D) k τ) lam ε → IsEnum (parB (Ptw D) D.R.m τ) lam' ε' → ε = allPos n ∧ ε' = allPos N ∧ ∃ x₁ x₃ : ℤ, (x₁ : ℚ) = expS D k τ + (n : ℚ) / 2 ∧ (x₃ : ℚ) = -((N : ℚ) / 2 + expT D k τ) ∧ ∃ (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν ∧ (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (allPos n) lam a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) ∧ ∀ b, Formalism.QuantumDeterminants.lowK (allPos N) lam' b = -(x₁ : ℝ) - ν (Fin.rev b) := by
  first | exact @GlobalTheory.LastStepParam.lastStep_param | exact GlobalTheory.LastStepParam.lastStep_param | (intros; apply GlobalTheory.LastStepParam.lastStep_param <;> assumption)
end
