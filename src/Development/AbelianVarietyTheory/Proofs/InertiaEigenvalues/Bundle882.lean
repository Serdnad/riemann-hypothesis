module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle852
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle195
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmQAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle280
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle859
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle873
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle870
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPullTame

theorem coprime_absNorm {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {m : ℕ}
    (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal) : Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  first
  | exact @_root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem
  | exact _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem
  | (apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem ..)


open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin) in
theorem tameAt_of_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Neutral.B1.Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) {r : G E Ω →* ℂˣ} {χ : Formalism.L2.Host.HChar E} (h : GlobalTheory.ToricDistribution.Corr art r χ)
    {P : HeightOneSpectrum (𝓞 E)} {B : ValuationSubring Ω} (hB : IsPlaceOver B P) {m : ℕ}
    (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal) (hi : ∀ σ ∈ Ine (F := E) B, r σ ^ m = 1) : χ.TameAt P := by
  intro x hx hx1
  obtain ⟨a, ha'⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ P
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  have hlt : Valued.v ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion E) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) (P.adicCompletion E)), GlobalTheory.Mem.WildChar.valued_algebraMap_lt_one]
    exact hmem
  have h3 := ha' _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx (Ideal.absNorm P.asIdeal ^ a)) (by
    rw [Units.val_pow_eq_pow_val]
    refine GlobalTheory.Mem.WildChar.val_pow_pow_sub_one_le _ (le_of_eq hx) (hx1.trans_lt ?_) hlt a
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num)
  rw [map_pow] at h3
  have h4 : χ.loc P x ^ m = 1 := by
    obtain ⟨σ, hσ, e⟩ := (ha.ine P B hB _).mp ⟨x, hx, rfl⟩
    have e2 : χ.loc P x = r σ := h _ σ e.symm
    rw [e2, hi σ hσ]
  have hc : Nat.Coprime m (Ideal.absNorm P.asIdeal ^ a) := (coprime_absNorm hm).pow_right a
  rw [← pow_one (χ.loc P x), ← hc.gcd_eq_one]
  exact pow_gcd_eq_one.2 ⟨h4, h3⟩

theorem ine_pow_of_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) {A : Type} [CommGroup A]
    {φ : G D.host.E N.Om →* A} (hanti : AntiHom X.cc φ) {P P' : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P P') {m : ℕ}
    (h : ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1)
    (B' : ValuationSubring N.Om) (hB' : IsPlaceOver B' P') (σ : G D.host.E N.Om) (hσ : σ ∈ Ine (F := D.host.E) B') :
    φ σ ^ m = 1 := by
  have h1 := GlobalTheory.TwistDet.cConj_mem_ine X hσ
  have h2 := GlobalTheory.TwistDet.isPlaceOver_moveVal_cc X (GlobalTheory.TwistDet.isConjPl_symm hc) hB'
  have h3 := h _ h2 _ h1
  rw [GlobalTheory.TwistDet.antiHom_cConj X hanti, inv_pow, inv_eq_one] at h3
  exact h3

theorem natCast_mem_conj {D : D7} {P P' : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P P') (m : ℕ) :
    ((m : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal ↔ ((m : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [GlobalTheory.TwistDet.isConjPl_iff.1 hc, map_natCast]

end GlobalTheory.TwistPullTame

namespace GlobalTheory.TwistPullTame

open GlobalTheory.TwistPull

theorem good_pull_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A), IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∃ m : ℕ, ((m : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  intro D N X a ha A _ φ hφ hanti Q hQ hQm hunr
  haveI := finite_range (D := D) hφ
  set M := Nat.card φ.range with hMdef
  have hM : M ≠ 0 := Nat.card_pos.ne'
  have hr : ∀ f : φ.range →* ℂˣ, IsOpen ((f.comp φ.rangeRestrict).ker : Set (G D.host.E N.Om)) ∧
      ∀ σ, (f.comp φ.rangeRestrict) σ ^ M = 1 := fun f => by
    refine ⟨Subgroup.isOpen_mono (H₁ := φ.ker) (fun g hg => ?_) hφ, fun σ => ?_⟩
    · have : φ.rangeRestrict g = 1 := Subtype.ext (MonoidHom.mem_ker.1 hg)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, this, map_one]
    · rw [MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]
  have hanti' : ∀ f : φ.range →* ℂˣ, AntiHom X.cc (f.comp φ.rangeRestrict) := fun f g g' hg => by
    have e : φ.rangeRestrict g' = (φ.rangeRestrict g)⁻¹ := Subtype.ext (hanti g g' hg)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_inv]

  have hin : ∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → ∃ m : ℕ,
      ((m : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal ∧
        ∀ B : ValuationSubring N.Om, IsPlaceOver B P' → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1 := by
    intro P hP P' hP'
    obtain ⟨m, hm, hB⟩ := hQm P hP
    rcases hP' with rfl | hc
    · exact ⟨m, hm, hB⟩
    · exact ⟨m, fun h => hm ((natCast_mem_conj hc m).1 h), ine_pow_of_conj X hanti hc hB⟩
  have htame : ∀ (f : φ.range →* ℂˣ) (χ : Formalism.L2.Host.HChar D.host.E),
      GlobalTheory.ToricDistribution.Corr a.art (f.comp φ.rangeRestrict) χ →
      ∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P' := by
    intro f χ hχ P hP P' hP'
    obtain ⟨m, hm, hB⟩ := hin P hP P' hP'
    obtain ⟨B, hB'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P'
    refine tameAt_of_ine ha.artin hχ hB' hm fun σ hσ => ?_
    have e : φ.rangeRestrict σ ^ m = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, MonoidHom.coe_rangeRestrict, hB B hB' σ hσ]; rfl)
    rw [MonoidHom.comp_apply, ← map_pow, e, map_one]
  refine ⟨isOpen_ker_pull ha hφ, fun x => pull_rat ha φ x, fun y => ?_, hQ, ?_, fun PP hPP => isResAt_resOf ?_⟩
  ·
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨h1, h2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha h1 hM h2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [real_C D N X a.art ha.artin _ _ hM h2 (hanti' f) c χ hc hχ y]
    simp
  ·
    intro x h1 h2 h3 h4
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨o1, o2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 hM o2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [GlobalTheory.T.heckeChar_unramified_outside_split_set_of_tame D N a.art ha.artin _ M hM o2 c χ hc hχ Q hQ (htame f χ hχ) (fun v hv hc' B hB σ hσ => by
      rw [MonoidHom.comp_apply, show φ.rangeRestrict σ = 1 from Subtype.ext (hunr v hv hc' B hB σ hσ), map_one]) x h1 h2 h3 h4]
    simp
  ·
    have hPP := hQ.isIdemAt hPP
    have same : ∀ (x x' : (AE D)ˣ) (u : (kP PP)ˣ), (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP →
        (1 - idemAt PP) * (x' : AE D) = 1 - idemAt PP →
        ∀ (hi : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
          (hi' : toEAf D (x' : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        resS D.host.F PP ⟨_, hi⟩ = u → resS D.host.F PP ⟨_, hi'⟩ = u → a.pull φ x = a.pull φ x' := by
      intro x x' u hx hx' hi hi' hu hu'
      refine pull_eq_of_chars a hφ fun f => ?_
      obtain ⟨o1, o2⟩ := hr f
      obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 hM o2
      have ht : χ.TameAt PP := htame f χ hχ PP ‹_› PP (Or.inl rfl)
      obtain ⟨ρ, hρ⟩ := GlobalTheory.exists_isRes_of_tameAt D χ PP ht
      have e : ∀ z : (AE D)ˣ, (1 - idemAt PP) * (z : AE D) = 1 - idemAt PP →
          ∀ (hz : toEAf D (z : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
          resS D.host.F PP ⟨_, hz⟩ = u → a.pull (f.comp φ.rangeRestrict) z = ρ u := fun z hz hzi hzu =>
        Units.ext ((hcr z).symm.trans (GlobalTheory.ConjTwist.eq_res_of_chrEq hc hPP ht hρ z hz hzi u hzu))
      rw [e x hx hi hu, e x' hx' hi' hu']
    have hlift := fun u => GlobalTheory.ConjTwist.exists_isLocUnit hPP u
    choose xs hxs using hlift
    have hmul : ∀ u v, a.pull φ (xs (u * v)) = a.pull φ (xs u * xs v) := fun u v => by
      obtain ⟨hi, hu⟩ := (hxs (u * v)).res
      obtain ⟨hi1, hu1⟩ := (hxs u).res
      obtain ⟨hi2, hu2⟩ := (hxs v).res
      have hi3 : toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
        rw [Units.val_mul, map_mul]
        exact mul_mem hi1 hi2
      refine same _ _ (u * v) (hxs (u * v)).off ?_ hi hi3 hu ?_
      · rw [Units.val_mul, ← mul_assoc, (hxs u).off, (hxs v).off]
      · have : (⟨_, hi3⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi1⟩ * ⟨_, hi2⟩ :=
          Subtype.ext (by
            change toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) = toEAf D (xs u : AE D) * toEAf D (xs v : AE D)
            rw [Units.val_mul, map_mul])
        rw [this, map_mul, hu1, hu2, Units.val_mul]
    refine ⟨MonoidHom.mk' (fun u => a.pull φ (xs u)) (fun u v => ?_), ?_⟩
    · show a.pull φ (xs (u * v)) = a.pull φ (xs u) * a.pull φ (xs v)
      rw [hmul, map_mul]
    · intro x hx hi u hu
      show a.pull φ x = a.pull φ (xs u)
      obtain ⟨hi', hu'⟩ := (hxs u).res
      exact same x (xs u) u hx (hxs u).off hi hi' hu hu'

end GlobalTheory.TwistPullTame
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.SpreadRestrict

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X}

theorem surj_conj {B : Type} [CommGroup B] (χ : G D.host.E N.Om →* B) (hA : AntiHom X.cc χ)
    {P P' : PlE D.host} (hPP : IsConjPl D.host P P')
    (hs : ∀ A : ValuationSubring N.Om, IsPlaceOver A P → ∀ b : B, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b)
    (A : ValuationSubring N.Om) (hA' : IsPlaceOver A P') (b : B) : ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    Formalism.BasicNotions.bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := X.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, X.cc (algebraMap D.host.E N.Om x) =
      algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E N.Om)) x).symm
  have hs' : ∀ x, X.cc.symm (algebraMap D.host.E N.Om x) =
      algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hinv : ∀ x, X.cc (X.cc x) = x := fun x => by
    apply j.injective
    rw [hj, hj]
    simp
  have hsymm : ∀ x, X.cc.symm x = X.cc x := fun x => by
    rw [RingEquiv.symm_apply_eq, hinv]
  have hP'P := GlobalTheory.GalChar.isConjPl_symm hPP
  have hpl : IsPlaceOver (A.comap X.cc.symm.toRingHom) P := fun y => by
    have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]
    exact hA' ⟨_, hint⟩
  obtain ⟨σ, hσ, hσb⟩ := hs _ hpl b⁻¹
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine X.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  have eA : (A.comap X.cc.symm.toRingHom).comap X.cc.symm.toRingHom = A := by
    ext y
    show X.cc.symm (X.cc.symm y) ∈ A ↔ y ∈ A
    rw [hsymm, hsymm, hinv]
  refine ⟨σ', eA ▸ h2, ?_⟩
  rw [hA σ σ' h1, hσb, inv_inv]

theorem sign_eq_one (hY : GlobalTheory.UnivChar.IsUnivChar Y) {i : X.Tw} {S : Finset (Pl D.host.E)} {M : ℕ}
    {P v : Pl D.host.E} (hP : P ∈ S) (hv : v ∈ S) (hc : IsConjPl D.host P v) (hPa : P ∈ admissibleConjugatePairPlaces X i S M) :
    (((Y.delU_conj i S M P hP v hv hc).choose : ℤ) : ZMod (X.l i ^ M)) = 1 := by
  classical
  have hs := (Y.delU_conj i S M P hP v hv hc).choose_spec
  have hva : v ∈ admissibleConjugatePairPlaces X i S M := conj_mem_admissibleConjugatePairPlaces hPa hc
  obtain ⟨-, P', -, -, hadm⟩ := mem_admissibleConjugatePairPlaces_iff.1 hPa
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hadm.2 P (by simp)
  have hDel : GlobalTheory.GalChar.IsDel D.host X.cc (X.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun w hw => h4 w (fun e => hw (Or.inl e)) (fun e => hw (Or.inr e)), fun w hw A hA b => ?_⟩
    have hsP : ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
      obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
      exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
    rcases hw with rfl | hw
    · exact hsP A hA b
    · exact surj_conj χ h2 hw hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host X.cc (X.l i) ⟨χ, hDel⟩
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P
  obtain ⟨σ, -, hσ⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd 1)
  have e := hs σ
  rw [delU_on hY σ ⟨v, hv⟩ hva, delU_on hY σ ⟨P, hP⟩ hPa] at e
  simp only at e
  rw [GlobalTheory.GalChar.pair_eq hc, hσ, toAdd_ofAdd, mul_one] at e
  exact e.symm

theorem spread_conj (hY : GlobalTheory.UnivChar.IsUnivChar Y) {i : X.Tw} {M : ℕ} {ch : Set (Pl D.host.E)} (hch : IsChoice ch)
    {S : Finset (Pl D.host.E)} (hS : admissibleConjugatePairPlaces X i S M = S) (x : ↥(half ch (admissibleConjugatePairPlaces X i S M)) → ZMod (X.l i ^ M))
    {v P : Pl D.host.E} (hvS : v ∈ S) (hvc : v ∉ ch) (hvP : IsConjPl D.host v P)
    (hPh : P ∈ half ch (admissibleConjugatePairPlaces X i S M)) :
    spread Y i S M ch x ⟨v, hvS⟩ = x ⟨P, hPh⟩ := by
  have hva : v ∈ admissibleConjugatePairPlaces X i S M := by rw [hS]; exact hvS
  have hne : v ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hva) hvP
  have hPv := GlobalTheory.GalChar.isConjPl_symm hvP
  have hPaa : P ∈ admissibleConjugatePairPlaces X i (admissibleConjugatePairPlaces X i S M) M := by
    simp only [hS]
    rw [← hS]
    exact (mem_half.1 hPh).1
  rw [spread_apply, Finset.sum_eq_single ⟨P, hPh⟩, weight, if_neg hne, dite_eq_left ⟨hva, hPv⟩, sign_eq_one hY _ _ hPv hPaa,
    one_mul]
  · intro P' _ h'
    rw [weight, if_neg fun e : v = P'.1 => hvc (e ▸ (mem_half.1 P'.2).2), dite_eq_right fun h => h' (Subtype.ext
      (GlobalTheory.GalChar.isConjPl_unique (GlobalTheory.GalChar.isConjPl_symm h.2) hvP)), zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem spread_restrict : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (M : ℕ) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (Q Q' : Finset (Pl D.host.E)) (hQQ : Q' ⊆ Q), admissibleConjugatePairPlaces X i Q M = Q → admissibleConjugatePairPlaces X i Q' M = Q' → ∀ (hsub : ∀ w ∈ half ch (admissibleConjugatePairPlaces X i Q' M), w ∈ half ch (admissibleConjugatePairPlaces X i Q M)) (c : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : Pl D.host.E) (hv : v ∈ Q'), spread Y i Q M ch c ⟨v, hQQ hv⟩ = spread Y i Q' M ch (fun w => c ⟨w.1, hsub w.1 w.2⟩) ⟨v, hv⟩ := by
  intro D N X Y hY i M ch hch Q Q' hQQ hQ hQ' hsub c v hv
  by_cases hc : v ∈ ch
  · have h1 : v ∈ half ch (admissibleConjugatePairPlaces X i Q M) := mem_half.2 ⟨by rw [hQ]; exact hQQ hv, hc⟩
    have h2 : v ∈ half ch (admissibleConjugatePairPlaces X i Q' M) := mem_half.2 ⟨by rw [hQ']; exact hv, hc⟩
    rw [spread_of_mem Y i Q M hch c ⟨v, hQQ hv⟩ h1, spread_of_mem Y i Q' M hch _ ⟨v, hv⟩ h2]
  · have hva : v ∈ admissibleConjugatePairPlaces X i Q' M := by rw [hQ']; exact hv
    obtain ⟨-, P, -, hvP, -⟩ := mem_admissibleConjugatePairPlaces_iff.1 hva
    have hne : v ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hva) hvP
    have hPc : P ∈ ch := by
      by_contra h
      exact hc ((hch.pair _ _ hvP hne).2 h)
    have hPa' : P ∈ admissibleConjugatePairPlaces X i Q' M := conj_mem_admissibleConjugatePairPlaces hva hvP
    have hPh' : P ∈ half ch (admissibleConjugatePairPlaces X i Q' M) := mem_half.2 ⟨hPa', hPc⟩
    rw [spread_conj hY hch hQ c (hQQ hv) hc hvP (hsub P hPh'), spread_conj hY hch hQ' _ hv hc hvP hPh']

end GlobalTheory.SpreadRestrict

end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.FockSubstHarm

theorem isLetters_unique {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) {lt lt' : LtN Dw n ≃ FVar D m n}
    (h : IsLetters Dw lt) (h' : IsLetters Dw lt') : lt = lt' := by
  refine Equiv.ext fun ℓ => ?_
  obtain ⟨hb, h1⟩ := h ℓ
  obtain ⟨hb', h1'⟩ := h' ℓ
  have hpsi : ∀ ρ, InPsi H (tauE D ρ) := fun ρ => (hΨ _).2 ⟨ρ, rfl⟩
  have hnot : ∀ ρ, ¬ InPsi H (ComplexEmbedding.conjugate (tauE D ρ)) := fun ρ hc =>
    (GlobalTheory.Harm.not_mem_hostType_iff H (ComplexEmbedding.conjugate (tauE D ρ))).2
      (by have e := ComplexEmbedding.involutive_conjugate _ (tauE D ρ); have := hpsi ρ; rw [← e] at this; exact this) hc
  rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases h1' with ⟨e1', e2'⟩ | ⟨e1', e2'⟩
  · have hρ : (lt ℓ).1 = (lt' ℓ).1 := GlobalTheory.StdRat.tauE_injective D (e1.symm.trans e1')
    exact Prod.ext hρ (Prod.ext (Fin.ext (by omega)) (hb.trans hb'.symm))
  · exact absurd (e1 ▸ hpsi (lt ℓ).1 : InPsi H ℓ.1) (e1' ▸ hnot (lt' ℓ).1)
  · exact absurd (e1' ▸ hpsi (lt' ℓ).1 : InPsi H ℓ.1) (e1 ▸ hnot (lt ℓ).1)
  · have hρ : (lt ℓ).1 = (lt' ℓ).1 :=
      GlobalTheory.StdRat.tauE_injective D ((ComplexEmbedding.involutive_conjugate _).injective (e1.symm.trans e1'))
    exact Prod.ext hρ (Prod.ext (Fin.ext (by omega)) (hb.trans hb'.symm))

end GlobalTheory.FockSubstHarm

noncomputable section
namespace GlobalTheory.FockSubstHarm

theorem rename_comp_fockSubst {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (u : GlobalTheory.ExportSeries.GLR D n) :
    (MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ rfl)).comp
        (GlobalTheory.ExportSeries.fockSubst (m := Dw.p + Dw.q) (fun _ => Dw.p) u) =
      (GlobalTheory.Harm.colSubst (p := Dw.p) (q := Dw.q)
        (fun t => (((u ((GlobalTheory.FockLetters.tauPsi hΨ).symm t))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
        (fun t => ((u ((GlobalTheory.FockLetters.tauPsi hΨ).symm t) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))).comp
        (MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ rfl)) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨ρ, i, b⟩ := v
  induction i using Fin.addCases with
  | left i =>
    have hi : ((Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q)) : ℕ) < (fun _ => Dw.p) ρ := by simp

    simp only [AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, MvPolynomial.aeval_X, if_pos hi, map_sum, map_mul,
    MvPolynomial.rename_C, MvPolynomial.rename_X]
    simp only [GlobalTheory.FockLetters.fockVarEquiv, Equiv.prodCongr_apply, Prod.map, finCongr_refl, Equiv.refl_trans,
      Equiv.refl_apply, finSumFinEquiv_symm_apply_castAdd]
    erw [GlobalTheory.Harm.colSubst_X_xVar]
    simp [GlobalTheory.Harm.xForm_apply]
  | right j =>
    have hj : ¬ ((Fin.natAdd Dw.p j : Fin (Dw.p + Dw.q)) : ℕ) < (fun _ => Dw.p) ρ := by simp

    simp only [AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, MvPolynomial.aeval_X, if_neg hj, map_sum, map_mul,
    MvPolynomial.rename_C, MvPolynomial.rename_X]
    simp only [GlobalTheory.FockLetters.fockVarEquiv, Equiv.prodCongr_apply, Prod.map, finCongr_refl, Equiv.refl_trans,
      Equiv.refl_apply, finSumFinEquiv_symm_apply_natAdd]
    erw [GlobalTheory.Harm.colSubst_X_yVar]
    simp [GlobalTheory.Harm.yForm_apply]

theorem rename_fockSubst_mem_HHa : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (lt : LtN Dw n ≃ FVar D m n),
    m = Dw.p + Dw.q → (∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) → IsLetters Dw lt →
    ∀ (u : GlobalTheory.ExportSeries.GLR D n) (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (Q : MvPolynomial (LtN Dw n) ℂ),
      Q ∈ HHa Dw.mult n ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)) →
      MvPolynomial.rename lt.symm (GlobalTheory.ExportSeries.fockSubst (m := m) (fun _ => Dw.p) u (MvPolynomial.rename lt Q)) ∈
        HHa Dw.mult n ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)) := by
  intro D H Dw m n lt hm hΨ hlt u wa Q hQ
  subst hm
  obtain rfl : lt = GlobalTheory.FockLetters.letterEquiv Dw hΨ rfl :=
    isLetters_unique Dw hΨ hlt (GlobalTheory.FockLetters.isLetters_letterEquiv Dw hΨ rfl)
  rcases GlobalTheory.Harm.HHa_eq_zero_or_rowHighest (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate D.host.E)
      (GlobalTheory.Harm.not_mem_hostType_iff H) (fun _ => GlobalTheory.Harm.mult_of_mem Dw) (fun _ => GlobalTheory.Harm.mult_conjEmb_of_mem Dw)
      (n := n) (K := ℂ) (fun τ i => wa (τ, i)) with h0 | ⟨k, k', -, hiff⟩
  · have hQ0 := h0 Q hQ
    rw [hQ0] at hQ ⊢
    rw [map_zero, map_zero, map_zero]
    exact hQ
  · rw [hiff] at hQ ⊢
    change MvPolynomial.rename (GlobalTheory.Harm.thetaLetterEquiv Dw n) _ ∈ _ at hQ
    change MvPolynomial.rename (GlobalTheory.Harm.thetaLetterEquiv Dw n) _ ∈ _
    have e1 : ∀ P : MvPolynomial (FVar D (Dw.p + Dw.q) n) ℂ,
        MvPolynomial.rename (GlobalTheory.Harm.thetaLetterEquiv Dw n)
          (MvPolynomial.rename (GlobalTheory.FockLetters.letterEquiv Dw hΨ rfl).symm P) =
        MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ rfl) P := fun P => by
      rw [MvPolynomial.rename_rename]
      refine congrArg (fun f => MvPolynomial.rename f P) (funext fun v => ?_)
      simp [GlobalTheory.FockLetters.letterEquiv]
    have e2 : MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ rfl)
        (MvPolynomial.rename (GlobalTheory.FockLetters.letterEquiv Dw hΨ rfl) Q) =
        MvPolynomial.rename (GlobalTheory.Harm.thetaLetterEquiv Dw n) Q := by
      rw [MvPolynomial.rename_rename]
      refine congrArg (fun f => MvPolynomial.rename f Q) (funext fun v => ?_)
      simp [GlobalTheory.FockLetters.letterEquiv]
    rw [e1, ← AlgHom.comp_apply, rename_comp_fockSubst, AlgHom.comp_apply, e2]
    exact GlobalTheory.Harm.colSubst_mem_rowHighest (fun t => Units.inv_mul _) hQ

end GlobalTheory.FockSubstHarm
end
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.conjugateHalf_vacuum_translate_sum_isThetaFockVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y) → IsThetaFunO ψ V W (∑ y ∈ Y, heisO ψ V W y f₀) ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) (∑ y ∈ Y, heisO ψ V W y f₀) := by
  first | exact @GlobalTheory.ConjHalfVac.sum_conj_half_vac | exact GlobalTheory.ConjHalfVac.sum_conj_half_vac | (intros; apply GlobalTheory.ConjHalfVac.sum_conj_half_vac <;> assumption)
end
