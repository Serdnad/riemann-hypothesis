module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle861
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle892
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.NotFamConstZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle548
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle104
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TameConjPlace

open GlobalTheory.ExportSeries Formalism.L2.JoinChr

section Density

variable {E : Type} [Field E] [NumberField E]

theorem tameAt_of_congr (H : Formalism.L2.Host.HChar E) (PP : HeightOneSpectrum (𝓞 E))
    (hc : ∀ (a b : 𝓞 E) (ka kb : Eˣ), (ka : E) = (a : E) → (kb : E) = (b : E) → a ∉ PP.asIdeal →
      a - b ∈ PP.asIdeal → H.locK PP ka = H.locK PP kb) : H.TameAt PP := by
  have hone : ∀ k : Eˣ, PP.valuation E ((k : E) - 1) < 1 → H.locK PP k = 1 := by
    intro k hk
    have hv1 : PP.valuation E (k : E) = 1 := by
      have e : (k : E) = 1 + ((k : E) - 1) := by ring
      have h1 : PP.valuation E ((k : E) - 1) < PP.valuation E 1 := by rwa [map_one]
      rw [e]
      first
        | rw [Valuation.map_add_eq_of_lt_right _ h1, map_one]
        | rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]
        | rw [add_comm, Valuation.map_add_eq_of_lt_right _ h1, map_one]
        | rw [add_comm, Valuation.map_add_eq_of_lt_left _ h1, map_one]
    obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer (k : E) hv1.le
    have hs : (s : 𝓞 E) ∉ PP.asIdeal := s.2
    have hsv := GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem PP _ hs
    have hav : PP.valuation E (algebraMap (𝓞 E) E a) = 1 := by
      rw [← h, map_mul, hv1, hsv, one_mul]
    have ha : a ∉ PP.asIdeal := by
      intro hm
      have hlt : PP.valuation E (algebraMap (𝓞 E) E a) < 1 :=
        (PP.valuation_lt_one_iff_mem (K := E) a).mpr hm
      exact absurd hav (ne_of_lt hlt)
    have hs0 : algebraMap (𝓞 E) E s ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hsv; exact zero_ne_one hsv
    have ha0 : algebraMap (𝓞 E) E a ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hav; exact zero_ne_one hav
    have hdiff : a - (s : 𝓞 E) ∈ PP.asIdeal := by
      apply (PP.valuation_lt_one_iff_mem (K := E) _).mp
      show PP.valuation E (algebraMap (𝓞 E) E (a - (s : 𝓞 E))) < 1
      rw [map_sub, ← h, ← sub_one_mul, map_mul, hsv, mul_one]
      exact hk
    let ka : Eˣ := Units.mk0 _ ha0
    let ks : Eˣ := Units.mk0 _ hs0
    have e1 : H.locK PP ka = H.locK PP ks := hc a (s : 𝓞 E) ka ks rfl rfl ha hdiff
    have hk' : k = ka * ks⁻¹ := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ka, ks]
      rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    rw [hk', map_mul, map_inv, e1, mul_inv_cancel]
  unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
  intro x _ hx1
  by_contra hne
  have hcont : Continuous (H.loc PP) := H.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele PP)
  have hW : IsOpen {y : (PP.adicCompletion E)ˣ | H.loc PP y ≠ 1} := isOpen_ne_fun hcont continuous_const
  obtain ⟨T, hT, hTe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hW
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hxT : (x : PP.adicCompletion E) ∈ T ∩ {z | Valued.v (z - 1) < 1} := by
    refine ⟨?_, lt_of_le_of_lt hx1 hlt⟩
    have : x ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion E)ˣ) := by rw [hTe]; exact hne
    exact this
  have hU : IsOpen (T ∩ {z : PP.adicCompletion E | Valued.v (z - 1) < 1}) :=
    hT.inter ((GlobalTheory.ChainOnto.TameRes.isOpen_ltOne PP).preimage (continuous_sub_right 1))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap E PP).exists_mem_open hU ⟨_, hxT⟩
  have hk1 : PP.valuation E (k - 1) < 1 := by
    rw [← GlobalTheory.ChainOnto.TameRes.val_alg, map_sub, map_one]; exact hk.2
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk1
  have hloc := hone (Units.mk0 k hk0) hk1
  have hmem : Formalism.L2.Host.atFin PP (Units.mk0 k hk0) ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion E)ˣ) := hk.1
  rw [hTe] at hmem
  exact hmem hloc

end Density

variable {D : D7}



theorem chi_locE_congr (δ : Twist D Circle) (hδ : δ.Good) {PP : Pl D.host.E} (hPP : PP ∈ δ.Q) (a b : 𝓞 D.host.E)
    (ha : a ∉ PP.asIdeal) (hab : a - b ∈ PP.asIdeal) (x y : (AE D)ˣ)
    (hx : (x : AE D) = 1 + idemAt PP * (incA D (a : D.host.E) - 1))
    (hy : (y : AE D) = 1 + idemAt PP * (incA D (b : D.host.E) - 1)) : δ.chi x = δ.chi y := by
  have he := hδ.split.isIdemAt hPP
  have hee : idemAt PP * idemAt PP = idemAt PP := he.1.1
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have hma : (Ideal.Quotient.mk PP.asIdeal a : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact ha
  let u : (kP PP)ˣ := Units.mk0 _ hma
  have key : ∀ (c : 𝓞 D.host.E) (z : (AE D)ˣ), (z : AE D) = 1 + idemAt PP * (incA D (c : D.host.E) - 1) →
      Ideal.Quotient.mk PP.asIdeal c = (u : kP PP) → δ.chi z = δ.res PP u := by
    intro c z hz hcu
    have hv : Formalism.IndefR.Datum.toEAf D (z : AE D) =
        ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E c - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := by
      have hb : Formalism.IndefR.Datum.toEAf D (incA D (c : D.host.E)) =
          ((oToS D.host.F D.host.E c : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := rfl
      rw [hz, GlobalTheory.ConjTwist.map_loc, hb]
      rfl
    have hzi : Formalism.IndefR.Datum.toEAf D (z : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [hv]; exact Subtype.property _
    refine hδ.res PP hPP z ?_ hzi u ?_
    · rw [hz]; linear_combination (1 - incA D (c : D.host.E)) * hee
    · have e2 : (⟨_, hzi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E c - 1) :=
        Subtype.ext hv
      rw [e2, GlobalTheory.ConjTwist.map_loc, h1, resS_oToS, hcu]
      ring
  have hb : Ideal.Quotient.mk PP.asIdeal b = (u : kP PP) := by
    show Ideal.Quotient.mk PP.asIdeal b = Ideal.Quotient.mk PP.asIdeal a
    exact (Ideal.Quotient.eq.mpr hab).symm
  rw [key a x hx rfl, key b y hy hb]



theorem locK_congr_conj (δ : Twist D Circle) (hδ : δ.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq δ.chi χ)
    {P' : Pl D.host.E} (hP' : P' ∈ δ.Q) {P : Pl D.host.E} (hPP : Formalism.IndefR.Lev.IsConjPl P' P)
    (a b : 𝓞 D.host.E) (ka kb : D.host.Eˣ) (hka : (ka : D.host.E) = (a : D.host.E)) (hkb : (kb : D.host.E) = (b : D.host.E))
    (ha : a ∉ P.asIdeal) (hab : a - b ∈ P.asIdeal) : χ.locK P ka = χ.locK P kb := by
  have he' := hδ.split.isIdemAt hP'
  have he : Formalism.L2.NTheta.IsIdemAt (cA D (idemAt P')) P :=
    (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 P' _ _ he' hPP
  have hee : cA D (idemAt P') * cA D (idemAt P') = cA D (idemAt P') := he.1.1
  have hcc : cA D (cA D (idemAt P')) = idemAt P' := GlobalTheory.MovedIdem.cA_cA _

  have step : ∀ (k : D.host.Eˣ) (c : 𝓞 D.host.E), (k : D.host.E) = star (c : D.host.E) →
      ∀ z : (AE D)ˣ, (z : AE D) = 1 + idemAt P' * (incA D (c : D.host.E) - 1) →
      ((χ.locK P k : ℂˣ) : ℂ) = ((δ.chi z : Circle) : ℂ)⁻¹ := by
    intro k c hk z hz
    let x := locU hee k
    have h1 : ((δ.chi x : Circle) : ℂ) = ((χ.locK P k : ℂˣ) : ℂ) :=
      hc.2 P _ (GlobalTheory.HeckeDetChar.isPlIdem he) k x (locU_val hee k)
    have hxz : cA D (x : AE D) = (z : AE D) := by
      rw [locU_val, locE, hz, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hcc,
        GlobalTheory.MovedIdem.cA_incA, hk, star_star]
    have hfix : cA D ((x * z : (AE D)ˣ) : AE D) = ((x * z : (AE D)ˣ) : AE D) := by
      rw [Units.val_mul, RingHom.map_mul, hxz, ← hxz, GlobalTheory.MovedIdem.cA_cA, mul_comm]
    obtain ⟨α, hα⟩ := (GlobalTheory.DetRootRows.fixed_iff_idF (x * z)).1 hfix
    have h2 : δ.chi x * δ.chi z = 1 := by rw [← map_mul, ← hα, hδ.real]
    rw [← h1]
    have h3 : ((δ.chi x : Circle) : ℂ) * ((δ.chi z : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, h2, Circle.coe_one]
    exact eq_inv_of_mul_eq_one_left h3
  have hsym := GlobalTheory.ParahoricLift.isConjPl_symm hPP

  have hca : Formalism.L2.Col.cO _ a ∉ P'.asIdeal := by
    intro hm
    obtain ⟨c', hc', hc'e⟩ := hPP _ hm
    apply ha
    have : c' = a := RingOfIntegers.ext (by rw [hc'e]; exact star_star (a : D.host.E))
    rwa [← this]
  have hcab : Formalism.L2.Col.cO _ a - Formalism.L2.Col.cO _ b ∈ P'.asIdeal := by
    obtain ⟨c', hc', hc'e⟩ := hsym _ hab
    have : c' = Formalism.L2.Col.cO _ a - Formalism.L2.Col.cO _ b := RingOfIntegers.ext (by
      rw [hc'e]
      show star (((a - b : 𝓞 D.host.E)) : D.host.E) = star (a : D.host.E) - star (b : D.host.E)
      push_cast
      exact star_sub _ _)
    rwa [← this]
  have hcne : ∀ c : 𝓞 D.host.E, c ∉ P'.asIdeal → (c : D.host.E) ≠ 0 := fun c hc0 h0 =>
    hc0 (by rw [show c = 0 from RingOfIntegers.ext h0]; exact zero_mem _)
  have hcb : Formalism.L2.Col.cO _ b ∉ P'.asIdeal := fun hm => hca (by
    have := add_mem hcab hm
    rwa [sub_add_cancel] at this)
  have he'e : idemAt P' * idemAt P' = idemAt P' := he'.1.1
  let za := locU he'e (Units.mk0 _ (hcne _ hca))
  let zb := locU he'e (Units.mk0 _ (hcne _ hcb))
  have hza := step ka (Formalism.L2.Col.cO _ a) (by rw [hka]; exact (star_star (a : D.host.E)).symm) za (locU_val he'e _)
  have hzb := step kb (Formalism.L2.Col.cO _ b) (by rw [hkb]; exact (star_star (b : D.host.E)).symm) zb (locU_val he'e _)
  have heq := chi_locE_congr δ hδ hP' _ _ hca hcab za zb (locU_val he'e _) (locU_val he'e _)
  apply Units.ext
  rw [hza, hzb, heq]

theorem tameAt_conj : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E),
    ChrEq δ.chi χ → ∀ P' ∈ δ.Q, ∀ P : Pl D.host.E, Formalism.IndefR.Lev.IsConjPl P' P → χ.TameAt P := by
  intro D δ hδ χ hc P' hP' P hPP
  exact tameAt_of_congr χ P fun a b ka kb hka hkb ha hab =>
    locK_congr_conj δ hδ χ hc hP' hPP a b ka kb hka hkb ha hab

end GlobalTheory.TameConjPlace
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DeltaGood

theorem coprime_fifteen_of_prime_mod_fifteen_eq_one {q : ℕ} (hq : q.Prime) (hm : q % 15 = 1) : Nat.Coprime 15 q := by
  rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
  intro hd
  have := Nat.le_of_dvd (by norm_num) hd
  have h1 : q = 1 := by omega
  exact hq.one_lt.ne' h1

theorem twistOf_delta_good : ∀ (D : D7) (a : Recip D D.nd.Om), a.Good → ∀ (i : D.ntw.Tw) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (f : D.ntw.O0 i →+* ℂ), Function.Injective f → ∀ b : Bool, (twistOf a f ch (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))).Good := by
  intro D a ha i ch hch f _ b
  classical
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hval : ∀ σ, ψ σ = 1 ↔ D.ntw.delta i σ = 1 := fun σ => by
    cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
  have hopen : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by ext σ; simp only [MonoidHom.mem_ker]; exact hval σ
    rw [this]; exact D.ntw.delta_open i
  have hanti : AntiHom D.ntw.cc ψ := fun g g' h => by
    cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, D.ntw.delta_anti i g g' h]

  set p := if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde with hp
  have hpp : p.Prime ∧ p % 15 = 1 := by
    rw [hp]; split_ifs
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2⟩
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1⟩
  have hmem : ∀ v : Pl D.host.E, v ∈ D.ntw.pD i ↔ ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := fun v => by
    have := D.ntw.pD_eq i
    rw [Set.ext_iff] at this
    exact this v
  have h15 : ∀ P ∈ D.ntw.pD i, ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP h
    have hpP := (hmem P).1 hP
    have hcop : Nat.Coprime 15 p := coprime_fifteen_of_prime_mod_fifteen_eq_one hpp.1 hpp.2
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 hcop
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have : ((u * (15 : ℕ) + w * (p : ℕ) : ℤ) : 𝓞 D.host.E) = 1 := by rw [huw]; simp
    rw [← this]
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by exact_mod_cast h)) (Ideal.mul_mem_left _ _ (by exact_mod_cast hpP))
  have hconj : ∀ P ∈ D.ntw.pD i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.pD i := by
    intro P hP P' hc
    rw [hmem] at hP ⊢
    exact (hc _ _ (by simp)).1 hP
  set Q := half ch (D.ntw.pD i) with hQ
  have hsplit : SplitSet Q := by
    refine GlobalTheory.UnivGood.splitSet_of_split (fun P hP => GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i P (mem_half.1 hP).1) fun P hP P' hP' hc => ?_
    have hne : P ≠ P' := ne_of_split (GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i P (mem_half.1 hP).1) hc
    exact (hch.pair P P' hc hne).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  let g : (D.ntw.O0 i)ˣ →* Circle := unitPart.comp (Units.map f.toMonoidHom)
  have hkey : charOf a f ψ = a.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  show (⟨Q, charOf a f ψ, resOf (charOf a f ψ)⟩ : Twist D Circle).Good
  rw [hkey]
  refine GlobalTheory.T.split_set_inertia_power_trivial D D.nd D.ntw a ha Circle (g.comp ψ) ?_ ?_ Q hsplit ?_ ?_
  · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) hopen
  · intro x x' hx
    show g (ψ x') = (g (ψ x))⁻¹
    rw [hanti x x' hx, map_inv]
  · intro P hP
    have hPD := (mem_half.1 hP).1
    refine ⟨15, h15 P hPD, fun B hB σ hσ => ?_⟩
    have hc := D.ntw.delta_15 i P hPD B hB
    have h1 : D.ntw.delta i σ ^ 15 = 1 := by
      have := pow_card_eq_one' (G := ((Ine (F := D.host.E) B).map (D.ntw.delta i)))
        (x := ⟨D.ntw.delta i σ, Subgroup.mem_map_of_mem _ hσ⟩)
      rw [hc] at this
      exact congrArg Subtype.val this
    have h2 : ψ σ ^ 15 = 1 := by
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h1]
    rw [MonoidHom.comp_apply, ← map_pow, h2, map_one]
  · intro v hv hnc B hB σ hσ
    have hvD : v ∉ D.ntw.pD i := by
      intro hvD
      by_cases hc : v ∈ ch
      · exact hv (mem_half.2 ⟨hvD, hc⟩)
      · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
        have hv'D := hconj v hvD v' hv'
        have hne := ne_of_split (GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i v hvD) hv'
        have hv'c : v' ∈ ch := by
          by_contra h
          exact hc (((hch.pair v v' hv' hne).2 h))
        exact hnc v' (mem_half.2 ⟨hv'D, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
    have h1 : D.ntw.delta i σ = 1 := by
      by_contra h
      exact hvD ((D.ntw.delta_ram i v B hB).1 ⟨σ, hσ, h⟩)
    rw [MonoidHom.comp_apply, (hval σ).2 h1, map_one]

end GlobalTheory.DeltaGood

end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct



namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def embS {D : D7} (S : NX.RatDat D.ntw) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) :
    S.Ks →+* ℂ_[D.ntw.l i] :=
  iC.comp (NX.ιK S i b)

section Ball

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem embC_eKs (a : S.Ks) : embC YS iC b (eKs YS a) = embS S iC b a := by
  simp only [embC, embS, RingHom.comp_apply, sideK_eKs]
  rfl

def locBall : Set (NX.FmK S ((j : ℕ) + 1)) :=
  {f | ∀ z : Pts YS iC b ((j : ℕ) + 1), ‖valC z.1 (cuspOf YS fw j f : T0.R ((j : ℕ) + 1))‖ ≤ 1}

variable {iC b} in
theorem valC_cuspOf_smul (z : FrC YS iC b ((j : ℕ) + 1)) (a : S.Ks) (f : NX.FmK S ((j : ℕ) + 1)) :
    valC z (cuspOf YS fw j (a • f) : T0.R ((j : ℕ) + 1)) = embS S iC b a * valC z (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)) := by
  rw [cuspOf_smul, Submodule.coe_smul, valC_smul, embC_eKs]

end Ball

end GlobalTheory.GeoTie
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct




namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

theorem exists_delta_root {ρ : GlobalTheory.SeriesTie.Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (z : (Formalism.L2.Theta.AE D)ˣ) : ∃ a : FractionRing (D.ntw.O i),
      ρ.e i b a = (((ρ.B i j b).de.chi z : Circle) : ℂ) ∧ ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_, _, hn, ?_⟩
  · rw [hρ.delta i j b]
    exact (GlobalTheory.SeriesTie.charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm
  · rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, map_one, map_one]

section Side

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) (j : Fin D.R.m)

theorem valC_geoHecke {P : PlE D.host} {k : ℕ} (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T0.Q.l P.asIdeal (charAt P))
    (s : T0.Q.c.F) {f g : T0.R ((j : ℕ) + 1)} (hf : f ∈ sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n)
    (hfg : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T0 ((j : ℕ) + 1) P.asIdeal (charAt P) k s f g)
    (z : FrC YS iC b ((j : ℕ) + 1)) (quot : HkKer P.asIdeal (charAt P) k z → FrC YS iC b ((j : ℕ) + 1))
    (hq : ∀ C, IsHkQuot P.asIdeal (charAt P) k z C (quot C)) :
    valC z g = embC YS iC b s * ∑ᶠ C, valC (quot C) f := by
  have hrel := hfg (PAt (embC YS iC b)) z
  have hL : GlobalTheory.Reg.EvLaws (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp _ _ _ _ _ _).1
  have hfun := GlobalTheory.HeckePointLaw.heckePointLaws.2.2.1 _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hP
  have hterm : ∀ C, hkTerm (fun S _ _ => FrPt (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := T0.Q.Xo ((j : ℕ) + 1)) P.asIdeal (charAt P) k Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P.asIdeal (charAt P) k (GlobalTheory.ThetaTrace.hkTr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (charAt P)) Ω y C z)
      f z C = valC (quot C) f := by
    intro C
    have hex : ∃ w, hkRelFr P.asIdeal (charAt P) k (GlobalTheory.ThetaTrace.hkTr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (charAt P))
        (PAt (embC YS iC b)) z C w := ⟨quot C, hq C⟩
    unfold hkTerm
    rw [dite_eq_left hex]
    have hm := hfun (PAt (embC YS iC b)) z C _ _ hex.choose_spec (hq C)
    exact (GlobalTheory.Reg.PChartModel.evR_map hL hf.1 (AlgHom.id _ _) hm).symm
  change toCp _ (evR (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c g z) = _
  unfold evR
  rw [hrel, map_mul, toCp_algebraMap]
  congr 1
  unfold hkVal
  exact finsum_congr hterm

end Side

end GlobalTheory.GeoTie
end
end
