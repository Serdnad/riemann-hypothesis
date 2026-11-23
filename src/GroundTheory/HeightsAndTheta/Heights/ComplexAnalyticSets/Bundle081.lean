module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PLengthDecomp
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem isCohenMacaulayLocalRing_of_minimalPrimes_sup_span {R : Type*} [CommRing R] [IsNoetherianRing R]
    {J W : Ideal R} {g : R} [J.IsPrime] [W.IsPrime] (hg : g ∉ J)
    (hW : W ∈ (J ⊔ Ideal.span {g}).minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hgW : g ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ W := by rwa [Ideal.mk_ker]
  set W' : Ideal (R ⧸ J) := W.map (Ideal.Quotient.mk J) with hW'
  have : W'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : W'.comap (Ideal.Quotient.mk J) = W := by
    rw [hW', Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker]
  have hmem : ∀ a : R, Ideal.Quotient.mk J a ∈ W' ↔ a ∈ W := fun a => by
    rw [← Ideal.mem_comap, hcomap]
  have hsub : W.primeCompl.map (Ideal.Quotient.mk J) = W'.primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · intro hx
      obtain ⟨b, hb, hba⟩ := Submonoid.mem_map.mp hx
      change Ideal.Quotient.mk J a ∉ W'
      rw [← hba, hmem]
      exact hb
    · intro ha
      exact Submonoid.mem_map.mpr ⟨a, fun h => ha ((hmem a).mpr h), rfl⟩
  have hloc : IsLocalization.AtPrime (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      W' := by
    have h := Vertical.SpecChart.isLocalization_quot W J
    rw [hsub] at h
    exact h
  have : IsLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.AtPrime.isLocalRing _ W'
  have : IsDomain (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors W')
  set x := algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
    (Ideal.Quotient.mk J g) with hx
  have hg0 : Ideal.Quotient.mk J g ≠ 0 := fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hx0 : x ≠ 0 := by
    intro h
    apply hg0
    have h0 : x = algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) 0 := by
      rw [map_zero]
      exact h
    exact IsLocalization.injective (S := Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors W') h0
  have hxm : x ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W']
    exact Ideal.mem_map_of_mem _ ((hmem g).mpr hgW)
  have hheight : W'.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hW) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h
    apply hg0
    rw [← Ideal.mem_bot, ← h]
    exact (hmem g).mpr hgW
  refine { exists_isWeaklyRegular := ⟨[x], ?_, ?_, ?_⟩ }
  · intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hxm
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    intro a b hab
    simp only [smul_eq_mul] at hab
    exact mul_left_cancel₀ hx0 hab
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height W', hheight]
    simp

theorem CMHeightOneGeneral.proof (hopen : CMLocusOpen.Statement) : CMHeightOneGeneral.Statement := by
  intro n J W g hJ hg hW
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  obtain ⟨f, hfW, hf⟩ := hopen n J W hJW (isCohenMacaulayLocalRing_of_minimalPrimes_sup_span hg hW)
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := fun p hp =>
    RingHom.mem_ker.mpr (hq p hp)
  exact hf _ (hJW.trans hWq) (fun h => hfq (RingHom.mem_ker.mp h))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem CurveMinimalPrimeQuotient.proof : CurveMinimalPrimeQuotient.Statement := by
  intro n I q p hp
  have hpP : p.IsPrime := hp.1.1

  let ext : Ideal (MvPolynomial (Fin n) ℂ) → Ideal (Localization.AtPrime (RingHom.ker (eval q))) :=
    fun K ↦ K.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  let mk := Ideal.Quotient.mk (ext I)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomp : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) =
      mk.comp (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) := rfl

  let P : Ideal (Localization.AtPrime (RingHom.ker (eval q))) := p.comap mk
  have hPP : P.IsPrime := Ideal.comap_isPrime mk p
  have hIP : ext I ≤ P := fun x hx ↦ by
    change mk x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact p.zero_mem
  have hpmap : P.map mk = p := Ideal.map_comap_of_surjective mk hmk p
  let J : Ideal (MvPolynomial (Fin n) ℂ) :=
    P.comap (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  have hJP : J.IsPrime := Ideal.comap_isPrime _ P
  have hJmem : ∀ f, f ∈ J ↔ algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ p := fun f ↦ by
    rw [hcomp]; rfl
  have hextJ : ext J = P := IsLocalization.map_under (RingHom.ker (eval q)).primeCompl _ P
  have hIJ : I ≤ J := fun f hf ↦ hIP (Ideal.mem_map_of_mem _ hf)
  have hJm : J ≤ RingHom.ker (eval q) := by
    intro f hf
    by_contra h
    exact hpP.ne_top (Ideal.eq_top_of_isUnit_mem _ ((hJmem f).1 hf)
      (isUnit_algebraMap_curveLocalRing I q f fun h' ↦ h (RingHom.mem_ker.2 h')))

  have hJmin : J ∈ I.minimalPrimes := by
    refine ⟨⟨hJP, hIJ⟩, fun J' hJ' hJ'J ↦ ?_⟩
    obtain ⟨hJ'P, hIJ'⟩ := hJ'
    have hdisj : Disjoint ((RingHom.ker (eval q)).primeCompl : Set (MvPolynomial (Fin n) ℂ)) J' :=
      Set.disjoint_left.2 fun x hx hx' ↦ hx (hJm (hJ'J hx'))
    have hP'P : (ext J').IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl _ J' hJ'P hdisj
    have hIP' : ext I ≤ ext J' := Ideal.map_mono hIJ'
    have hker : RingHom.ker mk ≤ ext J' := by
      rw [Ideal.mk_ker]; exact hIP'
    have hp'P : ((ext J').map mk).IsPrime := Ideal.map_isPrime_of_surjective hmk hker
    have hp'le : (ext J').map mk ≤ p := by
      rw [← hpmap, ← hextJ]
      exact Ideal.map_mono (Ideal.map_mono hJ'J)
    have hpp' : p ≤ (ext J').map mk := hp.2 ⟨hp'P, bot_le⟩ hp'le
    intro f hf
    have h1 : mk (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) f) ∈ (ext J').map mk :=
      hpp' ((hJmem f).1 hf)
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective mk hmk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.2 hIP'] at h1
    have h2 := (IsLocalization.under_map_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl
      (Localization.AtPrime (RingHom.ker (eval q))) hJ'P hdisj)
    rw [← h2]
    exact h1

  have hle : ext I ≤ ext J := Ideal.map_mono hIJ
  refine ⟨J, hJmin, hJm, (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q),
    Ideal.Quotient.factor_surjective hle, ?_, fun f ↦ Ideal.Quotient.factor_mk hle _⟩
  change RingHom.ker (Ideal.Quotient.factor hle) = p
  rw [Ideal.Quotient.factor_ker, hextJ]
  exact hpmap

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem withBot_enat_le_zero_of_add_one_le_one {x : WithBot ℕ∞} (h : x + 1 ≤ 1) : x ≤ 0 := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    have h' : e + 1 ≤ 1 := by exact_mod_cast h
    have : e ≤ 0 := by
      induction e using ENat.recTopCoe with
      | top => simp at h'
      | coe k =>
        have hk : k + 1 ≤ 1 := by exact_mod_cast h'
        exact_mod_cast (show k ≤ 0 by omega)
    exact_mod_cast this

theorem CurveNormalisationQuotientLength.proof (hF : CurveNormalisationFinite.Statement) :
    CurveNormalisationQuotientLength.Statement := by
  intro n I q hrad hdim
  set O := curveLocalRing I q
  set N := curveNormalisation I q
  set M := N ⧸ LinearMap.range (Algebra.linearMap O N)
  have hfin : Module.Finite O N := hF n I q hrad

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := N)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s
    (fun x : N ↦ ((show ↥(integralClosure O (FractionRing O)) from x) : FractionRing O))
  have hmul : ∀ y : N, (b : O) • y ∈ LinearMap.range (Algebra.linearMap O N) := by
    intro y
    have hle : Submodule.span O (s : Set N) ≤
        (LinearMap.range (Algebra.linearMap O N)).comap ((b : O) • LinearMap.id) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨a, ha⟩ := hb x hx
      refine ⟨a, Subtype.ext ?_⟩
      exact ha
    exact hle (hs ▸ Submodule.mem_top : y ∈ Submodule.span O (s : Set N))
  have hann : (b : O) ∈ Module.annihilator O M := by
    rw [Module.mem_annihilator]
    intro m
    induction m using Submodule.Quotient.induction_on with
    | H y => rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hmul y

  have hd := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (Module.annihilator O M))
    Ideal.Quotient.mk_surjective b.2 (Ideal.Quotient.eq_zero_iff_mem.2 hann)
  rw [hdim] at hd
  have : Ring.KrullDimLE 0 (O ⧸ Module.annihilator O M) :=
    Ring.krullDimLE_iff.2 (by exact_mod_cast withBot_enat_le_zero_of_add_one_le_one hd)
  have : IsArtinianRing (O ⧸ Module.annihilator O M) := isArtinianRing_iff_krullDimLE_zero.2 inferInstance
  let := Module.quotientAnnihilator (R := O) (M := M)
  have := (Module.isTorsionBySet_annihilator O M).isScalarTower (S := O)
  have : Module.Finite (O ⧸ Module.annihilator O M) M := Module.Finite.of_restrictScalars_finite O _ _
  have : IsArtinian O M := isArtinian_of_surjective_algebraMap (S := O) (R := O ⧸ Module.annihilator O M)
    (show Function.Surjective (algebraMap O (O ⧸ Module.annihilator O M)) from Ideal.Quotient.mk_surjective)
  exact Module.length_ne_top

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem CurveResidueDegree.proof : CurveResidueDegree.Statement := by
  intro n I q _ hdim P
  have := P.isMaximal
  let _ : Field (curveNormalisation I q ⧸ P.asIdeal) := Ideal.Quotient.field _

  have hO : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)

  have hIq : ∀ g ∈ I, eval q g = 0 := by
    intro g hg
    by_contra hgq
    have hu := isUnit_algebraMap_curveLocalRing I q g hgq
    have h0 : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) g = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
    rw [h0] at hu
    exact not_isUnit_zero hu

  let evL : Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) →+* ℂ :=
    IsLocalization.lift (M := (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl) (g := eval q)
      (fun s ↦ isUnit_iff_ne_zero.2 fun h ↦ s.2 (RingHom.mem_ker.2 h))
  have hJ : ∀ a ∈ I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))), evL a = 0 := by
    intro a ha
    have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ)
        (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))) ≤ RingHom.ker evL := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      simp [evL, IsLocalization.lift_eq, hIq g hg]
    exact hle ha
  let ε : curveLocalRing I q →+* ℂ := Ideal.Quotient.lift _ evL hJ
  let K := curveNormalisation I q ⧸ P.asIdeal
  let π : curveLocalRing I q →+* K := algebraMap (curveLocalRing I q) K
  let ι : ℂ →+* K := π.comp ((algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)).comp C)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  have hmax : (P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
  have hmax' := Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))))))
    Ideal.Quotient.mk_surjective (K := P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q)))
    (H := hmax)
  have hloc := IsLocalRing.eq_maximalIdeal hmax'
  have hker : ∀ a ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ),
      π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) a) = 0 := by
    intro a ha
    rw [← Localization.AtPrime.under_maximalIdeal (I := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)),
      Ideal.under, Ideal.mem_comap, ← hloc] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha

  have hcomp : π = ι.comp ε := by
    refine Ideal.Quotient.ringHom_ext ?_
    refine IsLocalization.ringHom_ext (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl ?_
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) =
        ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)))
      have he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) = c := by
        show evL (algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (C c)) = c
        simp [evL, IsLocalization.lift_eq]
      rw [he]
      rfl
    · have h1 : (X i - C (q i) : MvPolynomial (Fin n) ℂ) ∈ RingHom.ker (eval q) := by simp
      have h2 := hker _ h1
      rw [map_sub, map_sub, sub_eq_zero] at h2
      show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) =
        ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)))
      have he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) = q i := by
        show evL (algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (X i)) = q i
        simp [evL, IsLocalization.lift_eq]
      rw [he]
      exact h2

  have hint : ι.IsIntegral := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hb : IsIntegral (curveLocalRing I q) b := Algebra.IsIntegral.isIntegral b
    obtain ⟨p, hp, he⟩ := hb.map (Ideal.Quotient.mkₐ (curveLocalRing I q) P.asIdeal)
    refine ⟨p.map ε, hp.map ε, ?_⟩
    rw [Polynomial.eval₂_map, ← hcomp]
    exact he
  have hsurj : Function.Surjective ι := (IsAlgClosed.ringHom_bijective_of_isIntegral ι hint).2
  have hπ : Function.Surjective π := fun y ↦ by
    obtain ⟨c, hc⟩ := hsurj y
    exact ⟨_, hc⟩

  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, fun x hx y ↦ ?_⟩
  obtain ⟨r, hr⟩ := hπ (y * x⁻¹)
  refine ⟨r, ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  change π r * x = y
  rw [hr, mul_assoc, inv_mul_cancel₀ hx, mul_one]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

theorem length_quotient_sup_span {L : Type} [CommRing L] (J : Ideal L) (g : L) :
    Module.length L (L ⧸ (J ⊔ Ideal.span {g})) =
      Module.length (L ⧸ J) ((L ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J g}) := by
  have hK : (Ideal.span {g}).map (Ideal.Quotient.mkₐ L J) = Ideal.span {Ideal.Quotient.mk J g} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← (DoubleQuot.quotQuotEquivQuotSupₐ L J (Ideal.span {g})).toLinearEquiv.length_eq, hK]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem length_localization_eq_length_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    Module.length (Localization.AtPrime (RingHom.ker (eval q)))
        (Localization.AtPrime (RingHom.ker (eval q)) ⧸ (I ⊔ Ideal.span {f}).map
          (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))) =
      Module.length (curveLocalRing I q)
        (curveLocalRing I q ⧸ Ideal.span {algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f}) := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact length_quotient_sup_span _ _

theorem length_quotient_ne_top {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (hdim : ringKrullDim O = 1) {x : O} (hx : x ∈ nonZeroDivisors O) :
    Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ := by
  by_cases hm : x ∈ IsLocalRing.maximalIdeal O
  · have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hx hm
    rw [hdim] at h
    have h0 : ringKrullDim (O ⧸ Ideal.span {x}) ≤ (0 : ℕ) := by
      generalize ringKrullDim (O ⧸ Ideal.span {x}) = d at h ⊢
      induction d using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe k =>
        have h' : k + 1 = 1 := by exact_mod_cast h
        induction k using ENat.recTopCoe with
        | top => simp at h'
        | coe m =>
          have hm : m + 1 = 1 := by exact_mod_cast h'
          have : m = 0 := by omega
          subst this
          simp
    have : Ring.KrullDimLE 0 (O ⧸ Ideal.span {x}) := Ring.krullDimLE_iff.2 h0
    have := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := O ⧸ Ideal.span {x})
    rw [Module.length_eq_of_surjective (R := O ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective]
    exact Module.length_ne_top
  · have hu : IsUnit x := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hm
    rw [Ideal.span_singleton_eq_top.2 hu,
      Module.length_eq_zero_iff.2 (Ideal.Quotient.subsingleton_iff.2 rfl)]
    exact ENat.zero_ne_top

theorem CurveNormalisationLength.proof (hFin : CurveNormalisationFinite.Statement)
    (hQ : CurveNormalisationQuotientLength.Statement) (hE : ExtensionQuotientLength.Statement) :
    CurveNormalisationLength.Statement := by
  intro n I q f hrad hdim hf
  set O := curveLocalRing I q
  set f' := algebraMap (MvPolynomial (Fin n) ℂ) O f
  have : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing O := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : Module.Finite O (curveNormalisation I q) := hFin n I q hrad
  have hfin := length_quotient_ne_top hdim hf

  have hnzd : algebraMap O (curveNormalisation I q) f' ∈ nonZeroDivisors (curveNormalisation I q) := by
    let ι : curveNormalisation I q →+* FractionRing O :=
      (integralClosure O (FractionRing O)).val.toRingHom
    refine mem_nonZeroDivisors_of_injective (f := ι) Subtype.val_injective ?_
    exact (IsLocalization.map_units (FractionRing O) (⟨f', hf⟩ : nonZeroDivisors O)).mem_nonZeroDivisors
  have hEq := hE O (curveNormalisation I q) f' (algebraMap_curveNormalisation_injective I q) hnzd
    (hQ n I q hrad hdim)
  rw [localMult, dite_eq_left (isPrime_ker_eval q), length_localization_eq_length_curveLocalRing,
    ENat.natCast_toNat hfin, hEq]
  exact GroundTheory.Heights₂.Heights.Vertical.LengthDecomp.proof O (curveNormalisation I q) _ (hEq ▸ hfin)

end

end GroundTheory.Heights₂.Heights
end
