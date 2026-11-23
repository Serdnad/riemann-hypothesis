module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle055
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle009
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem subring_eq_of_isLocalization_atPrime {F : Type*} [Field F] {B R₁ R₂ : Subring F}
    (h₁ : B ≤ R₁) (h₂ : B ≤ R₂) (𝔭 : Ideal B) [𝔭.IsPrime]
    (hl₁ : letI := (Subring.inclusion h₁).toAlgebra; IsLocalization.AtPrime R₁ 𝔭)
    (hl₂ : letI := (Subring.inclusion h₂).toAlgebra; IsLocalization.AtPrime R₂ 𝔭) : R₁ = R₂ := by
  have key : ∀ (R₁ R₂ : Subring F) (h₁ : B ≤ R₁) (h₂ : B ≤ R₂),
      (letI := (Subring.inclusion h₁).toAlgebra; IsLocalization.AtPrime R₁ 𝔭) →
      (letI := (Subring.inclusion h₂).toAlgebra; IsLocalization.AtPrime R₂ 𝔭) → R₁ ≤ R₂ := by
    intro R₁ R₂ h₁ h₂ hl₁ hl₂ z hz
    let _ := (Subring.inclusion h₁).toAlgebra
    let _ := (Subring.inclusion h₂).toAlgebra
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔭.primeCompl (⟨z, hz⟩ : R₁)
    obtain ⟨t, ht⟩ := (IsLocalization.map_units R₂ s).exists_right_inv
    have e₁ : z * ((s : B) : F) = ((b : B) : F) := congrArg Subtype.val hbs
    have e₂ : ((s : B) : F) * (t : F) = 1 := congrArg Subtype.val ht
    have hzt : z = (b : F) * t := by
      calc z = z * (((s : B) : F) * t) := by rw [e₂, mul_one]
        _ = (z * ((s : B) : F)) * t := by ring
        _ = (b : F) * t := by rw [e₁]
    rw [hzt]
    exact R₂.mul_mem (h₂ b.2) t.2
  exact le_antisymm (key R₁ R₂ h₁ h₂ hl₁ hl₂) (key R₂ R₁ h₂ h₁ hl₂ hl₁)

theorem prime_eq_of_isLocalization_atPrime {F : Type*} [Field F] {B R : Subring F} (h : B ≤ R)
    (𝔭₁ 𝔭₂ : Ideal B) [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (hl₁ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₁)
    (hl₂ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₂) : 𝔭₁ = 𝔭₂ := by
  let _ := (Subring.inclusion h).toAlgebra
  have := hl₁
  have := hl₂
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔭₁
  rw [← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₁ inferInstance,
    ← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₂ inferInstance]

theorem BlowUpOverLocMax.proof (h₁ : BlowUpOverLocMaxPoint.Statement.{u})
    (h₂ : BlowUpOverLocPointMax.Statement.{u}) (h₃ : BlowUpLocRingInj.Statement.{u}) :
    BlowUpOverLocMax.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  have hpt := h₁ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have hmx := h₂ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  choose f hfT hfloc hfdeg using
    fun 𝔫 : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal} => hpt 𝔫.1 𝔫.2

  have hmh : ∀ W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes, IsMultiHomogIdeal W' :=
    fun W' hW' => MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  refine ⟨Equiv.ofBijective (fun 𝔫 => ⟨f 𝔫, hfT 𝔫⟩) ⟨?_, ?_⟩, fun 𝔫 => ⟨hfloc 𝔫, hfdeg 𝔫⟩⟩
  ·
    intro 𝔫₁ 𝔫₂ h12
    have hf : f 𝔫₁ = f 𝔫₂ := congrArg Subtype.val h12
    have hl₁ := hfloc 𝔫₁
    rw [hf] at hl₁
    obtain ⟨k₁, l₁⟩ := hl₁
    obtain ⟨k₂, l₂⟩ := hfloc 𝔫₂
    have := 𝔫₁.2.isPrime
    have := 𝔫₂.2.isPrime
    exact Subtype.ext (prime_eq_of_isLocalization_atPrime k₂ 𝔫₁.1 𝔫₂.1 l₁ l₂)
  ·
    rintro ⟨W', hW'⟩
    obtain ⟨k, 𝔫, h𝔫, hl⟩ := hmx W' hW'.1 hW'.2.1 hW'.2.2
    refine ⟨⟨𝔫, h𝔫⟩, Subtype.ext ?_⟩
    obtain ⟨k', hl'⟩ := hfloc ⟨𝔫, h𝔫⟩
    have := h𝔫.isPrime
    have hring : blowUpLocRing P u (f ⟨𝔫, h𝔫⟩) = blowUpLocRing P u W' :=
      subring_eq_of_isLocalization_atPrime k' k 𝔫 hl' hl
    have hT := hfT ⟨𝔫, h𝔫⟩
    exact h₃ O K ι J P u _ _ hT.1.1.1 (hmh _ hT.1) hT.2.1 (le_trans le_sup_left hT.1.1.2)
      hW'.1.1.1 (hmh _ hW'.1) hW'.2.1 (le_trans le_sup_left hW'.1.1.2) hring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocFibreMinimal.proof (h₁ : BlowUpOverLocPointLoc.Statement.{u})
    (h₂ : BlowUpLocRingInj.Statement.{u}) : BlowUpOverLocFibreMinimal.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  have := hP.multiProj.isPrime
  have hxW : x ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  have hxW' : liftForm x ∈ W' := by
    rw [← Ideal.mem_comap, hW'c]
    exact hxW
  have hle : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ W' :=
    sup_le hW'le ((Ideal.span_singleton_le_iff_mem _).mpr hxW')
  refine ⟨⟨hW'p, hle⟩, fun Q hQ hQW' => ?_⟩
  have := hQ.1
  obtain ⟨Q₀, hQ₀min, hQ₀Q⟩ := Ideal.exists_minimalPrimes_le hQ.2
  have hQ₀W' : Q₀ ≤ W' := hQ₀Q.trans hQW'
  have hQ₀p : Q₀.IsPrime := hQ₀min.1.1
  have hQ₀h : IsMultiHomogIdeal Q₀ :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ Q₀
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hQ₀min
  have hQ₀r : IsRelevant Q₀ := fun k => by
    obtain ⟨i, hi⟩ := hW'r k
    exact ⟨i, fun h => hi (hQ₀W' h)⟩
  have hQ₀le : blowUpOf P u ≤ Q₀ := le_sup_left.trans hQ₀min.1.2
  have hQ₀c : Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) = W := by
    obtain ⟨hcp, hPc, -, -⟩ := comap_liftForm_facts hQ₀p hQ₀le hQ₀r
    have hxc : x ∈ Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) :=
      hQ₀min.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hcW : Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := hW'c ▸ Ideal.comap_mono hQ₀W'
    exact le_antisymm hcW (hWmin.2 ⟨hcp, sup_le hPc ((Ideal.span_singleton_le_iff_mem _).mpr hxc)⟩ hcW)
  obtain ⟨h, 𝔫, h𝔫, hl⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  obtain ⟨h₀, 𝔮, h𝔮, hl₀⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel Q₀ hQ₀p hQ₀h hQ₀r hQ₀le hQ₀c
  have hsub : blowUpLocRing P u W' ≤ blowUpLocRing P u Q₀ := by
    refine Subring.closure_mono ?_
    rintro z ⟨b, F, G, hF, hG, hGW', hz⟩
    exact ⟨b, F, G, hF, hG, fun hGQ => hGW' (hQ₀W' hGQ), hz⟩
  let _ := (Subring.inclusion h).toAlgebra
  let _ := (Subring.inclusion h₀).toAlgebra
  have := h𝔫.isPrime
  have := h𝔮.isPrime
  have : IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫 := hl
  have : IsLocalization.AtPrime (blowUpLocRing P u Q₀) 𝔮 := hl₀
  have : IsLocalRing (blowUpLocRing P u Q₀) := IsLocalization.AtPrime.isLocalRing _ 𝔮
  have hq : 𝔮 ≤ 𝔫 := by
    intro s hs
    by_contra hsn
    have hu1 : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') s) :=
      IsLocalization.map_units (M := 𝔫.primeCompl) _ ⟨s, hsn⟩
    have hu2 : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u Q₀) s) :=
      hu1.map (Subring.inclusion hsub)
    have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff (blowUpLocRing P u Q₀) 𝔮 s).mpr hs
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu2
  have hqn : 𝔮 = 𝔫 := h𝔮.eq_of_le h𝔫.ne_top hq
  have hsup : blowUpLocRing P u Q₀ ≤ blowUpLocRing P u W' := by
    intro z hz
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl
      (⟨z, hz⟩ : blowUpLocRing P u Q₀)
    replace hbs : IsLocalization.mk' (blowUpLocRing P u Q₀) b s = ⟨z, hz⟩ := hbs
    have hs : (s : blowUpOverLoc P W u) ∈ 𝔫.primeCompl := hqn ▸ s.2
    obtain ⟨v, hv⟩ : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') s) :=
      IsLocalization.map_units (M := 𝔫.primeCompl) _ ⟨s, hs⟩
    have e1 : z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) =
        ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) := by
      have := congrArg Subtype.val (IsLocalization.mk'_spec (blowUpLocRing P u Q₀) b s)
      rw [hbs] at this
      exact this
    have e2 : ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) *
        (((v⁻¹ : (blowUpLocRing P u W')ˣ) : blowUpLocRing P u W') : FractionRing (MRing ι O ⧸ P)) = 1 := by
      have := congrArg Subtype.val v.mul_inv
      rw [hv] at this
      exact this
    have e3 : z = ((algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') b *
        ((v⁻¹ : (blowUpLocRing P u W')ˣ) : blowUpLocRing P u W') : blowUpLocRing P u W') :
          FractionRing (MRing ι O ⧸ P)) := by
      rw [Subring.coe_mul, ← mul_one z, ← e2, ← mul_assoc, e1]
      rfl
    rw [e3]
    exact Subtype.property _
  have heq : Q₀ = W' :=
    h₂ O K ι J P u Q₀ W' hQ₀p hQ₀h hQ₀r hQ₀le hW'p hW'h hW'r hW'le (le_antisymm hsup hsub)
  rw [← heq]
  exact hQ₀Q

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem blowUpEval_ne_zero_of_not_mem {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {O : Type u}
    [CommRing O] {P : Ideal (MRing ι O)} [P.IsPrime] {u : J → MRing ι O} {F : MRing (extIdx ι J) O}
    {b : Option K → ℕ} (hF : IsMultiHomog F b) (hFb : F ∉ blowUpOf P u) :
    algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  intro h
  apply hFb
  show F ∈ RingHom.ker (aeval (blowUpSubst P u))
  rw [RingHom.mem_ker]
  show aeval (blowUpSubst P u) F = 0
  rw [aeval_blowUpSubst_of_isMultiHomog P u hF, h, map_zero, zero_mul]

theorem div_mul_div_mul_cancel_of_ne_zero {F : Type*} [Field F] (a b c w : F) (hb : b ≠ 0) :
    a / b * (b / c * w) = a / c * w := by
  rw [← mul_assoc, div_mul_div_comm, mul_comm a b, mul_div_mul_left _ _ hb]

theorem BlowUpOverLocPointLoc.proof (hfin : BlowUpOverLocFinite.Statement.{u})
    (hcen : BlowUpOverLocMaxCentre.Statement.{u}) (hinj : BlowUpLocRingInj.Statement.{u}) :
    BlowUpOverLocPointLoc.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW'p hmh hW'rel hbl hW'W
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' :=
    iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof O K ι J P u W' hbl
  obtain ⟨hlocT, hunitT⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hWp : W.IsPrime := hWmin.1.1
  obtain ⟨hlocA, hunitA⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  let 𝔫 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)

  have hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (homLocRing P W) ≤
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rintro ⟨z, hz⟩ ha
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
      obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (HomLocRingMem.proof O K ι P W hWp hPW z).mp hz
      have hfW : f ∈ W := by
        by_contra hfW
        exact ha ((hunitA b f g hf hg hgW hz).mpr hfW)
      have hgW' : liftForm (J := J) g ∉ W' := fun h => hgW (by rw [← hW'W]; exact h)
      have hfW' : liftForm (J := J) f ∈ W' := by rw [← hW'W] at hfW; exact hfW
      have hlf := isMultiHomog_liftForm (J := J) hf
      have hlg := isMultiHomog_liftForm (J := J) hg
      have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm f)) /
          algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
          homLocRing (blowUpOf P u) W' :=
        Subring.subset_closure ⟨liftMDeg b, _, _, hlf, hlg, hgW', rfl⟩
      have hnu : ¬ IsUnit (⟨_, hz'⟩ : homLocRing (blowUpOf P u) W') :=
        fun h => (hunitT _ _ _ hlf hlg hgW' hz').mp h hfW'
      have hφz : Subring.inclusion hBR (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩) =
          φ ⟨_, hz'⟩ := by
        apply Subtype.ext
        rw [hφ _ _ _ hlf hlg hgW', blowUpEval_liftForm, blowUpEval_liftForm]
        rfl
      rw [Ideal.mem_comap, Ideal.mem_comap, hφz, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_map_iff]
      exact hnu
    have hne : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) ≠ ⊤ :=
      Ideal.comap_ne_top _ (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hne) hle]
    infer_instance
  obtain ⟨hfinite, -⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have h𝔫 : 𝔫.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (Algebra.IsIntegral.isIntegral) 𝔫 hcomapA
  refine ⟨hBR, 𝔫, h𝔫, ?_⟩

  obtain ⟨W₁, hW₁p, hW₁h, hW₁r, hW₁b, -, h₁, hl₁⟩ :=
    hcen O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  let _ := (Subring.inclusion h₁).toAlgebra
  have := h𝔫.isPrime
  have hl : IsLocalization.AtPrime (blowUpLocRing P u W₁) 𝔫 := hl₁

  have hunitB : ∀ s : blowUpOverLoc P W u, s ∉ 𝔫 → IsUnit (Subring.inclusion hBR s) := by
    intro s hs
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)

  have h3 : blowUpLocRing P u W₁ ≤ blowUpLocRing P u W' := by
    intro z hz
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔫.primeCompl (⟨z, hz⟩ : blowUpLocRing P u W₁)
    obtain ⟨t, ht⟩ := (hunitB s s.2).exists_right_inv
    have e₁ : z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) :=
      congrArg Subtype.val hbs
    have e₂ : ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * (t : FractionRing (MRing ι O ⧸ P)) = 1 := congrArg Subtype.val ht
    have hzt : z = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t := by
      calc z = z * (((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t) := by rw [e₂, mul_one]
        _ = (z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P))) * t := by ring
        _ = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t := by rw [e₁]
    rw [hzt]
    exact (blowUpLocRing P u W').mul_mem (hBR b.2) t.2

  have hdom : ∀ (y : FractionRing (MRing ι O ⧸ P)) (hy₁ : y ∈ blowUpLocRing P u W₁) (hy' : y ∈ blowUpLocRing P u W'),
      IsUnit (⟨y, hy'⟩ : blowUpLocRing P u W') → IsUnit (⟨y, hy₁⟩ : blowUpLocRing P u W₁) := by
    intro y hy₁ hy' hyu
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔫.primeCompl (⟨y, hy₁⟩ : blowUpLocRing P u W₁)
    have e₁ : y * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) :=
      congrArg Subtype.val hbs
    have hb : b ∉ 𝔫 := by
      intro hb
      have hb' : Subring.inclusion hBR b ∈ IsLocalRing.maximalIdeal (blowUpLocRing P u W') := hb
      apply (IsLocalRing.mem_maximalIdeal _).mp hb'
      have hprod : Subring.inclusion hBR b = (⟨y, hy'⟩ : blowUpLocRing P u W') * Subring.inclusion hBR s :=
        Subtype.ext e₁.symm
      rw [hprod]
      exact hyu.mul (hunitB s s.2)
    have hbu : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W₁) b) :=
      IsLocalization.map_units (M := 𝔫.primeCompl) _ (⟨b, hb⟩ : 𝔫.primeCompl)
    rw [← hbs] at hbu
    exact isUnit_of_mul_isUnit_left hbu

  have h5 : blowUpLocRing P u W' ≤ blowUpLocRing P u W₁ := by
    refine Subring.closure_le.mpr ?_
    rintro z ⟨d, F, G, hF, hG, hGW', rfl⟩
    obtain ⟨i, hi⟩ := powMonomial_not_mem hW₁p hW₁r d
    have hH := isMultiHomog_powMonomial (R := O) d i
    have hσH : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ≠ 0 :=
      blowUpEval_ne_zero_of_not_mem hH (fun h => hi (hW₁b h))
    have hσG : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) ≠ 0 := blowUpEval_ne_zero_of_not_mem hG (fun h => hGW' (hbl h))
    have hy₁ : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ∈ blowUpLocRing P u W₁ :=
      Subring.subset_closure ⟨d, G, _, hG, hH, hi, rfl⟩
    have hFH : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ∈ blowUpLocRing P u W₁ :=
      Subring.subset_closure ⟨d, F, _, hF, hH, hi, rfl⟩
    have hinv : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) ∈ blowUpLocRing P u W' :=
      Subring.subset_closure ⟨d, _, G, hH, hG, hGW', rfl⟩
    have hyu : IsUnit (⟨_, h3 hy₁⟩ : blowUpLocRing P u W') := by
      refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : blowUpLocRing P u W') (Subtype.ext ?_)
      show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) * (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G)) = 1
      field_simp
    obtain ⟨v, hv⟩ := hdom _ hy₁ (h3 hy₁) hyu
    have e : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
        (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) = 1 := by
      have := congrArg Subtype.val v.mul_inv
      rw [hv] at this
      exact this
    have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
        (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) := by
      calc algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G)
          = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) * (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
            (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P))) := by rw [e, mul_one]
        _ = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
            (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) :=
          div_mul_div_mul_cancel_of_ne_zero _ _ _ _ hσG
    rw [hz]
    exact (blowUpLocRing P u W₁).mul_mem hFH (Subtype.property _)
  have heq : W₁ = W' :=
    hinj O K ι J P u W₁ W' hW₁p hW₁h hW₁r hW₁b hW'p hmh hW'rel hbl (le_antisymm h3 h5)
  subst heq
  exact hl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem LeftSideAdditiveInDegree.proof
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (d : ℕ) (hP : IsModelOver P (d + 1))
    (b : K → ℤ) (f g : MRing ι O) (hD : IsVerticalDivisor P ϖ b f g)
    (c₁ c₂ : K → ℕ) (L : Fin d → K → ℤ) :
    cutIdentityLeftSide P f g (c₁ + c₂) L =
      cutIdentityLeftSide P f g c₁ L + cutIdentityLeftSide P f g c₂ L := by
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → ∀ W, divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    intro h e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨MinimalPrimeMultiHomog.full O K ι _ W (SupSpanMultiHomog.full O K ι P h e hPmh he) hW'.1,
        hW'.1.1.1, le_sup_left.trans hW'.1.1.2⟩
    · exact absurd rfl hW

  have hadd : ∀ W, ratDiv P f g W ≠ 0 →
      vNum W (Matrix.vecCons (fun k => ((c₁ + c₂) k : ℤ)) L) =
        vNum W (Matrix.vecCons (fun k => (c₁ k : ℤ)) L) +
          vNum W (Matrix.vecCons (fun k => (c₂ k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    obtain ⟨hWm, hWp, hPW⟩ : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · exact hmh g bg hbg W fun hWg => hW (by simp [ratDiv, hWf, hWg])
      · exact hmh f bf hbf W hWf
    have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
    have hdrop := DimStrictDrop.full (MRing ι O) P W hlt
    rw [hP.dim] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [SpecialQuotDim.full O ϖ hϖ K ι W hϖW]
      have e : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [e] at hdrop
      exact lt_natCast_of_add_one_le hdrop
    have key := IntNumAddFirst.full (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWm)
      hdim (fun k => (c₁ k : ℤ)) (fun k => (c₂ k : ℤ)) L
    have hsum : (fun k => ((c₁ + c₂) k : ℤ)) = (fun k => (c₁ k : ℤ)) + (fun k => (c₂ k : ℤ)) := by
      funext k; simp
    unfold vNum
    rw [hsum, key]
  have hZfin := ratDiv_support_finite DivCycleFiniteSupport.full P f g
  unfold cutIdentityLeftSide cycEval
  rw [← finsum_add_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
    (hZfin.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  · beta_reduce
    rw [hadd W hW, mul_add]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
