module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.Length

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem zero_le_divCycle {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) (W : Ideal (MRing ι R)) : 0 ≤ divCycle P f W := by
  unfold divCycle
  split_ifs <;> positivity

theorem BlowUpExcessDecreases.proof (hpos : ExcessPositive.Statement.{u})
    (hres : ResidualComparison.Statement.{u}) (hexc : ExceptionalComparison.Statement.{u}) :
    BlowUpExcessDecreases.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH hcommon
  set N := commonExcess ϖ P f g s with hN
  have hε : 0 < N := hpos O ϖ hϖ K ι P d hP b f g hD s hsP hcommon

  have hbdd : BddAbove (Set.range fun G : {G : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G} =>
      (divCycle P s G.1 * ratDiv P f g G.1).toNat) := by
    refine (((DivCycleFiniteSupport.proof O K ι P s).image
      fun G => (divCycle P s G * ratDiv P f g G).toNat).insert 0).bddAbove.mono ?_
    rintro _ ⟨G, rfl⟩
    by_cases h : divCycle P s G.1 = 0
    · left; simp [h]
    · right; exact ⟨G.1, h, rfl⟩
  have hle : ∀ G, (C ϖ : MRing ι O) ∈ G → ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → x ≤ divCycle P s G →
      y ≤ ratDiv P f g G → x * y ≤ N := by
    intro G hG x y hx hy hxG hyG
    have h1 : (divCycle P s G * ratDiv P f g G).toNat ≤ N := le_ciSup hbdd ⟨G, hG⟩
    have h2 : x * y ≤ divCycle P s G * ratDiv P f g G := mul_le_mul hxG hyG hy (hx.trans hxG)
    exact h2.trans ((Int.self_le_toNat _).trans (by exact_mod_cast h1))

  have hterm : ∀ x y : ℤ, 0 ≤ x → (0 < x → 0 < y → x * y < N) → (x * y).toNat ≤ N - 1 := by
    intro x y hx h
    rcases lt_or_ge 0 x with hx' | hx'
    · rcases lt_or_ge 0 y with hy | hy
      · have h1 := h hx' hy
        generalize x * y = p at h1 ⊢
        omega
      · have h1 : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy
        generalize x * y = p at h1 ⊢
        omega
    · obtain rfl : x = 0 := le_antisymm hx' hx
      simp
  have hne : Nonempty {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O) //
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G'} := ⟨⟨⊤, Submodule.mem_top⟩⟩
  constructor
  ·
    have h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m)
        (liftForm s) ≤ N - 1 := by
      refine ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_
      obtain ⟨G, hG, h1, h2⟩ :=
        hres O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy
      have h3 := hle G hG _ _ hx.le (add_nonneg hx.le hy.le) h1 h2
      exact (mul_lt_mul_of_pos_left (lt_add_of_pos_left _ hx) hx).trans_le h3
    omega
  ·
    have h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) (newVar none) ≤ N - 1 := by
      refine ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_
      obtain ⟨G, hG, h1, h2⟩ :=
        hexc O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy
      have h3 := hle G hG _ _ (add_nonneg hx.le hy.le) hy.le h1 h2
      exact (mul_lt_mul_of_pos_right (lt_add_of_pos_right _ hy) hy).trans_le h3
    omega

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem subring_map_maximal_cases {D : Type*} [CommRing D] [IsLocalRing D] (C : Subring D)
    (hC : IsLocalRing.maximalIdeal D ≤ ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (m : Ideal C) (hm : m.IsMaximal) :
    m.map C.subtype = ⊤ ∨ IsLocalRing.maximalIdeal D ≤ m.map C.subtype := by
  by_cases h : m ≤ (IsLocalRing.maximalIdeal D).comap C.subtype
  · right
    rw [hm.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal D).ne_top) h]
    exact hC
  · left
    obtain ⟨c, hcm, hc⟩ := Set.not_subset.mp h
    have hu : IsUnit (C.subtype c) := by
      by_contra hnu
      exact hc (IsLocalRing.mem_maximalIdeal _ |>.mpr hnu)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hcm) hu

theorem length_quot_le_of_subring (h₂ : LengthMapIdealLe.Statement.{u})
    (h₃ : IntermediateRingQuotLength.Statement.{u}) {A D : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing D] [IsDomain D] [IsLocalRing D] (hdim : ringKrullDim A = 1)
    (C : Subring D) (f : A →+* C) (hfinj : Function.Injective f)
    (hfrac : ∀ c : C, ∃ a, a ≠ 0 ∧ f a * c ∈ Set.range f)
    (hmax : IsLocalRing.maximalIdeal D ≤
      ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (a : A) (ha : a ≠ 0) :
    Module.length D (D ⧸ Ideal.span {(f a : D)}) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  let _ : Algebra A C := f.toAlgebra
  have s3 := h₃ A C hdim hfinj
    (fun c => by
      obtain ⟨b, hb, hbc⟩ := hfrac c
      exact ⟨b, hb, by rw [Algebra.smul_def]; exact hbc⟩) a ha
  have s2 : Module.length C (C ⧸ Ideal.span {algebraMap A C a}) ≤
      Module.length A (C ⧸ Ideal.span {algebraMap A C a}) := by
    have h := Submodule.length_le_length_restrictScalars A
      (⊤ : Submodule C (C ⧸ Ideal.span {algebraMap A C a}))
    rwa [Submodule.restrictScalars_top, Module.length_top, Module.length_top] at h
  have s1 := h₂ C D C.subtype (subring_map_maximal_cases C hmax) (Ideal.span {algebraMap A C a})
  rw [Ideal.map_span, Set.image_singleton] at s1
  exact s1.trans (s2.trans s3)

theorem BlowUpOrderLe.proof (h₁ : LocalizedQuotLength.Statement.{u})
    (h₂ : LengthMapIdealLe.Statement.{u}) (h₃ : IntermediateRingQuotLength.Statement.{u})
    (h₄ : BlowUpLocalChart.Statement.{u}) : BlowUpOrderLe.Statement.{u} := by
  intro R _ _ K _ ι _ J _ P hP u G' y hy hG' hrel x hx hG z hz
  have hGp : G'.IsPrime := hG'.1.1
  obtain ⟨G₀, W₀, hG₀p, hW₀p, hG₀, hW₀⟩ := BlowUpLocalChart.exists_quotient_primes hGp
    (le_sup_left.trans hG'.1.2) (le_sup_left.trans hG.1.2)
  have hRHS0 : (0 : ℤ) ≤ divCycle P z (G'.comap (liftForm (J := J))) := by
    unfold divCycle
    split_ifs <;> positivity
  by_cases hL : G' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm z}).minimalPrimes ∧ IsRelevant G'
  swap
  · have h0 : divCycle (blowUpOf P u) (liftForm z) G' = 0 := by
      unfold divCycle
      rw [dite_eq_right hL]
    rw [h0]
    exact hRHS0
  have hzG : z ∈ G'.comap (liftForm (J := J)) :=
    hL.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hcp : (G'.comap (liftForm (J := J))).IsPrime := hG.1.1
  have hRmin : G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {z}).minimalPrimes := by
    have h := mem_minimalPrimes_sup_span_mul (P := P) (W := G'.comap (liftForm (J := J))) hz hG
    refine ⟨⟨hcp, sup_le (le_sup_left.trans hG.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hzG)⟩, ?_⟩
    intro q hq hqG
    refine h.2 ⟨hq.1, sup_le (le_sup_left.trans hq.2) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hqG
    exact q.mul_mem_left x (hq.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self z)))
  have hRrel : IsRelevant (G'.comap (liftForm (J := J))) := by
    intro k
    obtain ⟨i, hi⟩ := hL.2 (some k)
    refine ⟨i, fun hmem => hi ?_⟩
    rw [Ideal.mem_comap] at hmem
    simpa [liftForm, rename_X] using hmem
  have hfin := length_localizedQuot_ne_top (P ⊔ Ideal.span {z}) (G'.comap (liftForm (J := J))) hRmin
  unfold divCycle
  rw [dite_eq_left hL, dite_eq_left ⟨hRmin, hRrel⟩]
  suffices key : multAt (blowUpOf P u ⊔ Ideal.span {liftForm z}) G' ≤
      multAt (P ⊔ Ideal.span {z}) (G'.comap (liftForm (J := J))) by
    exact_mod_cast ENat.toNat_le_toNat key hfin

  obtain ⟨C, f, hfinj, hfrac, hfcompat, hmax⟩ := h₄ R K ι J P hP u G' y hy hG' hrel x hx hG G₀ hG₀ W₀ hW₀
  have hQp : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hSn : IsNoetherianRing (MRing ι R ⧸ P) := inferInstance
  have hAn : IsNoetherianRing (Localization.AtPrime G₀) :=
    IsLocalization.isNoetherianRing G₀.primeCompl _ hSn
  have hAinj : Function.Injective (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀)) :=
    IsLocalization.injective (Localization.AtPrime G₀) (Ideal.primeCompl_le_nonZeroDivisors G₀)
  have hdim : ringKrullDim (Localization.AtPrime G₀) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height G₀ (Localization.AtPrime G₀)]
    have hmap : (G'.comap (liftForm (J := J))).map (Ideal.Quotient.mk P) = G₀ := by
      rw [← hG₀, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have hle : G₀.height ≤ 1 := hmap ▸ Ideal.map_height_le_one_of_mem_minimalPrimes hG
    have hne : G₀.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      have hxG : Ideal.Quotient.mk P x ∈ G₀ := by
        rw [← Ideal.mem_comap, hG₀]
        exact hG.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
      rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hxG
      exact hx hxG
    have h1 : G₀.height = 1 := le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
    rw [h1]
    rfl
  set a : Localization.AtPrime G₀ :=
    algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀) (Ideal.Quotient.mk P z) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    rw [ha_def, ← map_zero (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀))] at h0
    exact hz (Ideal.Quotient.eq_zero_iff_mem.mp (hAinj h0))
  have hDom : IsDomain (Localization.AtPrime W₀) := inferInstance
  have hchain := length_quot_le_of_subring h₂ h₃ hdim C f hfinj hfrac hmax a ha
  rw [ha_def, hfcompat z] at hchain
  have e₁ := h₁ (MRing (extIdx ι J) R) (blowUpOf P u) W₀ (liftForm z)
  have e₂ := h₁ (MRing ι R) P G₀ z
  have key : ∀ (H : Ideal (MRing (extIdx ι J) R)) [H.IsPrime] (G : Ideal (MRing ι R)) [G.IsPrime],
      W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = H → G₀.comap (Ideal.Quotient.mk P) = G →
      multAt (blowUpOf P u ⊔ Ideal.span {liftForm z}) H ≤ multAt (P ⊔ Ideal.span {z}) G := by
    intro H _ G _ hH hGG
    subst hH
    subst hGG
    unfold multAt
    exact e₁.le.trans (hchain.trans e₂.ge)
  exact key _ _ hW₀ hG₀

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Helpers

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

private theorem divCycle_eq_zero_of_not_mem' {P W : Ideal (MRing ι R)} {x : MRing ι R} (h : x ∉ W) :
    divCycle P x W = 0 := by
  by_contra h'
  exact h (form_mem_of_divCycle_ne_zero h')

private theorem divCycle_nonneg' (P : Ideal (MRing ι R)) (x : MRing ι R) (W : Ideal (MRing ι R)) :
    0 ≤ divCycle P x W := by
  unfold divCycle
  split_ifs <;> positivity

private theorem facts_of_divCycle_ne_zero' {P W : Ideal (MRing ι R)} {x : MRing ι R}
    (h : divCycle P x W ≠ 0) : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

end Helpers

section Rel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type u} [CommRing R]
  [IsNoetherianRing R]

private theorem ratDiv_eq_of_rel {P W : Ideal (MRing ι R)} (hP : P.IsPrime) (hPW : P ≤ W)
    {f g a v : MRing ι R} (hf : f ∉ P) (hg : g ∉ P) (ha : a ∉ W) (h : a * f - v * g ∈ P) :
    v ∉ P ∧ ratDiv P f g W = divCycle P v W := by
  have haP : a ∉ P := fun h' => ha (hPW h')
  have hv : v ∉ P := by
    intro hv
    have e : a * f = (a * f - v * g) + v * g := by ring
    have h1 : a * f ∈ P := by rw [e]; exact P.add_mem h (P.mul_mem_right _ hv)
    exact (hP.mem_or_mem h1).elim haP hf
  refine ⟨hv, ?_⟩
  have e1 := congrFun (divCycle_congr_of_sub_mem h) W
  rw [DivCycleMul.proof R K ι P a f hP haP hf, DivCycleMul.proof R K ι P v g hP hv hg] at e1
  simp only [Pi.add_apply] at e1
  rw [divCycle_eq_zero_of_not_mem' ha] at e1
  unfold ratDiv
  linarith

end Rel

section Proof

theorem ExceptionalComparison.proof (h₁ : BlowUpDecomposition.Statement.{u}) (h₂ : BlowUpOrderLe.Statement.{u})
    (h₃ : ExceptionalContraction.Statement.{u}) : ExceptionalComparison.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH G' hϖG' hY₀ hE
  obtain ⟨hQm, -, hsQ, hY₀Q, hD₁, -, -, -⟩ :=
    h₁ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH
  have hG := h₃ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH G' hϖG' hY₀ hE
  set Q := blowUpOf P (blowUpGens s g f m e) with hQdef
  set G := G'.comap (liftForm (J := BlowUpIdx ι)) with hGdef
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hQp : Q.IsPrime := hQm.multiProj.isPrime
  obtain ⟨hG'min, hG'rel⟩ := facts_of_divCycle_ne_zero' hY₀.ne'
  have hGp : G.IsPrime := hG.1.1
  have hPG : P ≤ G := le_sup_left.trans hG.1.2
  have hGrel : IsRelevant G := by
    intro k
    obtain ⟨i, hi⟩ := hG'rel (some k)
    refine ⟨i, fun h => hi ?_⟩
    rw [hGdef, Ideal.mem_comap] at h
    simpa [liftForm, rename_X] using h
  have hlift : ∀ {p : MRing ι O}, p ∉ P → liftForm (J := BlowUpIdx ι) p ∉ Q := by
    intro p hp h
    rw [hQdef, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hp h
  have hliftP : ∀ {p : MRing ι O}, p ∈ P → liftForm (J := BlowUpIdx ι) p ∈ Q := by
    intro p hp
    rw [hQdef, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
      Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hfP : f ∉ P := hD.1.num_not_mem
  have hgP : g ∉ P := hD.1.den_not_mem
  have hY₁Q : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ Q := hD₁.1.num_not_mem
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) Q
  have hnm : ∀ {x y}, x ∉ Q → y ∉ Q → x * y ∉ Q := fun hx hy h => (hQp.mem_or_mem h).elim hx hy

  have e1 := congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'
  rw [map_mul, hmul _ _ hQp (hnm (hlift hsP) (hlift hgP)) hY₁Q, hmul _ _ hQp (hlift hsP) (hlift hgP),
    hmul _ _ hQp (hlift (fun h => (hPp.mem_or_mem h).elim hfP hmP)) hY₀Q] at e1
  simp only [Pi.add_apply] at e1
  have eE : ratDiv Q (liftForm (f * m)) (liftForm g * newVar (some none)) G' =
      ratDiv Q (liftForm f) (liftForm g) G' - ratDiv Q (newVar (some none)) (liftForm m) G' := by
    unfold ratDiv
    rw [map_mul, hmul _ _ hQp (hlift hfP) (hlift hmP), hmul _ _ hQp (hlift hgP) hY₁Q]
    simp only [Pi.add_apply]
    ring
  have eE' : ratDiv Q (liftForm (f * m)) (liftForm g * newVar (some none)) G' =
      divCycle Q (liftForm s) G' - divCycle Q (newVar none) G' := by
    unfold ratDiv
    rw [hmul _ _ hQp (hlift hgP) hY₁Q]
    simp only [Pi.add_apply]
    linarith

  have hD₁G' : 0 ≤ ratDiv Q (newVar (some none)) (liftForm m) G' := by
    by_cases h0 : ratDiv Q (newVar (some none)) (liftForm m) G' = 0
    · exact h0.ge
    have hW : G' ∈ (Q ⊔ Ideal.span {newVar (some none)}).minimalPrimes ∧ IsRelevant G' ∨
        G' ∈ (Q ⊔ Ideal.span {liftForm m}).minimalPrimes ∧ IsRelevant G' := by
      unfold ratDiv at h0
      by_cases h1 : divCycle Q (newVar (some none)) G' = 0
      · right; exact facts_of_divCycle_ne_zero' (fun h2 => h0 (by rw [h1, h2, sub_zero]))
      · left; exact facts_of_divCycle_ne_zero' h1
    have hW' : G'.IsPrime ∧ Q ≤ G' ∧ IsRelevant G' := by
      rcases hW with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1.1.1, le_sup_left.trans h1.1.2, h2⟩
      · exact ⟨h1.1.1, le_sup_left.trans h1.1.2, h2⟩
    obtain ⟨a, v, ha, hrel⟩ := hD₁.2 G' hW'.1 hW'.2.1 hW'.2.2
    have := ratDiv_eq_of_rel hQp hW'.2.1 hY₁Q (hlift hmP) ha hrel
    rw [this.2]
    exact divCycle_nonneg' _ _ _

  obtain ⟨a, v, haG, hrelP⟩ := hD.2 G hGp hPG hGrel
  obtain ⟨hvP, hfgG⟩ := ratDiv_eq_of_rel hPp hPG hfP hgP haG hrelP
  have hrelQ : liftForm a * liftForm f - liftForm v * liftForm g ∈ Q := by
    have := hliftP hrelP
    rwa [map_sub, map_mul, map_mul] at this
  have haG' : liftForm (J := BlowUpIdx ι) a ∉ G' := fun h => haG (by rw [hGdef, Ideal.mem_comap]; exact h)
  have hQG' : Q ≤ G' := le_sup_left.trans hG'min.1.2
  obtain ⟨-, hfgG'⟩ := ratDiv_eq_of_rel hQp hQG' (hlift hfP) (hlift hgP) haG' hrelQ

  have hs' := h₂ O K ι (BlowUpIdx ι) P hPp (blowUpGens s g f m e) G' (newVar none) hY₀Q hG'min hG'rel
    s hsP hG s hsP
  have hv' := h₂ O K ι (BlowUpIdx ι) P hPp (blowUpGens s g f m e) G' (newVar none) hY₀Q hG'min hG'rel
    s hsP hG v hvP
  refine ⟨G, ?_, ?_, ?_⟩
  · rw [hGdef, Ideal.mem_comap]
    simpa [liftForm] using hϖG'
  · rw [eE']
    linarith
  · rw [eE, hfgG', hfgG]
    linarith

end Proof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IsLocalRing

universe u

theorem length_localizedModule_quotient_eq {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

theorem comap_C_map_C_polynomial {R : Type*} [CommRing R] (p : Ideal R) :
    (p.map (Polynomial.C : R →+* Polynomial R)).comap (Polynomial.C : R →+* Polynomial R) = p := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h n
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem

theorem PolynomialLocalizedLength.full : PolynomialLocalizedLength.Statement.{u} := by
  intro R _ q _ I
  set Q := q.map (Polynomial.C : R →+* Polynomial R) with hQdef
  have : Q.LiesOver q := ⟨by
    rw [Ideal.under, Polynomial.algebraMap_eq, hQdef]
    exact (comap_C_map_C_polynomial q).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver q Q
  set A := Localization.AtPrime q
  set B := Localization.AtPrime Q
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom q Q (algebraMap R (Polynomial R))
      Ideal.LiesOver.over))
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R (Polynomial R) B, ← Ideal.map_map, Polynomial.algebraMap_eq,
      ← hQdef, Localization.AtPrime.map_eq_maximalIdeal]
  have h1 : Module.length B (B ⧸ maximalIdeal B) = 1 := by
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal B, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have key := IsLocalRing.length_baseChange A B (A ⧸ I.map (algebraMap R A))
  rw [hm, h1, mul_one, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (I.map (algebraMap R A))).toLinearEquiv.length_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq R (Polynomial R) B, ← Ideal.map_map, Polynomial.algebraMap_eq] at key
  rw [length_localizedModule_quotient_eq, length_localizedModule_quotient_eq]
  exact key

end GroundTheory.Heights₂.Heights.NumbersDVR
end
