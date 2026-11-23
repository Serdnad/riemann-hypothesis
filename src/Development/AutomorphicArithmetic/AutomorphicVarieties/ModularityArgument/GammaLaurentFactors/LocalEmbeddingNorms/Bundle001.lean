module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle009
import Formalism.DoubleCosetMeasures.Statement
public import GroundTheory.AutomorphicForms.GL2.GJStandardLCuspidalGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOneSubBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

private theorem count_cls {Y T : Type*} (E : T → T → Prop) (hE : ∀ t, E t t) (R : Y → T → Prop)
    (hR : ∀ y t, R y t → ∀ t', R y t' ↔ E t t') (s : Multiset Y) (t : T) :
    ((s.filter fun y => ∃ t, R y t).map fun y => {t | R y t}).count {t' | E t t'} = (s.filter fun y => R y t).card := by
  rw [Multiset.count_map, Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun y _ => ⟨fun h => ?_, fun h => ⟨?_, t, h⟩⟩
  · have : t ∈ {t' | E t t'} := hE t
    rw [h.1] at this
    exact this
  · exact Set.ext fun t' => (hR y t h t').symm

private theorem count_ncls {Y T : Type*} (E : T → T → Prop) (R : Y → T → Prop)
    (hR : ∀ y t, R y t → ∀ t', R y t' ↔ E t t') (s : Multiset Y) (S : Set T) (hS : ¬ ∃ t, S = {t' | E t t'}) :
    ((s.filter fun y => ∃ t, R y t).map fun y => {t | R y t}).count S = 0 := by
  rw [Multiset.count_eq_zero]
  intro h
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 h
  obtain ⟨t, ht⟩ := (Multiset.mem_filter.1 hy).2
  exact hS ⟨t, Set.ext fun t' => hR y t ht t'⟩

private theorem total {Y T ι : Type*} [Fintype ι] {Y' : ι → Type*} (E : T → T → Prop) (hE : ∀ t, E t t)
    (R : Y → T → Prop) (hR : ∀ y t, R y t → ∀ t', R y t' ↔ E t t')
    (R' : ∀ i, Y' i → T → Prop) (hR' : ∀ i y t, R' i y t → ∀ t', R' i y t' ↔ E t t')
    (s : Multiset Y) (s' : ∀ i, Multiset (Y' i)) (F : ℕ) (f : ι → ℕ)
    (h : ∀ t, F * (s.filter fun y => R y t).card = ∑ i, f i * ((s' i).filter fun y => R' i y t).card) :
    F * (s.filter fun y => ∃ t, R y t).card = ∑ i, f i * ((s' i).filter fun y => ∃ t, R' i y t).card := by
  have key : F • ((s.filter fun y => ∃ t, R y t).map fun y => {t | R y t}) =
      ∑ i, f i • (((s' i).filter fun y => ∃ t, R' i y t).map fun y => {t | R' i y t}) := by
    ext S
    rw [Multiset.count_sum']
    simp only [Multiset.count_nsmul]
    by_cases hS : ∃ t, S = {t' | E t t'}
    · obtain ⟨t, rfl⟩ := hS
      rw [count_cls E hE R hR, h t]
      exact Finset.sum_congr rfl fun i _ => by rw [count_cls E hE (R' i) (hR' i)]
    · rw [count_ncls E R hR s S hS, mul_zero]
      exact (Finset.sum_eq_zero fun i _ => by rw [count_ncls E (R' i) (hR' i) _ S hS, mul_zero]).symm
  have := congrArg Multiset.card key
  simpa [Multiset.card_sum, Multiset.card_nsmul] using this

private theorem card_le_sum {s : Multiset ℕ} (h : ∀ y ∈ s, 0 < y) : s.card ≤ s.sum := by
  simpa using Multiset.card_nsmul_le_sum (a := 1) h

private theorem sum_card_filter {Y : Type*} (s : Multiset Y) (d F : ℕ) (A : Y → ℕ → Prop) (B : Y → Prop)
    (h1 : ∀ y, B y → ((Finset.range d).filter (A y)).card = F) (h2 : ∀ y j, A y j → B y) :
    ∑ j ∈ Finset.range d, (s.filter fun y => A y j).card = F * (s.filter B).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons y s ih =>
    simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib, ih, mul_add]
    congr 1
    by_cases hB : B y
    · rw [← h1 y hB, Finset.card_filter, if_pos hB, Multiset.card_singleton, mul_one]
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    · rw [if_neg hB]
      exact Finset.sum_eq_zero fun j _ => by rw [if_neg fun hA => hB (h2 y j hA)]; simp

private theorem loc_pow {K : Type} [Field K] [NumberField K] (η : HChar K) (j : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (η ^ j).loc v = η.loc v ^ j := by
  ext1 x
  show (η ^ j).1 _ = η.1 _ ^ j
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem cls_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ζ a b : kˣ →* ℂˣ} (h : IsUnram (ζ * a)) : IsUnram (ζ * b) ↔ IsUnram (a⁻¹ * b) := by
  constructor
  · intro h'
    have := isUnram_mul (isUnram_inv h) h'
    rwa [show (ζ * a)⁻¹ * (ζ * b) = a⁻¹ * b by rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]] at this
  · intro h'
    have := isUnram_mul h h'
    rwa [mul_assoc, mul_inv_cancel_left] at this

private theorem all_of_le {Y : Type*} {s : Multiset Y} {p : Y → Prop} (h : s.card ≤ (s.filter p).card) :
    ∀ y ∈ s, p y :=
  Multiset.filter_eq_self.1 (Multiset.eq_of_le_of_card_le (Multiset.filter_le p s) h)

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.upDownOf :
    UpperTheory.V.Z.Gam.UpDownOf := by
  intro hS hN hM K L _ _ _ _ _ _ _ _ hp n hn π P hBC v
  obtain ⟨η, hη, hloc⟩ := hN K L hp
  have hSK := hS K n (by omega) π v
  have hSL := fun w : PlacesOver L v => hS L n (by omega) P w.1
  obtain ⟨s, hs⟩ := hSK.1
  choose s' hs' using fun w => (hSL w).1
  obtain ⟨w₀⟩ : Nonempty (PlacesOver L v) :=
    ⟨(placesOverEquiv L v).symm (Classical.choice (Ideal.nonempty_primesOver v.asIdeal))⟩
  have hf : ∀ w : PlacesOver L v, 0 < fdeg w := fun w => Ideal.inertiaDeg'_pos _ _
  have hcs : s.card ≤ n := by
    obtain ⟨-, h1, h2⟩ := hSK.2.2.1 s hs
    rw [← h1, ← Multiset.card_map Sigma.fst s]
    exact card_le_sum fun d hd => by obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hd; exact h2 y hy
  have hcs' : ∀ w, (s' w).card ≤ n := fun w => by
    obtain ⟨-, h1, h2⟩ := (hSL w).2.2.1 _ (hs' w)
    rw [← h1, ← Multiset.card_map Sigma.fst (s' w)]
    exact card_le_sum fun d hd => by obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hd; exact h2 y hy
  have key := total (T := {θ : (v.adicCompletion K)ˣ →* ℂˣ // IsSmoothChar θ})
    (fun a b => IsUnram ((a.1⁻¹ * b.1).comp (nm w₀))) (fun a x _ => by simp)
    (fun y t => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram ((ξ * t.1).comp (nm w₀)))
    (by
      rintro y t ⟨ξ, hξ, rfl, h⟩ t'
      refine Iff.trans ⟨?_, fun h' => ⟨ξ, hξ, rfl, h'⟩⟩
        (cls_iff (ζ := ξ.comp (nm w₀)) (a := t.1.comp (nm w₀)) (b := t'.1.comp (nm w₀)) h)
      rintro ⟨ξ', hξ', e, h'⟩
      obtain rfl := IrrGL.ofChar_inj.1 e
      exact h')
    (fun (w : PlacesOver L v) y t => ∃ ζ hζ, y = IrrGL.ofChar ζ hζ ∧ IsUnram (ζ * t.1.comp (nm w)))
    (by
      rintro w y t ⟨ζ, hζ, rfl, h⟩ t'
      refine Iff.trans ⟨?_, fun h' => ⟨ζ, hζ, rfl, h'⟩⟩ ((cls_iff (b := t'.1.comp (nm w)) h).trans
        ⟨(hloc v w).2.1 w₀ (t.1⁻¹ * t'.1), (hloc v w₀).2.1 w (t.1⁻¹ * t'.1)⟩)
      rintro ⟨ξ', hξ', e, h'⟩
      obtain rfl := IrrGL.ofChar_inj.1 e
      exact h')
    s s' (∑ w : PlacesOver L v, fdeg w) (fun w => fdeg w) (fun t => by
      refine Eq.trans ?_ (hM K L hp n hn π P hBC η hη v s s' hs hs' t.1 t.2)
      symm
      refine sum_card_filter s _ _
        (fun y j => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (t.1 * (η ^ j).loc v))) _ ?_ ?_
      · rintro y ⟨ξ, hξ, rfl, h⟩
        rw [← ((hloc v w₀).2.2 (ξ * t.1) (hξ.mul t.2)).2.2 h]
        congr 1
        refine Finset.filter_congr fun j _ => ⟨?_, fun h' => ⟨ξ, hξ, rfl, by rwa [← mul_assoc]⟩⟩
        rintro ⟨ξ', hξ', e, h'⟩
        obtain rfl := IrrGL.ofChar_inj.1 e
        rwa [mul_assoc]
      · rintro y j ⟨ξ, hξ, rfl, h⟩
        refine ⟨ξ, hξ, rfl, fun x hx => ?_⟩
        have h1 := ((hloc v w₀).2.2 _ (isSmoothChar_of_isUnram h)).2.1 h x hx
        have h2 : η.loc v (nm w₀ x) = 1 := DFunLike.congr_fun (hloc v w₀).1 x
        simpa [loc_pow, h2] using h1)
  constructor
  · intro hT w
    have h1 := (hSK.2.2.1 s hs).1.1 hT
    have hn' : s.card = n := by
      rw [← (hSK.2.2.1 s hs).2.1, Multiset.map_congr rfl h1]; simp
    rw [Multiset.filter_eq_self.2 fun y hy => by
      obtain ⟨ξ, hξ, rfl⟩ := GlobalTheory.LocGL.TemperedTests.exists_eq_ofChar y (h1 y hy)
      exact ⟨⟨ξ⁻¹, hξ.inv⟩, ξ, hξ, rfl, fun x _ => by simp⟩, hn', Finset.sum_mul] at key
    have h2 := (Finset.sum_eq_sum_iff_of_le fun w _ => Nat.mul_le_mul_left _
      ((Multiset.card_le_card (Multiset.filter_le _ _)).trans (hcs' w))).1 key.symm w (Finset.mem_univ w)
    have h3 := all_of_le ((hcs' w).trans (Nat.eq_of_mul_eq_mul_left (hf w) h2).ge)
    refine ⟨((hSL w).2.2.1 _ (hs' w)).1.2 fun y hy => ?_, fun r hr ζ hζ hm => ?_⟩
    · obtain ⟨t, ζ, hζ, rfl, -⟩ := h3 y hy
      rfl
    · obtain rfl := (hSL w).2.1 _ _ (hs' w) hr
      obtain ⟨t, ζ', hζ', e, h⟩ := h3 _ hm
      obtain rfl := IrrGL.ofChar_inj.1 e
      exact ⟨t.1, t.2, h⟩
  · intro hT
    have h1 := fun w => ((hSL w).2.2.1 _ (hs' w)).1.1 (hT w).1
    have hn' : ∀ w, (s' w).card = n := fun w => by
      rw [← ((hSL w).2.2.1 _ (hs' w)).2.1, Multiset.map_congr rfl (h1 w)]; simp
    replace key := key.trans (Finset.sum_congr (g := fun w : PlacesOver L v => fdeg w * n) rfl fun w _ => by
      rw [Multiset.filter_eq_self.2 fun y hy => by
        obtain ⟨ζ, hζ, rfl⟩ := GlobalTheory.LocGL.TemperedTests.exists_eq_ofChar y (h1 w y hy)
        obtain ⟨χ, hχ, h⟩ := (hT w).2 _ (hs' w) ζ hζ hy
        exact ⟨⟨χ, hχ⟩, ζ, hζ, rfl, h⟩, hn' w])
    rw [← Finset.sum_mul] at key
    have hF : 0 < ∑ w : PlacesOver L v, fdeg w := Finset.sum_pos (fun w _ => hf w) ⟨w₀, Finset.mem_univ _⟩
    have h3 := all_of_le (hcs.trans (Nat.eq_of_mul_eq_mul_left hF key).ge)
    refine (hSK.2.2.1 s hs).1.2 fun y hy => ?_
    obtain ⟨t, ζ, hζ, rfl, -⟩ := h3 y hy
    rfl
end
end

section

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LocGL UpperTheory.V.Z.Inf
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardLCuspidal
open scoped Classical

namespace UpperTheory.V.Z.Gam

private theorem localEmbedding_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (w.adicCompletion K)) :
    AdelicGLn.localEmbedding w g = locGL K n w g := by
  refine Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun v => ?_
  change ((AdelicGLn.finiteRestrictedEquiv K n).symm _ : AdelicGLn.FiniteAdelicGL K n) a b v = _
  rw [AdelicGLn.finiteRestrictedEquiv_symm_apply, RestrictedProduct.coe_mulSingle_apply]
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (pLoc_locGL v g)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (pLoc_locGL_of_ne h g)).symm

end UpperTheory.V.Z.Gam

open UpperTheory.V UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.locIso :
    UpperTheory.V.Z.Gam.LocIso := by
  intro K _ _ _ n σ h D v
  let τ : SmIrr (GL (Fin n) (v.adicCompletion K)) :=
    { V := D.finite.W v
      ρ := D.finite.π v
      smooth := (D.finite.isAdmissible v).1
      irred := D.finite.isIrreducible v }
  have hτ : σ.IsLocComp v τ := by
    obtain ⟨a, x, hx, ha, hx0, -⟩ := exists_pureTensor_spherical (Cm.toRep σ h) D
    refine ⟨(Cm.carrierEq σ).toLinearMap ∘ₗ Iv D a x hx v, fun e => ?_, fun g y => ?_⟩
    · have e' : Iv D a x hx v (x v) = 0 := (Cm.carrierEq σ).map_eq_zero_iff.1 (LinearMap.congr_fun e (x v))
      rw [Iv_self] at e'
      exact phi_ne D a x hx ha hx0 e'
    · refine ((congrArg (Cm.carrierEq σ) (Iv_int D a x hx v g y)).trans (Cm.carrierEq_τ σ _ _)).trans ?_
      rw [localEmbedding_eq]
      rfl
  refine ⟨?_, fun B hB => ?_⟩
  · rintro s ⟨σ', h1, h2⟩
    obtain ⟨e⟩ := LocUniq.isLocComp_unique σ v σ' τ h1 hτ
    exact h2.of_equiv e
  · obtain ⟨α, -, h'⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp σ ((CG.hasSat_mk σ v B).1 hB) hτ
    have h1 : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.SplitWeil.KO (v.adicCompletion K) (Fin n)) := h'.2.1
    have hsph : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL v (n := n)) := by
      rwa [GlobalTheory.SmGL.SphCompletion.KO_completion v n] at h1
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsph
    rw [(Af.Smo.sphDict K n v).1]
    exact (Submodule.ne_bot_iff _).2 ⟨x, fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk, hx0⟩
end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ
open GroundTheory.Global.SemiLocal

namespace UpperTheory.V.Z.Gam

namespace BaseChangeLocalFactorRegrouping

private theorem one_period {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (y : ℂ) :
    ∏ j ∈ Finset.range f, (1 - ζ ^ j * y) = 1 - y ^ f := by
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) (X_pow_sub_C_eq_prod h hf (rfl : y ^ f = y ^ f))
  rw [Polynomial.eval_prod] at h1
  simpa using h1.symm

private theorem periods {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (y : ℂ) (g : ℕ) :
    ∏ j ∈ Finset.range (g * f), (1 - ζ ^ j * y) = (1 - y ^ f) ^ g := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Nat.succ_mul, Finset.prod_range_add, ih, pow_succ, ← one_period h hf y]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [pow_add, mul_comm g f, pow_mul, h.pow_eq_one, one_pow, one_mul]

private theorem fac_eq {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (g : ℕ) (B : Multiset ℂ) (x : ℂ) :
    ∏ j ∈ Finset.range (g * f), ((B.map (· * ζ ^ j)).map fun b => (1 - b * x)⁻¹).prod =
      (((B.map (· ^ f)).map fun b => (1 - b * x ^ f)⁻¹).prod) ^ g := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons a B ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [Finset.prod_mul_distrib, ih, mul_pow, Finset.prod_inv_distrib, ← mul_pow a x, inv_pow, ← periods h hf]
    congr 2
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

private theorem cast_pow_cpow (N f : ℕ) (z : ℂ) : (((N ^ f : ℕ)) : ℂ) ^ z = (((N : ℕ) : ℂ) ^ z) ^ f := by
  induction f with
  | zero => simp
  | succ f ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem norm_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm p.asIdeal ^ fdeg w :=
  Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.1.asIdeal p.asIdeal p.isPrime p.ne_bot

private theorem under_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) : w.1.under (𝓞 K) = p := by
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact w.2.over.symm

private theorem nonempty_over (p : HeightOneSpectrum (𝓞 K)) : Nonempty (PlacesOver L p) := by
  haveI := p.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) p.asIdeal
  exact ⟨⟨⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩, hP⟩⟩

private theorem core (d : ℕ) (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (SL : Set (HeightOneSpectrum (𝓞 L)))
    (BK : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (BL : HeightOneSpectrum (𝓞 L) → Multiset ℂ)
    (e : HeightOneSpectrum (𝓞 K) → ℂ) (c₀ : ℝ) (r : ℕ) (hd : 0 < d)
    (hS : ∀ w, w ∈ SL ↔ w.under (𝓞 K) ∈ MainNotions)
    (h : ∀ p ∉ MainNotions, Multiset.card (BK p) ≤ r ∧ (∀ b ∈ BK p, ‖b‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀) ∧
      ∀ w : PlacesOver L p, IsPrimitiveRoot (e p) (fdeg w) ∧ Fintype.card (PlacesOver L p) * fdeg w = d ∧
        BL w.1 = (BK p).map (· ^ fdeg w))
    (s : ℂ) (hs : c₀ + 1 < s.re) :
    ∏ j ∈ Finset.range d, eulerL K (fun p => (BK p).map (· * e p ^ j)) MainNotions s = eulerL L BL SL s := by
  have hf : ∀ p ∉ MainNotions, ∀ w : PlacesOver L p, 0 < fdeg w := by
    intro p hp w
    have := ((h p hp).2.2 w).2.1
    rcases Nat.eq_zero_or_pos (fdeg w) with h0 | h0
    · rw [h0] at this; omega
    · exact h0
  have hL := (GlobalTheory.HenQ.Regroup.multipliable_E L SL BL c₀ r (by
    intro w hw
    have hp : w.under (𝓞 K) ∉ MainNotions := (hS w).not.mp hw
    let w' : PlacesOver L (w.under (𝓞 K)) := ⟨w, ⟨rfl⟩⟩
    obtain ⟨h1, h2, h3⟩ := h _ hp
    have hB : BL w = _ := (h3 w').2.2
    have hN : Ideal.absNorm w.asIdeal = _ := norm_eq w'
    refine ⟨by rw [hB, Multiset.card_map]; exact h1, fun b hb => ?_⟩
    rw [hB] at hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [hN, norm_pow, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h2 a ha) _) s hs).hasProd
  have hK : ∀ j ∈ Finset.range d, Multipliable (fun p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions} =>
      (((BK p.1).map (· * e p.1 ^ j)).map fun b => (1 - b * ((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) := by
    intro j _
    refine GlobalTheory.HenQ.Regroup.multipliable_E K MainNotions (fun p => (BK p).map (· * e p ^ j)) c₀ r ?_ s hs
    intro p hp
    obtain ⟨h1, h2, h3⟩ := h _ hp
    obtain ⟨w⟩ := nonempty_over (L := L) p
    have he : ‖e p‖ = 1 := (h3 w).1.norm'_eq_one (hf p hp w).ne'
    refine ⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [norm_mul, norm_pow, he, one_pow, mul_one]
    exact h2 a ha
  let E : (Σ p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions}, PlacesOver L p.1) ≃
      {w : HeightOneSpectrum (𝓞 L) // w ∉ SL} :=
    { toFun := fun x => ⟨x.2.1, by rw [hS, under_eq x.2]; exact x.1.2⟩
      invFun := fun w => ⟨⟨w.1.under (𝓞 K), (hS w.1).not.mp w.2⟩, ⟨w.1, ⟨rfl⟩⟩⟩
      left_inv := by
        rintro ⟨⟨p, hp⟩, w⟩
        have hw := under_eq w
        obtain ⟨w, hw'⟩ := w
        simp only at hw
        subst hw
        rfl
      right_inv := by intro w; rfl }
  have h2 := (E.hasProd_iff).mpr hL
  unfold eulerL
  rw [← Multipliable.tprod_finsetProd hK]
  refine (h2.sigma ?_).tprod_eq
  rintro ⟨p, hp⟩
  obtain ⟨w₀⟩ := nonempty_over (L := L) p
  obtain ⟨-, -, h3⟩ := h p hp
  have hcard : 0 < Fintype.card (PlacesOver L p) := Fintype.card_pos_iff.mpr ⟨w₀⟩
  have hff : ∀ w : PlacesOver L p, fdeg w = fdeg w₀ := fun w =>
    Nat.eq_of_mul_eq_mul_left hcard ((h3 w).2.1.trans (h3 w₀).2.1.symm)
  convert hasProd_fintype _ using 1
  · dsimp only [E, Equiv.coe_fn_mk, Function.comp_apply]
    rw [← (h3 w₀).2.1, fac_eq (h3 w₀).1 (hf p hp w₀), ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(h3 w).2.2, norm_eq w, cast_pow_cpow, hff w]

end BaseChangeLocalFactorRegrouping

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam.BaseChangeLocalFactorRegrouping in
theorem UpperTheory.V.Z.Gam.regroupBC :
    UpperTheory.V.Z.Gam.RegroupBC := by
  intro K L _ _ _ _ _ d MainNotions SL BK BL e c₀ r hd hS h
  refine ⟨c₀ + 1, fun s => ⟨fun hs => core d MainNotions SL BK BL e c₀ r hd.pos hS
    (fun p hp => ⟨(h p hp).1, fun b hb => ((h p hp).2.1 b hb).1, (h p hp).2.2⟩) s hs, fun hs => ?_⟩⟩
  unfold eulerLd
  rw [← core d MainNotions SL (fun p => (BK p).map (·⁻¹)) (fun w => (BL w).map (·⁻¹)) (fun p => (e p)⁻¹) c₀ r hd.pos hS
    ?_ (1 - s) ?_]
  · refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    funext p
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, mul_inv, inv_pow]
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := h p hp
    refine ⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_, fun w => ⟨(h3 w).1.inv, (h3 w).2.1, ?_⟩⟩
    · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
      exact (h2 a ha).2
    · simp only [(h3 w).2.2, Multiset.map_map]
      refine Multiset.map_congr rfl fun b _ => ?_
      simp only [Function.comp_apply, inv_pow]
  · simp only [Complex.sub_re, Complex.one_re]
    linarith
end
end
