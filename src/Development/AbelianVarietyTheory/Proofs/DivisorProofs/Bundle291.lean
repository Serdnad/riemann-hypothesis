module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle242
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle175
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle180
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue.CombEx

theorem chart_rebuild {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top (Sp S)) hx.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have e : CommRingCat.ofHom (chartHom V x hx) = x.appLE V ⊤ hx.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := rfl
  show Spec.map (CommRingCat.ofHom (chartHom V x hx)) ≫ hV.fromSpec = x
  rw [e, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem top_of_comp {A B Y : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ Y) (V : Y.Opens) (h : g ⁻¹ᵁ V = ⊤) :
    (f ≫ g) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun x _ => h.ge (show f x ∈ (⊤ : B.Opens) from trivial)

theorem fromSpec_comp_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {x x' : Sp S ⟶ Y}
    (e : x = x') (h : x ⁻¹ᵁ V = ⊤) (h' : x' ⁻¹ᵁ V = ⊤) : chartHom V x h = chartHom V x' h' := by
  subst e; rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem chartHom_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) (hc : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap χ ≫ hV.fromSpec) hc = χ := by
  have e := chart_rebuild hV (spMap χ ≫ hV.fromSpec) hc
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem chartHom_spMap_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S S' : Type} [CommRing S]
    [CommRing S'] (g : S →+* S') (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ x) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap g ≫ x) h' = g.comp (chartHom V x hx) := by
  have e : spMap (chartHom V (spMap g ≫ x) h') ≫ hV.fromSpec =
      spMap (g.comp (chartHom V x hx)) ≫ hV.fromSpec := by
    rw [chart_rebuild, spMap_comp', Category.assoc, chart_rebuild]
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

end GlobalTheory.SecGlue.CombEx

namespace GlobalTheory.SecGlue.CombEx

theorem mul_eq_zero_of_sq {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {s t : S} (hs : q s = 0) (ht : q t = 0) : s * t = 0 := by
  have h : s * t ∈ RingHom.ker q ^ 2 := by
    rw [sq]; exact Ideal.mul_mem_mul (RingHom.mem_ker.2 hs) (RingHom.mem_ker.2 ht)
  rw [hsq] at h
  exact (Submodule.mem_bot S).1 h

def combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S) (hq : ∀ i, q.comp (ψ i) = q.comp φ) :
    A →+* S where
  toFun x := φ x + ∑ i, a i * (ψ i x - φ x)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add (f := _), mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  map_mul' x y := by
    have hd : ∀ i z, q (ψ i z - φ z) = 0 := fun i z => by
      rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
    have hD : ∀ z, q (∑ i, a i * (ψ i z - φ z)) = 0 := fun z => by

      simp only [map_sum, map_mul, hd, mul_zero, Finset.sum_const_zero]
    have e1 : ∀ i, ψ i (x * y) - φ (x * y) = φ x * (ψ i y - φ y) + (ψ i x - φ x) * φ y := fun i => by
      have := mul_eq_zero_of_sq q hsq (hd i x) (hd i y)
      rw [map_mul, map_mul]; linear_combination this
    have e2 := mul_eq_zero_of_sq q hsq (hD x) (hD y)
    have s : ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
        φ x * ∑ i, a i * (ψ i y - φ y) + φ y * ∑ i, a i * (ψ i x - φ x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [e1 i]; ring
    show φ (x * y) + ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
      (φ x + ∑ i, a i * (ψ i x - φ x)) * (φ y + ∑ i, a i * (ψ i y - φ y))
    linear_combination s + map_mul φ x y - e2

theorem combHom_apply {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (x : A) :
    combHom q hsq φ ψ a hq x = φ x + ∑ i, a i * (ψ i x - φ x) := rfl

theorem comp_combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) : q.comp (combHom q hsq φ ψ a hq) = q.comp φ := by
  ext x
  have hd : ∀ i, q (ψ i x - φ x) = 0 := fun i => by
    rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]

  simp only [RingHom.comp_apply, combHom_apply, map_add (f := _), map_sum, map_mul, hd, mul_zero,
  Finset.sum_const_zero, add_zero]

theorem combHom_comp_eq {R A S T : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (θ : R →+* A) (hθ : ∀ i, (ψ i).comp θ = φ.comp θ) :
    (combHom q hsq φ ψ a hq).comp θ = φ.comp θ := by
  ext r
  have h : ∀ i, ψ i (θ r) = φ (θ r) := fun i => RingHom.congr_fun (hθ i) r
  simp only [RingHom.comp_apply, combHom_apply, h, sub_self, mul_zero, Finset.sum_const_zero, add_zero]

theorem exists_comb : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), u ⁻¹ᵁ V = ⊤ →
    (∀ i, spMap q ≫ w i = spMap q ≫ u) →
    ∃ c : Sp S ⟶ Y, GlobalTheory.SecGlue.IsCombIn V u c w a ∧ spMap q ≫ c = spMap q ≫ u ∧
      ∀ (R' : Type) [CommRing R'] (p : Y ⟶ Sp R'), (∀ i, w i ≫ p = u ≫ p) → c ≫ p = u ≫ p := by
  intro Y V hV S T _ _ q hqs hsq ι _ u w a hu hw
  have hwV : ∀ i, w i ⁻¹ᵁ V = ⊤ := fun i => (GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero S T q hqs hsq Y (w i) u (hw i) V).trans hu
  have hq : ∀ i, q.comp (chartHom V (w i) (hwV i)) = q.comp (chartHom V u hu) := fun i => by
    rw [← chartHom_spMap_comp hV q (w i) (hwV i) (top_of_comp _ _ V (hwV i)),
      ← chartHom_spMap_comp hV q u hu (top_of_comp _ _ V hu)]
    exact chartHom_congr V (hw i) _ _
  let χ := combHom q hsq (chartHom V u hu) (fun i => chartHom V (w i) (hwV i)) a hq
  have hc := fromSpec_comp_top hV χ
  refine ⟨spMap χ ≫ hV.fromSpec, ⟨hu, hc, hwV, fun x => ?_⟩, ?_, ?_⟩
  · rw [chartHom_fromSpec hV χ hc]; rfl
  · calc spMap q ≫ spMap χ ≫ hV.fromSpec = spMap (q.comp χ) ≫ hV.fromSpec := by
          rw [spMap_comp', Category.assoc]
      _ = spMap (q.comp (chartHom V u hu)) ≫ hV.fromSpec := by rw [comp_combHom]
      _ = spMap q ≫ u := by rw [spMap_comp', Category.assoc, chart_rebuild]
  · intro R' _ p hp
    let θ : CommRingCat.of R' ⟶ Γ(Y, V) := Spec.preimage (hV.fromSpec ≫ p)
    have key : ∀ (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤), x ≫ p = spMap ((chartHom V x hx).comp θ.hom) := by
      intro x hx
      calc x ≫ p = spMap (chartHom V x hx) ≫ hV.fromSpec ≫ p := by rw [← Category.assoc, chart_rebuild]
        _ = spMap (chartHom V x hx) ≫ Spec.map θ := by rw [Spec.map_preimage]
        _ = spMap ((chartHom V x hx).comp θ.hom) := by
          show _ = Spec.map (CommRingCat.ofHom _)
          rw [show CommRingCat.ofHom ((chartHom V x hx).comp θ.hom) = θ ≫ CommRingCat.ofHom (chartHom V x hx)
            from rfl, Spec.map_comp]
    have hθ : ∀ i, (chartHom V (w i) (hwV i)).comp θ.hom = (chartHom V u hu).comp θ.hom := fun i => by
      have e := (key (w i) (hwV i)).symm.trans ((hp i).trans (key u hu))
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    rw [key _ hc, key u hu, chartHom_fromSpec hV χ hc]
    exact congrArg spMap (combHom_comp_eq q hsq _ _ a hq θ.hom hθ)

end GlobalTheory.SecGlue.CombEx
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem awayMap_surjective_of_surjective (π : R →+* R₀) (hπ : Function.Surjective π) (f : R) :
    Function.Surjective (Localization.awayMap π f) :=
  Localization.awayMap_surjective_iff.2 fun a =>
    (hπ a).elim fun b hb => ⟨b, 0, by simp [hb]⟩

theorem isNilpotent_of_awayMap_eq_zero (π : R →+* R₀) (hnil : IsNilpotent (RingHom.ker π)) (f : R)
    (x : Localization.Away f) (hx : Localization.awayMap π f x = 0) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) x
  have hc : (Localization.awayMap π f).comp (algebraMap R (Localization.Away f)) =
      (algebraMap R₀ (Localization.Away (π f))).comp π := IsLocalization.map_comp _
  have h1 : algebraMap R₀ (Localization.Away (π f)) (π a) = 0 := by
    have := congrArg (Localization.awayMap π f) hs
    rw [map_mul, hx, zero_mul] at this
    rw [← RingHom.comp_apply, ← hc, RingHom.comp_apply, ← this]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (π f)) _ _).1 h1
  have hmem : f ^ k * a ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_mul, map_pow]; exact hk
  have h0 : (f ^ k * a) ^ N = 0 := by
    have := Ideal.pow_mem_pow hmem N
    rw [hN] at this
    exact Ideal.mem_bot.1 this
  have hu : IsUnit (algebraMap R (Localization.Away f) (s * f ^ k)) := by
    rw [map_mul, map_pow]
    exact (IsLocalization.map_units _ s).mul ((IsLocalization.Away.algebraMap_isUnit f).pow k)
  refine ⟨N, (hu.pow N).mul_left_eq_zero.1 ?_⟩
  rw [← mul_pow, map_mul, ← mul_assoc, hs, ← map_mul, mul_comm a, ← map_pow, h0, map_zero]

theorem exists_liftIn_unfolded : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀ ∧
    e ⁻¹ᵁ V = ⊤ := by
  intro R R₀ _ _ π hπ hnil X hX g₀ hg p
  haveI := hX
  have hker : RingHom.ker π ≤ p.asIdeal := fun a ha => by
    obtain ⟨N, hN⟩ := hnil
    have := Ideal.pow_mem_pow ha N
    rw [hN] at this
    exact p.isPrime.mem_of_pow_mem N ((Ideal.mem_bot.1 this) ▸ p.asIdeal.zero_mem)
  obtain ⟨p₀, hp₀⟩ : p ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [_root_.range_comap_of_surjective (R := R) R₀ π hπ]
    exact hker
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g₀ p₀)) isOpen_univ
  obtain ⟨_, ⟨r, rfl⟩, hp₀r, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p₀) (u := {q : PrimeSpectrum R₀ | g₀ q ∈ V}) hxV (g₀ ⁻¹ᵁ V).isOpen
  obtain ⟨f, rfl⟩ := hπ r
  refine ⟨f, ?_, V, hV, ?_⟩
  · rw [← hp₀]
    exact hp₀r
  have hsurj := awayMap_surjective_of_surjective π hπ f
  have hnilL := isNilpotent_of_awayMap_eq_zero π hnil f
  have hc : (Localization.awayMap π f).comp (algebraMap R (Localization.Away f)) =
      (algebraMap R₀ (Localization.Away (π f))).comp π := IsLocalization.map_comp _
  have hx0 : Set.range (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀) ⊆ V := by
    rintro _ ⟨q, rfl⟩
    apply hsub
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away (π f)) (π f)).subset ⟨q, rfl⟩
  obtain ⟨x, h₁, h₂⟩ := GlobalTheory.exists_lift_of_smooth_of_isAffineOpen X.hom (isAffineOpen_top (Sp R)) hV
    (fun _ _ => trivial) (CommRingCat.ofHom (Localization.awayMap π f))
    (spMap (algebraMap R (Localization.Away f))) (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀)
    (by
      rw [Category.assoc, hg, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      exact (congrArg (fun φ : R →+* Localization.Away (π f) => φ a) hc).symm)
    (fun _ _ => trivial) hx0 (by
      intro R' A _ _ _ _ _ _ π' hπ' φ
      exact ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.exists_lift_nil π'
        (fun c => (hsurj c).imp fun b hb => (hπ' b).trans hb)
        (fun a ha => hnilL a (by rw [RingHom.mem_ker] at ha; rw [← ha]; exact (hπ' a).symm)) φ)
  refine ⟨x, h₂, h₁, top_unique fun q _ => ?_⟩
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (Localization.awayMap π f)) := by
    rw [_root_.range_comap_of_surjective (R := Localization.Away f) _ _ hsurj]
    intro a ha
    obtain ⟨n, hn⟩ := hnilL a ha
    exact (q : PrimeSpectrum (Localization.Away f)).isPrime.mem_of_pow_mem n (hn ▸ q.asIdeal.zero_mem)
  show x q ∈ V
  have : x q = (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀) q' := by
    rw [← h₁]
    exact congrArg x hq'.symm
  rw [this]
  exact hx0 ⟨q', rfl⟩

theorem exists_liftIn : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ GlobalTheory.SecLift.LiftIn π X g₀ f V :=
  exists_liftIn_unfolded

end GlobalTheory.SecLift
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

noncomputable section

namespace GlobalTheory.PtClosed

theorem represents_away (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop)
    (V : S.Opens) (hV : IsAffineOpen V) (a : Γ(S, V)) (J : Ideal Γ(S, S.basicOpen a))
    (hJ : Represents (ptQ P (S.basicOpen a) (hV.basicOpen a)) J) :
    ∃ J' : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J' := by
  let ρ := (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom
  letI : Algebra Γ(S, V) Γ(S, S.basicOpen a) := ρ.toAlgebra
  haveI : IsLocalization.Away a Γ(S, S.basicOpen a) := hV.isLocalization_basicOpen a
  let e : Localization.Away a ≃ₐ[Γ(S, V)] Γ(S, S.basicOpen a) :=
    IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) Γ(S, S.basicOpen a)
  refine ⟨J.map (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a), ?_⟩
  intro R' _ h
  have hc : h.comp (algebraMap Γ(S, V) (Localization.Away a)) =
      (h.comp (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a)).comp ρ := by
    ext x
    simp only [RingHom.comp_apply]
    congr 1
    have := e.symm.commutes x
    rw [← this]
    rfl
  have hs : ∀ g : Γ(S, S.basicOpen a) →+* R',
      spMap (g.comp ρ) ≫ hV.fromSpec = spMap g ≫ (hV.basicOpen a).fromSpec := by
    intro g
    rw [← hV.map_fromSpec (hV.basicOpen a) (homOfLE (S.basicOpen_le a)).op]
    simp only [ρ, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  show P R' (spMap _ ≫ hV.fromSpec) ↔ _
  rw [hc, hs, Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  exact hJ R' _

end GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem affine_local_represents : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∀ (V : S.Opens) (hV : IsAffineOpen V), ∃ s : Finset Γ(S, V), Ideal.span (s : Set Γ(S, V)) = ⊤ ∧
    ∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J := by
  intro S P hcov V hV
  let T : Set Γ(S, V) := {a | ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J}
  have hT : Ideal.span T = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro z hzV
    obtain ⟨U, hU, hzU, K, hK⟩ := hcov z
    obtain ⟨a, b, hab, hz⟩ := exists_basicOpen_le_affine_inter hV hU z ⟨hzV, hzU⟩
    have hle : S.basicOpen a ≤ U := hab ▸ S.basicOpen_le b
    have hJ := represents_restrict S P U (S.basicOpen a) hU (hV.basicOpen a) hle K hK
    have haT : a ∈ T := represents_away S P V hV a _ hJ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, haT⟩, hz⟩
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).1 hT
  exact ⟨s, hs, fun a ha ↦ hsT ha⟩

end GlobalTheory.PtClosed
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem of_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ (V : S.Opens) (hV : IsAffineOpen V), Represents (ptQ P V hV) (killIdeal (ptQ P V hV))) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S),
    (∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom) → P R' x := by
  intro S P hloc hrep R' _ x hx
  have key : ∀ (V : S.Opens) (hV : IsAffineOpen V) (r : R'),
      (∀ q : PrimeSpectrum R', r ∉ q.asIdeal → x.base q ∈ V) →
      P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x) := by
    intro V hV r hsub
    have e : (⊤ : (Sp (Localization.Away r)).Opens) ≤
        (spMap (algebraMap R' (Localization.Away r)) ≫ x) ⁻¹ᵁ V := by
      intro q _
      show x.base ((spMap (algebraMap R' (Localization.Away r))).base q) ∈ V
      apply hsub
      intro h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit r))
    let g' : Γ(S, V) ⟶ CommRingCat.of (Localization.Away r) :=
      (spMap (algebraMap R' (Localization.Away r)) ≫ x).appLE V ⊤ e ≫ (Scheme.ΓSpecIso _).hom
    have hy : spMap (algebraMap R' (Localization.Away r)) ≫ x = spMap g'.hom ≫ hV.fromSpec := by
      have h1 := IsAffineOpen.SpecMap_appLE_fromSpec (spMap (algebraMap R' (Localization.Away r)) ≫ x) hV
        (isAffineOpen_top (Sp (Localization.Away r))) e
      rw [IsAffineOpen.fromSpec_top] at h1
      rw [(Iso.inv_comp_eq _).1 h1.symm, Scheme.isoSpec_Spec_hom]
      simp only [spMap, CommRingCat.ofHom_hom, g', Spec.map_comp, Category.assoc]
    have hker : killIdeal (ptQ P V hV) ≤ RingHom.ker g'.hom := by
      refine (hx V hV).trans ?_
      intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      have hg : g' = x.app V ≫ ((spMap (algebraMap R' (Localization.Away r))).appLE (x ⁻¹ᵁ V) ⊤ e ≫
          (Scheme.ΓSpecIso _).hom) := by
        simp only [g', Scheme.Hom.comp_appLE, Category.assoc]
      rw [hg, CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]
    have := (hrep V hV (Localization.Away r) g'.hom).2 hker
    rw [hy]
    exact this
  let G : Set R' := {r | ∃ V : S.Opens, IsAffineOpen V ∧ ∀ q : PrimeSpectrum R', r ∉ q.asIdeal → x.base q ∈ V}
  have hG : Ideal.span G = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum R' := ⟨m, hm.isPrime⟩
    obtain ⟨V, hV, hpV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
      (show x.base p ∈ (⊤ : S.Opens) from trivial)
    have hpV' : p ∈ (x ⁻¹ᵁ V : TopologicalSpace.Opens (PrimeSpectrum R')) := hpV
    obtain ⟨W, ⟨r, rfl⟩, hpW, hW⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (PrimeSpectrum.isBasis_basic_opens (R := R'))) hpV'
    have hr : r ∈ G := ⟨V, hV, fun q hq => hW (show q ∈ PrimeSpectrum.basicOpen r from hq)⟩
    exact hpW (hle (Ideal.subset_span hr))
  obtain ⟨t, ht, hspan⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine hloc R' x t hspan fun r hr => ?_
  obtain ⟨V, hV, hsub⟩ := ht hr
  exact key V hV r hsub

end GlobalTheory.PtClosed
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem fromSpec_Sp_eq (R' : Type) [CommRing R'] {W : (Sp R').Opens} (hW : IsAffineOpen W) :
    hW.fromSpec = spMap ((Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
      (Sp R').presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (𝟙 (Sp R')) (isAffineOpen_top (Sp R')) hW le_top
  rw [Category.comp_id, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h]
  simp [spMap, Scheme.Hom.appLE]

theorem killIdeal_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
    P R' x → P R'' (spMap g ≫ x)) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), P R' x →
    ∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom := by
  intro S P hP R' _ x hx V hV a ha
  rw [RingHom.mem_ker]
  apply (Sp R').IsSheaf.section_ext
  intro p hp
  obtain ⟨W, hWa, hpW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Sp R').isBasis_affineOpens) hp
  refine ⟨W, hWle, hpW, ?_⟩
  have hW : IsAffineOpen W := hWa
  have e : hW.fromSpec ≫ x = spMap (x.appLE V W hWle).hom ≫ hV.fromSpec := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec x hV hW hWle]; rfl
  have hy : ptQ P V hV _ (x.appLE V W hWle).hom := by
    show P _ (spMap (x.appLE V W hWle).hom ≫ hV.fromSpec)
    rw [← e, fromSpec_Sp_eq]
    exact hP _ _ _ x hx
  have h0 := ha _ _ hy
  rw [map_zero]
  simpa [Scheme.Hom.appLE] using h0

end GlobalTheory.PtClosed
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem _root_.GlobalTheory.T.fderiv_eq_mulVec_of_schrodinger_annihilated : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → ∀ f : Sch l, (∀ j : l, dRho (s *ᵥ Pi.single (.inl j) 1) f = I • dRho (s *ᵥ Pi.single (.inr j) 1) f) → ∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * ((-(Q * P⁻¹))ᵀ *ᵥ fun i => (x i : ℂ)) a * f x := by
  first | exact @GlobalTheory.RealWeil.fderiv_eq_of_annihilated | exact GlobalTheory.RealWeil.fderiv_eq_of_annihilated | (intros; apply GlobalTheory.RealWeil.fderiv_eq_of_annihilated <;> assumption)
end

section


theorem _root_.GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G) (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q] (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π → (∀ κ x, π x = 0 → π (ρ κ x) = 0) → (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧ IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) → ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) → ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by
  first | exact @GlobalTheory.lift_forms_of_card_isUnit | exact GlobalTheory.lift_forms_of_card_isUnit | (intros; apply GlobalTheory.lift_forms_of_card_isUnit <;> assumption)
end
