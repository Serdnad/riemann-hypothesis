module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.valPtsX_of :
    ValPtsX := by
  intro S K h hp V _ _ _ z
  have : IsProper h := hp
  constructor
  · intro g g' hg hg' e
    have c : CommSq (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ g)
        (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z :=
      ⟨by rw [Category.assoc, hg]⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, _, z, c⟩
    have hs : Subsingleton Q.commSq.LiftStruct := IsSeparated.valuativeCriterion h Q
    let l₁ : Q.commSq.LiftStruct := ⟨g, rfl, hg⟩
    let l₂ : Q.commSq.LiftStruct := ⟨g', e.symm, hg'⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
  · intro g hg
    have c : CommSq g (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z := ⟨hg⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, g, z, c⟩
    have hu : (ValuativeCriterion.Existence ⊓ @QuasiCompact) h := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    obtain ⟨l, h₁, h₂⟩ := (hu.1 Q).exists_lift
    exact ⟨l, h₂, h₁⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.frobRing_of :
    FrobRing := by
  intro p f hp κ _ _ A _ B Λ _ _ _ _ i hi ε₀ hε ν g hg
  have hpΛ : (p : Λ) = 0 := by
    have h := map_natCast (algebraMap κ Λ) p
    rw [CharP.cast_eq_zero κ p, map_zero] at h
    exact h.symm
  let σ : Λ →+* Λ := GlobalTheory.SS.FrobField.powHom Λ p f hp hpΛ
  have hσ : ∀ c, σ c = c ^ p ^ f := fun _ => rfl
  have h0 : (p : Γ(Sp Λ, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp Λ hpΛ
  have hfr : GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 = spMap σ :=
    GlobalTheory.SS.FrobField.absFrob_spec Λ p f hp h0 σ hσ
  have hmono : Mono i.left := (Over.forget _).map_mono i
  have h1 : (1 : algPt κ Λ ⟶ A).left = spMap (algebraMap κ Λ) ≫ spMap ε₀.toRingHom ≫ i.left := by
    have e : (1 : algPt κ Λ ⟶ A) = toUnit (algPt κ Λ) ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ A) := by
      simp
    have e2 : (toUnit (algPt κ Λ)).left = spMap (algebraMap κ Λ) := by
      have := Over.w (toUnit (algPt κ Λ))
      simpa using this
    rw [e, Over.comp_left, e2]
    exact congrArg (spMap (algebraMap κ Λ) ≫ ·) hε.symm
  have sc : ∀ {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (u : R →+* S) (v : S →+* T),
      spMap v ≫ spMap u = spMap (v.comp u) := by
    intro R S T _ _ _ u v
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have key : FrobKill p f hp g ↔ σ.comp ν.toRingHom = (σ.comp (algebraMap κ Λ)).comp ε₀.toRingHom := by
    constructor
    · intro h
      have h2 := h h0
      change GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 ≫ g.left =
        GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 ≫ (1 : algPt κ Λ ⟶ A).left at h2
      rw [hfr, hg, h1] at h2
      simp only [← Category.assoc] at h2
      have h3 := (cancel_mono i.left).1 h2
      rw [sc, sc, sc] at h3
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
    · intro h hh
      change GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh ≫ g.left =
        GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh ≫ (1 : algPt κ Λ ⟶ A).left
      rw [show GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh = spMap σ from hfr, hg, h1]
      simp only [← Category.assoc]
      rw [sc, sc, sc, h]
  rw [key]
  constructor
  · intro h x hx
    have := RingHom.congr_fun h x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx, map_zero] at this
    rw [hσ] at this
    exact this
  · intro h
    ext x
    have hy : ε₀ (x - algebraMap κ B (ε₀ x)) = 0 := by
      simp
    have h2 := h _ hy
    have h3 : σ (ν (x - algebraMap κ B (ε₀ x))) = 0 := by rw [hσ]; exact h2
    rw [map_sub, map_sub, AlgHom.commutes, sub_eq_zero] at h3
    simpa using h3
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem finrank_quotient_eq_add_finrank_ker_factor (κ Λ : Type) [Field κ] [CommRing Λ] [Algebra κ Λ]
    [Module.Finite κ Λ] (I J : Ideal Λ) (h : I ≤ J) :
    Module.finrank κ (Λ ⧸ I) = Module.finrank κ (Λ ⧸ J) +
      Module.finrank κ (LinearMap.ker (Ideal.Quotient.factorₐ κ h).toLinearMap) := by
  haveI : Module.Finite κ (Λ ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ I).toLinearMap Ideal.Quotient.mk_surjective
  have hs : Function.Surjective (Ideal.Quotient.factorₐ κ h).toLinearMap :=
    Ideal.Quotient.factor_surjective h
  rw [← LinearMap.finrank_range_add_finrank_ker (Ideal.Quotient.factorₐ κ h).toLinearMap,
    LinearMap.range_eq_top.mpr hs, finrank_top]


private theorem ideal_eq_span_pow_of_finrank (κ Λ : Type) [Field κ] [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ]
    [Module.Finite κ Λ] (ε : Λ →ₐ[κ] κ) (t : Λ)
    (ht : IsLocalRing.maximalIdeal Λ = Ideal.span {t}) (q : ℕ) :
    ∀ J : Ideal Λ, Module.finrank κ (Λ ⧸ J) = q → J = Ideal.span {t ^ q} := by
  classical
  intro J hJ
  haveI : IsArtinianRing Λ := IsArtinianRing.of_finite κ Λ
  haveI hfin : ∀ I : Ideal Λ, Module.Finite κ (Λ ⧸ I) := fun I ↦
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ I).toLinearMap Ideal.Quotient.mk_surjective
  have tm : t ∈ IsLocalRing.maximalIdeal Λ := by
    rw [ht]
    exact Ideal.subset_span rfl
  have mem_m : ∀ a, a ∈ IsLocalRing.maximalIdeal Λ ↔ ∃ b, b * t = a := fun a ↦ by
    rw [ht, Ideal.mem_span_singleton']
  have mem_pow : ∀ k x, x ∈ Ideal.span {t ^ k} ↔ ∃ a, a * t ^ k = x := fun k x ↦
    Ideal.mem_span_singleton'
  have unit_of : ∀ a : Λ, a ∉ IsLocalRing.maximalIdeal Λ → IsUnit a := fun a ha ↦ by
    by_contra hu
    exact ha ((IsLocalRing.mem_maximalIdeal a).2 hu)
  have hker : ∀ a : Λ, a - algebraMap κ Λ (ε a) ∈ IsLocalRing.maximalIdeal Λ := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map ε
    simp at this
  have dec : ∀ a : Λ, ∃ b, a = algebraMap κ Λ (ε a) + b * t := by
    intro a
    obtain ⟨b, hb⟩ := (mem_m _).1 (hker a)
    exact ⟨b, by rw [hb]; ring⟩
  have drop : ∀ k, t ^ k ∈ Ideal.span {t ^ (k + 1)} → t ^ k = 0 := by
    intro k hk
    obtain ⟨a, ha⟩ := (mem_pow _ _).1 hk
    have hu : IsUnit (1 - a * t) := unit_of _ (fun h ↦ by
      have h1 : (1 : Λ) ∈ IsLocalRing.maximalIdeal Λ := by
        have := (IsLocalRing.maximalIdeal Λ).add_mem h
          ((IsLocalRing.maximalIdeal Λ).mul_mem_left a tm)
        simpa using this
      exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one)
    have e : t ^ k * (1 - a * t) = 0 := by
      calc t ^ k * (1 - a * t) = t ^ k - a * t ^ (k + 1) := by ring
        _ = 0 := by rw [ha, sub_self]
    exact hu.mul_left_eq_zero.1 e
  have hNex : ∃ N, t ^ N = 0 := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Λ)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, ht] at hN
    refine ⟨N, ?_⟩
    have h := Ideal.pow_mem_pow (Ideal.subset_span rfl : t ∈ Ideal.span {t}) N
    rw [hN] at h
    simpa using h
  obtain ⟨n, hn, hlt⟩ : ∃ n, t ^ n = 0 ∧ ∀ k < n, t ^ k ≠ 0 :=
    ⟨Nat.find hNex, Nat.find_spec hNex, fun k hk ↦ Nat.find_min hNex hk⟩
  have dimB : ∀ k ≤ n, Module.finrank κ (Λ ⧸ Ideal.span {t ^ k}) = k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [pow_zero, Ideal.span_singleton_one]
      haveI : Subsingleton (Λ ⧸ (⊤ : Ideal Λ)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      exact Module.finrank_zero_of_subsingleton
    | succ k ih =>
      intro hk
      have hle : Ideal.span {t ^ (k + 1)} ≤ Ideal.span {t ^ k} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow t (Nat.le_succ k))
      rw [finrank_quotient_eq_add_finrank_ker_factor κ Λ _ _ hle, ih (by omega)]
      congr 1
      set v := Ideal.Quotient.mk (Ideal.span {t ^ (k + 1)}) (t ^ k) with hv
      apply le_antisymm
      · have hsub : LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap ≤ κ ∙ v := by
          intro z hz
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
          rw [LinearMap.mem_ker] at hz
          have hx : x ∈ Ideal.span {t ^ k} := by
            rw [← Ideal.Quotient.eq_zero_iff_mem]
            simpa using hz
          obtain ⟨a, rfl⟩ := (mem_pow _ _).1 hx
          obtain ⟨b, hb⟩ := dec a
          rw [Submodule.mem_span_singleton]
          refine ⟨ε a, ?_⟩
          have e : a * t ^ k = algebraMap κ Λ (ε a) * t ^ k + b * t ^ (k + 1) := by
            linear_combination (t ^ k) * hb
          have hb0 : Ideal.Quotient.mk (Ideal.span {t ^ (k + 1)}) (b * t ^ (k + 1)) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ b (Ideal.subset_span rfl))
          rw [e, map_add (f := _), hb0, add_zero, map_mul, Algebra.smul_def, Ideal.Quotient.mk_algebraMap]
        exact (Submodule.finrank_mono hsub).trans
          (by simpa using finrank_span_le_card ({v} : Set (Λ ⧸ Ideal.span {t ^ (k + 1)})))
      · have hvk : v ∈ LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap := by
          rw [LinearMap.mem_ker]
          simp only [v, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply_mk]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        have hv0 : v ≠ 0 := by
          intro h0
          exact hlt k (by omega) (drop k (Ideal.Quotient.eq_zero_iff_mem.1 h0))
        have hne : LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap ≠ ⊥ := fun hb ↦
          hv0 ((Submodule.mem_bot κ).1 (hb ▸ hvk))
        exact Nat.one_le_iff_ne_zero.2 (fun h ↦ hne (Submodule.finrank_eq_zero.1 h))
  have factA : ∃ k ≤ n, J = Ideal.span {t ^ k} := by
    by_cases h0 : J ≤ Ideal.span {t ^ n}
    · refine ⟨n, le_rfl, le_antisymm h0 ?_⟩
      rw [hn, Ideal.span_singleton_eq_bot.2 rfl]
      exact bot_le
    · have hex : ∃ k, ¬ J ≤ Ideal.span {t ^ k} := ⟨n, h0⟩
      obtain ⟨k0, hk0, hk0n, hmin⟩ : ∃ k0, ¬ J ≤ Ideal.span {t ^ k0} ∧ k0 ≤ n ∧
          ∀ j < k0, J ≤ Ideal.span {t ^ j} :=
        ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex h0,
          fun j hj ↦ not_not.1 (Nat.find_min hex hj)⟩
      have hk0pos : k0 ≠ 0 := by
        intro hz
        apply hk0
        rw [hz, pow_zero, Ideal.span_singleton_one]
        exact le_top
      obtain ⟨k, rfl⟩ : ∃ k, k0 = k + 1 := Nat.exists_eq_succ_of_ne_zero hk0pos
      have hJk : J ≤ Ideal.span {t ^ k} := hmin k (by omega)
      obtain ⟨x, hxJ, hx⟩ := SetLike.not_le_iff_exists.1 hk0
      obtain ⟨a, rfl⟩ := (mem_pow _ _).1 (hJk hxJ)
      have ha : a ∉ IsLocalRing.maximalIdeal Λ := by
        intro ham
        obtain ⟨b, rfl⟩ := (mem_m _).1 ham
        apply hx
        rw [mem_pow]
        exact ⟨b, by ring⟩
      obtain ⟨u, hu⟩ := unit_of a ha
      refine ⟨k, by omega, le_antisymm hJk ?_⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have e : t ^ k = ↑u⁻¹ * (a * t ^ k) := by
        rw [← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
      rw [e]
      exact J.mul_mem_left _ hxJ
  obtain ⟨k, hkn, rfl⟩ := factA
  rw [dimB k hkn] at hJ
  rw [hJ]

theorem UpperTheory.Gal.crystallineComparison.Mod.chainLoc_of :
    ChainLoc := by
  intro κ Λ _ _ _ _ _ ε t ht J q hq
  exact ideal_eq_span_pow_of_finrank κ Λ ε t ht q J hq
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private lemma spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  dsimp only [spMap]
  rw [← Spec.map_comp]
  rfl

private lemma spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap]

private lemma spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g := by
  have h' : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'

private lemma exists_algHom {κ B C : Type} [Field κ] [CommRing B] [CommRing C] [Algebra κ B] [Algebra κ C]
    (f : Sp C ⟶ Sp B) (hf : f ≫ spMap (algebraMap κ B) = spMap (algebraMap κ C)) :
    ∃ φ : B →ₐ[κ] C, spMap φ.toRingHom = f := by
  obtain ⟨φ, rfl⟩ : ∃ φ, f = Spec.map φ := ⟨Spec.preimage f, (Spec.map_preimage f).symm⟩
  have hφ : φ.hom.comp (algebraMap κ B) = algebraMap κ C := by
    apply spMap_inj
    rw [← spMap_comp']
    exact hf
  exact ⟨{ toRingHom := φ.hom, commutes' := fun r => RingHom.congr_fun hφ r }, rfl⟩

private noncomputable def ptOf {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (ε : B →ₐ[κ] κ) :
    𝟙_ (Over (Sp κ)) ⟶ algPt κ B :=
  Over.homMk (spMap ε.toRingHom) (by
    show spMap ε.toRingHom ≫ spMap (algebraMap κ B) = 𝟙 _
    rw [spMap_comp', ← spMap_id']
    congr 1
    ext r
    simp)

private lemma ptOf_surj {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (y : 𝟙_ (Over (Sp κ)) ⟶ algPt κ B) :
    ∃ ε : B →ₐ[κ] κ, ptOf ε = y := by
  obtain ⟨ε, hε⟩ := exists_algHom (C := κ) y.left (by
    rw [Algebra.algebraMap_self, spMap_id']
    exact Over.w y)
  refine ⟨ε, Over.OverMorphism.ext ?_⟩
  rw [← hε]
  rfl

private lemma ptOf_inj {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] {ε ε' : B →ₐ[κ] κ}
    (h : ptOf ε = ptOf ε') : ε = ε' := by
  have h1 : spMap ε.toRingHom = spMap ε'.toRingHom := congrArg CommaMorphism.left h
  have h2 := spMap_inj h1
  ext x
  exact RingHom.congr_fun h2 x

end UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.repHomog_of :
    RepHomog := by
  intro κ _ A _ P hSub B _ _ i hmono hiff
  haveI : Mono i := hmono
  refine ⟨?_, ?_⟩
  · refine Nat.card_congr (Equiv.ofBijective
      (fun ε => (⟨ptOf ε ≫ i, (hiff _ _).1 ⟨_, rfl⟩⟩ : { g // P (𝟙_ (Over (Sp κ))) g })) ⟨?_, ?_⟩)
    · intro a b h
      apply ptOf_inj
      exact (cancel_mono i).1 (congrArg Subtype.val h)
    · rintro ⟨g, hg⟩
      obtain ⟨y, hy⟩ := (hiff _ _).2 hg
      obtain ⟨ε, rfl⟩ := ptOf_surj y
      exact ⟨ε, Subtype.ext hy⟩
  · obtain ⟨y, hy⟩ := (hiff _ _).2 (hSub (𝟙_ (Over (Sp κ)))).1
    obtain ⟨ε₀, rfl⟩ := ptOf_surj y
    refine ⟨ε₀, ?_, fun ε => ?_⟩
    · show spMap ε₀.toRingHom ≫ i.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left
      rw [← hy]
      rfl
    · let c : algPt κ B ⟶ A := toUnit (algPt κ B) ≫ ptOf ε ≫ i
      have hc : c = toUnit (algPt κ B) ≫ ptOf ε ≫ i := rfl
      have hcP : P _ c := (hiff _ _).1 ⟨toUnit _ ≫ ptOf ε, by rw [hc, Category.assoc]⟩
      have hiP : P _ i := (hiff _ _).1 ⟨𝟙 _, Category.id_comp _⟩
      have hcinvP : P _ c⁻¹ := by
        have h' := (hSub (algPt κ B)).2 1 c (hSub _).1 hcP
        simpa using h'
      have hm : P _ (i * c) := by
        have h' := (hSub (algPt κ B)).2 i c⁻¹ hiP hcinvP
        simpa using h'
      have hm' : P _ (i * c⁻¹) := (hSub _).2 i c hiP hcP
      obtain ⟨s, hs⟩ := (hiff _ _).2 hm
      obtain ⟨s', hs'⟩ := (hiff _ _).2 hm'
      have hsc : ∀ t : algPt κ B ⟶ algPt κ B, t ≫ c = c := by
        intro t
        rw [hc, ← Category.assoc, comp_toUnit]
      have h1 : s ≫ s' = 𝟙 _ := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs', comp_mul, hs, GrpObj.comp_inv, hsc, Category.id_comp,
          mul_inv_cancel_right]
      have h2 : s' ≫ s = 𝟙 _ := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs, comp_mul, hs', hsc, Category.id_comp, inv_mul_cancel_right]
      have hpt : ptOf ε₀ ≫ s = ptOf ε := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs, comp_mul, hy, _root_.one_mul, hc, ← Category.assoc,
          toUnit_unique (ptOf ε₀ ≫ toUnit _) (𝟙 _), Category.id_comp]
      obtain ⟨τ, hτ⟩ := exists_algHom (C := B) s.left (Over.w s)
      obtain ⟨τ', hτ'⟩ := exists_algHom (C := B) s'.left (Over.w s')
      have e1 : τ.comp τ' = AlgHom.id κ B := by
        have h' : spMap (τ.comp τ').toRingHom = spMap (RingHom.id B) := by
          rw [spMap_id']
          show spMap (τ.toRingHom.comp τ'.toRingHom) = _
          rw [← spMap_comp', hτ, hτ']
          exact congrArg CommaMorphism.left h1
        exact AlgHom.ext fun x => RingHom.congr_fun (spMap_inj h') x
      have e2 : τ'.comp τ = AlgHom.id κ B := by
        have h' : spMap (τ'.comp τ).toRingHom = spMap (RingHom.id B) := by
          rw [spMap_id']
          show spMap (τ'.toRingHom.comp τ.toRingHom) = _
          rw [← spMap_comp', hτ, hτ']
          exact congrArg CommaMorphism.left h2
        exact AlgHom.ext fun x => RingHom.congr_fun (spMap_inj h') x
      refine ⟨AlgEquiv.ofAlgHom τ τ' e1 e2, ?_⟩
      rw [AlgEquiv.coe_algHom_ofAlgHom]
      apply ptOf_inj
      apply Over.OverMorphism.ext
      show spMap (ε₀.toRingHom.comp τ.toRingHom) = (ptOf ε).left
      rw [← hpt]
      show _ = spMap ε₀.toRingHom ≫ s.left
      rw [← hτ, spMap_comp']
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private lemma closed_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of O)) (z : X) :
    s z = IsLocalRing.closedPoint O ↔ z ∉ X.basicOpen (fn s ϖ) := by
  have key : z ∈ X.basicOpen (fn s ϖ) ↔ ϖ ∉ (s z).asIdeal := by
    rw [show X.basicOpen (fn s ϖ) = s ⁻¹ᵁ (Spec (CommRingCat.of O)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) from (Scheme.preimage_basicOpen_top s _).symm]
    change s z ∈ (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) ↔ _
    rw [basicOpen_eq_of_affine]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [key, not_not]
  constructor
  · intro h
    have hm : (s z).asIdeal = IsLocalRing.maximalIdeal O := congrArg PrimeSpectrum.asIdeal h
    rw [hm]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  · intro h
    have hne : (s z).asIdeal ≠ ⊥ := fun hb0 => hϖ.ne_zero (by simpa [hb0] using h)
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne (s z).2))

theorem UpperTheory.Gal.crystallineComparison.Mod.genDown_of :
    GenDown := by
  intro O _ _ _ ϖ hϖ X Y s h hflat y hy
  have hc : ∀ y' : Y, s (h y') = IsLocalRing.closedPoint O ↔
      y' ∉ Y.basicOpen (fn (h ≫ s) ϖ) := by
    intro y'
    rw [← closed_iff hϖ (h ≫ s) y', Scheme.Hom.comp_apply]
  refine ⟨(hc y).mpr hy.1, fun z' hz' hsp => ?_⟩
  obtain ⟨y', hy'sp, rfl⟩ := Flat.generalizingMap h hsp
  have := hy.2 y' ((hc y').mp hz') hy'sp
  rw [this]
end
