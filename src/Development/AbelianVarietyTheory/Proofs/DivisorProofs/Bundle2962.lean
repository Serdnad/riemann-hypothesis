module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

open scoped TensorProduct

theorem piScalarRight_tmul_one {h M : ℕ} (a : Fin h ⊕ Fin h → ℤ) :
    TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h) ((1 : ZMod M) ⊗ₜ[ℤ] a) = reduceMod M a := by
  funext i
  simp [TensorProduct.piScalarRight_apply, reduceMod]

theorem omegaMod_reduceMod {h M : ℕ} (a c : Fin h ⊕ Fin h → ℤ) :
    omegaMod M (reduceMod M a) (reduceMod M c) = ((omegaStd a c : ℤ) : ZMod M) := by
  simp [omegaMod, omegaStd, reduceMod]

theorem sp_exists_spMap {A B : Type} [CommRing A] [CommRing B] (g : Sp B ⟶ Sp A) : ∃ f : A →+* B, g = spMap f :=
  ⟨(Spec.preimage g).hom, by simp [spMap]⟩

theorem sympCond_fibre_existsUnique : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  Odd M → 1 ≤ h → ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)),
  (∀ a, ∃ n : ℕ, IsMultOf a n ∧ σ a (zetaAway M) = zetaAway M ^ n) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    (t₁ t₁' : Sp K ⟶ Sp (cycAway M)) (lv lv' : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)),
    SympCond o h M (Over.mk x) t₁ lv → SympCond o h M (Over.mk x) t₁' lv' →
    ∃! a : sympSimGrp h M, t₁ ≫ spMap (σ a) = t₁' ∧ ∀ c, sympTwist a lv c = lv' c := by
  intro p _ D R _ b N h M hM hodd hh σ hσ S t o K _ _ x t₁ t₁' lv lv' H H'
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, -, hgeo⟩ := H
  obtain ⟨hadd', -, hgeo'⟩ := H'
  obtain ⟨β, hβ⟩ := sp_exists_spMap t₁
  obtain ⟨β', hβ'⟩ := sp_exists_spMap t₁'
  have hζ : ∀ g₀ : cycAway M →+* K, g₀ (zetaAway M) ^ M = 1 := fun g₀ => by
    rw [← map_pow, zetaAway_pow_self M hM.ne', map_one]
  let z : Kˣ := Units.ofPowEqOne _ M (hζ β) hM.ne'
  let z' : Kˣ := Units.ofPowEqOne _ M (hζ β') hM.ne'
  obtain ⟨hk, hon, hW⟩ := hgeo K (𝟙 _) β z (by rw [Category.id_comp, hβ]) rfl
  obtain ⟨hk', hon', hW'⟩ := hgeo' K (𝟙 _) β' z' (by rw [Category.id_comp, hβ']) rfl
  let jx : Over.mk (𝟙 (Sp K) ≫ x) ⟶ Over.mk x := Over.homMk (𝟙 _) rfl
  have canc : ∀ f g : Over.mk x ⟶ o.A, jx ≫ f = jx ≫ g → f = g := by
    intro f g e
    apply Over.OverMorphism.ext
    have := congrArg CommaMorphism.left e
    simpa [jx] using this
  let φ : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A) := fun a => jx ≫ lv a
  let φ' : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A) := fun a => jx ≫ lv' a
  have hφ : ∀ a c, φ (a + c) = φ a * φ c := fun a c => by simp only [φ, hadd, MonObj.comp_mul]
  have hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c := fun a c => by simp only [φ', hadd', MonObj.comp_mul]
  have hkφ : ∀ a, φ a = 1 ↔ ∃ c, a = M • c := fun a => hk a
  have hkφ' : ∀ a, φ' a = 1 ↔ ∃ c, a = M • c := fun a => hk' a
  have hr : ∀ b, ∃ c, φ c = φ' b := fun b => hon (φ' b) (by
    rw [← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ', (hkφ' _).2 ⟨b, rfl⟩])
  have hr' : ∀ c, ∃ b, φ' b = φ c := fun c => hon' (φ c) (by
    rw [← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ, (hkφ _).2 ⟨c, rfl⟩])
  obtain ⟨e, he⟩ := GlobalTheory.UPel.TensorTorsionNsmul.exists_equiv M φ φ' hφ hφ' hkφ hkφ' hr hr'
  let E := TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h)
  let e' := E.symm.trans (e.trans E)
  have he' : ∀ b c, e' (reduceMod M b) = reduceMod M c ↔ φ c = φ' b := by
    intro b c
    rw [← he, ← piScalarRight_tmul_one, ← piScalarRight_tmul_one]
    show E (e (E.symm (E _))) = E _ ↔ _
    rw [LinearEquiv.symm_apply_apply, E.injective.eq_iff]
  have hz : IsPrimitiveRoot z M := IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hM.ne' β)
  obtain ⟨i, hcop, he_i⟩ := exists_pow_of_isLocalRing hM.ne' β β'
  have hzi : z ^ i = z' := Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    exact he_i.symm)
  have h2u : IsUnit (2 : ZMod M) := by
    have := (ZMod.isUnit_iff_coprime 2 M).2 (Nat.coprime_two_left.2 hodd)
    exact_mod_cast this
  have hval : ∀ a b c d, φ c = φ' a → φ d = φ' b →
      ((omegaStd c d : ℤ) : ZMod M) = (i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) := by
    intro a b c d hc hd
    have w₁ := hW c d
    have w₂ := hW' a b
    change Out.WeilIs _ _ _ (φ' a) (φ' b) _ at w₂
    change Out.WeilIs _ _ _ (φ c) (φ d) _ at w₁
    rw [← hc, ← hd] at w₂
    have e₁ := H1.unitOn_injective
      (GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) w₂ w₁)
    rw [← hzi, ← zpow_natCast, ← zpow_mul] at e₁
    have h2 : z ^ ((i : ℤ) * (2 * omegaStd a b) - 2 * omegaStd c d) = 1 := by
      rw [zpow_sub, e₁, mul_inv_cancel]
    rw [hz.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    push_cast at h2
    have h3 : (2 : ZMod M) * ((i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) - ((omegaStd c d : ℤ) : ZMod M)) = 0 := by
      linear_combination h2
    have h4 := h2u.mul_right_eq_zero.1 h3
    linear_combination -h4
  have hmul : ∀ X Y, omegaMod M (e' X) (e' Y) = (i : ZMod M) * omegaMod M X Y := by
    intro X Y
    obtain ⟨a, rfl⟩ : ∃ a, reduceMod M a = X := ⟨liftMod X, reduceMod_liftMod X⟩
    obtain ⟨b, rfl⟩ : ∃ b, reduceMod M b = Y := ⟨liftMod Y, reduceMod_liftMod Y⟩
    obtain ⟨c, hc⟩ := hr a
    obtain ⟨d, hd⟩ := hr b
    rw [(he' a c).2 hc, (he' b d).2 hd, omegaMod_reduceMod, omegaMod_reduceMod]
    exact hval a b c d hc hd
  have hsim : e' ∈ sympSimGrp h M :=
    ⟨ZMod.unitOfCoprime i hcop, fun X Y => by rw [ZMod.coe_unitOfCoprime]; exact hmul X Y⟩
  let a₀ : sympSimGrp h M := ⟨e', hsim⟩
  have hmul₀ : IsMultOf a₀ i := hmul
  refine ⟨a₀, ⟨?_, fun c => canc _ _ ?_⟩, ?_⟩
  · obtain ⟨n, hn, hσn⟩ := hσ a₀
    have hni : (n : ZMod M) = i := isMultOf_unique hh hn hmul₀
    have hc : β.comp (σ a₀) = β' := cycAway_hom_ext hM.ne' (by
      rw [RingHom.comp_apply, hσn, zetaAway_pow_eq M hM.ne' hni, map_pow, he_i])
    rw [hβ, hβ', spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  · change φ (liftMod (e' (reduceMod M c))) = φ' c
    exact (he' c _).1 (reduceMod_liftMod _).symm
  · rintro a ⟨-, ha⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    obtain ⟨b', rfl⟩ : ∃ b', reduceMod M b' = X := ⟨liftMod X, reduceMod_liftMod X⟩
    have h1 : φ (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))) = φ' b' :=
      congrArg (jx ≫ ·) (ha b')
    rw [← reduceMod_liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))]
    exact ((he' b' _).2 h1).symm

end GlobalTheory.HTSympCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

theorem reduceMod_eq_zero_iff {h : ℕ} (M : ℕ) (u : Fin h ⊕ Fin h → ℤ) :
    reduceMod M u = 0 ↔ ∃ c, u = M • c := by
  constructor
  · intro hu
    refine ⟨fun i => u i / M, ?_⟩
    funext i
    have hi : ((u i : ℤ) : ZMod M) = 0 := congrFun hu i
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' hi).symm
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]

theorem omegaStd_cast {h : ℕ} (M : ℕ) (u v : Fin h ⊕ Fin h → ℤ) :
    ((omegaStd u v : ℤ) : ZMod M) = omegaMod M (reduceMod M u) (reduceMod M v) := by
  simp [omegaStd, omegaMod, reduceMod]

theorem sympCond_twist : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
    (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)), SympCond o h M T t₁ lv →
    ∀ (a : sympSimGrp h M) (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n →
      σ (zetaAway M) = zetaAway M ^ n → SympCond o h M T (t₁ ≫ spMap σ) (sympTwist a lv) := by
  intro p _ D R _ b N h M hM S t o T t₁ lv hlv a n σ hn hσ
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, htor, hgeo⟩ := hlv

  let φ : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (T ⟶ o.A) :=
    MonoidHom.mk' (fun u => lv (Multiplicative.toAdd u)) (fun u v => hadd _ _)
  have hsm : ∀ (k : ℕ) (w : Fin h ⊕ Fin h → ℤ), lv (k • w) = lv w ^ k := by
    intro k w
    have := map_pow φ (Multiplicative.ofAdd w) k
    simpa [φ, ← ofAdd_nsmul] using this
  have per : ∀ {u v : Fin h ⊕ Fin h → ℤ}, reduceMod M u = reduceMod M v → lv u = lv v := by
    intro u v huv
    have h0 : reduceMod M (u - v) = 0 := by
      funext i
      have := congrFun huv i
      simp only [reduceMod, Pi.sub_apply, Pi.zero_apply, Int.cast_sub] at this ⊢
      rw [this, sub_self]
    obtain ⟨w, hw⟩ := (reduceMod_eq_zero_iff M _).1 h0
    have : u = v + M • w := by rw [← hw]; abel
    rw [this, hadd, hsm, htor, _root_.mul_one]
  let g := (a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
  have tw : ∀ u, sympTwist a lv u = lv (liftMod (g (reduceMod M u))) := fun u => rfl
  have redAdd : ∀ u v : Fin h ⊕ Fin h → ℤ, reduceMod M (u + v) = reduceMod M u + reduceMod M v := by
    intro u v; funext i; simp [reduceMod]
  refine ⟨fun u c => ?_, fun u => ?_, fun k _ _ x β' z' hx' hz' => ?_⟩
  · rw [tw, tw, tw, ← hadd]
    apply per
    rw [reduceMod_liftMod, redAdd, redAdd, reduceMod_liftMod, reduceMod_liftMod, map_add (f := _)]
  · rw [tw]; exact htor _
  ·
    set β : cycAway M →+* k := (Spec.preimage (x ≫ t₁)).hom with hβdef
    have hβ : x ≫ t₁ = spMap β := by
      simp only [spMap, hβdef, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hβ' : β' = β.comp σ := by
      have e : spMap β' = spMap (β.comp σ) := by
        rw [spMap_comp, ← hx', ← hβ, Category.assoc]
      have := Spec.map_injective e
      exact congrArg CommRingCat.Hom.hom this
    have hζM : β (zetaAway M) ^ M = 1 := by
      rw [← map_pow, zetaAway_pow_self M hM.ne', map_one]
    have hne : β (zetaAway M) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM.ne'] at hζM
      exact zero_ne_one hζM
    set z : kˣ := Units.mk0 (β (zetaAway M)) hne with hzdef
    have hz : (z : k) = β (zetaAway M) := rfl
    have hzz : z' = z ^ n := by
      ext
      rw [hz', hβ', RingHom.comp_apply, hσ, map_pow, Units.val_pow_eq_pow_val, hz]
    have hzM : z ^ (M : ℤ) = 1 := by
      rw [zpow_natCast]; ext; rw [Units.val_pow_eq_pow_val, hz, hζM]; rfl
    obtain ⟨hK, hS, hW⟩ := hgeo k x β z hβ hz
    refine ⟨fun u => ?_, fun g' hg' => ?_, fun u c => ?_⟩
    · rw [tw, hK]
      constructor
      · rintro ⟨c, hc⟩
        apply (reduceMod_eq_zero_iff M u).1
        have : g (reduceMod M u) = 0 := by
          rw [← reduceMod_liftMod (g (reduceMod M u)), hc]
          exact (reduceMod_eq_zero_iff M _).2 ⟨c, rfl⟩
        exact (LinearEquiv.map_eq_zero_iff _).1 this
      · intro hu
        apply (reduceMod_eq_zero_iff M _).1
        rw [reduceMod_liftMod, (reduceMod_eq_zero_iff M u).2 hu, map_zero]
    · obtain ⟨u₀, hu₀⟩ := hS g' hg'
      refine ⟨liftMod (g.symm (reduceMod M u₀)), ?_⟩
      rw [tw, reduceMod_liftMod, LinearEquiv.apply_symm_apply, per (reduceMod_liftMod _)]
      exact hu₀
    · rw [tw, tw]
      set u' := liftMod (g (reduceMod M u))
      set c' := liftMod (g (reduceMod M c))
      have hcast : ((2 * omegaStd u' c' : ℤ) : ZMod M) = (((n : ℤ) * (2 * omegaStd u c) : ℤ) : ZMod M) := by
        push_cast
        rw [omegaStd_cast, omegaStd_cast, reduceMod_liftMod, reduceMod_liftMod]
        rw [show omegaMod M (g (reduceMod M u)) (g (reduceMod M c)) = n * omegaMod M (reduceMod M u) (reduceMod M c)
          from hn _ _]
        ring
      have e : z' ^ (2 * omegaStd u c) = z ^ (2 * omegaStd u' c') := by
        rw [hzz, ← zpow_natCast z, ← zpow_mul, zpow_eq_zpow_emod _ hzM, zpow_eq_zpow_emod (2 * omegaStd u' c') hzM]
        congr 1
        exact ((ZMod.intCast_eq_intCast_iff' _ _ _).1 hcast).symm
      rw [e]
      exact hW u' c'

end GlobalTheory.HTSympCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A)
  (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)

theorem prod_tw {T : Over (Sp R)} (x : T ⟶ D₀.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (x.left ≫ twφ D₀ D β b i) ^ twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have hu : x ≫ toUnit D₀.P.A = toUnit T := toUnit_unique _ _
  rw [Fin.prod_univ_three]
  show h (x ≫ (β * (toUnit D₀.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₀.P.A ≫ b).left ^ (-1 : ℤ) *
    h (x ≫ toUnit D₀.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
  rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
  rfl

theorem lift_β {T : Over (Sp R)} (p q : T ⟶ D₀.P.A) :
    (lift p q).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left =
      (lift (p ≫ β) (q ≫ β)).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]

variable {D₀ D β b} [IsMonHom β]

theorem wv_mul {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen)
    {wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D.P.A D.P.L).pull
      (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left)} (hΛ : wΛ.IsGen)
    {T : Over (Sp R)} (x y : T ⟶ D₀.P.A) {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') :
    wv w (x * y).left z J J' * wv w (1 : T ⟶ D₀.P.A).left z J J' *
        lamVal wΛ (lift (1 : T ⟶ D₀.P.A) (1 : T ⟶ D₀.P.A)).left z J J' =
      wv w x.left z J J' * wv w y.left z J J' * lamVal wΛ (lift x y).left z J J' *
        cubV D.cub z J (x ≫ β) (y ≫ β) (toUnit T ≫ b) := by
  have hG := GlobalTheory.globalFns_holds
  let B₀ := D₀.P.A
  let f : B₀ ⊗ B₀ ⟶ B₀ := fst B₀ B₀
  let s : B₀ ⊗ B₀ ⟶ B₀ := snd B₀ B₀
  have H := (((((reg_wv hw (f * s).left).mul (reg_wv hw f.left).inv).mul (reg_wv hw s.left).inv).mul
    (reg_wv hw (1 : B₀ ⊗ B₀ ⟶ B₀).left)).mul (reg_lam hΛ (lift f s).left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b))).left).inv
  have ev : ∀ x y : T ⟶ B₀,
      wv w ((lift x y).left ≫ (f * s).left) z J J' * (wv w ((lift x y).left ≫ f.left) z J J')⁻¹ *
        (wv w ((lift x y).left ≫ s.left) z J J')⁻¹ * wv w ((lift x y).left ≫ (1 : B₀ ⊗ B₀ ⟶ B₀).left) z J J' *
        (lamVal wΛ ((lift x y).left ≫ (lift f s).left) z J J')⁻¹ *
        (val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          ((lift x y).left ≫ (lift (f ≫ β) (lift (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b))).left) z J)⁻¹ =
      wv w (x * y).left z J J' * (wv w x.left z J J')⁻¹ * (wv w y.left z J J')⁻¹ *
        wv w (1 : T ⟶ B₀).left z J J' * (lamVal wΛ (lift x y).left z J J')⁻¹ *
        (cubV D.cub z J (x ≫ β) (y ≫ β) (toUnit T ≫ b))⁻¹ := fun x y => by
    have hu : lift x y ≫ toUnit (B₀ ⊗ B₀) = toUnit T := toUnit_unique _ _
    simp only [← Over.comp_left]
    rw [MonObj.comp_mul, MonObj.comp_one, comp_lift, comp_lift, comp_lift, ← Category.assoc (lift x y) (toUnit _), hu,
      lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]
    rfl
  have E := H.rigid D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ * _ * _ = _
      rw [prod_tw, prod_tw, prod_tw, prod_tw, lift_β, prod_lam, prod_lam]
      erw [prod_cub (G := D.P.A) (f ≫ β) (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b) h]
      rw [MonObj.mul_comp, MonObj.one_comp,
        _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    ((snd B₀ B₀).left ≫ B₀.hom) (surj_comp (surj_snd hG D₀.P.isAb _) (hG _ _ D₀.P.isAb).2)
    (lift x y).left (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left (by
      rw [Over.w, Over.w, Over.w]) z hJ hJ'
  have E' := (ev x y).symm.trans (E.trans (ev 1 1))
  rw [MonObj.one_comp, (isCub_cubV D.cub hJ).face, _root_.mul_one (1 : T ⟶ B₀)] at E'
  apply Additive.ofMul.injective
  have e := congrArg Additive.ofMul E'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e ⊢
  linear_combination (norm := abel) e

theorem wv_inv (hb : padd D.P.A b b = η[D.P.A]) {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen)
    {T : Over (Sp R)} (x : T ⟶ D₀.P.A) {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') :
    wv w x.left z J J' * val D.sym (x ≫ β).left z J * cubV D.cub z J (x ≫ β) (toUnit T ≫ b) (toUnit T ≫ b) =
      wv w (x⁻¹).left z J J' * val D₀.sym x.left z J' * cubV D.cub z J (x ≫ β) (x ≫ β)⁻¹ (toUnit T ≫ b) := by
  have hG := GlobalTheory.globalFns_holds
  let B₀ := D₀.P.A
  let f : B₀ ⟶ B₀ := 𝟙 B₀
  have hbb : (toUnit B₀ ≫ b) * (toUnit B₀ ≫ b) = 1 := by
    rw [← MonObj.comp_mul]; exact congrArg (toUnit B₀ ≫ ·) hb
  have H := (((((reg_wv hw f.left).mul (reg_val (L' := D₀.P.L) D.sym_gen (f ≫ β).left)).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (toUnit B₀ ≫ b) (toUnit B₀ ≫ b))).left)).mul (reg_wv hw (f⁻¹).left).inv).mul
      (reg_val' (L := D.P.L) D₀.sym_gen f.left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (f ≫ β)⁻¹ (toUnit B₀ ≫ b))).left).inv
  have ev : ∀ x : T ⟶ B₀,
      wv w (x.left ≫ f.left) z J J' * val D.sym (x.left ≫ (f ≫ β).left) z J *
        val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          (x.left ≫ (lift (f ≫ β) (lift (toUnit B₀ ≫ b) (toUnit B₀ ≫ b))).left) z J *
        (wv w (x.left ≫ (f⁻¹).left) z J J')⁻¹ * (val D₀.sym (x.left ≫ f.left) z J')⁻¹ *
        (val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          (x.left ≫ (lift (f ≫ β) (lift (f ≫ β)⁻¹ (toUnit B₀ ≫ b))).left) z J)⁻¹ =
      wv w x.left z J J' * val D.sym (x ≫ β).left z J * cubV D.cub z J (x ≫ β) (toUnit T ≫ b) (toUnit T ≫ b) *
        (wv w (x⁻¹).left z J J')⁻¹ * (val D₀.sym x.left z J')⁻¹ *
        (cubV D.cub z J (x ≫ β) (x ≫ β)⁻¹ (toUnit T ≫ b))⁻¹ := fun x => by
    have hu : x ≫ toUnit B₀ = toUnit T := toUnit_unique _ _
    simp only [← Over.comp_left]
    rw [comp_lift, comp_lift, comp_lift, comp_lift, ← Category.assoc x (toUnit _), hu, GrpObj.comp_inv, GrpObj.comp_inv,
      ← Category.assoc x f, Category.comp_id]
    rfl
  have E := H.rigid D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ * _ * _ = _
      rw [prod_tw, prod_tw, GlobalTheory.GaugeValues.prod_sym, GlobalTheory.GaugeValues.prod_sym]
      erw [prod_cub (G := D.P.A) (f ≫ β) (toUnit B₀ ≫ b) (toUnit B₀ ≫ b) h,
        prod_cub (G := D.P.A) (f ≫ β) (f ≫ β)⁻¹ (toUnit B₀ ≫ b) h]
      rw [GrpObj.inv_comp,
        _root_.mul_assoc (f ≫ β), hbb, _root_.mul_one (f ≫ β), mul_inv_cancel (f ≫ β), _root_.one_mul (toUnit B₀ ≫ b)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    B₀.hom (hG _ _ D₀.P.isAb).2 x.left (1 : T ⟶ B₀).left (by rw [Over.w, Over.w]) z hJ hJ'
  have E' := (ev x).symm.trans (E.trans (ev 1))
  rw [MonObj.one_comp, (isCub_cubV D.cub hJ).face, (isCub_cubV D.cub hJ).face, inv_one,
    GlobalTheory.GaugeValues.val_sym_one D hJ, GlobalTheory.GaugeValues.val_sym_one D₀ hJ'] at E'
  apply Additive.ofMul.injective
  have e := congrArg Additive.ofMul E'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e ⊢
  linear_combination (norm := abel) e

end GlobalTheory.MumCmp.Point
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp

theorem exists_cmpGen_of_lbIso (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A)
    (H : LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)
      (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)) :
    ∃ u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u.IsGen := by
  obtain ⟨w, hw⟩ := H
  have h₁ := isPart_inl P₁.L P₂.L
  have h₂ := isPart_inr P₁.L P₂.L
  have le : ∀ j : KK → (join P₁.L P₂.L).ι, LB.wchart (join P₁.L P₂.L) (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) j ≤
      (LB.div (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)
        (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)).U
        (fun k => (j (.inl k)).2, fun k => (j (.inr k)).1) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => (h₂.mem _ _).1 (Set.mem_iInter.1 hy (.inl k)),
      Set.mem_iInter.2 fun k => (h₁.mem _ _).1 (Set.mem_iInter.1 hy (.inr k))⟩
  let c : ChartPull (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)
      (LB.div (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)
        (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)) (𝟙 _) :=
    { idx := fun j => (fun k => (j (.inl k)).2, fun k => (j (.inr k)).1)
      le := le
      g := fun y j j' hj hj' => by
        refine (gm_linComb (join P₁.L P₂.L) _ _ (𝟙 _) y j j' hj hj').trans ?_
        refine Eq.trans ?_ (gm_div _ _ (𝟙 _) y _ _ ⟨le j hj, le j' hj'⟩).symm
        refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹)
          (gm_linComb P₂.L _ _ (𝟙 _) y _ _ (le j hj).1 (le j' hj').1)
          (gm_linComb P₁.L _ _ (𝟙 _) y _ _ (le j hj).2 (le j' hj').2)).symm
        rw [Fintype.prod_sum_type, ← Finset.prod_inv_distrib]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ _) ?_)
          (Finset.prod_congr rfl fun k _ => (zpow_neg _ _).trans (congrArg (fun u => (u ^ _)⁻¹) ?_))
        · refine Eq.trans ?_ (h₂.g _ (𝟙 _ ≫ (psum P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] k.down).left) y _ _
            ((h₂.mem _ _).1 (Set.mem_iInter.1 hj (.inl k))) ((h₂.mem _ _).1 (Set.mem_iInter.1 hj' (.inl k))))
          simp only [cmpφ, Sum.elim_inl, Category.assoc]
        · refine Eq.trans ?_ (h₁.g _ (𝟙 _ ≫ (psum P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] k.down).left) y _ _
            ((h₁.mem _ _).1 (Set.mem_iInter.1 hj (.inr k))) ((h₁.mem _ _).1 (Set.mem_iInter.1 hj' (.inr k))))
          simp only [cmpφ, Sum.elim_inr, Category.assoc] }
  exact ⟨cGen c w, cGen_isGen c hw⟩

end GlobalTheory.Mum.Two.WeilCmp
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem _root_.GlobalTheory.T.existsUnique_similitude_between_symplecticLevels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  Odd M → 1 ≤ h → ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)),
  (∀ a, ∃ n : ℕ, IsMultOf a n ∧ σ a (zetaAway M) = zetaAway M ^ n) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    (t₁ t₁' : Sp K ⟶ Sp (cycAway M)) (lv lv' : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)),
    SympCond o h M (Over.mk x) t₁ lv → SympCond o h M (Over.mk x) t₁' lv' →
    ∃! a : sympSimGrp h M, t₁ ≫ spMap (σ a) = t₁' ∧ ∀ c, sympTwist a lv c = lv' c := by
  first | exact @GlobalTheory.HTSympCover.sympCond_fibre_existsUnique | exact GlobalTheory.HTSympCover.sympCond_fibre_existsUnique | (intros; apply GlobalTheory.HTSympCover.sympCond_fibre_existsUnique <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem _root_.GlobalTheory.T.symplecticLevel_twist_by_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
    (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)), SympCond o h M T t₁ lv →
    ∀ (a : sympSimGrp h M) (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n →
      σ (zetaAway M) = zetaAway M ^ n → SympCond o h M T (t₁ ≫ spMap σ) (sympTwist a lv) := by
  first | exact @GlobalTheory.HTSympCover.sympCond_twist | exact GlobalTheory.HTSympCover.sympCond_twist | (intros; apply GlobalTheory.HTSympCover.sympCond_twist <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

theorem _root_.GlobalTheory.T.exists_weilComparisonGenerator_of_lambdaBundleIso : ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∃ u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u.IsGen := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso | exact GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso | (intros; apply GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso <;> assumption)

end
end
