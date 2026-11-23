module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.SpreadGrp

theorem grpObj_of_agree : ∀ (R : Type) [CommRing R] [IsDomain R] (f g : R), f ≠ 0 → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), Flat q → IsSeparated q → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsCommMonObj A → ∀ i : A.left ⟶ X, IsPullback i A.hom q (awayMap f) → ∀ (H : Over (Sp (Localization.Away g))) (h : H.left ⟶ X), IsPullback h H.hom q (awayMap g) → ∀ (m : H ⊗ H ⟶ H) (n : H ⟶ H) (o : 𝟙_ (Over (Sp (Localization.Away g))) ⟶ H), (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a b : Over.mk t₁ ⟶ H) (a' b' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → b.left ≫ h = b'.left ≫ i → (lift a b ≫ m).left ≫ h = (a' * b').left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a : Over.mk t₁ ⟶ H) (a' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → (a ≫ n).left ≫ h = (a'⁻¹).left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)), t₁ ≫ awayMap g = t₀ ≫ awayMap f → t₁ ≫ o.left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i) → ∃ _ : GrpObj H, MulAgree H A h i := by
  intro R _ _ f g hf X q hq hs A _ _ i hA H h hH m n o hm hn ho
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsSchemeTheoreticallyDominant (awayMap f) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective
      (CommRingCat.ofHom (algebraMap R (Localization.Away f))) hinj
  have : Flat (awayMap g) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (Submonoid.powers g))
  have : Flat H.hom := MorphismProperty.of_isPullback hH hq
  have : IsSeparated H.hom := MorphismProperty.of_isPullback hH hs
  have := ExtUnique.flat_tensorUnit (S := Sp (Localization.Away g))
  have := ExtUnique.flat_tensorObj H H
  have := ExtUnique.flat_tensorObj (𝟙_ _) H
  have := ExtUnique.flat_tensorObj H (𝟙_ _)
  have := ExtUnique.flat_tensorObj (H ⊗ H) H
  let j := pullback.fst (awayMap g) (awayMap f)
  let k := pullback.snd (awayMap g) (awayMap f)
  have w : ∀ T : Over (pullback (awayMap g) (awayMap f)), (T.hom ≫ j) ≫ awayMap g = (T.hom ≫ k) ≫ awayMap f := by
    intro T; simp only [Category.assoc, j, k, pullback.condition]

  have key : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} {t₀ : T ⟶ Sp (Localization.Away f)},
      t₁ ≫ awayMap g = t₀ ≫ awayMap f → ∀ a : Over.mk t₁ ⟶ H, ∃ a' : Over.mk t₀ ⟶ A, a.left ≫ h = a'.left ≫ i := by
    intro T t₁ t₀ e a
    have e' : (a.left ≫ h) ≫ q = t₀ ≫ awayMap f := by
      rw [Category.assoc, hH.w, ← Category.assoc, Over.w a]; exact e
    exact ⟨Over.homMk (hA.lift (a.left ≫ h) t₀ e') (hA.lift_snd _ _ _), (hA.lift_fst _ _ _).symm⟩

  have inj : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} (a b : Over.mk t₁ ⟶ H),
      a.left ≫ h = b.left ≫ h → a = b := by
    intro T t₁ a b e
    exact Over.OverMorphism.ext (hH.hom_ext e (by rw [Over.w a, Over.w b]))
  have hone : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} {t₀ : T ⟶ Sp (Localization.Away f)},
      t₁ ≫ awayMap g = t₀ ≫ awayMap f → (toUnit (Over.mk t₁) ≫ o).left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i := by
    intro T t₁ t₀ e
    simpa using ho T t₁ t₀ e
  letI : MonObj H :=
    { one := o
      mul := m
      one_mul := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ snd _ _ = x := ⟨_, rfl⟩
        have ht : t = lift (toUnit _) x :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        rw [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hone (w T)) hx', _root_.one_mul, hx']
      mul_one := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ fst _ _ = x := ⟨_, rfl⟩
        have ht : t = lift x (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        rw [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        apply inj
        rw [hm _ _ _ _ _ _ _ hx' (hone (w T)), _root_.mul_one, hx']
      mul_assoc := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ fst _ _ ≫ fst _ _ = x := ⟨_, rfl⟩
        obtain ⟨y, hy⟩ : ∃ y, t ≫ fst _ _ ≫ snd _ _ = y := ⟨_, rfl⟩
        obtain ⟨z, hz⟩ : ∃ z, t ≫ snd _ _ = z := ⟨_, rfl⟩
        have ht : t = lift (lift x y) z := by
          ext <;> simp [← hx, ← hy, ← hz]
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        obtain ⟨y', hy'⟩ := key (w T) y
        obtain ⟨z', hz'⟩ := key (w T) z
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hm _ _ _ _ _ _ _ hx' hy') hz', hm _ _ _ _ _ _ _ hx' (hm _ _ _ _ _ _ _ hy' hz'),
          _root_.mul_assoc] }
  letI : GrpObj H :=
    { inv := n
      left_inv := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x', hx'⟩ := key (w T) t
        change _ ≫ lift n (𝟙 H) ≫ m = _ ≫ toUnit H ≫ o
        rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hn _ _ _ _ _ hx') hx', inv_mul_cancel, hone (w T)]
      right_inv := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x', hx'⟩ := key (w T) t
        change _ ≫ lift (𝟙 H) n ≫ m = _ ≫ toUnit H ≫ o
        rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ hx' (hn _ _ _ _ _ hx'), mul_inv_cancel, hone (w T)] }
  exact ⟨inferInstance, fun T t₁ t₂ a b a' b' ha hb => hm T t₁ t₂ a b a' b' ha hb⟩

end GlobalTheory.Desc.SpreadGrp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
noncomputable section

namespace GlobalTheory.Desc

theorem exists_desc_specStalk : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R), f ≠ 0 → ∀ (x : Sp R)
    (S₁ B Z B₀ B₁ : Scheme.{0}) (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)), Flat ξ' → Surjective ξ' →
    QuasiCompact ξ' → ∀ (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → IsSeparated pZ →
    ∀ (φ₀ : B₀ ⟶ B) (q₀ : B₀ ⟶ Sp (Localization.Away f)) (u₀ : B₀ ⟶ Z) (φ₁ : B₁ ⟶ B) (q₁ : B₁ ⟶ S₁)
      (u₁ : B₁ ⟶ Z), IsPullback φ₀ q₀ pB (awayMap f) → IsPullback φ₁ q₁ pB (ξ' ≫ (Sp R).fromSpecStalk x) →
    u₁ ≫ pZ = φ₁ ≫ pB →
    (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t₁ : T ⟶ B₁), t₀ ≫ φ₀ = t₁ ≫ φ₁ → t₀ ≫ u₀ = t₁ ≫ u₁) →
    ∃ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB ∧
      ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)),
        t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u := by
  intro R _ _ f hf x S₁ B Z B₀ B₁ ξ' hξf hξs hξq pB pZ hpB hpZ φ₀ q₀ u₀ φ₁ q₁ u₁ h₀ h₁ hu₁ H
  have hs : Flat ((Sp R).fromSpecStalk x) := GenericExt.flat_fromSpecStalk _ x
  let π : B₁ ⟶ pullback pB ((Sp R).fromSpecStalk x) :=
    pullback.lift φ₁ (q₁ ≫ ξ') (by rw [h₁.w, Category.assoc])
  have hπ₁ : π ≫ pullback.fst _ _ = φ₁ := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ pullback.snd _ _ = q₁ ≫ ξ' := pullback.lift_snd _ _ _
  have hsq : IsPullback π q₁ (pullback.snd pB ((Sp R).fromSpecStalk x)) ξ' := by
    refine IsPullback.of_right ?_ hπ₂ (IsPullback.of_hasPullback pB ((Sp R).fromSpecStalk x))
    rw [hπ₁]; exact h₁
  have : Flat π := MorphismProperty.of_isPullback hsq.flip hξf
  have : Surjective π := MorphismProperty.of_isPullback hsq.flip hξs
  have : QuasiCompact π := MorphismProperty.of_isPullback hsq.flip hξq
  have : Flat φ₁ := by rw [← hπ₁]; infer_instance
  have key : pullback.fst π π ≫ u₁ = pullback.snd π π ≫ u₁ := by
    let g : pullback π π ⟶ Sp R := pullback.fst π π ≫ φ₁ ≫ pB
    have hg : Flat g := inferInstance
    have hφ : pullback.fst π π ≫ φ₁ = pullback.snd π π ≫ φ₁ := by
      rw [← hπ₁, pullback.condition_assoc]
    have hAf : IsSchemeTheoreticallyDominant (awayMap f) :=
      schDom_spec_map _ (IsLocalization.injective (Localization.Away f)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hf))
    have hdom : IsSchemeTheoreticallyDominant (pullback.fst g (awayMap f)) :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback g (awayMap f)).flip
    refine ext_of_schDom pZ ?_ (pullback.fst g (awayMap f)) ?_
    · simp only [Category.assoc, hu₁]; exact (reassoc_of% hφ) pB
    · let t₀ : pullback g (awayMap f) ⟶ B₀ :=
        h₀.lift (pullback.fst g (awayMap f) ≫ pullback.fst π π ≫ φ₁) (pullback.snd g (awayMap f))
          (by simpa [g] using pullback.condition (f := g) (g := awayMap f))
      have ht₀ : t₀ ≫ φ₀ = pullback.fst g (awayMap f) ≫ pullback.fst π π ≫ φ₁ := h₀.lift_fst _ _ _
      have e₁ := H _ t₀ (pullback.fst g (awayMap f) ≫ pullback.fst π π) (by rw [ht₀, Category.assoc])
      have e₂ := H _ t₀ (pullback.fst g (awayMap f) ≫ pullback.snd π π) (by rw [ht₀, Category.assoc, hφ])
      simp only [Category.assoc] at e₁ e₂
      rw [← e₁, ← e₂]
  have hE : EffectiveEpi π := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  let u := EffectiveEpi.desc π u₁ (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hu : π ≫ u = u₁ := EffectiveEpi.fac _ _ _
  have : Epi π := Flat.epi_of_flat_of_surjective π
  refine ⟨u, ?_, ?_⟩
  · rw [← cancel_epi π, reassoc_of% hu, hu₁, reassoc_of% hπ₁]
  · intro T t₀ t ht
    have : Epi (pullback.fst t π) := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.fst t π), pullback.condition_assoc, hu]
    have := H _ (pullback.fst t π ≫ t₀) (pullback.snd t π) (by
      rw [Category.assoc, ht, pullback.condition_assoc, hπ₁])
    simpa only [Category.assoc] using this

end GlobalTheory.Desc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.LocusQA

open GlobalTheory.Cartier.CartierDiv

variable {Y : Scheme.{0}} [IsIntegral Y] {y : Y}

theorem regAt_pow {f : Y.functionField} (hf : RegAt y f) (n : ℕ) : RegAt y (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

theorem unitAt_pow_iff {f : Y.functionField} (hf : RegAt y f) {n : ℕ} (hn : n ≠ 0) :
    UnitAt y (f ^ n) ↔ UnitAt y f := by
  obtain ⟨a, rfl⟩ := hf
  refine ⟨fun ⟨b, hb, e⟩ => ?_, fun ⟨b, hb, e⟩ => ⟨b ^ n, hb.pow n, by rw [map_pow, e]⟩⟩
  rw [← map_pow] at e
  obtain rfl := IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField e
  exact ⟨a, (isUnit_pow_iff hn).1 hb, rfl⟩

theorem regAt_div {f g : Y.functionField} (hf : RegAt y f) (hg : UnitAt y g) : RegAt y (f / g) := by
  rw [div_eq_mul_inv]; exact hf.mul hg.inv.regAt

theorem unitAt_div_iff {f g : Y.functionField} (hg : UnitAt y g) : UnitAt y (f / g) ↔ UnitAt y f := by
  refine ⟨fun h => ?_, fun h => by rw [div_eq_mul_inv]; exact h.mul hg.inv⟩
  have := h.mul hg
  rwa [div_mul_cancel₀ _ hg.ne_zero] at this

theorem pow_div_pow_eqn {K : Type} [Field K] (a b c : K) (hc : c ≠ 0) (m n : ℕ) :
    (a * c ^ m) ^ n / (b * c ^ n) ^ m = a ^ n / b ^ m := by
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m n, mul_div_mul_right _ _ (pow_ne_zero _ hc)]

theorem isQuasiAffine_locus : ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (D : CartierDiv Y), AmpleDiv D → ∀ (k : ℕ), 1 ≤ k → ∀ s ∈ Sec D k, ∀ V : Y.Opens,
    (V : Set Y) = locus D k s → V.toScheme.IsQuasiAffine := by
  intro Y _ _ _ D hD k hk s hs V hV
  have memV : ∀ y, y ∈ V ↔ (k • D).GeneratesAt y s := fun y => by
    rw [← SetLike.mem_coe, hV]; rfl
  have loc : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
      RegAt y (s * (e : Y.functionField) ^ k) ∧ (y ∈ V ↔ UnitAt y (s * (e : Y.functionField) ^ k)) := by
    intro y e he
    have h := he.nsmul k
    have h1 := h.regularAt_iff.1 (hs y)
    have h2 := (memV y).trans h.generatesAt_iff
    rw [Units.val_pow_eq_pow_val] at h1 h2
    exact ⟨h1, h2⟩
  have stepC : ∀ k', 1 ≤ k' → ∀ u ∈ Sec D k', ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y) = locus D k' u →
      IsAffineOpen (V ⊓ U) := by
    intro k' hk' u hu U hUa hUl
    have memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u := fun y => by
      rw [← SetLike.mem_coe, hUl]; rfl
    have locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
        (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k')) := by
      intro y e he
      have h := he.nsmul k'
      have h2 := (memU y).trans h.generatesAt_iff
      rw [Units.val_pow_eq_pow_val] at h2
      exact h2
    by_cases hg : genericPoint Y ∈ U
    swap
    · have : U = ⊥ := eq_bot_iff.2 fun y hy => (hg (gen_mem hy)).elim
      rw [this, inf_bot_eq]
      exact isAffineOpen_bot Y
    have hreg : ∀ y ∈ U, RegAt y (s ^ k' / u ^ k) := by
      intro y hy
      obtain ⟨e, he⟩ := D.exists_isEqn y
      have hB := (locU y e he).1 hy
      rw [← pow_div_pow_eqn s u _ e.ne_zero k k']
      exact regAt_div (regAt_pow (loc y e he).1 _) ((unitAt_pow_iff hB.regAt (by omega)).2 hB)
    obtain ⟨a, ha⟩ := exists_fnOf_eq hg hreg
    have e₁ : V ⊓ U = Y.basicOpen a := by
      ext y
      refine ⟨fun ⟨hyV, hyU⟩ => ?_, fun hy => ?_⟩
      · obtain ⟨e, he⟩ := D.exists_isEqn y
        have hB := (locU y e he).1 hyU
        refine (unitAt_fnOf_iff hyU hg a).1 ?_
        rw [ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB),
          unitAt_pow_iff (loc y e he).1 (by omega)]
        exact (loc y e he).2.1 hyV
      · have hyU : y ∈ U := Y.basicOpen_le a hy
        obtain ⟨e, he⟩ := D.exists_isEqn y
        have hB := (locU y e he).1 hyU
        have h := (unitAt_fnOf_iff hyU hg a).2 hy
        rw [ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB),
          unitAt_pow_iff (loc y e he).1 (by omega)] at h
        exact ⟨(loc y e he).2.2 h, hyU⟩
    rw [e₁]
    exact hUa.basicOpen a
  have : CompactSpace V := by
    choose kk hkk u hu U hUa hUl hxU using hD
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set Y)) (fun y => (U y).isOpen)
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxU y⟩)
    have e : (V : Set Y) = ⋃ y ∈ t, ((V ⊓ U y : Y.Opens) : Set Y) := by
      refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion₂_subset fun y _ => fun z hz => hz.1)
      obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
      exact Set.mem_iUnion₂.2 ⟨y, hy, hz, hzy⟩
    have hc : IsCompact (V : Set Y) := e ▸ t.isCompact_biUnion fun y _ =>
      (stepC (kk y) (hkk y) (u y) (hu y) (U y) (hUa y) (hUl y)).isCompact
    exact isCompact_iff_compactSpace.mp hc
  have : CompactSpace V.toScheme := inferInstanceAs (CompactSpace V)
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen _ fun x => ?_
  obtain ⟨k', hk', u, hu, U, hUa, hUl, hxU⟩ := hD x.1
  have memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u := fun y => by
    rw [← SetLike.mem_coe, hUl]; rfl
  have locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
      RegAt y (u * (e : Y.functionField) ^ k') ∧ (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k')) := by
    intro y e he
    have h := he.nsmul k'
    have h1 := h.regularAt_iff.1 (hu y)
    have h2 := (memU y).trans h.generatesAt_iff
    rw [Units.val_pow_eq_pow_val] at h1 h2
    exact ⟨h1, h2⟩
  have hg : genericPoint Y ∈ V := gen_mem x.2
  have hreg : ∀ y ∈ V, RegAt y (u ^ k / s ^ k') := by
    intro y hy
    obtain ⟨e, he⟩ := D.exists_isEqn y
    have hA := (loc y e he).2.1 hy
    rw [← pow_div_pow_eqn u s _ e.ne_zero k' k]
    exact regAt_div (regAt_pow (locU y e he).1 _) ((unitAt_pow_iff hA.regAt (by omega)).2 hA)
  obtain ⟨a, ha⟩ := exists_fnOf_eq hg hreg
  have e₁ : Y.basicOpen a = V ⊓ U := by
    ext y
    refine ⟨fun hy => ?_, fun ⟨hyV, hyU⟩ => ?_⟩
    · have hyV : y ∈ V := Y.basicOpen_le a hy
      obtain ⟨e, he⟩ := D.exists_isEqn y
      have hA := (loc y e he).2.1 hyV
      have h := (unitAt_fnOf_iff hyV hg a).2 hy
      rw [ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA),
        unitAt_pow_iff (locU y e he).1 (by omega)] at h
      exact ⟨hyV, (locU y e he).2.2 h⟩
    · obtain ⟨e, he⟩ := D.exists_isEqn y
      have hA := (loc y e he).2.1 hyV
      refine (unitAt_fnOf_iff hyV hg a).1 ?_
      rw [ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA),
        unitAt_pow_iff (locU y e he).1 (by omega)]
      exact (locU y e he).2.1 hyU
  have him := Scheme.Opens.ι_image_basicOpen_topIso_inv (U := V) a
  rw [e₁] at him
  refine ⟨V.topIso.inv a, ?_, ?_⟩
  · rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, him]
    exact stepC k' hk' u hu U hUa hUl
  · have hm : V.ι x ∈ V.ι ''ᵁ V.toScheme.basicOpen (V.topIso.inv a) := by
      rw [him]; exact ⟨x.2, hxU⟩
    obtain ⟨z, hz, hzx⟩ := hm
    rwa [V.ι.isOpenEmbedding.injective hzx] at hz

end GlobalTheory.Desc.LocusQA
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.FlagPlucker


open GlobalTheory.FlagMod Formalism.L2.Pj in
theorem isAmpleLB_LL_flagModel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagModel Y) (z : Y.X), ∃ V : Y.X.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB ((X.F.LL (fun ix => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ))).pull (X.π ⁻¹ᵁ V).ι) := by
  intro E _ _ _ H Dw l Xo c Y X z
  have hprop : IsProper X.π := X.proper
  by_cases hz : z ∈ Set.range X.π.base
  · obtain ⟨y, rfl⟩ := hz
    obtain ⟨k0, hk0⟩ := TopologicalSpace.Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ y))
    have hzM : X.π y ∈ (X.F.M k0).U := X.F.le k0 hk0
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVM⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show X.π y ∈ ((X.F.M k0).U : Set Y.X) from hzM) (X.F.M k0).U.isOpen
    refine ⟨V, hzV, hV, ?_⟩
    have hg : ⊤ ≤ ((X.π ⁻¹ᵁ V).ι ≫ X.π) ⁻¹ᵁ (X.F.M k0).toMChart.U := fun p _ => hVM (by
      show X.π ((X.π ⁻¹ᵁ V).ι p) ∈ V
      have : (X.π ⁻¹ᵁ V).ι p ∈ X.π ⁻¹ᵁ V := by
        have h := Scheme.Opens.range_ι (X.π ⁻¹ᵁ V)
        exact (h.le ⟨p, rfl⟩ : _)
      exact this)
    have hf : IsProper ((X.π ∣_ V) ≫ hV.isoSpec.hom) := inferInstance
    choose t ht using fun (p : Σ σ : E →+* ℂ, Fin (Dw.mult σ)) (q : Fin (plkNum (X.F.M k0).toMChart p.2 + 1)) =>
      GlobalTheory.T.pluckerMinors_sections_inverseDetFlagBundle X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg p.1 p.2 q
    have hnz : ∀ p, ⨆ q, nonzeroLocus (t p q) = ⊤ := fun p =>
      GlobalTheory.T.sections_of_pulled_back_line_bundles_on_frames X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg p.1 p.2 (t p) (ht p)
    refine isAmpleLB_of_finite_fibres Γ(Y.X, V) _ ((X.π ∣_ V) ≫ hV.isoSpec.hom) hf (Σ σ : E →+* ℂ, Fin (Dw.mult σ))
      (fun p => (X.F.LL (ind p.1 p.2)).pull (X.π ⁻¹ᵁ V).ι) (fun p => LB.isLB_pull (X.F.isLB_LL _) _)
      (fun p => plkNum (X.F.M k0).toMChart p.2) t hnz ?_ (fun _ => 1) (fun _ => le_rfl) _
      (LB.isLB_pull (X.F.isLB_LL _) _) ?_
    · intro K _ _ a
      have hfin := X.fin K (a ≫ (X.π ⁻¹ᵁ V).ι)
      refine (hfin.preimage (f := fun a' : Sp K ⟶ _ => a' ≫ (X.π ⁻¹ᵁ V).ι)
        fun b _ b' _ e => (cancel_mono _).1 e).subset ?_
      rintro a' ⟨h1, h2⟩
      have e : (X.π ⁻¹ᵁ V).ι ≫ X.π = ((X.π ∣_ V) ≫ hV.isoSpec.hom) ≫ hV.fromSpec := by
        rw [← hV.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
      have hx : a ≫ (X.π ⁻¹ᵁ V).ι ≫ X.π = a' ≫ (X.π ⁻¹ᵁ V).ι ≫ X.π := by
        rw [e]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ hV.fromSpec) h1.symm).trans (Category.assoc _ _ _))
      exact GlobalTheory.T.lieFlag_eq_of_pluckerPoints_eq_field_points X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg (fun σ m => t ⟨σ, m⟩)
        (fun σ m => ht ⟨σ, m⟩) (fun σ m => hnz ⟨σ, m⟩) _ K a a' hx (fun σ m => (h2 ⟨σ, m⟩).symm)
    · have he : (fun ix : Ix Dw => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ)) =
          ∑ p : Σ σ : E →+* ℂ, Fin (Dw.mult σ), ind p.1 p.2 := by
        funext ix
        rcases ix with _ | ⟨σ, i⟩
        · simp [ind]
        · rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single σ]
          · simp only [ind, Option.elim, true_and]
            rw [Finset.sum_boole]
            have : (Finset.univ.filter fun m : Fin (Dw.mult σ) => (i : ℕ) ≤ m) = Finset.Ici i := by
              ext m; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
            simp only [this, Fin.card_Ici]
            push_cast [Nat.cast_sub i.2.le]
            ring
          · intro σ' _ h
            refine Finset.sum_eq_zero fun m _ => ?_
            simp [ind, Ne.symm h]
          · simp
      have h2 : ∀ p : Σ σ : E →+* ℂ, Fin (Dw.mult σ),
          1 • CechPic.cls ((X.F.LL (ind p.1 p.2)).pull (X.π ⁻¹ᵁ V).ι) (LB.isLB_pull (X.F.isLB_LL _) _) =
            CechPic.pull (X.π ⁻¹ᵁ V).ι (CechPic.cls (X.F.LL (ind p.1 p.2)) (X.F.isLB_LL _)) :=
        fun p => one_smul _ _

      rw [CechPic.cls_pull (X.F.isLB_LL _), Finset.sum_congr rfl fun p _ => h2 p, ← map_sum,
      ← GlobalTheory.T.cechPicardClass_gradedTensorBundle_finset_sum X.F Finset.univ (fun p : Σ σ : E →+* ℂ, Fin (Dw.mult σ) => ind p.1 p.2)]
      congr 2
      exact congrArg _ he
  · have hcl : IsClosed (Set.range X.π.base) := X.π.isClosedMap.isClosed_range
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVc⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ (Set.range X.π.base)ᶜ from hz) hcl.isOpen_compl
    refine ⟨V, hzV, hV, ?_⟩
    haveI : IsEmpty (X.π ⁻¹ᵁ V).toScheme := ⟨fun p => hVc p.2 ⟨p.1, rfl⟩⟩
    haveI : IsAffine (X.π ⁻¹ᵁ V).toScheme := isAffine_of_isEmpty
    exact isAmpleLB_of_isAffine (LB.isLB_pull (X.F.isLB_LL _) _)

end GlobalTheory.FlagPlucker

end
end
