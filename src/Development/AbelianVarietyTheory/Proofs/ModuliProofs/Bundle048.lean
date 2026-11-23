module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevelMap

theorem of_baseChange (P : MorphismProperty Scheme.{0})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {X₀ X₁ S₀ S₁ T : Scheme.{0}} (s₀ : X₀ ⟶ S₀) (s₁ : X₁ ⟶ S₁) (k : S₁ ⟶ S₀) (r : X₁ ⟶ X₀)
    (hr : r ≫ s₀ = s₁ ≫ k) (i₀ : T ⟶ S₀) (i₁ : T ⟶ S₁) (hi : i₁ ≫ k = i₀)
    [Surjective i₁] [Flat i₁] [QuasiCompact i₁]
    (rF : pullback s₁ i₁ ⟶ pullback s₀ i₀) (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r)
    (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) (h : P rF) : P (pullback.lift r s₁ hr) := by
  subst hi
  let p : pullback s₀ (i₁ ≫ k) ⟶ pullback s₀ k :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i₁) (by simp [pullback.condition])
  have hp : IsPullback p (pullback.snd _ _) (pullback.snd s₀ k) i₁ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback s₀ k)
    have : p ≫ pullback.fst s₀ k = pullback.fst _ _ := pullback.lift_fst _ _ _
    rw [this]
    exact IsPullback.of_hasPullback _ _
  have hq : IsPullback (pullback.fst s₁ i₁) rF (pullback.lift r s₁ hr) p := by
    refine IsPullback.of_bot ?_ ?_ hp
    · rw [h₂, pullback.lift_snd]
      exact IsPullback.of_hasPullback _ _
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, h₁]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, reassoc_of% h₂, pullback.condition]
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := P)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hq.flip ⟨⟨?_, ?_⟩, ?_⟩ h
  · exact MorphismProperty.of_isPullback (P := @Surjective) hp.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hp.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip ‹_›

theorem isFinite_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsFinite : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isAffineHom_descendsAlong_fpqc.{0}
  refine ⟨fun {A X Y Z fst snd f g} H hf hfst => ?_⟩
  have a2 : IsAffineHom g := MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) H hf inferInstance
  have a3 : UniversallyClosed g :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H hf inferInstance
  have a4 : LocallyOfFiniteType g :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) H hf inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩

theorem surjective_spMap {K L : Type} [Field K] [Field L] (k : K →+* L) : Surjective (spMap k) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y⟩ : Nonempty (Sp L) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩

theorem flat_spMap {K L : Type} [Field K] [Field L] (k : K →+* L) : Flat (spMap k) := by
  rw [Flat.SpecMap_iff]
  algebraize [k]
  exact (inferInstance : Module.Flat K L)

theorem finite_etale_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  constructor
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

theorem exists_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H), l₀.Dvd l₁ → ∃ (k : KA l₀ →+* KA l₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k), IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ LevComp (Xo l₁).univ (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) ∧ IsFinite r ∧ Etale r ∧ Surjective r := by
  intro E _ _ _ H D Xo hN l₀ l₁ hd
  obtain ⟨r, k, ν, hk, hr, h1, h2, -, hc⟩ := hN l₀ l₁ (Xo l₀) (Xo l₁) hd
  obtain ⟨c₁⟩ : Nonempty (Coeff l₁) := inferInstance
  have hle : KA l₀ ≤ c₁.F := fun x hx => by
    have := c₁.le (k ⟨x, hx⟩).2
    rwa [hk] at this
  let c₀ : Coeff l₀ :=
    { F := c₁.F
      fin := c₁.fin
      conj := c₁.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := LevelExist.zeta_eq_pow_of_dvd (a := l₀.M') (LevelExist.M'_pos l₁)
          (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l₀.M' ∣ l₁.M')
        rw [he]
        exact pow_mem c₁.zeta_mem e
      le := hle }
  obtain ⟨rF, e1, e2, f1, f2, f3, -⟩ := hc c₀ c₁ rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c₁.F)).toRingHom = 𝟙 (Sp c₁.F) := by
    rw [← Spec.map_id]
    rfl
  have e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _ := e2.trans ((congrArg _ hid).trans (Category.comp_id _))
  have hi : spMap (IntermediateField.inclusion c₁.le).toRingHom ≫ spMap k =
      spMap (IntermediateField.inclusion c₀.le).toRingHom := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact hk x
  have := surjective_spMap (IntermediateField.inclusion c₁.le).toRingHom
  have := flat_spMap (IntermediateField.inclusion c₁.le).toRingHom
  have := isFinite_descendsAlong_fpqc
  have g1 : IsFinite (pullback.lift r _ hr) := of_baseChange @IsFinite _ _ _ r hr _ _ hi rF e1 e2' f1
  have g2 : Etale (pullback.lift r _ hr) := of_baseChange @Etale _ _ _ r hr _ _ hi rF e1 e2' f2
  have g3 : Surjective (pullback.lift r _ hr) := of_baseChange @Surjective _ _ _ r hr _ _ hi rF e1 e2' f3
  have := c₁.fin
  have : FiniteDimensional ℚ (KA l₁) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion c₁.le).toLinearMap
      (IntermediateField.inclusion c₁.le).injective
  obtain ⟨k1, k2⟩ := finite_etale_spMap k
  have k3 := surjective_spMap k
  have hfac : pullback.lift r _ hr ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  refine ⟨k, r, ν, hr, hk, ⟨h1, h2⟩, g1, g2, g3, ?_, ?_, ?_⟩
  all_goals
    rw [← hfac]
    infer_instance

end GlobalTheory.LevelMap

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LiePull

theorem exists_pushEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f) :
    ∃ e : (T ⟶ G') ≃* (Over.mk g ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  subst hg
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => ?_, fun y => ?_⟩, fun x => rfl⟩
  · have e' : x.left ≫ φ = y.left ≫ φ := congrArg (fun z => z.left) e
    exact Over.OverMorphism.ext (h.1.hom_ext e' ((Over.w x).trans (Over.w y).symm))
  · exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem basis_transport {A B k : Type} [Monoid A] [Monoid B] (e : A ≃* B) {P : A → Prop} {Q : B → Prop}
    {R : k → A → A → Prop} {R' : k → B → B → Prop} (hP : ∀ x, P x ↔ Q (e x))
    (hR : ∀ c x y, R c x y ↔ R' c (e x) (e y)) (n : ℕ)
    (H : ∃ v : Fin n → A, (∀ i, P (v i)) ∧ ∀ w, P w →
      ∃! c : Fin n → k, ∃ u : Fin n → A, (∀ i, R (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod) :
    ∃ v : Fin n → B, (∀ i, Q (v i)) ∧ ∀ w, Q w →
      ∃! c : Fin n → k, ∃ u : Fin n → B, (∀ i, R' (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod := by
  obtain ⟨v, hv, H⟩ := H
  refine ⟨fun i => e (v i), fun i => (hP _).1 (hv i), fun w hw => ?_⟩
  obtain ⟨w, rfl⟩ := e.surjective w
  have pr : ∀ u : Fin n → A, e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  refine (existsUnique_congr fun c => ⟨?_, ?_⟩).1 (H w ((hP _).2 hw))
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
    rw [pr, hw]
    simp

theorem lieMult_pull : ∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n := by
  intro O _ S S' G G' _ _ f φ a a' h hact k _ x τ n
  obtain ⟨e, he⟩ := exists_pushEquiv h (epsPt x) (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : ∀ c : k, spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap k (DualNumber k)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (c : k) (u v : epsPt x ⟶ G'), u.left = spMap (epsScale c) ≫ v.left ↔
      (e u).left = spMap (epsScale c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScale c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc c))
  have hP : ∀ v : epsPt x ⟶ G', IsLieEigen a' x τ v ↔ IsLieEigen a (x ≫ f) τ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
      refine (congrArg (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ ·) (Over.w v)).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
    · have E : e (v ≫ a'.act c) = e v ≫ a.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
      rw [hR, E]
  constructor
  · exact basis_transport e (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left) hP hR n
  · exact basis_transport e.symm (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (fun v => by rw [hP, e.apply_symm_apply])
      (fun c u v => by rw [hR, e.apply_symm_apply, e.apply_symm_apply]) n

end GlobalTheory.LiePull
end
