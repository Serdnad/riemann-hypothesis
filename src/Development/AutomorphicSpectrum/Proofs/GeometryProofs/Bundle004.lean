module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
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
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ggeo.LocalLift

theorem exists_mul_eq_of_isPushout {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (po : IsPushout f g h k) (M : Submonoid A)
    (hg : ∀ c : C, ∃ a, ∃ m ∈ M, c * g.hom m = g.hom a) (d : D) :
    ∃ m ∈ M, ∃ b, d * h.hom (f.hom m) = h.hom b := by
  have GlobalTheory.CompanionTheory.Ar.Conj.hw : ∀ a, h.hom (f.hom a) = k.hom (g.hom a) := fun a => by
    have := congrArg (fun φ : A ⟶ D => φ.hom a) po.w
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have GlobalTheory.CompanionTheory.RedCov.Levi.hd : d ∈ Subring.closure
      (Set.range (ConcreteCategory.hom h) ∪ Set.range (ConcreteCategory.hom k)) := by
    rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout po]
    exact Subring.mem_top d
  refine Subring.closure_induction
    (p := fun x _ => ∃ m ∈ M, ∃ b, x * h.hom (f.hom m) = h.hom b) ?_ ?_ ?_ ?_ ?_ ?_ GlobalTheory.CompanionTheory.RedCov.Levi.hd
  · rintro x (⟨b, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨1, M.one_mem, b, ?_⟩
      show h.hom b * h.hom (f.hom 1) = h.hom b
      simp
    · show ∃ m ∈ M, ∃ b, k.hom c * h.hom (f.hom m) = h.hom b
      obtain ⟨a, m, hm, hca⟩ := hg c
      refine ⟨m, hm, f.hom a, ?_⟩
      rw [GlobalTheory.CompanionTheory.Ar.Conj.hw, GlobalTheory.CompanionTheory.Ar.Conj.hw, ← map_mul, hca]
  · exact ⟨1, M.one_mem, 0, by simp⟩
  · exact ⟨1, M.one_mem, 1, by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨m₁, hm₁, b₁, e₁⟩ := hx
    obtain ⟨m₂, hm₂, b₂, e₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, b₁ * f.hom m₂ + b₂ * f.hom m₁, ?_⟩
    simp only [map_mul, map_add (f := _)]
    linear_combination h.hom (f.hom m₂) * e₁ + h.hom (f.hom m₁) * e₂
  · intro x _ hx
    obtain ⟨m, hm, b, e⟩ := hx
    exact ⟨m, hm, -b, by rw [neg_mul, e, map_neg]⟩
  · intro x y _ _ hx hy
    obtain ⟨m₁, hm₁, b₁, e₁⟩ := hx
    obtain ⟨m₂, hm₂, b₂, e₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, b₁ * b₂, ?_⟩
    simp only [map_mul]
    linear_combination (y * h.hom (f.hom m₂)) * e₁ + h.hom b₁ * e₂

theorem stalk_exists_mul_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U)
    (c : X.presheaf.stalk p) :
    ∃ a m : Γ(X, U), IsUnit ((X.presheaf.germ U p hp).hom m) ∧
      c * (X.presheaf.germ U p hp).hom m = (X.presheaf.germ U p hp).hom a := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  have hloc := hU.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨⟨a, m⟩, hm⟩ := @IsLocalization.surj _ _ _ _ _ _ hloc c
  exact ⟨a, m, @IsLocalization.map_units _ _ _ _ _ _ hloc m, hm⟩

theorem fromSpecStalk_appLE {X : Scheme.{0}} {U : X.Opens} {p : X} (hp : p ∈ U)
    (h : (⊤ : (Spec (X.presheaf.stalk p)).Opens) ≤ X.fromSpecStalk p ⁻¹ᵁ U) :
    (X.fromSpecStalk p).appLE U ⊤ h =
      X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso (X.presheaf.stalk p)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hp, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  have e : (homOfLE (le_top : X.fromSpecStalk p ⁻¹ᵁ U ≤ ⊤)).op ≫ (homOfLE h).op =
      𝟙 (Opposite.op (⊤ : (Spec (X.presheaf.stalk p)).Opens)) := by
    first
    | exact Subsingleton.elim _ _
    | rfl
  rw [e]
  exact (congrArg (fun t => X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso (X.presheaf.stalk p)).inv ≫ t)
    ((Spec (X.presheaf.stalk p)).presheaf.map_id _)).trans (by simp only [Category.comp_id])

theorem exists_extension {X Y Z P : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y) (hy : π y₀ = p)
    (fst : P ⟶ Y) (snd : P ⟶ Spec (X.presheaf.stalk p))
    (H : IsPullback fst snd π (X.fromSpecStalk p)) (c : Z ⟶ P) [IsClosedImmersion c]
    (s : Γ(Z, ⊤)) :
    ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧ ((c ≫ fst).app W).hom f =
      Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ W ≤ ⊤)).op s := by
  obtain ⟨V, hV, hpV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := p) (by simp)
  have hy₀ : y₀ ∈ π ⁻¹ᵁ V := (Scheme.Hom.mem_preimage π).2 (by rw [hy]; exact hpV)
  obtain ⟨W₀, hW₀, hy₀W₀, hW₀V⟩ := exists_isAffineOpen_mem_and_subset hy₀
  have hUSX : W₀ ≤ π ⁻¹ᵁ V := fun x hx => hW₀V hx
  have hUST : (⊤ : (Spec (X.presheaf.stalk p)).Opens) ≤ X.fromSpecStalk p ⁻¹ᵁ V := by
    intro x _
    have hx : X.fromSpecStalk p x ∈ Set.range (X.fromSpecStalk p) := ⟨x, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hx
    have hx' : X.fromSpecStalk p x ⤳ p := hx
    exact (Scheme.Hom.mem_preimage _).2 (Specializes.mem_open hx' V.isOpen hpV)
  obtain ⟨UY, hUY⟩ : ∃ UY, UY = fst ⁻¹ᵁ W₀ ⊓ snd ⁻¹ᵁ ⊤ := ⟨_, rfl⟩
  have hUYle : UY ≤ fst ⁻¹ᵁ W₀ := by
    rw [hUY]
    exact inf_le_left
  have hpo := (isIso_pushoutSection_iff H hUST hUSX hUY).1
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hV (isAffineOpen_top _) hW₀)
  have hUYaff : IsAffineOpen UY := by
    have hpb := Scheme.Hom.isPullback_resLE H hUST hUSX hUY
    haveI : IsAffine (W₀ : Scheme.{0}) := hW₀
    haveI : IsAffine (V : Scheme.{0}) := hV
    haveI : IsAffine ((⊤ : (Spec (X.presheaf.stalk p)).Opens) : Scheme.{0}) :=
      isAffineOpen_top _
    haveI := Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      (π.resLE V W₀ hUSX) ((X.fromSpecStalk p).resLE V ⊤ hUST)
    exact IsAffine.of_isIso hpb.isoPullback.hom
  obtain ⟨d, GlobalTheory.CompanionTheory.RedCov.Levi.hd⟩ := Scheme.Hom.app_surjective c UY hUYaff
    ((Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op).hom s)
  have hd' : (c.app UY).hom d = (Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op).hom s :=
    GlobalTheory.CompanionTheory.RedCov.Levi.hd
  have hg : ∀ c' : Γ(Spec (X.presheaf.stalk p), ⊤), ∃ a, ∃ m ∈
      (IsUnit.submonoid (X.presheaf.stalk p)).comap (X.presheaf.germ V p hpV).hom,
      c' * ((X.fromSpecStalk p).appLE V ⊤ hUST).hom m =
        ((X.fromSpecStalk p).appLE V ⊤ hUST).hom a := by
    intro c'
    obtain ⟨a, m, hmu, hm⟩ := GlobalTheory.CompanionTheory.Ggeo.LocalLift.stalk_exists_mul_eq hV hpV
      ((Scheme.ΓSpecIso (X.presheaf.stalk p)).hom.hom c')
    refine ⟨a, m, Submonoid.mem_comap.2 ((IsUnit.mem_submonoid_iff _).2 hmu), ?_⟩
    rw [GlobalTheory.CompanionTheory.Ggeo.LocalLift.fromSpecStalk_appLE hpV, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply,
      ← hm, map_mul]
    exact congrArg (fun t => t * _) (CommRingCat.inv_hom_apply _ c').symm
  obtain ⟨m, hmM, b, hb⟩ := GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_mul_eq_of_isPushout hpo _ hg d
  have hmu : IsUnit ((X.presheaf.germ V p hpV).hom m) :=
    (IsUnit.mem_submonoid_iff _).1 (Submonoid.mem_comap.1 hmM)
  have hy₀W : y₀ ∈ Y.basicOpen ((π.appLE V W₀ hUSX).hom m) := by
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.basicOpen_res]
    refine TopologicalSpace.Opens.mem_inf.2 ⟨hy₀W₀, ?_⟩
    rw [← Scheme.preimage_basicOpen, Scheme.Hom.mem_preimage, hy]
    exact (X.mem_basicOpen m p hpV).2 hmu
  obtain ⟨fm, hfm⟩ : ∃ fm, (π.appLE V W₀ hUSX).hom m = fm := ⟨_, rfl⟩
  rw [hfm] at hb hy₀W
  have hWW₀ : Y.basicOpen fm ≤ W₀ := Y.basicOpen_le fm
  have hu : IsUnit ((Y.presheaf.map (homOfLE hWW₀).op).hom fm) :=
    RingedSpace.isUnit_res_basicOpen _ fm
  refine ⟨Y.basicOpen fm, (Y.presheaf.map (homOfLE hWW₀).op).hom b * ↑hu.unit⁻¹, hy₀W, ?_⟩
  have hQ : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ c ⁻¹ᵁ UY := by
    rw [hUY]
    intro z hz
    exact (Scheme.Hom.mem_preimage c).2 (TopologicalSpace.Opens.mem_inf.2
      ⟨(Scheme.Hom.mem_preimage fst).2 (hWW₀ ((Scheme.Hom.mem_preimage (c ≫ fst)).1 hz)),
        (Scheme.Hom.mem_preimage snd).2 (by simp)⟩)
  have E₁ : Y.presheaf.map (homOfLE hWW₀).op ≫ (c ≫ fst).app (Y.basicOpen fm) =
      fst.appLE W₀ UY hUYle ≫ c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
  have e₁ : ∀ x, ((c ≫ fst).app (Y.basicOpen fm)).hom
      ((Y.presheaf.map (homOfLE hWW₀).op).hom x) =
      (c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ).hom ((fst.appLE W₀ UY hUYle).hom x) := by
    intro x
    have := congrArg (fun φ => CommRingCat.Hom.hom φ x) E₁
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have E₂ : Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op ≫
      Z.presheaf.map (homOfLE hQ).op =
      Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ ⊤)).op := by
    (rw [← Functor.map_comp]) <;> rfl
  have e₂ : (c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ).hom d =
      (Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ ⊤)).op).hom s := by
    have h₂ := congrArg (fun φ => CommRingCat.Hom.hom φ s) E₂
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h₂
    rw [← h₂, ← hd', Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [map_mul, e₁ b, ← hb, map_mul, e₂, ← e₁ fm, mul_assoc, ← map_mul, hu.mul_val_inv,
    map_one, mul_one]

theorem exists_open_extension : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y), π y₀ = p →
    ∀ (c : Z ⟶ pullback π (X.fromSpecStalk p)) [IsClosedImmersion c] (s : Γ(Z, ⊤)),
    ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧
      ((c ≫ pullback.fst π (X.fromSpecStalk p)).app W).hom f =
        Z.presheaf.map (homOfLE (le_top : (c ≫ pullback.fst π (X.fromSpecStalk p)) ⁻¹ᵁ W ≤ ⊤)).op s := by
  intro X Y Z π p y₀ hy c _ s
  exact exists_extension π p y₀ hy _ _ (IsPullback.of_hasPullback π (X.fromSpecStalk p)) c s

end GlobalTheory.CompanionTheory.Ggeo.LocalLift
end

section

open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem finite_primeSpectrum_height_one {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {a : A} (ha : a ≠ 0) :
    {P : PrimeSpectrum A | a ∈ P.asIdeal ∧ P.asIdeal.height = 1}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).preimage
    (f := PrimeSpectrum.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_
  rintro ⟨P, hP⟩ ⟨haP, h1⟩
  simp only at haP h1
  refine ⟨⟨hP, (Ideal.span_singleton_le_iff_mem _).mpr haP⟩, fun Q hQ hQP => ?_⟩
  have := hQ.1
  have haQ : a ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.2
  have hQ0 : Q ≠ ⊥ := fun h => ha (by rw [h] at haQ; exact haQ)
  have hQ1 : P.height ≤ Q.height := by
    rw [h1]
    exact Order.one_le_iff_ne_zero.mpr (fun h => hQ0 (Ideal.height_eq_zero_iff_eq_bot.mp h))
  exact (Ideal.eq_of_le_of_height_le (I := Q) hQP hQ1).ge

theorem exists_primeSpectrum_height_one_le {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {a : A} (ha : a ≠ 0) (P : PrimeSpectrum A) (hP : a ∈ P.asIdeal) :
    ∃ Q : PrimeSpectrum A, a ∈ Q.asIdeal ∧ Q.asIdeal.height = 1 ∧ Q ≤ P := by
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a}) (J := P.asIdeal)
    ((Ideal.span_singleton_le_iff_mem _).mpr hP)
  have hQp : Q.IsPrime := hQ.1.1
  have haQ : a ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.1.2
  have hQ0 : Q ≠ ⊥ := fun h => ha (by rw [h] at haQ; exact haQ)
  refine ⟨⟨Q, hQp⟩, haQ, le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ)
    (Order.one_le_iff_ne_zero.mpr (fun h => hQ0 (Ideal.height_eq_zero_iff_eq_bot.mp h))), hQP⟩

theorem ringKrullDim_stalk_fromSpec {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(Z, U)) :
    ringKrullDim (Z.presheaf.stalk (hU.fromSpec P)) = P.asIdeal.height := by
  have hmem : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  letI := TopCat.Presheaf.algebra_section_stalk Z.presheaf (U := U) ⟨hU.fromSpec P, hmem⟩
  have := hU.isLocalization_stalk' P hmem
  exact @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ P.asIdeal _ _ _ _ this

theorem fromSpec_notMem_basicOpen_iff {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (f : Γ(Z, ⊤)) (P : PrimeSpectrum Γ(Z, U)) :
    hU.fromSpec P ∉ Z.basicOpen f ↔
      Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f ∈ P.asIdeal := by
  have hmem : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  have h := hU.fromSpec_preimage_basicOpen (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f)
  have h2 : hU.fromSpec P ∈ Z.basicOpen (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f) ↔
      Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f ∉ P.asIdeal := by
    rw [← PrimeSpectrum.mem_basicOpen, ← h]
    rfl
  rw [Scheme.basicOpen_res] at h2
  have h3 : hU.fromSpec P ∈ U ⊓ Z.basicOpen f ↔ hU.fromSpec P ∈ Z.basicOpen f :=
    ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩
  rw [← h3, h2, not_not]

theorem finite_codim_one_zero_set_and_exists :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsNoetherian Z] (ϖ : Γ(Z, ⊤)), ϖ ≠ 0 →
      {x : Z | x ∉ Z.basicOpen ϖ ∧ ringKrullDim (Z.presheaf.stalk x) = 1}.Finite ∧
      ∀ y : Z, y ∉ Z.basicOpen ϖ →
        ∃ x : Z, x ∉ Z.basicOpen ϖ ∧ ringKrullDim (Z.presheaf.stalk x) = 1 ∧
          y ∈ closure {x} := by
  intro Z _ _ ϖ hϖ
  have hex : ∀ y : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ y ∈ U := fun y => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨U, hU, hy⟩
  choose U hU hyU using hex
  have hne : ∀ y, Nonempty (U y) := fun y => ⟨⟨y, hyU y⟩⟩
  have hnoeth : ∀ y, IsNoetherianRing Γ(Z, U y) := fun y =>
    IsLocallyNoetherian.component_noetherian ⟨U y, hU y⟩
  have hres : ∀ y, Z.presheaf.map (homOfLE (le_top : U y ≤ ⊤)).op ϖ ≠ 0 := fun y h =>
    hϖ (map_injective_of_isIntegral Z (homOfLE (le_top : U y ≤ ⊤)) (h.trans (map_zero _).symm))
  constructor
  · obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : Z => (U y : Set Z))
      (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩)
    refine (t.finite_toSet.biUnion (fun y _ =>
      (finite_primeSpectrum_height_one (hres y)).image (hU y).fromSpec)).subset ?_
    rintro x ⟨hx, hx1⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
    rw [← (hU y).range_fromSpec] at hxy
    obtain ⟨P, rfl⟩ := hxy
    refine ⟨P, ⟨(fromSpec_notMem_basicOpen_iff (hU y) ϖ P).mp hx, ?_⟩, rfl⟩
    rw [ringKrullDim_stalk_fromSpec (hU y) P] at hx1
    exact_mod_cast hx1
  · intro y hy
    have hy' : y ∈ Set.range (hU y).fromSpec := by
      rw [(hU y).range_fromSpec]; exact hyU y
    obtain ⟨P, hP⟩ := hy'
    obtain ⟨Q, hQ, hQ1, hQP⟩ := exists_primeSpectrum_height_one_le (hres y) P
      ((fromSpec_notMem_basicOpen_iff (hU y) ϖ P).mp (by rw [hP]; exact hy))
    refine ⟨(hU y).fromSpec Q, (fromSpec_notMem_basicOpen_iff (hU y) ϖ Q).mpr hQ, ?_, ?_⟩
    · rw [ringKrullDim_stalk_fromSpec (hU y) Q, hQ1]; rfl
    · have := ((PrimeSpectrum.le_iff_specializes Q P).mp hQP).map (hU y).fromSpec.continuous
      rw [hP] at this
      exact specializes_iff_mem_closure.mp this

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Arith.DedekindDescent

theorem single_ext (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (σ : F →+* ℂ) {κ : Type} [Fintype κ] (b : κ → ℂ)
    (hb : ∀ c : κ → F, ∑ k, σ (c k) * b k = 0 → c = 0) (x : κ → K)
    (h : ∀ τ : K →+* ℂ, τ.comp (algebraMap F K) = σ → ∑ k, b k * τ (x k) = 0) : x = 0 := by
  let _ : Algebra F ℂ := σ.toAlgebra
  have : CharZero F := ⟨fun a b hab => Nat.cast_injective (R := ℂ) (by
    have := congrArg σ hab
    simpa only [map_natCast] using this)⟩
  have key : ∀ y : K, ∑ k, σ (Algebra.trace F K (x k * y)) * b k = 0 := by
    intro y
    have htr : ∀ k, σ (Algebra.trace F K (x k * y)) = ∑ φ : K →ₐ[F] ℂ, φ (x k * y) :=
      fun k => trace_eq_sum_embeddings ℂ (x := x k * y)
    simp only [htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun φ _ => ?_
    have hφ := h (φ : K →+* ℂ) φ.comp_algebraMap
    have hsplit : ∑ k, φ (x k * y) * b k = φ y * ∑ k, b k * (φ : K →+* ℂ) (x k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, AlgHom.coe_toRingHom]
      ring
    rw [hsplit, hφ, mul_zero]
  funext k0
  by_contra hne
  have h0 := congrFun (hb _ (key (x k0)⁻¹)) k0
  simp only [Pi.zero_apply] at h0 hne
  rw [mul_inv_cancel₀ hne, ← map_one (algebraMap F K), Algebra.trace_algebraMap, nsmul_eq_mul,
    mul_one, Nat.cast_eq_zero] at h0
  exact (Module.finrank_pos (R := F) (M := K)).ne' h0

theorem linIndep_descent : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (J : Type) (K : J → Type) [∀ j, Field (K j)] [∀ j, Algebra F (K j)] [∀ j, FiniteDimensional F (K j)] (ι : Type) [Fintype ι] (v : ι → ∀ j, K j), (∀ a : ι → F, (∀ j, ∑ l, algebraMap F (K j) (a l) * v l j = 0) → a = 0) → ∀ d : ι → ℂ, (∀ j (τ : K j →+* ℂ), τ.comp (algebraMap F (K j)) = σ → ∑ l, d l * τ (v l j) = 0) → d = 0 := by
  intro F _ σ J K _ _ _ ι _ v hv d hd
  let _ : Algebra F ℂ := σ.toAlgebra
  let S := Submodule.span F (Set.range d)
  have : FiniteDimensional F S := FiniteDimensional.span_of_finite F (Set.finite_range d)
  let B := Module.finBasis F S
  have hmem : ∀ l, d l ∈ S := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hval : ∀ e : Fin (Module.finrank F S) → F,
      ((∑ k, e k • B k : S) : ℂ) = ∑ k, σ (e k) * (B k : ℂ) := by
    intro e
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
  have hdc : ∀ l, d l = ∑ k, σ (B.repr ⟨d l, hmem l⟩ k) * (B k : ℂ) := by
    intro l
    rw [← hval]
    exact (congrArg Subtype.val (B.sum_repr ⟨d l, hmem l⟩)).symm
  have hbind : ∀ e : Fin (Module.finrank F S) → F, ∑ k, σ (e k) * (B k : ℂ) = 0 → e = 0 := by
    intro e he
    have h1 : ∑ k, e k • B k = 0 := by
      apply Subtype.ext
      rw [hval, he]
      rfl
    funext k
    exact Fintype.linearIndependent_iff.1 B.linearIndependent e h1 k
  have hx : ∀ j k, ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j = 0 := by
    intro j
    have hτ' : ∀ τ : K j →+* ℂ, τ.comp (algebraMap F (K j)) = σ →
        ∀ a, τ (algebraMap F (K j) a) = σ a := fun τ hτ a => by rw [← hτ]; rfl
    have := single_ext F (K j) σ (fun k => (B k : ℂ)) hbind
      (fun k => ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j) (fun τ hτ => by
        refine Eq.trans ?_ (hd j τ hτ)

        simp only [map_sum, map_mul, hτ' τ hτ]
        rw [Finset.sum_congr rfl fun l _ => congrArg (· * τ (v l j)) (hdc l)]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
    intro k
    exact congrFun this k
  have hc0 : ∀ k, (fun l => B.repr ⟨d l, hmem l⟩ k) = 0 := fun k => hv _ fun j => hx j k
  funext l
  rw [hdc l, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrFun (hc0 k) l
  simp only [Pi.zero_apply] at this
  rw [this, map_zero, zero_mul]

end GlobalTheory.CompanionTheory.Arith.DedekindDescent
end

section

namespace GlobalTheory.CompanionTheory.Kaehler

theorem finrank_kaehlerDifferential_of_adjoin_eq_top (K L : Type) [Field K] [Field L] [Algebra K L]
    (I : Type) [Fintype I] (u : I → L) (hu : AlgebraicIndependent K u)
    (hadj : IntermediateField.adjoin K (Set.range u) = ⊤) :
    Module.finrank L (KaehlerDifferential K L) = Fintype.card I := by
  classical
  letI : Algebra (MvPolynomial I K) L := (MvPolynomial.aeval u).toRingHom.toAlgebra
  have hmap : ∀ q : MvPolynomial I K, algebraMap (MvPolynomial I K) L q = MvPolynomial.aeval u q :=
    fun _ => rfl
  have : IsScalarTower K (MvPolynomial I K) L :=
    IsScalarTower.of_algebraMap_eq fun x => by rw [hmap, AlgHom.commutes]
  have : FaithfulSMul (MvPolynomial I K) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hu
  have : IsFractionRing (MvPolynomial I K) L := IsFractionRing.of_field (MvPolynomial I K) L fun z => by
    have hz : z ∈ IntermediateField.adjoin K (Set.range u) := by rw [hadj]; trivial
    obtain ⟨r, s, h⟩ := (IntermediateField.mem_adjoin_range_iff K u z).1 hz
    exact ⟨r, s, h⟩
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors (MvPolynomial I K))
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale K (MvPolynomial I K) L
  rw [Module.finrank_eq_card_basis (hbc.basis (KaehlerDifferential.mvPolynomialBasis K I))]

end GlobalTheory.CompanionTheory.Kaehler
end

section

namespace GlobalTheory.CompanionTheory.Ar.Lat

theorem wedge_matrix_mul_family (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ)
    (e : Fin n → V) (P : Matrix (Fin n) (Fin n) Ω) :
    exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j) = P.det • exteriorPower.ιMulti Ω n e := by
  let L : (Fin n → Ω) →ₗ[Ω] V := (Pi.basisFun Ω (Fin n)).constr Ω e
  have hL : ∀ c : Fin n → Ω, L c = ∑ j, c j • e j := fun c => by
    simp [L, Module.Basis.constr_apply_fintype]
  have hLe : (fun i => L (Pi.basisFun Ω (Fin n) i)) = e := funext fun i => by simp [L]
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff Ω _).1 fun f => ?_
  let A : (Fin n → Ω) [⋀^Fin n]→ₗ[Ω] Ω :=
    (f.compAlternatingMap (exteriorPower.ιMulti Ω n (M := V))).compLinearMap L
  have h := congrArg (fun g => g (fun i => P i))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun Ω (Fin n)) A)
  simp only [AlternatingMap.smul_apply, Pi.basisFun_det_apply, smul_eq_mul] at h
  have h1 : A (fun i => P i) = f (exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j)) := by
    simp only [A, AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply]
    congr 2
    funext i
    exact hL _
  have h2 : A (Pi.basisFun Ω (Fin n)) = f (exteriorPower.ιMulti Ω n e) := by
    simp only [A, AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply]
    congr 2
  have h3 : (Matrix.of fun i => P i) = P := rfl
  rw [h1, h2, h3] at h
  rw [map_sub, map_smul, h, smul_eq_mul, mul_comm, sub_self]

end GlobalTheory.CompanionTheory.Ar.Lat
end
