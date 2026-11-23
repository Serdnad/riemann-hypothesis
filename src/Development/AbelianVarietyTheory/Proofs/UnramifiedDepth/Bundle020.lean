module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.FormalChartAtZero

@[expose] public section

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem torsVal_valuationRing {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C]
    {v : Valuation C NNReal} (hv : v.Integers O) : ValuationRing O := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inr hc.symm⟩
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inl hc.symm⟩

private theorem torsVal_exists_point {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : Spec (CommRingCat.of Ω) ⟶ A) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ P, p ≫ ψ = x := by
  have hJ : JacobsonSpace ↥(Limits.pullback ψ x) :=
    LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd ψ x)
  obtain ⟨w⟩ : Nonempty ↥(Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨z₀, -⟩ := (Limits.pullback.snd ψ x).surjective w
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(Limits.pullback ψ x)))
    ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (Limits.pullback.snd ψ x) z hz ≫ Limits.pullback.fst _ _, ?_⟩
  rw [Category.assoc, Limits.pullback.condition, pointOfClosedPoint_comp_assoc]

private theorem torsVal_lift {R₀ : Type} [CommRing R₀] {X Y : Over (Spec (CommRingCat.of R₀))}
    (m : X ⟶ Y) [IsFinite m.left] {O C : Type} [CommRing O] [Field C] [Algebra R₀ O] [Algebra O C]
    [Algebra R₀ C] [IsScalarTower R₀ O C] {v : Valuation C NNReal} (hv : v.Integers O)
    (x : sp (R₀ := R₀) O ⟶ Y) (z : sp (R₀ := R₀) C ⟶ X)
    (h : z ≫ m = spMap (IsScalarTower.toAlgHom R₀ O C) ≫ x) :
    ∃! y : sp (R₀ := R₀) O ⟶ X, y ≫ m = x ∧ spMap (IsScalarTower.toAlgHom R₀ O C) ≫ y = z := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := torsVal_valuationRing hv
  haveI : IsFractionRing O C := hv.isFractionRing
  have hE : ValuativeCriterion.Existence m.left := by
    have h : UniversallyClosed m.left := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness m.left := IsSeparated.valuativeCriterion m.left
  let S : ValuativeCommSq m.left :=
    { R := O, K := C, i₁ := z.left, i₂ := x.left, commSq := ⟨congrArg Over.Hom.left h⟩ }
  obtain ⟨⟨l, h1, h2⟩⟩ := hE S
  have hw : l ≫ X.hom = (sp (R₀ := R₀) O).hom := by
    rw [← Over.w m, ← Category.assoc, h2]
    exact Over.w x
  refine ⟨Over.homMk l hw, ⟨Over.OverMorphism.ext h2, Over.OverMorphism.ext h1⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have := (hU S).elim ⟨y.left, congrArg Over.Hom.left hy2, congrArg Over.Hom.left hy1⟩ ⟨l, h1, h2⟩
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)

private theorem torsVal_comp_pow {R₀ : Type} [CommRing R₀] {G T : Over (Spec (CommRingCat.of R₀))}
    [GrpObj G] (y : T ⟶ G) (p : ℕ) : y ≫ ((𝟙 G) ^ p : G ⟶ G) = y ^ p := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem points_divisible_and_torsion_of_valuation_integers :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), v.Integers (O : Type) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) (O : Type) ⟶ G, ∃ y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = x) ∧
    ∀ z : sp (R₀ := R₀) C ⟶ G, z ^ p = 1 → ∃! y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = 1 ∧ spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ y = z) := by
  intro R₀ _ G _ _ O C _ _ _ v _ _ _ p hv hfin hsurj
  refine ⟨fun x => ?_, fun z hz => ?_⟩
  · obtain ⟨w, hw⟩ := torsVal_exists_point ((𝟙 G) ^ p : G ⟶ G).left
      (spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ x).left
    have hw' : w ≫ G.hom = (sp (R₀ := R₀) C).hom := by
      rw [← Over.w ((𝟙 G) ^ p : G ⟶ G), ← Category.assoc, hw]
      exact Over.w _
    obtain ⟨y, ⟨hy, -⟩, -⟩ := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv x (Over.homMk w hw')
      (Over.OverMorphism.ext hw)
    exact ⟨y, by rw [← torsVal_comp_pow, hy]⟩
  · have := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv 1 z
      (by rw [torsVal_comp_pow, hz, MonObj.comp_one])
    simpa only [torsVal_comp_pow] using this

end GlobalTheory
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finRep_exists_isPullback_spec {X Y : Scheme.{0}} (m : X ⟶ Y) [IsFinite m] [Flat m]
    (O : CommRingCat.{0}) (u : Spec O ⟶ Y) :
    ∃ (A : CommRingCat.{0}) (φ : O ⟶ A) (y : Spec A ⟶ X),
      φ.hom.Finite ∧ φ.hom.Flat ∧ IsPullback y (Spec.map φ) m u := by
  let N := Limits.pullback m u
  haveI : IsAffine N := isAffine_of_isAffineHom (Limits.pullback.snd m u)
  let f : Spec Γ(N, ⊤) ⟶ Spec O := N.isoSpec.inv ≫ Limits.pullback.snd m u
  have hf : Spec.map (Spec.preimage f) = f := Spec.map_preimage f
  refine ⟨Γ(N, ⊤), Spec.preimage f, N.isoSpec.inv ≫ Limits.pullback.fst m u, ?_, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hf]
    infer_instance
  · rw [← HasRingHomProperty.Spec_iff (P := @Flat), hf]
    infer_instance
  · rw [hf]
    refine (IsPullback.of_hasPullback m u).of_iso N.isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_ <;> simp [f]

theorem finRep_one_left {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
    {P S : Type} [CommRing P] [Algebra R₀ P] [CommRing S] [Algebra R₀ S] (g : P →ₐ[R₀] S) :
    (1 : sp (R₀ := R₀) S ⟶ G).left =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (1 : sp (R₀ := R₀) P ⟶ G).left := by
  rw [← spMap_left, ← Over.comp_left, MonObj.comp_one]

theorem finRep_kernel_mul_finite_free :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (p : ℕ), IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Smooth G.hom →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra (O : Type) A) (_ : Algebra R₀ A) (_ : IsScalarTower R₀ (O : Type) A),
      Module.Free (O : Type) A ∧ Module.Finite (O : Type) A ∧ ∃ y : sp (R₀ := R₀) A ⟶ G, y ^ p = 1 ∧
      ∀ (S : Type) [CommRing S] [Algebra (O : Type) S] [Algebra R₀ S] [IsScalarTower R₀ (O : Type) S] (z : sp (R₀ := R₀) S ⟶ G), z ^ p = 1 →
        ∃! φ : A →ₐ[(O : Type)] S, spMap (φ.restrictScalars R₀) ≫ y = z) := by
  intro R₀ _ G _ _ O p hfin hflat _
  obtain ⟨A, φ, y, hφf, hφl, hpb⟩ := finRep_exists_isPullback_spec ((𝟙 G) ^ p : G ⟶ G).left
    (CommRingCat.of (O : Type)) (1 : sp (R₀ := R₀) (O : Type) ⟶ G).left
  letI : Algebra (O : Type) A := φ.hom.toAlgebra
  letI : Algebra R₀ A := (φ.hom.comp (algebraMap R₀ (O : Type))).toAlgebra
  haveI : IsScalarTower R₀ (O : Type) A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (O : Type) A := hφf
  haveI : Module.Flat (O : Type) A := hφl
  have hpow : ∀ {T : Over (Spec (CommRingCat.of R₀))} (z : T ⟶ G),
      z.left ≫ ((𝟙 G) ^ p : G ⟶ G).left = (z ^ p).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hy : y ≫ G.hom = (sp (R₀ := R₀) A).hom := by
    rw [← Over.w ((𝟙 G) ^ p : G ⟶ G), ← Category.assoc, hpb.w, Category.assoc,
      Over.w (1 : sp (R₀ := R₀) (O : Type) ⟶ G)]
    simp only [sp, Over.mk_hom]
    rw [← Spec.map_comp]
    rfl
  let y' : sp (R₀ := R₀) A ⟶ G := Over.homMk y hy
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.free_of_flat_of_isLocalRing, inferInstance, y', ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [← hpow, finRep_one_left G (IsScalarTower.toAlgHom R₀ (O : Type) A)]
    exact hpb.w
  · intro S _ _ _ _ z hz
    have hw : z.left ≫ ((𝟙 G) ^ p : G ⟶ G).left =
        Spec.map (CommRingCat.ofHom (algebraMap (O : Type) S)) ≫
          (1 : sp (R₀ := R₀) (O : Type) ⟶ G).left := by
      rw [hpow, hz, finRep_one_left G (IsScalarTower.toAlgHom R₀ (O : Type) S)]
      rfl
    let l : Spec (CommRingCat.of S) ⟶ Spec A := hpb.lift _ _ hw
    have hl : Spec.map (Spec.preimage l) = l := Spec.map_preimage l
    have h1 : φ ≫ Spec.preimage l = CommRingCat.ofHom (algebraMap (O : Type) S) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hl]
      exact hpb.lift_snd _ _ hw
    refine ⟨⟨(Spec.preimage l).hom, fun r => congrArg (fun f => f.hom r) h1⟩, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      change Spec.map (Spec.preimage l) ≫ y = z.left
      rw [hl]
      exact hpb.lift_fst _ _ hw
    · intro ψ hψ
      have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom : A ⟶ CommRingCat.of S) = l := by
        apply hpb.hom_ext
        · rw [hpb.lift_fst _ _ hw, ← hψ]
          rfl
        · rw [hpb.lift_snd _ _ hw, ← Spec.map_comp]
          congr 1
          ext r
          exact ψ.commutes r
      have h3 := Spec.map_injective (h2.trans hl.symm)
      ext a
      exact congrArg (fun f => f.hom a) h3

end GlobalTheory
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem bxFibre_exists_chart {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] [IsLocalRing P] (x : Spec (CommRingCat.of P) ⟶ Y)
    (h : x (closedPoint P) ∈ U) :
    ∃ φ : Γ(Y, U) →+* P, x = Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec := by
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have hsp : (p : PrimeSpectrum P) ⤳ closedPoint P :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum P).isPrime.ne_top)
    exact hsp.mem_open (x ⁻¹ᵁ U).isOpen h
  refine ⟨(x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU
    (isAffineOpen_top (Spec (CommRingCat.of P))) hx
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem bxFibre_closed {Y : Scheme.{0}} {P Q : Type} [CommRing P] [IsLocalRing P] [CommRing Q]
    [IsLocalRing Q] (f : P →+* Q) [IsLocalHom f] (x : Spec (CommRingCat.of P) ⟶ Y) :
    (Spec.map (CommRingCat.ofHom f) ≫ x) (closedPoint Q) = x (closedPoint P) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => x y) ?_)
  exact IsLocalRing.comap_closedPoint f

theorem bxFibre_comp {Y : Scheme.{0}} {A P Q : Type} [CommRing A] [CommRing P] [CommRing Q]
    (φ : A →+* P) (f : P →+* Q) (g : Spec (CommRingCat.of A) ⟶ Y) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom φ) ≫ g =
      Spec.map (CommRingCat.ofHom (f.comp φ)) ≫ g := by
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem bxFibre_inj {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] {φ ψ : Γ(Y, U) →+* P}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) : φ = ψ := by
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem bxFibre_affine {Y : Scheme.{0}} (y : Y) : ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  exact ⟨U, hU, hmem⟩

theorem bxFibre_unique {Y : Scheme.{0}} {F P Q : Type} [CommRing F] [IsLocalRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] (p : F →+* P) [IsLocalHom p] (q : F →+* Q)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t) (c c' : Spec (CommRingCat.of F) ⟶ Y)
    (hp : Spec.map (CommRingCat.ofHom p) ≫ c = Spec.map (CommRingCat.ofHom p) ≫ c')
    (hq : Spec.map (CommRingCat.ofHom q) ≫ c = Spec.map (CommRingCat.ofHom q) ≫ c') :
    c = c' := by
  obtain ⟨U, hU, hmem⟩ := bxFibre_affine (c (closedPoint F))
  have hmem' : c' (closedPoint F) ∈ U := by
    rw [← bxFibre_closed p c', ← hp, bxFibre_closed p c]
    exact hmem
  obtain ⟨φ, hφ⟩ := bxFibre_exists_chart hU c hmem
  obtain ⟨ψ, hψ⟩ := bxFibre_exists_chart hU c' hmem'
  rw [hφ, hψ] at hp hq ⊢
  have h1 : p.comp φ = p.comp ψ := bxFibre_inj hU
    ((bxFibre_comp φ p hU.fromSpec).symm.trans (hp.trans (bxFibre_comp ψ p hU.fromSpec)))
  have h2 : q.comp φ = q.comp ψ := bxFibre_inj hU
    ((bxFibre_comp φ q hU.fromSpec).symm.trans (hq.trans (bxFibre_comp ψ q hU.fromSpec)))
  have : φ = ψ := RingHom.ext fun s =>
    hinj _ _ (RingHom.congr_fun h1 s) (RingHom.congr_fun h2 s)
  rw [this]

theorem bxFibre_exists {Y : Scheme.{0}} {F P Q R : Type} [CommRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] [IsLocalRing Q] [CommRing R] [IsLocalRing R]
    (p : F →+* P) (q : F →+* Q) (f : P →+* R) [IsLocalHom f] (g : Q →+* R) [IsLocalHom g]
    (hex : ∀ a b, f a = g b → ∃! c, p c = a ∧ q c = b)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t)
    (a : Spec (CommRingCat.of P) ⟶ Y) (b : Spec (CommRingCat.of Q) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f) ≫ a = Spec.map (CommRingCat.ofHom g) ≫ b) :
    ∃ c : Spec (CommRingCat.of F) ⟶ Y, Spec.map (CommRingCat.ofHom p) ≫ c = a ∧
      Spec.map (CommRingCat.ofHom q) ≫ c = b := by
  obtain ⟨U, hU, hmem⟩ := bxFibre_affine (a (closedPoint P))
  have hmem' : b (closedPoint Q) ∈ U := by
    rw [← bxFibre_closed g b, ← h, bxFibre_closed f a]
    exact hmem
  obtain ⟨φ, hφ⟩ := bxFibre_exists_chart hU a hmem
  obtain ⟨ψ, hψ⟩ := bxFibre_exists_chart hU b hmem'
  rw [hφ, hψ] at h ⊢
  erw [bxFibre_comp, bxFibre_comp] at h
  have h1 := bxFibre_inj hU h
  have h2 : ∀ s, ∃ c, p c = φ s ∧ q c = ψ s := fun s =>
    (hex _ _ (RingHom.congr_fun h1 s)).exists
  choose k hk hk' using h2
  let χ : Γ(Y, U) →+* F :=
    { toFun := k
      map_one' := hinj _ _ (by simp [hk]) (by simp [hk'])
      map_mul' := fun s t => hinj _ _ (by simp [hk]) (by simp [hk'])
      map_zero' := hinj _ _ (by simp [hk]) (by simp [hk'])
      map_add' := fun s t => hinj _ _ (by simp [hk]) (by simp [hk']) }
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec, ?_, ?_⟩
  · erw [bxFibre_comp]
    have : p.comp χ = φ := RingHom.ext hk
    rw [this]
  · erw [bxFibre_comp]
    have : q.comp χ = ψ := RingHom.ext hk'
    rw [this]

theorem points_fibre_product :
  (∀ {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀))) {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R) (f₂ : LHom R₂ R),
    IsFibreSq p₁ p₂ f₁ f₂ → ∀ (a : sp (R₀ := R₀) (R₁ : Type) ⟶ X) (b : sp (R₀ := R₀) (R₂ : Type) ⟶ X), spMap f₁.1 ≫ a = spMap f₂.1 ≫ b →
    ∃! c : sp (R₀ := R₀) (F : Type) ⟶ X, spMap p₁.1 ≫ c = a ∧ spMap p₂.1 ≫ c = b) := by
  intro R₀ _ X F R₁ R₂ R p₁ p₂ f₁ f₂ hsq a b hab
  obtain ⟨hc, -, -, hex⟩ := hsq
  haveI : IsLocalHom p₁.1.toRingHom := p₁.2
  haveI : IsLocalHom f₁.1.toRingHom := f₁.2
  haveI : IsLocalHom f₂.1.toRingHom := f₂.2
  have hinj : ∀ s t, p₁.1.toRingHom s = p₁.1.toRingHom t → p₂.1.toRingHom s = p₂.1.toRingHom t →
      s = t := fun s t h1 h2 =>
    (hex (p₁.1 t) (p₂.1 t) (AlgHom.congr_fun hc t)).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩
  obtain ⟨c, h1, h2⟩ := bxFibre_exists (Y := X.left) p₁.1.toRingHom p₂.1.toRingHom
    f₁.1.toRingHom f₂.1.toRingHom hex hinj a.left b.left (congrArg (·.left) hab)
  have hw : c ≫ X.hom = (sp (R₀ := R₀) (F : Type)).hom := by
    refine bxFibre_unique p₁.1.toRingHom p₂.1.toRingHom hinj _ _ ?_ ?_
    · rw [← Category.assoc, h1]
      exact (Over.w a).trans (Over.w (spMap p₁.1)).symm
    · rw [← Category.assoc, h2]
      exact (Over.w b).trans (Over.w (spMap p₂.1)).symm
  refine ⟨Over.homMk c hw, ⟨Over.OverMorphism.ext h1, Over.OverMorphism.ext h2⟩, ?_⟩
  rintro c' ⟨k1, k2⟩
  apply Over.OverMorphism.ext
  exact bxFibre_unique (Y := X.left) p₁.1.toRingHom p₂.1.toRingHom hinj _ _
    ((congrArg (·.left) k1).trans h1.symm) ((congrArg (·.left) k2).trans h2.symm)

end GlobalTheory
end
