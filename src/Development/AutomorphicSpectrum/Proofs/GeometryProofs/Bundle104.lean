module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle082
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Alg

variable {A K V T : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [AddCommGroup V] [Module A V] [AddCommGroup T] [Module K T] [Module A T] [IsScalarTower A K T]

theorem finrank_eq_of_isLocalized (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] [Module K T]
    [IsScalarTower A K T] (j : V →ₗ[A] T) [IsLocalizedModule (nonZeroDivisors A) j] :
    Module.finrank A V = Module.finrank K T := by
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors A) j le_rfl
  have h2 : Module.finrank K T = Module.finrank A T :=
    congrArg Cardinal.toNat (IsLocalization.rank_eq K (N := T) (nonZeroDivisors A) le_rfl)
  exact h1.symm.trans h2.symm

theorem injective_of_isLocalized [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] : Function.Injective j := by
  intro x y h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors A) j).1 h
  exact smul_right_injective V (nonZeroDivisors.ne_zero c.2) hc

def resMap (j : V →ₗ[A] T) (W : Submodule K T) : (W.restrictScalars A).comap j →ₗ[A] W where
  toFun x := ⟨j x, x.2⟩
  map_add' x y := Subtype.ext (map_add j _ _)
  map_smul' c x := Subtype.ext (map_smul j c _)

theorem isLocalized_resMap [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] (W : Submodule K T) :
    IsLocalizedModule (nonZeroDivisors A) (resMap j W) := by
  constructor
  · intro a
    have hk : algebraMap A K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have key : ∀ w : W, algebraMap A (Module.End A W) a w = algebraMap A K a • w := fun w => by
      rw [Module.algebraMap_end_apply, algebraMap_smul]
    refine (Module.End.isUnit_iff _).2 ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A K a)⁻¹ • w, ?_⟩⟩
    · rw [key, key] at h
      exact smul_right_injective W hk h
    · rw [key, smul_smul, mul_inv_cancel₀ hk, one_smul]
  · intro w
    obtain ⟨⟨y, a⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors A) j (w : T)
    have h' : (a : A) • (w : T) = j y := h
    have hy : j y ∈ W := by
      rw [← h', ← algebraMap_smul K (a : A) (w : T)]
      exact W.smul_mem _ w.2
    exact ⟨(⟨y, hy⟩, a), Subtype.ext h⟩
  · intro x y h
    refine ⟨1, ?_⟩
    rw [one_smul, one_smul]
    exact Subtype.ext (injective_of_isLocalized j (congrArg Subtype.val h))

theorem finrank_comap_eq [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] (W : Submodule K T) :
    Module.finrank A ((W.restrictScalars A).comap j) = Module.finrank K W := by
  haveI := isLocalized_resMap j W
  exact finrank_eq_of_isLocalized K (resMap j W)

theorem exists_smul_mem (j : V →ₗ[A] T) (S : Submodule A V) (B : Set T)
    (hB : ∀ w ∈ B, ∃ a : A, a ≠ 0 ∧ ∃ y ∈ S, a • w = j y) {w : T} (hw : w ∈ Submodule.span K B) :
    ∃ a : A, a ≠ 0 ∧ ∃ y ∈ S, a • w = j y := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact hB w hw
  | zero => exact ⟨1, one_ne_zero, 0, S.zero_mem, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, y, hy, e⟩ := hu
    obtain ⟨b, hb, y', hy', e'⟩ := hv
    refine ⟨a * b, mul_ne_zero ha hb, b • y + a • y', S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hy'), ?_⟩
    rw [map_add (f := _), map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm a b, mul_comm b a,
      mul_comm a b]
  | smul c u _ hu =>
    obtain ⟨a, ha, y, hy, e⟩ := hu
    obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hk : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    refine ⟨d * a, mul_ne_zero hd0 ha, b • y, S.smul_mem _ hy, ?_⟩
    rw [map_smul, ← e, ← algebraMap_smul K (d * a), ← algebraMap_smul K b, ← algebraMap_smul K a, smul_smul,
      smul_smul, map_mul]
    congr 1
    field_simp

end Alg

section Num

variable {L V T : Type} [Field L] [NumberField L] [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup T]
  [Module (𝓞 L) T]

theorem exists_nat_smul (j : V →ₗ[𝓞 L] T) [IsLocalizedModule (nonZeroDivisors (𝓞 L)) j] (w : T) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ y : V, (n : 𝓞 L) • w = j y := by
  obtain ⟨⟨y, a⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 L)) j w
  have ha : (a : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero a.2
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {(a : 𝓞 L)}))
  refine ⟨Ideal.absNorm (Ideal.span {(a : 𝓞 L)}), ?_, b • y, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha
  · have h' : (a : 𝓞 L) • w = j y := h
    rw [← hb, mul_smul, map_smul, ← h']

end Num

section Geo

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li]
  [Module Ω Li] {L : Type} [Field L] [NumberField L] {z : Sp (𝓞 L) ⟶ X} {V : Type} [AddCommGroup V]
  [Module (𝓞 L) V] {T : Type} [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T]

theorem eq_pt_of_lifts {MB : LieModel G z V} {TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T}
    {j : V →ₗ[𝓞 L] T} (hl : ∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) {x : V}
    {v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G} (h : (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) :
    v = TL.pt (j x) := by
  have e : v.left ≫ 𝟙 G.left = (TL.pt (j x)).left ≫ 𝟙 G.left := h.trans (hl x).symm
  rw [Category.comp_id, Category.comp_id] at e
  exact Over.OverMorphism.ext e

theorem mem_subGens_of_nat {M : LieModel G ξ Li} {U : Submodule Ω Li} {MB : LieModel G z V}
    {TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T} {j : V →ₗ[𝓞 L] T}
    (hl : ∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) {e : Li} (he : e ∈ U) {w : T}
    (hv : M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)) (n : ℕ) {y : V} (hy : (n : 𝓞 L) • w = j y) :
    y ∈ subGens M U z MB := by
  obtain ⟨h1, -⟩ := id hv
  have key := hv.smul h1 (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))
  have e1 : (Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom
      (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z))) = (n : L) := map_natCast _ n
  rw [map_natCast, e1, ← TL.pt_smul] at key
  have e2 : (n : L) • w = j y := by
    rw [← hy, ← algebraMap_smul L (n : 𝓞 L) w, map_natCast]
  rw [e2] at key
  exact ⟨_, U.smul_mem _ he, _, key, hl y⟩

end Geo

theorem finrank_subFib : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V] (MB : LieModel G z V) (T : Type) [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T] (TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T) (j : V →ₗ[𝓞 L] T) (U : Submodule Ω Li), IsCptGen ξ → (∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) → IsBaseChange L j → Module.finrank (𝓞 L) V = Module.finrank L T ∧ Module.finrank (𝓞 L) (FlagFib.subFib M U z MB) = Module.finrank L (Submodule.span L {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)}) := by
  intro X G _ Ω _ ξ Li _ _ M L _ _ z V _ _ _ _ MB T _ _ _ _ TL j U _ hl hj
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L j).2 hj
  refine ⟨finrank_eq_of_isLocalized L j, ?_⟩
  set B : Set T := {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)} with hBdef
  have hinj : Function.Injective j := injective_of_isLocalized j
  have hS : ∀ y ∈ Submodule.span (𝓞 L) (subGens M U z MB), j y ∈ Submodule.span L B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, he, v, hv, hlift⟩ := hy
      have hv' := eq_pt_of_lifts hl hlift
      exact Submodule.subset_span ⟨e, he, hv' ▸ hv⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | smul c a _ ha =>
      rw [map_smul, ← algebraMap_smul L c (j a)]
      exact Submodule.smul_mem _ _ ha
  have hB : ∀ w ∈ B, ∃ a : 𝓞 L, a ≠ 0 ∧ ∃ y ∈ Submodule.span (𝓞 L) (subGens M U z MB), a • w = j y := by
    rintro w ⟨e, he, hv⟩
    obtain ⟨n, hn, y, hy⟩ := exists_nat_smul j w
    exact ⟨n, Nat.cast_ne_zero.2 hn, y, Submodule.subset_span (mem_subGens_of_nat hl he hv n hy), hy⟩
  have e : subFib M U z MB = ((Submodule.span L B).restrictScalars (𝓞 L)).comap j := by
    ext x
    rw [mem_subFib]
    constructor
    · rintro ⟨a, ha, hx⟩
      have h1 := hS _ hx
      rw [map_smul, ← algebraMap_smul L a (j x)] at h1
      have hk : algebraMap (𝓞 L) L a ≠ 0 := fun h0 => ha (by simpa using h0)
      exact (Submodule.smul_mem_iff (Submodule.span L B) hk).1 h1
    · intro hx
      obtain ⟨a, ha, y, hy, h⟩ := exists_smul_mem j _ B hB (K := L) hx
      refine ⟨a, ha, ?_⟩
      rwa [hinj (by rw [map_smul]; exact h : j (a • x) = j y)]
  rw [e]
  exact finrank_comap_eq j _

end GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg

private lemma valAt_unique_lemma {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) {b : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r') : r = r' := by
  obtain ⟨hs, s, hs1, hs2⟩ := h1
  obtain ⟨hs', s', hs1', hs2'⟩ := h2
  have hs1'' : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ s' = b := hs1'
  have e0 : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ (s - s') = 0 :=
    (map_sub _ s s').trans (by rw [hs1, hs1'', sub_self])
  have hnu : ¬ IsUnit (s - s') := by
    intro hu
    have hu' := hu.map (GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩)
    exact not_isUnit_zero ((congrArg IsUnit e0).mp hu')
  have e1 : (Scheme.stalkClosedPointTo z).hom (s - s') = r - r' := by
    rw [← hs2, ← hs2']
    exact map_sub _ _ _
  by_contra hne
  apply hnu
  apply (Scheme.isLocalHom_stalkClosedPointTo z).map_nonunit
  exact (congrArg IsUnit e1).mpr (sub_ne_zero.mpr hne).isUnit

private lemma valAt_mul_lemma_2 {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) {b b' : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b' r') :
    GlobalTheory.CompanionTheory.Ar.ValAt ξ z (b * b') (r * r') ∧ GlobalTheory.CompanionTheory.Ar.ValAt ξ z 1 1 := by
  obtain ⟨hs, s, hs1, hs2⟩ := h1
  obtain ⟨hs', s', hs1', hs2'⟩ := h2
  have hs1'' : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ s' = b' := hs1'
  exact ⟨⟨hs, s * s', (map_mul _ s s').trans (congrArg₂ (· * ·) hs1 hs1''),
      (map_mul _ s s').trans (congrArg₂ (· * ·) hs2 hs2')⟩,
    ⟨hs, 1, map_one _, map_one _⟩⟩

theorem coordsAt_blkV : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)), GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i → CoordTie ℤ ξ₀ (fun c' : (k : K₀) → J₀ k => ∏ k, y₀ ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ₀ y₀ (z ≫ h) (fun p => w (blkV bk bx p)) := by
  classical
  intro X X₀ Ω Ω₀ _ _ ξ ξ₀ h i K₀ K _ _ J₀ J _ _ y₀ y bk bx hdom htie hgen hy hval z w hw
  unfold GlobalTheory.CompanionTheory.Ar.Dominates at hdom
  have hpt : ∀ (a b : PrimeSpectrum Ω₀), a = b := fun a b =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans (Ideal.eq_bot_of_prime b.asIdeal).symm)
  have hsp : GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ⤳ GlobalTheory.CompanionTheory.Ar.centre (z ≫ h) := by
    have h2 := (hgen (GlobalTheory.CompanionTheory.Ar.centre z)).map h.continuous
    have e1 : h (GlobalTheory.CompanionTheory.Ar.genPt ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ₀ := by
      have hh := congrArg (fun f => f (IsLocalRing.closedPoint Ω)) hdom
      simp only [Scheme.Hom.comp_apply] at hh
      exact hh.trans (congrArg ξ₀ (hpt _ _))
    have e2 : h (GlobalTheory.CompanionTheory.Ar.centre z) = GlobalTheory.CompanionTheory.Ar.centre (z ≫ h) :=
      (Scheme.Hom.comp_apply z h _).symm
    rw [← e1, ← e2]
    exact h2
  unfold GlobalTheory.CompanionTheory.Ar.CoordsAt at hw ⊢
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c', hc'⟩ := hw1 (bk k)
    refine ⟨(bx k).symm c', ?_⟩
    simpa [GlobalTheory.CompanionTheory.Ar.Chg.blkV] using hc'
  · simp only [GlobalTheory.CompanionTheory.Ar.Chg.blkV] at hc ⊢
    obtain ⟨hyne, hrat⟩ := hw2 (bk k) (bx k c) hc
    have hy0c : y₀ ⟨k, c⟩ ≠ 0 := fun h0 => hyne (by rw [hy, h0, map_zero])
    refine ⟨hy0c, fun j => ?_⟩
    obtain ⟨c', hc'0, hc'reg⟩ := htie.cover ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩
    dsimp only at hc'0 hc'reg
    have hprod : ∀ c'' : (k' : K₀) → J₀ k', (∏ k', y₀ ⟨k', c'' k'⟩) =
        y₀ ⟨k, c'' k⟩ * ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c'' k'⟩ :=
      fun c'' => Fintype.prod_eq_mul_prod_compl k _
    have hQ : ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c' k'⟩ ≠ 0 := by
      intro h0
      apply hc'0
      rw [hprod c', h0, mul_zero]
    have hd : y₀ ⟨k, c' k⟩ ≠ 0 := by
      intro h0
      apply hc'0
      rw [hprod c', h0, zero_mul]
    have hrat0 : ∀ j' : J₀ k, y₀ ⟨k, j'⟩ / y₀ ⟨k, c' k⟩ ∈
        GlobalTheory.CompanionTheory.Ar.regAt ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ := by
      intro j'
      have hm := hc'reg (Function.update c' k j')
      have hrest : ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', Function.update c' k j' k'⟩ =
          ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c' k'⟩ := by
        apply Finset.prod_congr rfl
        intro k' hk'
        rw [Function.update_of_ne (by simpa using hk')]
      rw [hprod (Function.update c' k j'), hprod c', hrest, Function.update_self,
        mul_div_mul_right _ _ hQ] at hm
      exact hm
    obtain ⟨sj, hsj⟩ := RingHom.mem_range.mp (hrat0 j)
    obtain ⟨sc, hsc⟩ := RingHom.mem_range.mp (hrat0 c)
    have hvalc : GlobalTheory.CompanionTheory.Ar.ValAt ξ₀ (z ≫ h) (y₀ ⟨k, c⟩ / y₀ ⟨k, c' k⟩)
        ((Scheme.stalkClosedPointTo (z ≫ h)).hom sc) := ⟨hsp, sc, hsc, rfl⟩
    have hvalc' := hval z _ _ hvalc
    obtain ⟨rd, hrd, -⟩ := hrat (bx k (c' k))
    rw [hy, hy, ← map_div₀] at hrd
    obtain ⟨hprodv, hone⟩ := valAt_mul_lemma_2 ξ z hvalc' hrd
    rw [← map_mul, div_mul_div_comm, mul_comm (y₀ ⟨k, c⟩), div_self (mul_ne_zero hd hy0c),
      map_one] at hprodv
    have h1 := valAt_unique_lemma ξ z hprodv hone
    have hv : (Scheme.stalkClosedPointTo (z ≫ h)).hom sc ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hunit : IsUnit sc := (Scheme.isLocalHom_stalkClosedPointTo (z ≫ h)).map_nonunit _ (Ne.isUnit hv)
    let sci : X₀.presheaf.stalk (↑(⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ : GlobalTheory.CompanionTheory.Ar.Cpt ξ₀)) :=
      ↑hunit.unit⁻¹
    have hsci : sci * sc = 1 := by
      have hinv := hunit.unit.inv_mul
      rw [IsUnit.unit_spec] at hinv
      exact hinv
    have hgsci : GlobalTheory.CompanionTheory.Ar.genMap ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ sci *
        (y₀ ⟨k, c⟩ / y₀ ⟨k, c' k⟩) = 1 := by
      rw [← hsc, ← map_mul, hsci, map_one]
    have hs₀ : GlobalTheory.CompanionTheory.Ar.genMap ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ (sj * sci) =
        y₀ ⟨k, j⟩ / y₀ ⟨k, c⟩ := by
      rw [map_mul, hsj, eq_inv_of_mul_eq_one_left hgsci]
      field_simp
    have hex : GlobalTheory.CompanionTheory.Ar.ValAt ξ₀ (z ≫ h) (y₀ ⟨k, j⟩ / y₀ ⟨k, c⟩)
        ((Scheme.stalkClosedPointTo (z ≫ h)).hom (sj * sci)) := ⟨hsp, _, hs₀, rfl⟩
    have hex' := hval z _ _ hex
    obtain ⟨r, hr, hwr⟩ := hrat (bx k j)
    rw [hy, hy, ← map_div₀] at hr
    have hrr := valAt_unique_lemma ξ z hr hex'
    refine ⟨r, ?_, hwr⟩
    rw [hrr]
    exact hex

end GlobalTheory.CompanionTheory.Ar.Chg
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

theorem aeval_mul_homog {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {A : Type} [CommRing A] [Algebra ℤ A]
    (g : MRing J₀) (a : K₀ → ℕ) (hg : IsMultiHomog g a) (u : (Σ k, J₀ k) → A) (t : K₀ → A) :
    aeval (fun p => u p * t p.1) g = aeval u g * ∏ k, t k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, J₀ k), t i.1 ^ d i) = ∏ k, t k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, t k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem aeval_comp_ringHom {σ A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (φ : A →+* B) (u : σ → A)
    (g : MvPolynomial σ ℤ) : aeval (fun p => φ (u p)) g = φ (aeval u g) := by
  induction g using MvPolynomial.induction_on with
  | C m => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X]

theorem pow_mul_pow_sub_eq {F : Type} [Field F] (x b : F) (hb : b ≠ 0) {j n : ℕ} (hj : j ≤ n) :
    x ^ j * b ^ (n - j) = (x / b) ^ j * b ^ n := by
  have h : b ^ n = b ^ j * b ^ (n - j) := by rw [← pow_add]; congr 1; omega
  rw [h, div_pow]
  field_simp

theorem ratio_relation_at_complex_points :
    ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)]
      [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω)
      (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (q r : Σ k, J k) (n : ℕ) (c : ℕ → MRing J₀)
      (a : K₀ → ℕ), (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → q.1 = r.1 → y r ≠ 0 →
      (∀ j, IsMultiHomog (c j) a) →
      (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * (y q / y r) ^ j = 0) →
      ∀ z ∈ mcPts (mCoordIdeal y), z r ≠ 0 → ∀ w : (Σ k, J₀ k) → ℂ,
        SameOrbit (fun p => z (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx p)) w →
        ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
  intro K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ y₀ y bk bx i q r n c a hy hqr hr hc hrel z hz hzr w hw
  have hcone : ∀ g : MRing J₀, IsMultiHomog g a →
      mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) =
        MvPolynomial.C (i (aeval y₀ g)) * ∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k := by
    intro g hg
    have h1 : mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) =
        aeval (fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1)) g := by
      simp only [mConeMap]
      rw [aeval_rename]
      have e : ((fun p : (Σ k, J k) => (MvPolynomial.C (y p) : MvPolynomial K Ω) * MvPolynomial.X p.1) ∘
          GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) =
          fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1) := by
        funext p
        obtain ⟨k, b⟩ := p
        simp [GlobalTheory.CompanionTheory.Ar.Chg.blkV, hy]
      rw [e]
    rw [h1, aeval_mul_homog g a hg (fun p => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω)) (fun k => MvPolynomial.X (bk k))]
    congr 1
    exact aeval_comp_ringHom ((MvPolynomial.C : Ω →+* MvPolynomial K Ω).comp i) y₀ g
  have hXq : mConeMap y (MvPolynomial.X q) = MvPolynomial.C (y q) * MvPolynomial.X r.1 := by
    simp [mConeMap, hqr]
  have hXr : mConeMap y (MvPolynomial.X r) = MvPolynomial.C (y r) * MvPolynomial.X r.1 := by
    simp [mConeMap]
  let F : MRing J := ∑ j ∈ Finset.range (n + 1),
    rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j) * MvPolynomial.X q ^ j * MvPolynomial.X r ^ (n - j)
  have hF : F ∈ mCoordIdeal y := by
    show mConeMap y F = 0

    simp only [F, map_sum, map_mul, map_pow, hcone _ (hc _), hXq, hXr]
    have hterm : ∀ j ∈ Finset.range (n + 1),
        MvPolynomial.C (i (aeval y₀ (c j))) * (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) *
            (MvPolynomial.C (y q) * MvPolynomial.X r.1) ^ j * (MvPolynomial.C (y r) * MvPolynomial.X r.1) ^ (n - j) =
          (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) * MvPolynomial.X r.1 ^ n *
            MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) := by
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have e1 : y q ^ j * y r ^ (n - j) = (y q / y r) ^ j * y r ^ n := pow_mul_pow_sub_eq _ _ hr hjn
      have e2 : (MvPolynomial.X r.1 : MvPolynomial K Ω) ^ n = MvPolynomial.X r.1 ^ j * MvPolynomial.X r.1 ^ (n - j) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (MvPolynomial.C (y q) : MvPolynomial K Ω) ^ j * MvPolynomial.C (y r) ^ (n - j) =
          MvPolynomial.C ((y q / y r) ^ j * y r ^ n) := by
        rw [← e1]; simp only [map_mul, map_pow]
      rw [mul_pow, mul_pow, e2]
      have e4 : (MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) : MvPolynomial K Ω) =
          MvPolynomial.C (i (aeval y₀ (c j))) * MvPolynomial.C ((y q / y r) ^ j * y r ^ n) := by
        rw [← map_mul]; congr 1; ring
      rw [e4, ← e3]
      ring

    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum, ← Finset.mul_sum, hrel]
    simp
  obtain ⟨s, hs, he⟩ := hw
  have hev := hz.2 F hF
  have hren : ∀ j, eval z (map (Int.castRingHom ℂ) (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j))) =
      (∏ k, s k ^ a k) * eval w (map (Int.castRingHom ℂ) (c j)) := by
    intro j
    rw [map_rename, eval_rename]
    have : z ∘ GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx = fun p => s p.1 * w p := he
    rw [this, eval_smul_homog (c j) a (hc j) s w]

  simp only [F, map_sum, map_mul, map_pow, map_X, eval_X, hren] at hev
  have hP : (∏ k, s k ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hs k)
  have hfin : (∏ k, s k ^ a k) * z r ^ n *
      ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
    rw [← hev, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [mul_assoc ((∏ k, s k ^ a k) * _), pow_mul_pow_sub_eq _ _ hzr hjn]
    ring
  exact (mul_eq_zero.1 hfin).resolve_left (mul_ne_zero hP (pow_ne_zero _ hzr))

end GlobalTheory.CompanionTheory.Ar.Rel
end
end

section

open ReciprocityTheory.ChartRestriction.G.Geo

theorem _root_.GlobalTheory.T.chart_lattice_norm_membership : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (q : ℕ) (x : Ω), (∀ (c : (k : K) → ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ W : ValuationSubring Ω, (∀ p, y p / y ⟨p.1, c p.1⟩ ∈ W) → x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q ∈ W) → x * u ^ q ∈ chartLatNm y a q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartVal.mem_chartLatNm_of_forall_valuationSubring | exact GlobalTheory.CompanionTheory.Ar.ChartVal.mem_chartLatNm_of_forall_valuationSubring | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartVal.mem_chartLatNm_of_forall_valuationSubring <;> assumption)
end
