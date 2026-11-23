module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {S : Scheme.{0}}

def ClopenCond (T : Over S) (P : ∀ T' : Over S, (T' ⟶ T) → Prop) : Prop :=
  ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T), P T' h ↔ Set.range h.left ⊆ U

theorem ClopenCond.congr {T : Over S} {P P' : ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ClopenCond T P)
    (e : ∀ T' h, P' T' h ↔ P T' h) : ClopenCond T P' := by
  obtain ⟨U, hU, H⟩ := h
  exact ⟨U, hU, fun T' h => (e T' h).trans (H T' h)⟩

theorem ClopenCond.and {T : Over S} {P P' : ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ClopenCond T P)
    (h' : ClopenCond T P') : ClopenCond T fun T' h => P T' h ∧ P' T' h := by
  obtain ⟨U, hU, H⟩ := h
  obtain ⟨U', hU', H'⟩ := h'
  refine ⟨U ⊓ U', hU.inter hU', fun T' h => ?_⟩
  beta_reduce
  rw [H, H', TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]

theorem ClopenCond.forall_finite {T : Over S} {J : Type} [Finite J] {P : J → ∀ T' : Over S, (T' ⟶ T) → Prop}
    (h : ∀ i, ClopenCond T (P i)) : ClopenCond T fun T' h => ∀ i, P i T' h := by
  choose U hU H using h
  refine ⟨⟨⋂ i, (U i : Set T.left), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, isClosed_iInter hU,
    fun T' h => ?_⟩
  simp only [H, TopologicalSpace.Opens.coe_mk, Set.subset_iInter_iff]

theorem ClopenCond.forall_of_finite {T : Over S} {J κ : Type} [Finite κ] (q : J → κ)
    {P : J → ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ∀ i, ClopenCond T (P i))
    (hq : ∀ i j, q i = q j → ∀ T' h, P i T' h → P j T' h) : ClopenCond T fun T' h => ∀ i, P i T' h := by
  refine (ClopenCond.forall_finite (J := Set.range q) fun c => h c.2.choose).congr fun T' h => ?_
  exact ⟨fun H c => H _, fun H i => hq _ _ (⟨i, rfl⟩ : q i ∈ Set.range q).choose_spec T' h (H ⟨q i, i, rfl⟩)⟩

theorem exists_finite_mod (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    ∃ (κ : Type) (_ : Finite κ) (q : M → κ), ∀ a a', q a = q a' → ∃ c, a' = a + n • c := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let b := Module.Free.chooseBasis ℤ M
  refine ⟨Module.Free.ChooseBasisIndex ℤ M → ZMod n, inferInstance, fun a i => (b.repr a i : ZMod n),
    fun a a' h => ?_⟩
  have h1 : ∀ i, ∃ c : ℤ, b.repr a' i - b.repr a i = n * c := fun i =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun h i)
  choose c hc using h1
  refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
  rw [map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
  simp only [Module.Basis.equivFun_apply, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  linarith [hc i]

theorem clopenCond_eq {T Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (u u' : T ⟶ Z) :
    ClopenCond T fun _ h => h ≫ u = h ≫ u' := by
  refine ⟨(FinEt.agreeι u u').opensRange, (FinEt.agreeι u u').isClosedEmbedding.isClosed_range, fun T' h => ?_⟩
  refine Iff.trans ?_ (FinEt.comp_eq_comp_iff_range u u' h.left)
  exact ⟨fun e => congrArg CommaMorphism.left e, fun e => Over.OverMorphism.ext e⟩

def RepTors (G : Over S) [GrpObj G] (n : ℕ) (La : Type) [AddCommGroup La] (Z : Over S) (et : La → (Z ⟶ G)) : Prop :=
  IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧
    ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a + c) = et' a * et' c) → (∀ a, et' a ^ n = 1) →
      ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a

theorem RepTors.ext {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S} {et : La → (Z ⟶ G)}
    (R : RepTors G n La Z et) {T : Over S} {u u' : T ⟶ Z} (h : ∀ a, u ≫ et a = u' ≫ et a) : u = u' :=
  (R.2.2.2.2 T (fun a => u' ≫ et a) (fun a c => by rw [R.2.2.1, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one])).unique h fun _ => rfl

theorem RepTors.clopenCond {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S}
    {et : La → (Z ⟶ G)} (R : RepTors G n La Z et) {T : Over S} (x y : La → (T ⟶ G))
    (hx : ∀ a c, x (a + c) = x a * x c) (hx' : ∀ a, x a ^ n = 1)
    (hy : ∀ a c, y (a + c) = y a * y c) (hy' : ∀ a, y a ^ n = 1) :
    ClopenCond T fun _ h => ∀ a, h ≫ x a = h ≫ y a := by
  obtain ⟨u, hu, -⟩ := R.2.2.2.2 T x hx hx'
  obtain ⟨u', hu', -⟩ := R.2.2.2.2 T y hy hy'
  have := R.1
  have := R.2.1
  refine (clopenCond_eq u u').congr fun T' h => ⟨fun H => R.ext fun a => ?_, fun H a => ?_⟩
  · rw [Category.assoc, Category.assoc, hu, hu', H]
  · rw [← hu, ← hu', ← Category.assoc, H, Category.assoc]

theorem exists_lift_geom {W Z : Scheme.{0}} (p : W ⟶ Z) [IsFinite p] {k : Type} [Field k] [IsAlgClosed k]
    (z : Sp k ⟶ Z) (hz : Set.range z ⊆ Set.range p) : ∃ w : Sp k ⟶ W, w ≫ p = z := by
  let pt : Sp k := (⊥ : PrimeSpectrum k)
  have h1 : pt ∈ Set.range (pullback.snd p z) := by
    rw [Scheme.Pullback.range_snd]
    exact hz ⟨pt, rfl⟩
  obtain ⟨y, -⟩ := h1
  have : Nonempty (pullback p z : Scheme) := ⟨y⟩
  have : IsAffine (pullback p z) := isAffine_of_isAffineHom (pullback.snd p z)
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := (pullback p z : Scheme))).exists_closed_singleton Set.univ_nonempty
  refine ⟨pointOfClosedPoint (pullback.snd p z) x hx ≫ pullback.fst p z, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem exists_image {W Z : Over S} [IsFinite W.hom] [Etale W.hom] [IsFinite Z.hom] [Etale Z.hom] (p : W ⟶ Z) :
    ∃ U : Z.left.Opens, IsClosed (U : Set Z.left) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
      (z : Over.mk x ⟶ Z), Set.range z.left ⊆ U ↔ ∃ w : Over.mk x ⟶ W, w ≫ p = z := by
  have := FinEt.isFinite_left p
  have := FinEt.etale_left p
  refine ⟨⟨Set.range p.left, p.left.isOpenMap.isOpen_range⟩, p.left.isClosedMap.isClosed_range,
    fun k _ _ x z => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨w, hw⟩ := exists_lift_geom p.left z.left h
    refine ⟨Over.homMk w ?_, Over.OverMorphism.ext hw⟩
    show w ≫ W.hom = x
    rw [← Over.w p, ← Category.assoc, hw]
    exact Over.w z
  · rintro ⟨w, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨w.left y, by simp⟩

theorem exists_sub {Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (U : Z.left.Opens) (hU : IsClosed (U : Set Z.left)) :
    ∃ (V : Over S) (i : V ⟶ Z), IsFinite V.hom ∧ Etale V.hom ∧ Mono i ∧
      ∀ (T : Over S) (h : T ⟶ Z), Set.range h.left ⊆ U ↔ ∃ h' : T ⟶ V, h' ≫ i = h := by
  have hc : IsClosedImmersion U.ι := .of_isPreimmersion _ (by simpa using hU)
  refine ⟨Over.mk (U.ι ≫ Z.hom), Over.homMk U.ι rfl, inferInstanceAs (IsFinite (U.ι ≫ Z.hom)),
    inferInstanceAs (Etale (U.ι ≫ Z.hom)), ?_, fun T h => ?_⟩
  · have : Mono (Over.homMk U.ι rfl : Over.mk (U.ι ≫ Z.hom) ⟶ Z).left := inferInstanceAs (Mono U.ι)
    exact Over.mono_of_mono_left _
  · rw [FinEt.range_subset_iff_factors]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨Over.homMk t ?_, Over.OverMorphism.ext ht⟩
      show t ≫ U.ι ≫ Z.hom = T.hom
      rw [← Category.assoc, ht, Over.w h]
    · rintro ⟨t, ht⟩
      exact ⟨t.left, congrArg CommaMorphism.left ht⟩

theorem range_subset_of_geom {T Z : Over S} (h : T ⟶ Z) (U : Set Z.left)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ T), Set.range (y ≫ h).left ⊆ U) :
    Set.range h.left ⊆ U := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨k, _, _, a, ha⟩ := FinEt.exists_algClosed_point T.left t
  obtain ⟨p, rfl⟩ : t ∈ Set.range a := by rw [ha]; rfl
  exact H k (a ≫ T.hom) (Over.homMk a rfl) ⟨p, by simp⟩

theorem finiteEtale_tensor (X Y : Over S) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsFinite (X ⊗ Y).hom ∧ Etale (X ⊗ Y).hom :=
  ⟨inferInstanceAs (IsFinite (pullback.fst X.hom Y.hom ≫ X.hom)),
    inferInstanceAs (Etale (pullback.fst X.hom Y.hom ≫ X.hom))⟩

end GlobalTheory.LevCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace GlobalTheory.FiniteBirationalNear

theorem exists_common_smul_mem {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (S : Submonoid A) {N : Submodule A M} (hN : N.FG) (N' : Submodule A M)
    (h : ∀ m ∈ N, ∃ s ∈ S, s • m ∈ N') : ∃ s ∈ S, ∀ m ∈ N, s • m ∈ N' := by
  classical
  obtain ⟨T, rfl⟩ := hN
  choose! s hs hs' using h
  refine ⟨∏ t ∈ T, s t, prod_mem fun t ht => hs t (Submodule.subset_span ht), ?_⟩
  have : Submodule.span A (T : Set M) ≤ N'.comap ((∏ t ∈ T, s t) • LinearMap.id) := by
    refine Submodule.span_le.2 fun t ht => ?_
    change (∏ t ∈ T, s t) • t ∈ N'
    rw [← Finset.prod_erase_mul T s ht, mul_smul]
    exact N'.smul_mem _ (hs' t (Submodule.subset_span ht))
  exact fun m hm => this hm

theorem exists_away_isDomain {A O : Type*} [CommRing A] [IsNoetherianRing A] [CommRing O]
    [Algebra A O] (S : Submonoid A) [IsLocalization S O] [IsDomain O] :
    ∃ s ∈ S, ∀ (P : Type) [CommRing P] [Algebra A P] [IsLocalization.Away s P], IsDomain P := by
  obtain ⟨s, hs, h⟩ := exists_common_smul_mem S
    (IsNoetherian.noetherian (RingHom.ker (algebraMap A O))) ⊥ fun m hm => by
      obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff S O m).1 hm
      exact ⟨c, c.2, hc⟩
  refine ⟨s, hs, fun P _ _ _ => ?_⟩
  have hu : IsUnit (algebraMap A O s) := IsLocalization.map_units O ⟨s, hs⟩
  refine Function.Injective.isDomain (IsLocalization.Away.lift (S := P) s hu) ?_
  rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro e
    have := congrArg (IsLocalization.Away.lift (S := P) s hu) e
    simpa using this
  · intro e
    have h1 : x - y ∈ RingHom.ker (algebraMap A O) := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    have h2 : s * (x - y) = 0 := h _ h1
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalization.map_eq_zero_iff (.powers s) P _).2 ⟨⟨s, Submonoid.mem_powers s⟩, h2⟩

theorem exists_mul_mem_range {A O K B : Type*} [CommRing A] [IsDomain A] [CommRing O]
    [Algebra A O] (S : Submonoid A) [IsLocalization S O] [IsDomain O] [IsIntegrallyClosed O]
    [Field K] [Algebra A K] [IsFractionRing A K] [CommRing B] [Algebra A B] [Module.Finite A B]
    (ψ : B →ₐ[A] K) (hψ : Function.Injective ψ) :
    ∃ r ∈ S, ∀ b : B, ∃ a : A, algebraMap A B a = algebraMap A B r * b := by
  have hu (s : S) : IsUnit (algebraMap A K s) := by
    refine IsUnit.mk0 _ fun h0 => ?_
    have h1 : (s : A) = 0 := IsFractionRing.injective A K (by rw [h0, map_zero])
    have h2 := IsLocalization.map_units O s
    rw [h1, map_zero] at h2
    exact not_isUnit_zero h2
  let : Algebra O K := (IsLocalization.lift (S := O) hu).toAlgebra
  have : IsScalarTower A O K := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.lift_eq hu a).symm
  have : IsFractionRing O K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S O K
  obtain ⟨r, hr, h⟩ := exists_common_smul_mem S (Module.Finite.fg_top (R := A) (M := B))
    (LinearMap.range (Algebra.linearMap A B)) fun b _ => by
      have hb : IsIntegral O (ψ b) := ((Algebra.IsIntegral.isIntegral (R := A) b).map ψ).tower_top
      obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.mp hb
      obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj S o
      refine ⟨s, s.2, a, hψ ?_⟩
      have e' := congrArg (algebraMap O K) e
      rw [map_mul, ho, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e'
      rw [Algebra.linearMap_apply, ψ.commutes, map_smul, Algebra.smul_def, mul_comm, e']
  refine ⟨r, hr, fun b => ?_⟩
  obtain ⟨a, ha⟩ := h b trivial
  exact ⟨a, by rw [← Algebra.smul_def]; exact ha⟩

theorem exists_isIntegral_nhds {M : Scheme.{0}} [IsLocallyNoetherian M] (x : M)
    [IsDomain (M.presheaf.stalk x)] : ∃ V : M.Opens, x ∈ V ∧ IsIntegral V := by
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    M.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(M, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := M.presheaf.algebra_section_stalk (U := U) ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨s, hs, h⟩ := exists_away_isDomain (O := M.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have := hU.isLocalization_basicOpen s
  have : IsDomain Γ(M, M.basicOpen s) := h _
  refine ⟨M.basicOpen s, (M.mem_basicOpen s x hxU).2
    (IsLocalization.map_units (M.presheaf.stalk x) ⟨s, hs⟩), ?_⟩
  exact IsIntegral.of_isIso (hU.basicOpen s).isoSpec.inv

theorem exists_isIso_of_isIntegral {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [IsIntegral X]
    [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))] (y : Y)
    [IsIntegrallyClosed (Y.presheaf.stalk y)] : ∃ V : Y.Opens, y ∈ V ∧ IsIso (f ∣_ V) := by
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : Nonempty U := ⟨⟨y, hxU⟩⟩
  letI := (f.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  have hη := apply_genericPoint_of_isDominant f
  have hyU : f (genericPoint X) ∈ U := by
    rw [hη]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨_, hyU⟩
  have hfr_local (z : Y) (hzU : z ∈ U) (hz : z = genericPoint Y) :
      letI := Y.presheaf.algebra_section_stalk (U := U) ⟨z, hzU⟩
      IsFractionRing Γ(Y, U) (Y.presheaf.stalk z) := by
    haveI : Nonempty U := ⟨⟨z, hzU⟩⟩
    subst hz
    exact functionField_isFractionRing_of_isAffineOpen Y U hU
  haveI : IsFractionRing Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X))) :=
    hfr_local _ hyU hη
  have hgerm (a : Γ(Y, U)) : f.stalkMap (genericPoint X) (Y.presheaf.germ U _ hyU a) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hyU (f.app U a) :=
    f.germ_stalkMap_apply U _ hyU a
  have hbij : Function.Bijective (f.stalkMap (genericPoint X)) :=
    ConcreteCategory.bijective_of_isIso _
  have hinj : Function.Injective (f.app U) := by
    intro a a' h'
    apply germ_injective_of_isIntegral Y _ hyU
    apply hbij.1
    rw [hgerm, hgerm, h']
  let φ : Γ(X, f ⁻¹ᵁ U) ⟶ Y.presheaf.stalk (f (genericPoint X)) :=
    X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hyU ≫ inv (f.stalkMap (genericPoint X))
  have hφ (c : Γ(X, f ⁻¹ᵁ U)) : f.stalkMap (genericPoint X) (φ c) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hyU c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Y.presheaf.stalk (f (genericPoint X)) :=
    { φ.hom with
      commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  have hψ : Function.Injective ψ := fun b b' e => by
    apply germ_injective_of_isIntegral X (genericPoint X) hyU
    rw [← hφ b, ← hφ b']
    exact congr(f.stalkMap (genericPoint X) $e)
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) := IsFractionRing.toField Γ(Y, U)
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨y, hxU⟩
  have := hU.isLocalization_stalk ⟨y, hxU⟩
  obtain ⟨r, hr, h⟩ := exists_mul_mem_range (O := Y.presheaf.stalk y)
    (hU.primeIdealOf ⟨y, hxU⟩).asIdeal.primeCompl ψ hψ
  refine ⟨Y.basicOpen r, (Y.mem_basicOpen r y hxU).2
    (IsLocalization.map_units (Y.presheaf.stalk y) ⟨r, hr⟩), ?_⟩
  rw [isIso_morphismRestrict_iff_isIso_app _ (hU.basicOpen r),
    hU.app_basicOpen_eq_away_map f (hU.preimage f) r]
  refine IsIso.comp_isIso' ?_ inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  have := hU.isLocalization_basicOpen r
  have := (hU.preimage f).isLocalization_basicOpen (f.app U r)
  constructor
  · exact (IsLocalization.Away.map_injective_iff _ _ _).2 fun a ha =>
      ⟨0, by rw [hinj (ha.trans (map_zero _).symm), mul_zero]⟩
  · refine (IsLocalization.Away.map_surjective_iff _ _ _ _).2 fun b => ?_
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, 1, by rw [pow_one]; exact ha⟩

theorem main : ∀ (U M : Scheme.{0}) [IsLocallyNoetherian M] (u : U ⟶ M) (W : M.Opens), IsFinite u → IsReduced U → IsIso (u ∣_ W) → Dense (W : Set M) → Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) → ∀ x : M, IsDomain (M.presheaf.stalk x) → IsIntegrallyClosed (M.presheaf.stalk x) → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V) := by
  intro U M _ u W _ _ hW hd hd' x _ _
  obtain ⟨V, hxV, hV⟩ := exists_isIntegral_nhds x
  let f := u ∣_ V
  let W' : V.toScheme.Opens := V.ι ⁻¹ᵁ W
  have : IsFinite f := MorphismProperty.of_isPullback (P := @IsFinite)
    (isPullback_morphismRestrict u V).flip ‹_›
  have hW' : IsIso (f ∣_ W') := by
    have h1 : IsIso (u ∣_ W ∣_ (W.ι ⁻¹ᵁ V)) := inferInstance
    have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u W (W.ι ⁻¹ᵁ V))).1 h1
    have e : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V.ι ''ᵁ W' := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, inf_comm]
    exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u V W')).2
      (((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictEq u e)).1 h2)
  have hne : Nonempty W' := by
    obtain ⟨z, hz, hz'⟩ := hd.inter_open_nonempty V V.isOpen ⟨x, hxV⟩
    exact ⟨⟨⟨z, hz⟩, hz'⟩⟩
  have : IsIntegral W' := isIntegral_of_isOpenImmersion W'.ι
  have : IsIntegral (f ⁻¹ᵁ W') := IsIntegral.of_isIso (inv (f ∣_ W'))
  have hd₂ : Dense ((f ⁻¹ᵁ W' : (u ⁻¹ᵁ V).toScheme.Opens) : Set (u ⁻¹ᵁ V).toScheme) := by
    have e : f ⁻¹ᵁ W' = (u ⁻¹ᵁ V).ι ⁻¹ᵁ u ⁻¹ᵁ W := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
    rw [e]
    exact hd'.preimage (u ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap
  have : IrreducibleSpace (u ⁻¹ᵁ V).toScheme := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hd₂.closure_eq]
    refine IsIrreducible.closure ?_
    exact isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace (f ⁻¹ᵁ W').toScheme))
  have : IsIntegral (u ⁻¹ᵁ V).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict f W' hne
  have : IsIntegrallyClosed (V.toScheme.presheaf.stalk (⟨x, hxV⟩ : V)) :=
    IsIntegrallyClosed.of_equiv (R := M.presheaf.stalk x)
      (V.stalkIso ⟨x, hxV⟩).symm.commRingCatIsoToRingEquiv
  obtain ⟨V', hx', hV'⟩ := exists_isIso_of_isIntegral f ⟨x, hxV⟩
  refine ⟨V.ι ''ᵁ V', ⟨⟨x, hxV⟩, hx', rfl⟩, ?_⟩
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict u V V')).1 hV'

end GlobalTheory.FiniteBirationalNear
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericFlatScheme

theorem affine (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : CommRingCat.{0})
    (s : Spec A ⟶ Sp R) [LocallyOfFiniteType s] :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Flat (pullback.snd s (spMap φ)) := by
  obtain ⟨g, rfl⟩ : ∃ g : CommRingCat.of R ⟶ A, Spec.map g = s :=
    ⟨Spec.preimage s, Spec.map_preimage s⟩
  have hg : g.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  let : Algebra R A := g.hom.toAlgebra
  have : Algebra.FiniteType R A := hg
  obtain ⟨a, ha, hfree⟩ := (GlobalTheory.generic_freeness R).2.1 A A
  refine ⟨a, ha, fun R' _ φ hφ => ?_⟩
  let : Algebra R R' := φ.toAlgebra

  let : Algebra (Localization.Away a) R' := (IsLocalization.Away.lift a hφ).toAlgebra
  have : IsScalarTower R (Localization.Away a) R' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq a hφ x).symm
  have := hfree
  have hbc : IsBaseChange (Localization.Away a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) A) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) (Localization.Away a) _).mp
      inferInstance
  have : Module.Free (Localization.Away a) (Localization.Away a ⊗[R] A) :=
    Module.Free.of_equiv hbc.equiv.symm
  have hflat : Module.Flat R' (R' ⊗[R] A) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away a) R' R' A).symm

  have hA : g = CommRingCat.ofHom (algebraMap R A) := rfl
  have hF : Flat (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A)))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  rw [hA]
  change Flat (pullback.snd _ (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
  rw [← pullbackSymmetry_hom_comp_fst, ← pullbackSpecIso_hom_fst' R R' A]
  infer_instance

end GenericFlatScheme

theorem generic_flatness_scheme :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R),
      LocallyOfFiniteType s → QuasiCompact s → ∃ f : R, f ≠ 0 ∧
        ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
          Flat (pullback.snd s (spMap φ)) := by
  intro R _ _ _ Z s hs hq
  have := hs
  have := hq
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  let 𝒰 := Z.affineCover.finiteSubcover
  have key : ∀ i, ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Flat (pullback.snd (𝒰.f i ≫ s) (spMap φ)) :=
    fun i => by
      have : LocallyOfFiniteType (𝒰.f i ≫ s) := MorphismProperty.comp_mem _ _ _
        (inferInstance : LocallyOfFiniteType (𝒰.f i)) hs
      exact @GenericFlatScheme.affine R _ _ _ _ (𝒰.f i ≫ s) this
  choose e he0 heF using key
  refine ⟨∏ i, e i, Finset.prod_ne_zero_iff.mpr fun i _ => he0 i, fun R' _ φ hφ => ?_⟩

  have hloc : IsZariskiLocalAtSource @AlgebraicGeometry.Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Flat)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat)
    (𝒰.pullback₁ (pullback.fst s (spMap φ)))).mpr fun i => ?_
  change Flat (pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ))
  have := heF i R' φ
    (isUnit_of_dvd_unit (map_dvd φ (Finset.dvd_prod_of_mem e (Finset.mem_univ _))) hφ)
  have h : pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ) =
      ((pullbackSymmetry _ _).hom ≫ (pullbackRightPullbackFstIso s (spMap φ) (𝒰.f i)).hom) ≫
        pullback.snd (𝒰.f i ≫ s) (spMap φ) := by
    rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc]
  rw [h]
  infer_instance

end GlobalTheory
end
