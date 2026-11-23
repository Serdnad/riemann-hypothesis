module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FiniteEndFlat

theorem strictMono_of_locallyQuasiFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    StrictMono (f : X → Y) := by
  intro x y hxy
  have h : y ⤳ x := hxy.le
  refine lt_of_le_not_ge (show f y ⤳ f x from h.map f.continuous) fun h' => hxy.not_ge ?_
  have e : f y = f x := ((h.map f.continuous).antisymm h').eq
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have h2 : (⟨y, e⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := (subtype_specializes_iff _ _).mpr h
  have : y = x := congrArg Subtype.val h2.eq
  exact this.le

theorem apply_genericPoint {X : Scheme.{0}} [IrreducibleSpace X] [IsLocallyNoetherian X]
    (f : X ⟶ X) [LocallyQuasiFinite f] {o : X} (ho : f o = o) :
    f (genericPoint X) = genericPoint X := by
  have hs := strictMono_of_locallyQuasiFinite f
  let g : Set.Ici o → Set.Ici o := fun x =>
    ⟨f x, ho.ge.trans (show f x ⤳ f o from Specializes.map (show x.1 ⤳ o from x.2) f.continuous)⟩
  have hg : StrictMono g := fun x y h => hs h
  let ξ : Set.Ici o := ⟨genericPoint X, genericPoint_specializes o⟩
  have hfin : Order.height (g ξ) < ⊤ := by
    have h1 := Order.height_le_krullDim (g ξ)
    rw [← Order.coheight_eq_krullDim_Ici, ← ringKrullDim_stalk_eq_coheight] at h1
    have h2 := h1.trans_lt ringKrullDim_lt_top
    exact WithBot.coe_lt_coe.mp h2
  have hle : g ξ ≤ ξ := genericPoint_specializes (f (genericPoint X))
  have hge : ξ ≤ g ξ := by
    by_contra h
    exact (Order.height_strictMono (lt_of_le_not_ge hle h) hfin).not_ge
      (Order.height_le_height_apply_of_strictMono g hg ξ)
  exact (Specializes.antisymm (show f (genericPoint X) ⤳ genericPoint X from hge)
    (genericPoint_specializes _)).eq

theorem exists_flat_away {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A]
    (φ : A →+* B) (hφ : φ.Finite) :
    ∃ r : A, r ≠ 0 ∧ ∀ (C : Type) [CommRing C] [Algebra B C] [IsLocalization.Away (φ r) C],
      ((algebraMap B C).comp φ).Flat := by
  algebraize [φ]
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) B) (FractionRing A)
  refine ⟨r, nonZeroDivisors.ne_zero hr, fun C _ _ _ => ?_⟩
  letI : Algebra A C := ((algebraMap B C).comp φ).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers r)) C := by
    rw [Algebra.algebraMapSubmonoid_powers]; assumption
  have h1 : Module.Flat A (LocalizedModule (Submonoid.powers r) B) :=
    Module.Flat.trans A (Localization (Submonoid.powers r)) _
  exact Module.Flat.of_linearEquiv
    (IsLocalizedModule.iso (Submonoid.powers r) (IsScalarTower.toAlgHom A B C).toLinearMap).symm


open UnramifiedEndFlat in
theorem exists_open_flat {X Y : Scheme.{0}} [IrreducibleSpace X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (hf : f (genericPoint X) = genericPoint Y) :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ ∀ x ∈ W, (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨r, hr, H⟩ := exists_flat_away (f.app U).hom (f.finite_app U hU)
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  refine ⟨X.basicOpen (f.app U r), ⟨genericPoint X, ?_⟩, fun x hx => ?_⟩
  · rw [← Scheme.preimage_basicOpen, SetLike.mem_coe, Scheme.Hom.mem_preimage, hf]
    refine ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen r).2).mpr ?_
    rw [Set.univ_inter]
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp (by simpa using hr)
  · have := hV.isLocalization_basicOpen (f.app U r)
    have h1 := H Γ(X, X.basicOpen (f.app U r))
    have hxU : x ∈ f ⁻¹ᵁ U := X.basicOpen_le _ hx
    have h2 : (X.presheaf.germ _ x hx).hom.Flat := by
      rw [← Category.comp_id (X.presheaf.germ _ x hx), ← flat_iff_comp_germ (hV.basicOpen _)]
      exact RingHom.Flat.id _
    rw [flat_iff_comp_germ hU (x := f x) hxU, f.germ_stalkMap U x hxU,
      ← X.presheaf.germ_res (homOfLE (X.basicOpen_le (f.app U r))) x hx]
    exact h1.comp h2

end FiniteEndFlat


open UnramifiedEndFlat FiniteEndFlat in
theorem flat_and_surjective_of_isFinite_grpEnd (K : Type) [Field K] [IsAlgClosed K]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsIntegral G.left]
    [LocallyOfFiniteType G.hom] (φ : G ⟶ G) [IsMonHom φ] [IsFinite φ.left] :
    Flat φ.left ∧ Surjective φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  let o : G.left := η[G].left (IsLocalRing.closedPoint K)
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint K))
  have hξ := apply_genericPoint φ.left hfo
  refine ⟨?_, ⟨fun y => ?_⟩⟩
  · obtain ⟨W, hW, H⟩ := exists_open_flat φ.left hξ
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
    refine flat_of_closedPoints _ fun x hx => ?_
    let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
    let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
    let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
    let β := GrpObj.mulRight (A := G) ((y'⁻¹ * x') ≫ φ)
    have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
      simp only [α, β]
      generalize y'⁻¹ * x' = z
      simp [comp_lift_assoc]
    have hα : y' ≫ α.hom = x' := by
      have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
        simp [α, comp_lift_assoc, Hom.mul_def]
      rw [this, mul_inv_cancel_left]
    have hα' : α.hom.left y = x := by
      have h := congr(($hα).left (IsLocalRing.closedPoint K))
      rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
        ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
      exact h
    have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
    have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
    have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
      rw [Scheme.Hom.stalkMap_comp]
      exact (Flat.stalkMap β.hom.left _).comp (H y hy)
    rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
    rw [← hα']
    exact (RingHom.Flat.respectsIso.cancel_right_isIso
      (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1
  · exact (genericPoint_specializes y).mem_closed φ.left.isClosedMap.isClosed_range ⟨_, hξ⟩

theorem flat_and_surjective_of_isFinite_abelianEnd :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S),
      Smooth f → GeometricallyConnected f → GeometricallyIntegral f) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A],
      IsAbelianScheme A → ∀ f : A ⟶ A, IsMonHom f → IsFinite f.left →
        Flat f.left ∧ Surjective f.left := by
  intro h K _ _ A _ hA f _ _
  have := hA.smooth
  have := h _ _ A.hom hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact flat_and_surjective_of_isFinite_grpEnd K A f

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension {K B : Type} [Field K]
    [CommRing B] [IsDomain B] [Algebra K B] {g : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B)) :
    Algebra.trdeg K B = g := by
  obtain ⟨s, hs, hP⟩ := h
  obtain ⟨t, hts, ht⟩ : ∃ t ∈ s, t ≠ 0 := by
    by_contra! hz
    have hbot : Ideal.span s = ⊥ := Ideal.span_eq_bot.mpr hz
    exact top_ne_bot (hs.symm.trans hbot)
  have hPt := hP t hts
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hPt
  have hle : Submonoid.powers t ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ht
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
  have : Algebra.IsStandardSmooth K (Localization.Away t) := hPt.isStandardSmooth
  have hdim : ringKrullDim (Localization.Away t) = g :=
    AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := K)
  obtain ⟨d, hd1, hd2⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (Localization.Away t)
  have hdg : d = g := by
    rw [hdim] at hd1
    exact_mod_cast hd1.symm
  have : FaithfulSMul B (Localization.Away t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic B (Localization.Away t) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers t)
  have : FaithfulSMul K B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K B).injective
  rw [← trdeg_eq_of_isAlgebraic_top K B (Localization.Away t), hd2, hdg]

theorem trdeg_eq_of_smoothOfRelativeDimension :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X), IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g := by
  intro K _ X _ f g hf B _ _ _ j hj hjf
  have : IsIntegral (Spec (CommRingCat.of B)) := isIntegral_of_isOpenImmersion j
  have : IsDomain B := (affine_isIntegral_iff (CommRingCat.of B)).mp this
  have h0 : SmoothOfRelativeDimension (0 + g) (j ≫ f) := inferInstance
  rw [Nat.zero_add, hjf] at h0
  have hloc := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).mp h0
  exact trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension hloc

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.linearIndependent_of_comm_smul {K G V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] (A : G → V →ₗ[K] V) (c : G → G → K) (hA : ∀ x, Function.Injective (A x))
    (h : ∀ x y v, A x (A y v) = c x y • A y (A x v)) (hc : Function.Injective c) :
    LinearIndependent K A := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro g hg i hi
  by_contra hgi

  have htwist : ∀ y, ∑ x ∈ s, (g x * (c x y - c i y)) • A x = 0 := by
    intro y
    ext v
    have h0 := LinearMap.congr_fun hg v
    have h1 := LinearMap.congr_fun hg (A y v)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply] at h0 h1 ⊢
    have h2 : A y (∑ x ∈ s, (g x * c x y) • A x v) = 0 := by

      rw [map_sum, ← h1]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, h x y v, smul_smul]
    have h3 : ∑ x ∈ s, (g x * c x y) • A x v = 0 :=
      hA y (by rw [h2, map_zero])
    simp_rw [mul_sub, sub_smul, Finset.sum_sub_distrib, h3, zero_sub, neg_eq_zero]
    have h4 : ∑ x ∈ s, (g x * c i y) • A x v = c i y • ∑ x ∈ s, g x • A x v := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [smul_smul, mul_comm]
    rw [h4, h0, smul_zero]
  have hothers : ∀ x ∈ s, x ≠ i → g x = 0 := by
    intro x hx hxi
    by_contra hgx
    apply hxi
    apply hc
    funext y
    have hrel : ∑ z ∈ s.erase i, (g z * (c z y - c i y)) • A z = 0 := by
      rw [← htwist y, ← Finset.sum_erase_add s _ hi, sub_self, mul_zero, zero_smul, add_zero]
    have := ih (s.erase i) (Finset.erase_ssubset hi) _ hrel x (Finset.mem_erase.2 ⟨hxi, hx⟩)
    rcases mul_eq_zero.1 this with h5 | h5
    · exact absurd h5 hgx
    · exact sub_eq_zero.1 h5
  have hsingle : g i • A i = 0 := by
    rw [← hg, Finset.sum_eq_single_of_mem i hi]
    intro x hx hxi
    rw [hothers x hx hxi, zero_smul]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  apply hA i
  have := LinearMap.congr_fun hsingle v
  simp only [LinearMap.smul_apply, LinearMap.zero_apply] at this
  rw [map_zero]
  exact (smul_eq_zero.1 this).resolve_left hgi


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.heisenberg_family_irreducible : ∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro K G V _ _ _ _ _ _ U e hU he hcard W hW
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Or.inl (Submodule.eq_bot_of_subsingleton)
  haveI : Fintype G := Fintype.ofFinite G
  have hind : LinearIndependent K (fun x => (U x : V →ₗ[K] V)) := by
    refine _root_.GlobalTheory.linearIndependent_of_comm_smul (fun x => (U x : V →ₗ[K] V))
      (fun x y => (e x y : K)) (fun x => (U x).injective) (fun x y v => hU x y v) ?_
    intro x x' hxx'
    apply he
    ext y
    exact congr_fun hxx' y
  have hdim : Module.finrank K (V →ₗ[K] V) = Module.finrank K V ^ 2 := by
    rw [Module.finrank_linearMap, sq]
  have hle := hind.fintype_card_le_finrank
  rw [hdim] at hle
  rw [Nat.card_eq_fintype_card] at hcard
  have hspan := hind.span_eq_top_of_card_eq_finrank (le_antisymm hle hcard |>.trans hdim.symm)

  let S : Submodule K (V →ₗ[K] V) :=
    { carrier := {f | ∀ w ∈ W, f w ∈ W}
      add_mem' := fun hf hg w hw => W.add_mem (hf w hw) (hg w hw)
      zero_mem' := fun w _ => by simp
      smul_mem' := fun a f hf w hw => W.smul_mem a (hf w hw) }
  have hS : ∀ f : V →ₗ[K] V, ∀ w ∈ W, f w ∈ W := by
    intro f
    have : f ∈ Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) := by
      rw [hspan]; exact Submodule.mem_top
    have hsub : Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩ w hw
      exact hW x w hw
    exact hsub this
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hcon)
  rw [eq_top_iff]
  intro v _
  have := hS ((φ w)⁻¹ • φ.smulRight v) w hwW
  simpa [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ] using this

end GlobalTheory
end
