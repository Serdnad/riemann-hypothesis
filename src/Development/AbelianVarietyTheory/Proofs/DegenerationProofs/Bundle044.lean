module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueExtensionOfForallNormLeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace SemiAbTorsion

theorem finite_pow_eq_one_of_extension {T G B : Type*} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hi : Function.Injective i) (hk : ∀ x, q x = 1 → ∃ t, i t = x)
    (n : ℕ) (hT : Finite {t : T // t ^ n = 1}) (hB : Finite {b : B // b ^ n = 1}) :
    Finite {x : G // x ^ n = 1} := by
  let f : {x : G // x ^ n = 1} → {b : B // b ^ n = 1} :=
    fun x => ⟨q x.1, by rw [← map_pow, x.2, map_one]⟩
  refine Set.finite_univ_iff.mp (Set.Finite.of_finite_fibers f (Set.toFinite _) fun b hb => ?_)
  obtain ⟨x₀, -, rfl⟩ := hb
  rw [Set.univ_inter, ← Set.finite_coe_iff]
  have key : ∀ x : f ⁻¹' {f x₀}, ∃ t : {t : T // t ^ n = 1}, i t.1 = x.1.1 / x₀.1 := by
    intro x
    have hx : q x.1.1 = q x₀.1 := congrArg Subtype.val x.2
    obtain ⟨t, ht⟩ := hk (x.1.1 / x₀.1) (by rw [map_div, hx, div_self'])
    refine ⟨⟨t, hi ?_⟩, ht⟩
    rw [map_pow, ht, div_pow, x.1.2, x₀.2, map_one, div_one]
  choose g hg using key
  refine Finite.of_injective g fun x y h => Subtype.ext (Subtype.ext ?_)
  have := hg x
  rw [h, hg y] at this
  exact (div_left_inj.mp this).symm

theorem finite_chars_pow_eq_one (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (R : Type)
    [CommRing R] [IsDomain R] {n : ℕ} (hn : 1 ≤ n) :
    Finite {t : Multiplicative X →* Rˣ // t ^ n = 1} := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : AddGroup.FG X := Module.Finite.iff_addGroup_fg.mp inferInstance
  obtain ⟨S, hS, hfin⟩ := (Group.fg_iff.mp (inferInstance : Group.FG (Multiplicative X)))
  haveI : Finite S := hfin.to_subtype
  let g : {t : Multiplicative X →* Rˣ // t ^ n = 1} → (S → rootsOfUnity n R) := fun t s =>
    ⟨t.1 s.1, (mem_rootsOfUnity _ _).2 (by simpa using DFunLike.congr_fun t.2 s.1)⟩
  refine Finite.of_injective g fun a b h => Subtype.ext ?_
  refine MonoidHom.eq_of_eqOn_dense hS fun s hs => ?_
  exact congrArg Subtype.val (congrFun h ⟨s, hs⟩)

theorem finite_ringHom (A F : Type) [CommRing A] [CommRing F] [Finite F]
    [Algebra.FiniteType ℤ A] : Finite (A →+* F) := by
  obtain ⟨S, hS⟩ := (inferInstance : Algebra.FiniteType ℤ A).out
  refine Finite.of_injective (fun (φ : A →+* F) (s : S) => φ s.1) fun a b h => ?_
  have : a.toIntAlgHom = b.toIntAlgHom :=
    AlgHom.ext_of_adjoin_eq_top hS fun s hs => congrFun h ⟨s, hs⟩
  ext x
  exact DFunLike.congr_fun this x

theorem finite_hom_range_subset {X : Scheme.{0}} (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π]
    (F : CommRingCat.{0}) [Finite F] (V : X.Opens) (hV : IsAffineOpen V) :
    {f : Spec F ⟶ X | Set.range f ⊆ V}.Finite := by
  have h : LocallyOfFiniteType (hV.fromSpec ≫ π) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV.fromSpec ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have e : φ.hom = algebraMap ℤ Γ(X, V) := RingHom.ext_int _ _
  have h' : (algebraMap ℤ Γ(X, V)).FiniteType := e ▸ h
  have : Algebra.FiniteType ℤ Γ(X, V) := RingHom.finiteType_algebraMap.mp h'
  haveI := finite_ringHom Γ(X, V) F
  refine (Set.finite_range fun ψ : Γ(X, V) →+* F =>
    Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec).subset fun f hf => ?_
  have hf' : Set.range f ⊆ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hf
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec f hf')
  refine ⟨ψ.hom, ?_⟩
  change Spec.map ψ ≫ _ = _
  rw [hψ, IsOpenImmersion.lift_fac]

theorem finite_points_over {Z : Scheme.{0}} (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (G : Over Z)
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (F : Type) [Field F] [Finite F]
    (t : Sp F ⟶ Z) : Finite (Over.mk t ⟶ G) := by
  let pt : Sp F := default
  have hpt : ∀ y : Sp F, y = pt := fun y => Subsingleton.elim _ _
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (t pt)) isOpen_univ
  have hc : IsCompact (G.hom ⁻¹ᵁ U : Set G.left) :=
    QuasiCompact.isCompact_preimage (f := G.hom) _ U.isOpen hU.isCompact
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens).mp hc
  have hfin : (⋃ V ∈ s, {f : Sp F ⟶ G.left | Set.range f ⊆ V.1}).Finite :=
    hs.biUnion fun V _ => finite_hom_range_subset (G.hom ≫ π) (CommRingCat.of F) V.1 V.2
  haveI := hfin.to_subtype
  have hm : ∀ x : Over.mk t ⟶ G,
      x.left ∈ ⋃ V ∈ s, {f : Sp F ⟶ G.left | Set.range f ⊆ V.1} := by
    intro x
    have h1 : x.left pt ∈ G.hom ⁻¹ᵁ U := by
      change (x.left ≫ G.hom) pt ∈ U
      rw [Over.w x]
      exact hxU
    rw [hsU] at h1
    simp only [TopologicalSpace.Opens.mem_iSup] at h1
    obtain ⟨V, hV, hx⟩ := h1
    refine Set.mem_biUnion hV ?_
    rintro _ ⟨y, rfl⟩
    rw [hpt y]
    exact hx
  exact Finite.of_injective (fun x => (⟨x.left, hm x⟩ : (⋃ V ∈ s,
    {f : Sp F ⟶ G.left | Set.range f ⊆ V.1} : Set _)))
    fun a b h => Over.OverMorphism.ext (congrArg Subtype.val h)

theorem comp_pow_points {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (g : T ⟶ A)
    (n : ℕ) : f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

end SemiAbTorsion

open SemiAbTorsion

theorem semiAbelian_torsion_finite_and_closedPoint_finiteOrder : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → (∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension G) → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ G // x ^ n = 1}) ∧ (∀ (Z : Scheme.{0}) (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (G : Over Z) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (w : G.left), IsClosed ({w} : Set G.left) → ∃ n : ℕ, 1 ≤ n ∧ ∀ (K : Type) [Field K] (t : Sp K ⟶ Z) (x : Over.mk t ⟶ G), Set.range x.left = {w} → x ^ n = 1) := by
  intro hB
  refine ⟨?_, ?_⟩
  · rintro K _ _ G _ _ ⟨E⟩ n hn
    letI := E.addCommGroup
    letI := E.finite
    letI := E.grpB
    haveI := E.q_hom
    haveI := E.i_hom
    have hk := E.isKernel
    refine finite_pow_eq_one_of_extension (IsMonHom.monoidHom E.i (𝟙_ (Over (Sp K))))
      (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp K)))) ?_ ?_ n ?_ (hB K E.B E.isAbelian n hn)
    · intro a b h
      exact hk.hom_ext h (toUnit_unique _ _)
    · intro x hx
      have hx' : x ≫ E.q = 1 := hx
      exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
    · haveI : IsDomain Γ((𝟙_ (Over (Sp K))).left, ⊤) :=
        inferInstanceAs (IsDomain Γ(Sp K, ⊤))
      haveI := finite_chars_pow_eq_one E.X Γ((𝟙_ (Over (Sp K))).left, ⊤) hn
      let e := splitTorusPointsEquiv (Sp K) E.X (𝟙_ (Over (Sp K)))
      refine Finite.of_injective (fun t => (⟨e t.1, by rw [← map_pow, t.2, map_one]⟩ :
        {t : Multiplicative E.X →* Γ((𝟙_ (Over (Sp K))).left, ⊤)ˣ // t ^ n = 1})) ?_
      intro a b h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
  · intro Z π _ G _ _ _ w hw
    haveI : Finite (G.left.residueField w) :=
      (jacobson_closedPoints_tools_int G.left (G.hom ≫ π)).2.1 w hw
    let t₀ : Sp (G.left.residueField w) ⟶ Z := G.left.fromSpecResidueField w ≫ G.hom
    haveI := finite_points_over π G (G.left.residueField w) t₀
    let x₀ : Over.mk t₀ ⟶ G := Over.homMk (G.left.fromSpecResidueField w) rfl
    refine ⟨Nat.card (Over.mk t₀ ⟶ G), Nat.card_pos, fun K _ t x hx => ?_⟩
    obtain ⟨⟨z, φ⟩, hz⟩ := (Scheme.SpecToEquivOfField K G.left).symm.surjective x.left
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hz
    obtain rfl : z = w := by
      have : x.left (default : Sp K) ∈ ({w} : Set G.left) := hx ▸ Set.mem_range_self _
      rw [← hz] at this
      have h2 : (Spec.map φ ≫ G.left.fromSpecResidueField z) (default : Sp K) ∈
          Set.range (G.left.fromSpecResidueField z) := ⟨_, rfl⟩
      rw [Scheme.range_fromSpecResidueField] at h2
      exact h2.symm.trans this
    let u : Over.mk t ⟶ Over.mk t₀ := Over.homMk (Spec.map φ) (by
      change Spec.map φ ≫ G.left.fromSpecResidueField z ≫ G.hom = t
      rw [← Category.assoc, hz]
      exact Over.w x)
    have hu : x = u ≫ x₀ := Over.OverMorphism.ext hz.symm
    rw [hu, ← comp_pow_points, pow_card_eq_one', MonObj.comp_one]

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

namespace BoundedRegular

theorem valF_spMap_comp_eq {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}}
    (t : Sp F ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) (φ : Γ(X, U)) :
    valF (spMap f ≫ t) U φ =
      f ((Scheme.ΓSpecIso (CommRingCat.of F)).hom (t.appLE U ⊤ ht φ)) := by
  have h' : ⊤ ≤ (spMap f ≫ t) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap f q))
  rw [valF, dite_eq_left h']
  have e : (spMap f ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of F')).hom =
      t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom f := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap f) t U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  exact congrArg (fun g => g.hom φ) e

theorem valF_mul_valF_eq_one {F : Type} [Field F] {X : Scheme.{0}} (t : Sp F ⟶ X) (U : X.Opens)
    (ht : Set.range t ⊆ U) {φ φ' : Γ(X, U)} (h : φ * φ' = 1) :
    valF t U φ * valF t U φ' = 1 := by
  have h' : ⊤ ≤ t ⁻¹ᵁ U := fun q _ => ht ⟨q, rfl⟩
  rw [valF, valF, dite_eq_left h', dite_eq_left h', ← map_mul, ← map_mul, h, map_one, map_one]

theorem exists_point_norm_valF_eq {X : Scheme.{0}} {p : ℕ} [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ X) (U : X.Opens)
    (hy : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y) ⁻¹ᵁ U)
    (φ : Γ(X, U)) :
    ∃ y' : Sp (OO p) ⟶ X, y' (cPt p) = y (by
      haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
      haveI : IsLocalRing (integralClosure ℤ_[p] K) :=
        (integralClosureToPadicAlgClIntegers K).domain_isLocalRing
      exact IsLocalRing.closedPoint (integralClosure ℤ_[p] K)) ∧
      Set.range (gPt p ≫ y') ⊆ U ∧
      valF (gPt p ≫ y') U φ = (((Scheme.ΓSpecIso (.of K)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y).appLE
          U ⊤ hy φ) : K) : PadicAlgCl p) := by
  haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
  haveI : IsLocalRing (integralClosure ℤ_[p] K) :=
    (integralClosureToPadicAlgClIntegers K).domain_isLocalRing
  have e : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) ≫ y =
      spMap K.val.toRingHom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y := by
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  refine ⟨spMap (integralClosureToPadicAlgClIntegers K) ≫ y, ?_, ?_, ?_⟩
  · refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg y ?_)
    exact IsLocalRing.comap_closedPoint (integralClosureToPadicAlgClIntegers K)
  · rw [e]
    rintro _ ⟨q, rfl⟩
    exact hy (Set.mem_univ (spMap K.val.toRingHom q))
  · rw [e, valF_spMap_comp_eq _ _ U hy]
    rfl

theorem existsUnique_resG_eq {X : Scheme.{0}} [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π]
    [LocallyOfFiniteType π] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) {U W : X.Opens}
    (h : U ≤ W) (φ : Γ(X, U)) (hU : (U : Set X).Nonempty)
    (H : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) ∈ W →
      Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ ≤ 1) :
    ∃! ψ : Γ(X, W), resG X h ψ = φ := by
  haveI : Nonempty U := hU.to_subtype
  haveI : Nonempty W := (hU.mono h).to_subtype
  obtain ⟨ψ, hψ⟩ := exists_germToFunctionField_eq_of_frequently_norm_le_one π U W
    (fun x _ _ _ => (hX x).2) (φ := φ) fun p _ K hK => ⟨K, hK, le_rfl, fun y hy hW _ _ => by
      obtain ⟨y', h1, h2, h3⟩ := exists_point_norm_valF_eq K y U hy φ
      rw [← h3]
      exact H p y' (h1 ▸ hW) h2⟩
  have e : resG X h ψ = φ :=
    X.germToFunctionField_injective U ((X.presheaf.germ_res_apply (homOfLE h) _ _ ψ).trans hψ)
  exact ⟨ψ, e, fun ψ' h' => map_injective_of_isIntegral X (homOfLE h) (h'.trans e.symm)⟩

end BoundedRegular


open BoundedRegular in
theorem regular_of_bounded_at_padicAlgCl_points :
    (∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (x : X),
      IsClosed ({x} : Set X) → IsIntegrallyClosed (X.presheaf.stalk x) →
      ∀ (U : X.Opens) (φ : Γ(X, U)), (U : Set X).Nonempty →
      (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x →
        Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ ≤ 1) →
      ∃ (W : X.Opens) (ψ : Γ(X, W)), x ∈ W ∧
        resG X (inf_le_left : W ⊓ U ≤ W) ψ = resG X (inf_le_right : W ⊓ U ≤ U) φ) ∧
    (∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (U W : X.Opens) (h : U ≤ W) (φ : Γ(X, U)),
      (U : Set X).Nonempty →
      ((∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) ∈ W →
        Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ ≤ 1) →
          ∃! ψ : Γ(X, W), resG X h ψ = φ) ∧
      (IsUnit φ → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) ∈ W →
        Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ = 1) →
          ∃ ψ : Γ(X, W), IsUnit ψ ∧ resG X h ψ = φ)) := by
  refine ⟨fun X _ π _ _ x hx hn U φ hU H => ?_, fun X _ π _ _ hX U W h φ hU =>
    ⟨existsUnique_resG_eq π hX h φ hU, fun hφ H => ?_⟩⟩
  · haveI : Nonempty U := hU.to_subtype
    obtain ⟨p, hp, hpx⟩ := exists_prime_residueField_eq_zero π hx
    haveI : Fact p.Prime := ⟨hp⟩
    have hm := mem_range_stalk_of_forall_norm_le_one π hx hpx (φ := φ) fun K _ y hy hyx => by
      obtain ⟨y', h1, h2, h3⟩ := exists_point_norm_valF_eq K y U hy φ
      rw [← h3]
      exact H p y' (h1.trans hyx) h2
    obtain ⟨V, hV, s, hxV, -, hs⟩ :=
      exists_germToFunctionField_eq_of_mem_range_stalk hm (W := ⊤) trivial
    have hg : ∀ (W : X.Opens) [Nonempty W], genericPoint X ∈ W := fun W h =>
      ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using h)
    haveI : Nonempty (V ⊓ U : X.Opens) := ⟨⟨_, hg V, hg U⟩⟩
    refine ⟨V, s, hxV, X.germToFunctionField_injective (V ⊓ U) ?_⟩
    exact (X.presheaf.germ_res_apply (homOfLE inf_le_left) _ _ s).trans
      (hs.trans (X.presheaf.germ_res_apply (homOfLE inf_le_right) _ _ φ).symm)
  · haveI : Nonempty U := hU.to_subtype
    obtain ⟨φ', hφ'⟩ := hφ.exists_right_inv
    obtain ⟨ψ, hψ, -⟩ := existsUnique_resG_eq π hX h φ hU fun p _ y h1 h2 => (H p y h1 h2).le
    obtain ⟨ψ', hψ', -⟩ := existsUnique_resG_eq π hX h φ' hU fun p _ y h1 h2 => by
      have e := congrArg norm (valF_mul_valF_eq_one _ U h2 hφ')
      rw [norm_mul, H p y h1 h2, _root_.one_mul, norm_one] at e
      exact e.le
    refine ⟨ψ, IsUnit.of_mul_eq_one ψ' (map_injective_of_isIntegral X (homOfLE h) ?_), hψ⟩
    change resG X h (ψ * ψ') = resG X h 1
    rw [map_mul, hψ, hψ', hφ', map_one]

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

def HasWt {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G)
    (U : G.left.Opens) (f : Γ(G.left, U)) (α : X) : Prop :=
  ∀ (Z : Over S) (τ : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ U →
    gs ((τ ≫ i) * g).left z U f = (gm τ.left z ⊤ (charUnit S X α)).val * gs g.left z U f

def GenWt {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G)
    {Y : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (G.left ⟶ Y)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (α : X) : Prop :=
  ∀ (Z : Over S) (τ : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J : (Z.left ⟶ Y) → L.ι), Good L z J →
    val t ((τ ≫ i) * g).left z J = gm τ.left z ⊤ (charUnit S X α) * val t g.left z J

def Red {k : Type} [Field k] (Φ : FibPre k) {Y : Scheme.{0}} {L : LB Y} {π : Φ.E.B.left ⟶ Y} {N : ℕ}
    (c : ChartPull Φ.N₀ (npw L N) π) {K K' : Type} [Fintype K] [Fintype K'] {ψ : K → (Φ.E.B.left ⟶ Y)} {ε : K → ℤ}
    {φt : K' → (Φ.G.left ⟶ Y)} {εt : K' → ℤ} (t : LB.Gen (LB.LinComb L φt εt)) (b : LB.Sec (LB.LinComb L ψ ε))
    (φ : (Φ.H 1).Sec) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) (J : (Z ⟶ Y) → L.ι), Good L z J → ∀ l : Φ.N₀.ι,
    r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J (r ≫ Φ.D.q.left ≫ π) = c.idx l →
    gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) (φ.f l) = sval b (r ≫ Φ.D.q.left) z J * (val t r z J).val

end GlobalTheory.ZH.UFib
end
end
