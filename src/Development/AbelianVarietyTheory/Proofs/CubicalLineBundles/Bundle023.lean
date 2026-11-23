module

public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
import Mathlib.Algebra.Ring.BooleanRing
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
import Mathlib.RingTheory.Henselian
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.SummableAndAbsTsumSubIntegralLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TensorDet

section Algebra

noncomputable def rightAction (k O O' M : Type) [CommRing k] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O O']
    [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M] : O' →+* Module.End k (k ⊗[O] M) :=
  (Module.End.baseChangeHom O k M).toRingHom.comp (Algebra.lsmul O O M : O' →ₐ[O] Module.End O M).toRingHom

variable {k O O' M : Type} [CommRing k] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O O']
    [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]

theorem rightAction_apply (a : O') :
    rightAction k O O' M a = LinearMap.baseChange k (Algebra.lsmul O O M a : M →ₗ[O] M) := rfl

theorem rightAction_tmul (a : O') (c : k) (m : M) : rightAction k O O' M a (c ⊗ₜ m) = c ⊗ₜ (a • m) := rfl

theorem nonempty_eigenSub_equiv [Algebra O' k] [IsScalarTower O O' k] {I : Type} {σ : I → O' →+* k}
    (h : EigenSplit.IsSplitting σ) (i : I) (hi : σ i = algebraMap O' k) :
    Nonempty (EigenSplit.eigenSub (rightAction k O O' M) (σ i) ≃ₗ[k] k ⊗[O'] M) := by
  classical
  let ρ := rightAction k O O' M
  let π : k ⊗[O] M →ₗ[k] k ⊗[O'] M := ((TensorProduct.mk O' k M 1).restrictScalars O).liftBaseChange k
  have hπ : ∀ m, π (1 ⊗ₜ m) = 1 ⊗ₜ m := fun m => by simp [π]
  let ρ' : O' →+* Module.End k (k ⊗[O'] M) := (algebraMap k _).comp (σ i)
  have he : EigenSplit.IsEquivariant ρ ρ' π := fun a x => by
    have : π ∘ₗ ρ a = ρ' a ∘ₗ π := by
      ext m
      simp only [TensorProduct.AlgebraTensorModule.curry_apply,
        TensorProduct.curry_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, ρ, rightAction_tmul, hπ]
      simp [ρ', hi]
    exact congr($this x)
  let g : M →ₗ[O'] k ⊗[O] M :=
    { toFun := fun m => EigenSplit.proj h ρ i (1 ⊗ₜ m)
      map_add' := fun m n => by rw [TensorProduct.tmul_add, map_add (f := _)]
      map_smul' := fun a m => by
        rw [← rightAction_tmul, ← (EigenSplit.isEquivariant_action ρ a).proj h,
          EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem h ρ i _), hi, algebraMap_smul]
        rfl }
  let s : k ⊗[O'] M →ₗ[k] k ⊗[O] M := g.liftBaseChange k
  have h1 : s ∘ₗ π = EigenSplit.proj h ρ i := by
    ext m
    simp [hπ, s, g]
  have h2 : ∀ x, π (EigenSplit.proj h ρ i x) = π x := fun x => by
    rw [he.proj h]
    exact EigenSplit.proj_of_mem h (EigenSplit.mem_eigenSub.2 fun a => rfl)
  have h3 : π ∘ₗ s = LinearMap.id := by
    ext m
    simp [s, g, h2, hπ]
  refine ⟨LinearEquiv.ofBijective (π ∘ₗ Submodule.subtype _) ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_,
    fun y => ⟨EigenSplit.projTo h ρ i (s y), (h2 _).trans congr($h3 y)⟩⟩⟩
  refine Subtype.ext ((EigenSplit.proj_of_mem h x.2).symm.trans ?_)
  rw [← h1]
  exact (congrArg s hx).trans (map_zero s)

end Algebra

theorem injective_of_charZero {E k : Type} [Field E] [NumberField E] [Field k] [CharZero k] (τ : 𝓞 E →+* k) :
    Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot, ← Ideal.absNorm_eq_zero_iff]
  simpa using RingHom.mem_ker.1 (Ideal.absNorm_mem (RingHom.ker τ))

theorem finrank_eigenSub {E k O M : Type} [Field E] [NumberField E] [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing O] [Algebra O k] [Algebra O (𝓞 E)] [AddCommGroup M] [Module O M] [Module (𝓞 E) M]
    [IsScalarTower O (𝓞 E) M] (τ : 𝓞 E →+* k) (hτ : τ.comp (algebraMap O (𝓞 E)) = algebraMap O k) :
    Module.finrank k (EigenSplit.eigenSub (rightAction k O (𝓞 E) M) τ) = Module.finrank (𝓞 E) M := by
  have hs : EigenSplit.IsSplitting fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E) := by
    classical
    obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E k)
    exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  have hi := injective_of_charZero τ
  let _ := τ.toAlgebra
  have : IsScalarTower O (𝓞 E) k := IsScalarTower.of_algebraMap_eq' hτ.symm
  have : FaithfulSMul (𝓞 E) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have e : (IsFractionRing.lift hi : E →+* k).comp (algebraMap (𝓞 E) E) = τ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hi a
  obtain ⟨f⟩ := nonempty_eigenSub_equiv (O := O) (M := M) hs (IsFractionRing.lift hi) e
  rw [← (TensorProduct.isBaseChange (𝓞 E) M k).finrank_eq, ← f.finrank_eq, e]

theorem lieMult_of_param {k O V : Type} [Field k] [CommRing O] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {A : Over (Sp k)} [GrpObj A] (act : OAct O A) (ρ : O →+* Module.End k V) (Φ : V → (epsR k ⟶ A))
    (inj : Function.Injective Φ) (tan : ∀ x, IsTangent x ↔ x ∈ Set.range Φ) (add : ∀ y z, Φ (y + z) = Φ y * Φ z)
    (smul : ∀ (c : k) y, IsLieComb ![c] ![Φ y] (Φ (c • y))) (eqv : ∀ a y, Φ (ρ a y) = Φ y ≫ act.act a)
    (τ : O →+* k) {n : ℕ} (hn : Module.finrank k (EigenSplit.eigenSub ρ τ) = n) :
    LieMult act (𝟙 (Sp k)) τ n := by
  have sm : ∀ (c : k) y x, x.left = spMap (epsScaleR c) ≫ (Φ y).left ↔ x = Φ (c • y) := fun c y x => by
    rw [← (LieMultiple.isLieComb_one_iff _ _ _).1 (smul c y)]
    exact ⟨fun h => Over.OverMorphism.ext h, fun h => by rw [h]⟩
  let F : Multiplicative V →* (epsR k ⟶ A) := MonoidHom.mk' (fun y => Φ y.toAdd) (fun y z => add _ _)
  have pr : ∀ (n : ℕ) (y : Fin n → V), (List.ofFn fun i => Φ (y i)).prod = Φ (∑ i, y i) := fun n y => by
    have := map_list_prod F (List.ofFn fun i => Multiplicative.ofAdd (y i))
    rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum] at this
    exact this.symm
  let B := Module.finBasisOfFinrankEq k _ hn
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ A) ≃* (epsR k ⟶ A) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl A)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ A).left = η[A].left := Category.id_comp _
  have mem : ∀ y, y ∈ EigenSplit.eigenSub ρ τ ↔
      ∀ a, (Φ y ≫ act.act a).left = spMap (epsScaleR (τ a)) ≫ (Φ y).left := fun y => by
    rw [EigenSplit.mem_eigenSub]
    exact forall_congr' fun a => by rw [sm, ← eqv, inj.eq_iff]
  refine LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ)
    (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (P := fun w => IsTangent w ∧ ∀ a, (w ≫ act.act a).left = spMap (epsScaleR (τ a)) ≫ w.left)
    (fun w => and_congr (by rw [IsTangent, he', one]) (forall_congr' fun a => by
      rw [Over.comp_left, Over.comp_left, he']
      rfl))
    (fun c u v => by rw [he', he']; rfl) n
    ⟨fun i => Φ (B i), fun i => ⟨(tan _).2 ⟨_, rfl⟩, (mem _).1 (B i).2⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  obtain ⟨y, rfl⟩ := (tan w).1 hw
  let y' : EigenSplit.eigenSub ρ τ := ⟨y, (mem y).2 hw'⟩
  refine (existsUnique_congr fun d => ?_).1 (existsUnique_eq' (a' := B.equivFun y'))
  have e₁ : B.equivFun y' = d ↔ y = ∑ i, d i • (B i : V) := by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [y']
  rw [e₁, ← inj.eq_iff, ← pr]
  constructor
  · exact fun h => ⟨_, fun i => (sm _ _ _).2 rfl, h⟩
  · rintro ⟨u, hu, h⟩
    rw [h, show u = fun i => Φ (d i • (B i : V)) from funext fun i => (sm _ _ _).1 (hu i)]

end GlobalTheory.TensorDet
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TensorFinite

variable {S : Scheme.{0}}



set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.TensorFinite.isFinite_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y') (hf : IsFinite f.left)
    (hg : IsFinite g.left) : IsFinite (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @IsFinite) hf hg (Over.w f).symm (Over.w g).symm

end GlobalTheory.TensorFinite
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isIso_toUnit_splitTorus_punit (S : Scheme.{0}) : IsIso (toUnit (splitTorus S PUnit)) := by
  have h : 𝟙 (splitTorus S PUnit) = 1 := by
    rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
    congr 1
  exact ⟨η, h.symm, toUnit_unique _ _⟩

theorem isAbelianScheme_pullback_obj {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) := by
  have := h.comm
  have := h.smooth
  have := h.proper
  have := h.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · change Smooth (pullback.snd A.hom f)
    infer_instance
  · change IsProper (pullback.snd A.hom f)
    infer_instance
  · change GeometricallyConnected (pullback.snd A.hom f)
    infer_instance

noncomputable def torusExtensionOfAbelian {K : Type} [Field K] (A : Over (Spec (.of K))) [GrpObj A]
    (h : IsAbelianScheme A) : TorusExtension A where
  X := PUnit
  B := A
  isAbelian := h
  q := 𝟙 A
  q_hom := inferInstance
  q_flat := by rw [Over.id_left]; infer_instance
  q_surjective := by rw [Over.id_left]; infer_instance
  q_quasiCompact := by rw [Over.id_left]; infer_instance
  i := toUnit _ ≫ η
  i_hom := by have := h.comm; infer_instance
  isKernel := by
    have := isIso_toUnit_splitTorus_punit (Spec (.of K))
    exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩

theorem isSemiAbelian_of_isAbelianScheme {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsSemiAbelian A := by
  have := h.proper
  refine ⟨h.comm, h.smooth, inferInstance, inferInstance, h.geomConnected, ?_⟩
  intro Ω _ _ p
  exact ⟨torusExtensionOfAbelian _ (isAbelianScheme_pullback_obj p A h)⟩

theorem isAbelianScheme_powObj_of_isAbelianScheme {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : ∀ n, IsAbelianScheme (Out.powObj A n)
  | 0 => Diag.isAbelianScheme_unit S
  | n + 1 => AbelianSchemeGerms.isAbelianScheme_powObj A h n

theorem comp_list_prod_ofFn {S : Scheme.{0}} {T T' G : Over S} [MonObj G] (t : T' ⟶ T) :
    ∀ {n : ℕ} (u : Fin n → (T ⟶ G)), t ≫ (List.ofFn u).prod = (List.ofFn fun i => t ≫ u i).prod
  | 0, u => by simp
  | n + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul,
      comp_list_prod_ofFn t]

theorem isTangent_comp_of_isMonHom {R : Type} [CommRing R] {B G : Over (Sp R)} [GrpObj B] [GrpObj G]
    (Φ : B ⟶ G) [IsMonHom Φ] (v : epsR R ⟶ B) (hv : IsTangent v) : IsTangent (v ≫ Φ) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

noncomputable section

namespace GlobalTheory.PrincipalDatum

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem coe_add' (a b : 𝓞 E) : ((a + b : 𝓞 E) : E) = a + b := rfl

omit [NumberField E] in
theorem coe_mul' (a b : 𝓞 E) : ((a * b : 𝓞 E) : E) = a * b := rfl

theorem exists_clear (𝔞 : Submodule (𝓞 E) E) (h : 𝔞.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ ψ : 𝔞 →ₗ[𝓞 E] 𝓞 E, ∀ x, (ψ x : E) = N * (x : E) := by
  obtain ⟨a, ⟨N, hN, rfl⟩, ha⟩ :=
    FractionalIdeal.isFractional_of_fg (S := Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) h
  choose f hf using ha
  have hf' : ∀ x : 𝔞, ((f x x.2 : 𝓞 E) : E) = N * (x : E) := fun x => by
    have := hf x x.2
    rw [Algebra.smul_def] at this
    simpa using this
  refine ⟨N, nonZeroDivisors.ne_zero hN, ⟨⟨fun x => f x x.2, fun x y => ?_⟩, fun c x => ?_⟩, hf'⟩
  · apply RingOfIntegers.ext
    rw [coe_add', hf', hf', hf', Submodule.coe_add, mul_add]
  · apply RingOfIntegers.ext
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [coe_mul', hf', hf', Submodule.coe_smul, Algebra.smul_def]
    simp only [RingOfIntegers.coe_eq_algebraMap]
    ring

section Act

variable {M : Type} [AddCommGroup M] [Module (𝓞 E) M]






end Act

variable [IsCMField E]

theorem principal_root_re_zero_im_sq (H : Host E) : H.rt0.re = 0 ∧ H.rt0.im ^ 2 = H.d := by
  first
  | exact @_root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq
  | exact _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq
  | (apply _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq ..)

end GlobalTheory.PrincipalDatum
end
end
