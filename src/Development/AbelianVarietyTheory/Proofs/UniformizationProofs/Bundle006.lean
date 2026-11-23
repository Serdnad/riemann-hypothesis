module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle005
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

@[expose] public section

section

namespace GlobalTheory.NilpotentLift

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.NilpotentLift.isPushout_quotient_map {A : Type} [CommRing A] (J : Ideal A) {B : CommRingCat.{0}}
    (σ : CommRingCat.of A ⟶ B) :
    IsPushout σ (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap (J.map σ.hom) σ.hom Ideal.le_comap_map)) := by
  refine IsPushout.of_isColimit' (CommSq.mk ?_) ?_
  · ext a
    simp [Ideal.quotientMap_mk]
  · have key : ∀ s : PushoutCocone σ (CommRingCat.ofHom (Ideal.Quotient.mk J)),
        J.map σ.hom ≤ RingHom.ker s.inl.hom := by
      intro s
      rw [Ideal.map_le_iff_le_comap]
      intro j hj
      have h := congrArg (fun φ => φ.hom j) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      simp [RingHom.mem_ker, h, Ideal.Quotient.eq_zero_iff_mem.mpr hj]
    refine PushoutCocone.IsColimit.mk _
      (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (fun a ha => key s ha)))
      (fun s => ?_) (fun s => ?_) (fun s m h₁ _ => ?_)
    · ext b
      exact Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)
    · ext a
      have h := congrArg (fun φ => φ.hom a) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact (Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)).trans h
    · ext b
      have h := congrArg (fun φ => φ.hom b) h₁
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact h.trans (Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)).symm


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.NilpotentLift.main : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J →
    ∀ (G Y : Over (Spec (CommRingCat.of A))) [Smooth G.hom] [IsAffine Y.left]
      (f₀ : pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⟶ G.left),
      f₀ ≫ G.hom = pullback.fst _ _ ≫ Y.hom →
      (∃ W : G.left.Opens, IsAffineOpen W ∧ f₀ ⁻¹ᵁ W = ⊤) →
      ∃ f : Y ⟶ G, pullback.fst _ _ ≫ f.left = f₀ := by
  intro A _ J hJ G Y _ _ f₀ hf₀ hW
  obtain ⟨W, hWaff, hWtop⟩ := hW
  set e := Y.left.isoSpec with he
  obtain ⟨σ, hσdef⟩ : ∃ σ : CommRingCat.of A ⟶ Γ(Y.left, ⊤),
      σ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Y.hom.appTop := ⟨_, rfl⟩
  have hσ : e.hom ≫ Spec.map σ = Y.hom := by
    have h1 := Scheme.isoSpec_hom_naturality Y.hom
    rw [Scheme.isoSpec_Spec_hom] at h1
    rw [hσdef, Spec.map_comp, ← Category.assoc, he, h1, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have hσ' : e.inv ≫ Y.hom = Spec.map σ := by
    rw [← hσ, Iso.inv_hom_id_assoc]
  have hPB := isPullback_SpecMap_of_isPushout _ _ _ _ (_root_.GlobalTheory.NilpotentLift.isPushout_quotient_map J σ)
  have hPB' : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) ≫ e.inv)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map σ.hom) σ.hom Ideal.le_comap_map)))
      Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsPullback.of_iso hPB (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, hσ'])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
  have hx₀ : (hPB'.isoPullback.hom ≫ f₀) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) ≫ Spec.map σ := by
    rw [Category.assoc, hf₀, IsPullback.isoPullback_hom_fst_assoc, Category.assoc, hσ']
  obtain ⟨x, hx, hxs⟩ := _root_.GlobalTheory.exists_lift_of_smooth_of_isAffineOpen G.hom
    (isAffineOpen_top (Spec (CommRingCat.of A))) hWaff le_top
    (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) (Spec.map σ) (hPB'.isoPullback.hom ≫ f₀) hx₀
    (by simp)
    (by
      rintro _ ⟨y, rfl⟩
      have : hPB'.isoPullback.hom y ∈ f₀ ⁻¹ᵁ W := by rw [hWtop]; trivial
      simpa using this)
    (by
      intro R' A' _ _ _ _ _ _ π' hπ' φ
      have hsurj : Function.Surjective π' := by
        intro c
        obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective c
        exact ⟨b, (hπ' b).trans hb⟩
      have hnil : IsNilpotent (RingHom.ker π'.toRingHom) := by
        obtain ⟨n, hn⟩ := hJ
        refine ⟨n, eq_bot_iff.mpr ?_⟩
        have hle : RingHom.ker π'.toRingHom ≤ J.map σ.hom := fun b hb =>
          Ideal.Quotient.eq_zero_iff_mem.mp ((hπ' b).symm.trans hb)
        calc _ ≤ (J.map σ.hom) ^ n := Ideal.pow_right_mono hle n
          _ = ⊥ := by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
      exact ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective φ π' hsurj hnil⟩)
  refine ⟨Over.homMk (e.hom ≫ x) (by rw [Category.assoc, hxs, hσ]), ?_⟩
  rw [← cancel_epi hPB'.isoPullback.hom]
  show hPB'.isoPullback.hom ≫ pullback.fst _ _ ≫ e.hom ≫ x = hPB'.isoPullback.hom ≫ f₀
  rw [IsPullback.isoPullback_hom_fst_assoc, Category.assoc, Iso.inv_hom_id_assoc, hx]

end GlobalTheory.NilpotentLift
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PowMatrixLinear

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

theorem comp_prod {X Y M : C} [MonObj M] [IsCommMonObj M] {J : Type*} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ ∏ l ∈ s, g l = ∏ l ∈ s, f ≫ g l :=
  map_prod (MonoidHom.mk ⟨fun x : Y ⟶ M => f ≫ x, MonObj.comp_one f⟩
    (fun a b => MonObj.comp_mul f a b)) g s

theorem prod_comp {X M N : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N] {J : Type*}
    (s : Finset J) (g : J → (X ⟶ M)) (f : M ⟶ N) [IsMonHom f] :
    (∏ l ∈ s, g l) ≫ f = ∏ l ∈ s, g l ≫ f :=
  map_prod (IsMonHom.monoidHom f X) g s

end General

local instance splitTorus_isCommMonObj (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    IsCommMonObj (splitTorus S X) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj (splitTorusAff ZU X)))

end PowMatrixLinear


end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory

theorem flat_coker_of_complex_exact_mod_maximalIdeal : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] (D : ℕ → Type) [∀ i, AddCommGroup (D i)] [∀ i, Module A (D i)] [∀ i, Module.Finite A (D i)] [∀ i, Module V (D i)] [∀ i, IsScalarTower V A (D i)] [∀ i, Module.Flat V (D i)] (d : ∀ i, D (i + 1) →ₗ[A] D i), (∀ i x, d i (d (i + 1) x) = 0) → (∃ n, ∀ i, n < i → Subsingleton (D i)) → (∀ i (x : D (i + 1)), d i x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D i)) → x ∈ LinearMap.range (d (i + 1)) ⊔ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D (i + 1)))) → Module.Flat V (D 0 ⧸ LinearMap.range (d 0)) := by
  intro V A _ _ _ _ _ _ _ _ D _ _ _ _ _ _ d hdd _ hex
  set J : Ideal A := (IsLocalRing.maximalIdeal V).map (algebraMap V A) with hJ
  have hle : LinearMap.range (d 1) ≤ LinearMap.ker (d 0) := by
    rintro _ ⟨x, rfl⟩
    exact hdd 0 x
  let u : (D 1 ⧸ LinearMap.range (d 1)) →ₗ[A] D 0 := (LinearMap.range (d 1)).liftQ (d 0) hle
  have hr : LinearMap.range u = LinearMap.range (d 0) := Submodule.range_liftQ _ _ _
  have h := GlobalTheory.T.flat_quotient_range_of_injective_mod_maximal V A (D 1 ⧸ LinearMap.range (d 1)) (D 0) u (by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ LinearMap.range (d 1) ⊔ (J • ⊤ : Submodule A (D 1)) := hex 0 y hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have ha0 : (Submodule.Quotient.mk a : D 1 ⧸ LinearMap.range (d 1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ha
    rw [Submodule.Quotient.mk_add, ha0, zero_add]
    have : (LinearMap.range (d 1)).mkQ b ∈ (J • ⊤ : Submodule A (D 1)).map (LinearMap.range (d 1)).mkQ :=
      Submodule.mem_map_of_mem hb
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this)
  rwa [hr] at h

end GlobalTheory
end

section

namespace GlobalTheory

namespace CompleteFiniteExtension

open IsLocalRing

theorem isPrecomplete_of_le_of_pow_le {A : Type*} [CommRing A] {I J : Ideal A} (hJ : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [IsPrecomplete J A] : IsPrecomplete I A := by
  first
  | (rename_i h_1 h_7; revert A h_1 I J hJ e he h_7; exact @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le)
  | exact @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
  | exact _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
  | (apply _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le ..)

theorem isAdicComplete_of_finite_local (R S : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsAdicComplete (maximalIdeal S) S := by
  have := IsNoetherianRing.of_finite R S
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := R) S
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal S ^ e ≤ (maximalIdeal R).map (algebraMap R S) := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg (fun b hb => ?_) (IsNoetherian.noetherian _)
    obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := R) S b
      fun n hn => eq_maximalIdeal hn ▸ hb
    exact ⟨N, hN⟩
  have := isPrecomplete_of_le_of_pow_le
    (ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) S _ inferInstance) he
  exact ⟨⟩

end CompleteFiniteExtension

theorem exists_complete_dvr_finite_subalgebra :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] (F : Type) [Field F]
      [Algebra V F] [FaithfulSMul V F] [Algebra.IsAlgebraic V F] (s : Finset F),
      ∃ (W : Subalgebra V F) (_ : IsDiscreteValuationRing W),
        IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
        IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧
        Module.Finite V W ∧ Module.Free V W ∧ IsLocalHom (algebraMap V W) ∧
        (∀ x ∈ s, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) ∧
        ∀ x ∈ s, IsIntegral V x → x ∈ W := by
  intro V _ _ _ _ _ F _ _ _ _ s
  let K := FractionRing V
  let _ : Algebra K F := FractionRing.liftAlgebra V F
  have : IsScalarTower V K F := FractionRing.isScalarTower_liftAlgebra V F
  have : Algebra.IsAlgebraic K F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mp inferInstance
  let L : IntermediateField K F := IntermediateField.adjoin K (s : Set F)
  have : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let f : L →ₐ[V] F := L.val.restrictScalars V
  have hf : Function.Injective f := Subtype.val_injective
  let W : Subalgebra V F := (integralClosure V L).map f
  let e : integralClosure V L ≃ₐ[V] W := Subalgebra.equivMapOfInjective _ f hf
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  have hB : Module.Finite V (integralClosure V L) := IsIntegralClosure.finite V K L _
  have hBd : IsDiscreteValuationRing (integralClosure V L) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V K L
  have hfin : Module.Finite V W := Module.Finite.equiv e.toLinearEquiv
  have hd : IsDiscreteValuationRing W :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hmem : ∀ x ∈ L, IsIntegral V x → x ∈ W := fun x hx hi =>
    ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩
  have hsL : ∀ x ∈ s, x ∈ L := fun x hx => IntermediateField.subset_adjoin K _ hx
  refine ⟨W, hd, CompleteFiniteExtension.isAdicComplete_of_finite_local V W,
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra W, hfin, inferInstance, inferInstance,
    fun x hx => ?_, fun x hx => hmem x (hsL x hx)⟩
  obtain ⟨y, hy, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := V) x).exists_integral_multiple
  refine ⟨y • x, hmem _ ?_ h, algebraMap V F y, W.algebraMap_mem y,
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective V F)).2 hy, ?_⟩
  · rw [← algebraMap_smul K y x]
    exact L.smul_mem (hsL x hx)
  · rw [Algebra.smul_def, mul_comm]

end GlobalTheory
end
