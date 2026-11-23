module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle006
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle002
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle527
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SemiProd

theorem torus_prod_iso : ∀ (S : Scheme.{0}) (X₁ X₂ : Type) [AddCommGroup X₁] [AddCommGroup X₂], IsIso (lift (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂)) (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂))) := by
  intro S X₁ X₂ _ _
  let comb : ∀ {M : Type} [CommGroup M], (Multiplicative X₁ →* M) → (Multiplicative X₂ →* M) →
      (Multiplicative (X₁ × X₂) →* M) := fun u v =>
    u.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst X₁ X₂)) *
      v.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd X₁ X₂))
  let l : ∀ {Z : Over S}, (Z ⟶ splitTorus S X₁) → (Z ⟶ splitTorus S X₂) → (Z ⟶ splitTorus S (X₁ × X₂)) :=
    fun {Z} f g => (splitTorusPointsEquiv S (X₁ × X₂) Z).symm
      (comb (splitTorusPointsEquiv S X₁ Z f) (splitTorusPointsEquiv S X₂ Z g))
  have f₁ : ∀ {Z : Over S} (f : Z ⟶ splitTorus S X₁) (g : Z ⟶ splitTorus S X₂),
      l f g ≫ SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂) = f := by
    intro Z f g
    apply (splitTorusPointsEquiv S X₁ Z).injective
    rw [SplitTorusPow.points_comp_torusMap, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    simp [comb]
  have f₂ : ∀ {Z : Over S} (f : Z ⟶ splitTorus S X₁) (g : Z ⟶ splitTorus S X₂),
      l f g ≫ SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂) = g := by
    intro Z f g
    apply (splitTorusPointsEquiv S X₂ Z).injective
    rw [SplitTorusPow.points_comp_torusMap, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    simp [comb]
  have u : ∀ {Z : Over S} (m : Z ⟶ splitTorus S (X₁ × X₂)),
      m = l (m ≫ SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
        (m ≫ SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) := by
    intro Z m
    apply (splitTorusPointsEquiv S (X₁ × X₂) Z).injective
    rw [MulEquiv.apply_symm_apply, SplitTorusPow.points_comp_torusMap,
      SplitTorusPow.points_comp_torusMap]
    refine MonoidHom.ext fun x => ?_
    have hx : x = Multiplicative.ofAdd (AddMonoidHom.inl X₁ X₂ x.toAdd.1) *
        Multiplicative.ofAdd (AddMonoidHom.inr X₁ X₂ x.toAdd.2) := by
      rw [← ofAdd_add]; simp
    conv_lhs => rw [hx]
    rw [map_mul]
    rfl
  have hl : IsLimit (BinaryFan.mk (SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
      (SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂))) :=
    BinaryFan.IsLimit.mk _ (fun f g => l f g) (fun f g => f₁ f g) (fun f g => f₂ f g)
      (fun f g m h₁ h₂ => by rw [u m]; exact congrArg₂ l h₁ h₂)
  have e : lift (SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
      (SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) =
      (hl.conePointUniqueUpToIso (tensorProductIsBinaryProduct _ _)).hom := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact (hl.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct _ _) ⟨.left⟩).symm
    · rw [lift_snd]
      exact (hl.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct _ _) ⟨.right⟩).symm
  rw [e]
  infer_instance

theorem tensorHom_prop : ∀ (S : Scheme.{0}) (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange] (A B C D : Over S) (f : A ⟶ B) (g : C ⟶ D), P f.left → P g.left → P (f ⊗ₘ g).left := by
  intro S P _ _ A B C D f g hf hg
  have e : (f ⊗ₘ g).left = pullback.map A.hom C.hom B.hom D.hom f.left g.left (𝟙 S) (by simp) (by simp) := by
    first | rfl | simp
  rw [e]
  exact P.pullbackMap hf hg (Over.w f).symm (Over.w g).symm

theorem kernel_tensor : ∀ (S : Scheme.{0}) (T₁ T₂ G₁ G₂ B₁ B₂ : Over S) [GrpObj B₁] [GrpObj B₂] (i₁ : T₁ ⟶ G₁) (i₂ : T₂ ⟶ G₂) (q₁ : G₁ ⟶ B₁) (q₂ : G₂ ⟶ B₂), IsPullback i₁ (toUnit T₁) q₁ (η : 𝟙_ (Over S) ⟶ B₁) → IsPullback i₂ (toUnit T₂) q₂ (η : 𝟙_ (Over S) ⟶ B₂) → IsPullback (i₁ ⊗ₘ i₂) (toUnit (T₁ ⊗ T₂)) (q₁ ⊗ₘ q₂) (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) := by
  intro S T₁ T₂ G₁ G₂ B₁ B₂ _ _ i₁ i₂ q₁ q₂ h₁ h₂
  have e₁ : (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) ≫ fst _ _ = η := by simp [MonObj.tensorObj.one_def]
  have e₂ : (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) ≫ snd _ _ = η := by simp [MonObj.tensorObj.one_def]
  have c₁ : ∀ {W : Over S} (a : W ⟶ G₁ ⊗ G₂) (b : W ⟶ 𝟙_ (Over S)), a ≫ (q₁ ⊗ₘ q₂) = b ≫ η →
      (a ≫ fst _ _) ≫ q₁ = toUnit W ≫ η := by
    intro W a b h
    have := congrArg (· ≫ fst _ _) h
    simp only [Category.assoc, tensorHom_fst, e₁] at this
    rw [Category.assoc, this, toUnit_unique b (toUnit W)]
  have c₂ : ∀ {W : Over S} (a : W ⟶ G₁ ⊗ G₂) (b : W ⟶ 𝟙_ (Over S)), a ≫ (q₁ ⊗ₘ q₂) = b ≫ η →
      (a ≫ snd _ _) ≫ q₂ = toUnit W ≫ η := by
    intro W a b h
    have := congrArg (· ≫ snd _ _) h
    simp only [Category.assoc, tensorHom_snd, e₂] at this
    rw [Category.assoc, this, toUnit_unique b (toUnit W)]
  have w : (i₁ ⊗ₘ i₂) ≫ (q₁ ⊗ₘ q₂) = toUnit (T₁ ⊗ T₂) ≫ (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, e₁, tensorHom_fst_assoc]
      rw [h₁.w, ← Category.assoc, toUnit_unique (fst T₁ T₂ ≫ toUnit T₁) (toUnit _)]
    · simp only [Category.assoc, tensorHom_snd, e₂, tensorHom_snd_assoc]
      rw [h₂.w, ← Category.assoc, toUnit_unique (snd T₁ T₂ ≫ toUnit T₂) (toUnit _)]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => lift (h₁.lift (s.fst ≫ fst _ _) (toUnit _) (c₁ _ _ s.condition))
      (h₂.lift (s.fst ≫ snd _ _) (toUnit _) (c₂ _ _ s.condition)))
    (fun s => ?_) (fun s => toUnit_unique _ _) (fun s m hm _ => ?_)⟩⟩
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, lift_fst_assoc, h₁.lift_fst]
    · rw [Category.assoc, tensorHom_snd, lift_snd_assoc, h₂.lift_fst]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      apply h₁.hom_ext
      · rw [h₁.lift_fst, Category.assoc, ← tensorHom_fst, ← Category.assoc, hm]
      · exact toUnit_unique _ _
    · rw [lift_snd]
      apply h₂.hom_ext
      · rw [h₂.lift_fst, Category.assoc, ← tensorHom_snd, ← Category.assoc, hm]
      · exact toUnit_unique _ _

variable {S : Scheme.{0}}

theorem isAbelianScheme_tensor {A B : Over S} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) : IsAbelianScheme (A ⊗ B) := by
  haveI := hA.comm; haveI := hB.comm; haveI := hA.smooth; haveI := hB.smooth
  haveI := hA.proper; haveI := hB.proper; haveI := hA.geomConnected; haveI := hB.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · show Smooth (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · show IsProper (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · show GeometricallyConnected (pullback.fst A.hom B.hom ≫ A.hom); exact GeometricallyConnected.comp _ _

theorem torusExtension_of_prod {K : Type} [Field K] {G G₁ G₂ : Over (Spec (.of K))} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] (a₁ : G ⟶ G₁) (a₂ : G ⟶ G₂) [IsMonHom a₁] [IsMonHom a₂] [IsIso (lift a₁ a₂)]
    (E₁ : TorusExtension G₁) (E₂ : TorusExtension G₂) : Nonempty (TorusExtension G) := by
  letI := E₁.addCommGroup; haveI := E₁.free; haveI := E₁.finite; letI := E₁.grpB
  letI := E₂.addCommGroup; haveI := E₂.free; haveI := E₂.finite; letI := E₂.grpB
  haveI := E₁.q_hom; haveI := E₂.q_hom; haveI := E₁.i_hom; haveI := E₂.i_hom
  haveI := torus_prod_iso (Spec (.of K)) E₁.X E₂.X
  have hmon : ∀ {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (φ : X →+ X'),
      IsMonHom (SplitTorusPow.torusMap (Spec (.of K)) φ) := by
    intro X X' _ _ φ
    constructor
    · have h : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus _ X') ≫ SplitTorusPow.torusMap _ φ = 1 := by
        apply (splitTorusPointsEquiv _ X _).injective
        rw [SplitTorusPow.points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
      simpa [Hom.one_def] using h
    · have h : ∀ {Z : Over (Spec (.of K))} (a b : Z ⟶ splitTorus _ X'),
          (a * b) ≫ SplitTorusPow.torusMap _ φ = (a ≫ SplitTorusPow.torusMap _ φ) * (b ≫ SplitTorusPow.torusMap _ φ) := by
        intro Z a b
        apply (splitTorusPointsEquiv _ X Z).injective
        rw [map_mul, SplitTorusPow.points_comp_torusMap, SplitTorusPow.points_comp_torusMap,
          SplitTorusPow.points_comp_torusMap, map_mul, MonoidHom.mul_comp]
      simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] using
        h (fst (splitTorus _ X') (splitTorus _ X')) (snd _ _)
  haveI := hmon (AddMonoidHom.inl E₁.X E₂.X)
  haveI := hmon (AddMonoidHom.inr E₁.X E₂.X)
  have key := kernel_tensor _ _ _ _ _ _ _ E₁.i E₂.i E₁.q E₂.q E₁.isKernel E₂.isKernel
  haveI : IsIso (lift a₁ a₂).left := inferInstanceAs (IsIso ((Over.forget _).map (lift a₁ a₂)))
  haveI : IsMonHom (inv (lift a₁ a₂)) := inferInstanceAs (IsMonHom (asIso (lift a₁ a₂)).inv)
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange],
      P E₁.q.left → P E₂.q.left → P (lift a₁ a₂ ≫ (E₁.q ⊗ₘ E₂.q)).left := by
    intro P _ _ h₁ h₂
    rw [Over.comp_left]
    exact P.comp_mem _ _ (P.of_isIso _) (tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂)
  refine ⟨{ X := E₁.X × E₂.X
            B := E₁.B ⊗ E₂.B
            isAbelian := isAbelianScheme_tensor E₁.isAbelian E₂.isAbelian
            q := lift a₁ a₂ ≫ (E₁.q ⊗ₘ E₂.q)
            q_hom := inferInstance
            q_flat := hP @Flat E₁.q_flat E₂.q_flat
            q_surjective := hP @Surjective E₁.q_surjective E₂.q_surjective
            q_quasiCompact := hP @QuasiCompact E₁.q_quasiCompact E₂.q_quasiCompact
            i := lift (SplitTorusPow.torusMap _ (AddMonoidHom.inl E₁.X E₂.X))
                (SplitTorusPow.torusMap _ (AddMonoidHom.inr E₁.X E₂.X)) ≫ (E₁.i ⊗ₘ E₂.i) ≫ inv (lift a₁ a₂)
            i_hom := inferInstance
            isKernel := ?_ }⟩
  refine IsPullback.of_iso key (asIso (lift (SplitTorusPow.torusMap _ (AddMonoidHom.inl E₁.X E₂.X))
    (SplitTorusPow.torusMap _ (AddMonoidHom.inr E₁.X E₂.X)))).symm (asIso (lift a₁ a₂)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · exact toUnit_unique _ _
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem isSemiAbelian_tensor : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [GrpObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsSemiAbelian (G₁ ⊗ G₂) := by
  intro S G₁ G₂ _ _ h₁ h₂
  haveI := h₁.comm; haveI := h₂.comm; haveI := h₁.smooth; haveI := h₂.smooth
  haveI := h₁.separated; haveI := h₂.separated; haveI := h₁.quasiCompact; haveI := h₂.quasiCompact
  haveI := h₁.geomConnected; haveI := h₂.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, fun Ω _ _ p => ?_⟩
  · show Smooth (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show IsSeparated (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show QuasiCompact (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show GeometricallyConnected (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); exact GeometricallyConnected.comp _ _
  · obtain ⟨E₁⟩ := h₁.fibres Ω p
    obtain ⟨E₂⟩ := h₂.fibres Ω p
    haveI : IsIso (lift ((Over.pullback p).map (fst G₁ G₂)) ((Over.pullback p).map (snd G₁ G₂))) :=
      isIso_prodComparison_of_preservesLimit_pair (Over.pullback p) G₁ G₂
    exact torusExtension_of_prod ((Over.pullback p).map (fst G₁ G₂)) ((Over.pullback p).map (snd G₁ G₂)) E₁ E₂

end GlobalTheory.SemiProd
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem exists_primitive_dUnit_eq : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H],
    (∀ φ ∈ augIdeal K (CartierDual K H), φ ^ p = 0) →
    ∀ w : Cot K H, ∃ b : H, cobOne K H b = 0 ∧ dUnit (R := K) b = w := by
  intro p _ K H _ _ _ _ _ _ hnil w
  have hgen := GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top p K (CartierDual K H) hnil
  set e := CartierDual.bidual K H
  have hH : Algebra.adjoin K {b : H | cobOne K H b = 0} = ⊤ := by
    let f : CartierDual K (CartierDual K H) →ₐ[K] H :=
      ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) : CartierDual K (CartierDual K H) →ₐ[K] H)
    have himg : f '' {φ | cobOne K (CartierDual K (CartierDual K H)) φ = 0} ⊆
        {b : H | cobOne K H b = 0} := by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [Set.mem_setOf_eq] at hφ ⊢
      show cobOne K H ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) φ) = 0
      rw [← pullTwo_cobOne, hφ, map_zero]
    rw [eq_top_iff]
    intro x _
    refine Algebra.adjoin_mono himg ?_
    rw [Algebra.adjoin_image]
    refine ⟨e x, ?_, ?_⟩
    · rw [hgen]; trivial
    · exact e.symm_apply_apply x
  let P : Submodule K H := LinearMap.ker (cobOne K H)
  let S : Submodule K (Cot K H) := P.map (AugCot.d (counitAlgHom K H))
  have hS : ∀ a ∈ Algebra.adjoin K {b : H | cobOne K H b = 0}, dUnit (R := K) a ∈ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.mem_map_of_mem (p := P) hx
    | algebraMap r => rw [dUnit, AugCot.d_algebraMap]; exact S.zero_mem
    | add x y _ _ hx hy => rw [dUnit, map_add (f := _)]; exact S.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [dUnit, AugCot.d_mul]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hx)
  obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom K H) w
  obtain ⟨b, hb, hbd⟩ := hS a (by rw [hH]; trivial)
  exact ⟨b, hb, hbd⟩

end GlobalTheory.PDiv
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv.HeightOnePrim

theorem apply_eq_zero_of_mem_sq {K H : Type} [Field K] [CommRing H] [HopfAlgebra K H]
    [IsCocomm K H] [Module.Finite K H] {φ : CartierDual K H} (hφ : cobOne K (CartierDual K H) φ = 0) {b : H}
    (hb : b ∈ augIdeal K H ^ 2) : φ b = 0 := by
  have hp := isPrimitiveElem_of_mem_ker (R := K) (A := CartierDual K H) (b := φ) hφ
  have hmul : ∀ x y : H, φ (x * y) = φ x * counit (R := K) y + counit (R := K) x * φ y := by
    intro x y
    rw [← CartierDual.pair_comul_tmul, show comul φ = _ from hp, map_add (f := _), LinearMap.add_apply,
      CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, CartierDual.one_apply,
      CartierDual.one_apply]
  rw [pow_two] at hb
  refine Submodule.mul_induction_on hb (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have hx' : counit (R := K) x = 0 := hx
    have hy' : counit (R := K) y = 0 := hy
    rw [hmul, hx', hy', mul_zero, zero_mul, add_zero]
  · rw [map_add (f := _), hx, hy, add_zero]

theorem eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H]
    [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) →
    ∀ b : H, cobOne K H b = 0 → dUnit (R := K) b = 0 → b = 0 := by
  intro p _ K H _ _ _ _ _ _ hpow b hb hd
  have hcb : counit (R := K) b = 0 := (mulBy_of_cobOne_eq_zero hb 0).2
  have hsq : b ∈ augIdeal K H ^ 2 := by
    have := (AugCot.d_eq_zero_iff (counitAlgHom K H) b).1 hd
    simpa [hcb] using this
  have hgen := GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top p K H hpow
  have hall : ∀ φ : CartierDual K H, φ b = 0 := by
    intro φ
    have hφ : φ ∈ Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} := by
      rw [hgen]; trivial
    induction hφ using Algebra.adjoin_induction with
    | mem x hx => exact apply_eq_zero_of_mem_sq hx hsq
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      change r • (1 : CartierDual K H) b = 0
      rw [CartierDual.one_apply, hcb, smul_zero]
    | add x y _ _ hx hy => rw [WithConv.ofConv_add, LinearMap.add_apply, hx, hy, add_zero]
    | mul x y _ _ hx hy =>
      have := evalAt_mul (R := K) (A := H) ⟨b, hb⟩ x y
      simp only [CartierDual.evalAt_apply] at this
      rw [this, hx, hy, smul_zero, smul_zero, add_zero]
  exact CartierDual.eq_of_forall_apply (R := K) fun φ => by rw [hall φ, map_zero]

end GlobalTheory.PDiv.HeightOnePrim
end
end

section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

theorem _root_.GlobalTheory.T.integral_of_trace_integral_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : E, (∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (w * a + cc (w * a))) → IsIntegral ℤ w := by
  first | exact @GlobalTheory.LieDisc.isIntegral_of_trace_integral | exact GlobalTheory.LieDisc.isIntegral_of_trace_integral | (intros; apply GlobalTheory.LieDisc.isIntegral_of_trace_integral <;> assumption)
end

section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc

theorem exists_integral_add_cc_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    Unr E → ∃ t : E, IsIntegral ℤ t ∧ t + cc t = 1 := by
  intro E _ _ _ hE
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hE
  let σ := IsCMField.ringOfIntegersComplexConj E
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | ∃ t : 𝓞 E, algebraMap _ (𝓞 E) a = t + σ t}
      add_mem' := by
        rintro a b ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨s + t, by rw [map_add (f := _), hs, ht, map_add (f := _)]; ring⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨t, ht⟩
        refine ⟨algebraMap _ (𝓞 E) c * t, ?_⟩
        rw [smul_eq_mul, map_mul, ht, map_mul, AlgEquiv.commutes]
        ring }
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) m
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1
        (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))]; exact bot_le)
    have htr : ∀ t : 𝓞 E, t + σ t ∈ P := by
      intro t
      have hco : ((t + σ t : 𝓞 E) : E) = (t : E) + IsCMField.complexConj E t := by
        rw [← IsCMField.coe_ringOfIntegersComplexConj]
        rfl
      have hfix := (IsCMField.complexConj_eq_self_iff E ((t : E) + IsCMField.complexConj E t)).1 (by
        rw [map_add (f := _), IsCMField.complexConj_apply_apply, add_comm])
      have hi : IsIntegral ℤ (⟨_, hfix⟩ : maximalRealSubfield E) := by
        have h0 : IsIntegral ℤ ((t + σ t : 𝓞 E) : E) := (t + σ t).isIntegral_coe
        rw [hco] at h0
        exact (isIntegral_algebraMap_iff ).1 h0
      let a : 𝓞 (maximalRealSubfield E) := ⟨_, hi⟩
      have hA : algebraMap _ (𝓞 E) a = t + σ t := by
        apply RingOfIntegers.ext
        rw [hco]
        rfl
      have h1 : a ∈ Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P := by
        change a ∈ Ideal.under (𝓞 (maximalRealSubfield E)) P
        rw [hPm]
        exact hIm ⟨t, hA⟩
      exact hA ▸ Ideal.mem_comap.1 h1
    have hσ : ∃ s, σ.toAlgHom s ≠ s := by
      by_contra hc
      push Not at hc
      apply IsCMField.complexConj_ne_one E
      ext x
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
      have hc' : ∀ s : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E s :=
        fun s => congrArg (fun z : 𝓞 E => (z : E)) (hc s)
      simp [hc']
    obtain ⟨t, ht⟩ := GlobalTheory.UCls.Det.exists_sub_notMem σ.toAlgHom hσ P hP.ne_top
    apply ht
    have h2 := P.sub_mem (htr t) (P.mul_mem_right (σ t) (htr 1))
    convert h2 using 1
    change t - σ t = t + σ t - (1 + σ 1) * σ t
    rw [map_one]
    ring
  obtain ⟨t, ht⟩ : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := hI ▸ Submodule.mem_top
  refine ⟨(t : E), t.isIntegral_coe, ?_⟩
  have h := congrArg (fun z : 𝓞 E => (z : E)) ht
  rw [map_one] at h
  change (1 : E) = (t : E) + ((σ t : 𝓞 E) : E) at h
  rw [IsCMField.coe_ringOfIntegersComplexConj] at h
  rw [cc]
  exact h.symm

end GlobalTheory.LieDisc
end
end

section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.LocGenVal

theorem valuation_div_le_one_cofinite : ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (u : K),
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ S, ∀ a : K, Formalism.L2.LamCM.IsLocGen p a I → u ≠ 0 →
      p.valuation K (a / u) ≤ 1 := by
  intro K _ _ I u
  classical
  have h1 := Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := K) I)
  have h2 := Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors (K := K) (FractionalIdeal.spanSingleton (𝓞 K)⁰ u))
  refine ⟨(h1.union h2).toFinset, ?_⟩
  intro p hp a ha hu
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
  obtain ⟨hpI, hpu⟩ := hp
  have hau : a / u ≠ 0 := div_ne_zero ha.1 hu
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact ha.1
  have hsu : FractionalIdeal.spanSingleton (𝓞 K)⁰ u ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hu
  have hc : FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / u)) = 0 := by
    rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.count_mul K p hsa (inv_ne_zero hsu), FractionalIdeal.count_inv, ha.2, hpI, hpu]
    simp
  rw [Formalism.L2.LamCM.valuation_eq_exp_neg_count p hau, hc, neg_zero, WithZero.exp_zero]

end GlobalTheory.LocGenVal
end

section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

theorem _root_.GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z ↔ ∀ a b, (starRingEnd ℂ) (Z a b) = -((if ε a then (1 : ℂ) else -1) * (if ε b then (1 : ℂ) else -1) * Z b a) := by
  first | exact @GlobalTheory.pcLieEntry | exact GlobalTheory.pcLieEntry | (intros; apply GlobalTheory.pcLieEntry <;> assumption)
end
