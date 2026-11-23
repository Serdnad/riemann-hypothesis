module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle051
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle030
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem Scales.mul_scales {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Matrix (Fin n) (Fin 1) E}
    {a b : GAd σ J} {l l' : (AF F ⊗[F] E)ˣ} (e : Scales σ J x a l) (e' : Scales σ J x b l') :
    Scales σ J x (a * b) (l * l') := by
  unfold Scales at *
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', Matrix.mul_smul, e, smul_smul, Units.val_mul, mul_comm]

theorem iwasawaHeight_isHt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → IsHt (levelAll σ J L a) h ∧ ∀ p l, Scales σ J (col X) p l → ∀ g, h (p * g) = absE F E l * h g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D
  have law : ∀ p l, Scales σ J (col X) p l → ∀ g, h (p * g) = absE F E l * h g := by
    intro p l e g
    obtain ⟨p', l', e', k, hk, rfl⟩ := D.iwa g
    rw [← mul_assoc, D.ht _ _ (e.mul_scales e') k hk, D.ht _ _ e' k hk, map_mul, NNReal.coe_mul]
  refine ⟨⟨fun g => ?_, (GlobalTheory.T.height_function_compact_level_continuous F E σ n J r X Y L a h D).2, fun k hk => ?_, fun g => ?_⟩, law⟩
  · obtain ⟨p, l, e, k, hk, rfl⟩ := D.iwa g
    rw [D.ht _ _ e k hk]
    have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1))
  · have := D.ht 1 1 (by simp [Scales]) k hk
    simpa using this
  · obtain ⟨p, l, e, k, hk, rfl⟩ := D.iwa g
    refine ⟨k, hk, fun x => ?_⟩
    rw [mul_assoc, law p l e, D.ht _ _ e k hk]

end GlobalTheory.ResLine
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushEigen

def ptOverClosureIso (K : Type) [Field K] [IsAlgClosed K] :
    ptOver K (AlgebraicClosure K) ≅ 𝟙_ (Over (Sp K)) := by
  let σ : K ≃+* AlgebraicClosure K :=
    RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hI : IsIso (spMap (algebraMap K (AlgebraicClosure K))) := by
    change IsIso (Spec.map σ.toCommRingCatIso.hom)
    infer_instance
  exact Over.isoMk (asIso (spMap (algebraMap K (AlgebraicClosure K)))) (by
    change spMap _ ≫ 𝟙 _ = spMap _
    exact Category.comp_id _)

def ptClosureEquiv {K : Type} [Field K] [IsAlgClosed K] (B : AbVar K) :
    B.Pt ≃* (𝟙_ (Over (Sp K)) ⟶ B.X) where
  toFun x := (ptOverClosureIso K).inv ≫ x
  invFun y := (ptOverClosureIso K).hom ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.comp_mul _ x y

end GlobalTheory.PushEigen
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem bcMap_hom {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    (bcMap L f).hom = (Over.pullback (spMap (algebraMap K L))).map f.hom := rfl

instance spMap_surjective {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] :
    Surjective (spMap (algebraMap K L)) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

theorem bcMap_left_fst {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    (bcMap L f).hom.left ≫ pullback.fst B.X.hom (spMap (algebraMap K L)) =
      pullback.fst A.X.hom (spMap (algebraMap K L)) ≫ f.hom.left := by
  rw [bcMap_hom]
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem bcMap_injective {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K) :
    Function.Injective (bcMap L : (A ⟶ B) → _) := by
  intro f g h
  have : Epi (pullback.fst A.X.hom (spMap (algebraMap K L))) := Flat.epi_of_flat_of_surjective _
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change f.hom.left = g.hom.left
  rw [← cancel_epi (pullback.fst A.X.hom (spMap (algebraMap K L))), ← bcMap_left_fst, ← bcMap_left_fst, h]

theorem bcMap_add {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f g : A ⟶ B) :
    bcMap L (f + g) = bcMap L f + bcMap L g :=
  Subtype.ext (Functor.map_mul (Over.pullback (spMap (algebraMap K L))) f.hom g.hom)

theorem bcMap_comp {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B C : AbVar K} (f : A ⟶ B)
    (g : B ⟶ C) : bcMap L (f ≫ g) = bcMap L f ≫ bcMap L g :=
  Subtype.ext ((Over.pullback (spMap (algebraMap K L))).map_comp f.hom g.hom)

theorem bcMap_id {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) :
    bcMap L (𝟙 A) = 𝟙 _ :=
  Subtype.ext ((Over.pullback (spMap (algebraMap K L))).map_id A.X)

theorem bcMap_functorial : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B C : AbVar K),
    (∀ f g : A ⟶ B, bcMap L (f + g) = bcMap L f + bcMap L g) ∧
    (∀ (f : A ⟶ B) (g : B ⟶ C), bcMap L (f ≫ g) = bcMap L f ≫ bcMap L g) ∧ bcMap L (𝟙 A) = 𝟙 _ ∧
    Function.Injective (bcMap L : (A ⟶ B) → _) :=
  fun _ _ L _ _ A B _ => ⟨bcMap_add L, bcMap_comp L, bcMap_id L A, bcMap_injective L A B⟩

end GlobalTheory.AV.AbVar

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerKill

theorem flat_of_isFinite_field (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] (hf : IsFinite H.hom) :
    Flat H.hom := by
  have haff : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (G := Grp.mk H)).2 haff
  let B : Type := A.unop
  letI : HopfAlgebra K B := A.unop.hopfAlgebra
  let G : Over (Spec (CommRingCat.of K)) :=
    (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of K))
  letI : GrpObj G := instGrpObjSpecAsOverSpec (R := CommRingCat.of K) (A := CommRingCat.of B)
  let i : G ≅ H := (Grp.forget _).mapIso e
  obtain ⟨j, hj, hw⟩ : ∃ j : Spec (CommRingCat.of B) ⟶ H.left, IsIso j ∧
      Spec.map (CommRingCat.ofHom (algebraMap K B)) = j ≫ H.hom :=
    ⟨i.hom.left, inferInstanceAs (IsIso ((Over.forget _).map i.hom)), (Over.w i.hom).symm⟩
  haveI h1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have e : H.hom = inv j ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
    rw [hw, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

theorem kernel_killed : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left →
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  intro K _ A B f hf
  let H := pullback f.hom η[B.X]
  let i : H ⟶ A.X := pullback.fst _ _
  have hp : IsPullback i (toUnit H) f.hom η[B.X] := by
    rw [toUnit_unique (toUnit _) (pullback.snd f.hom η[B.X])]
    exact IsPullback.of_hasPullback _ _
  haveI : Mono i := ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩
  let lift {W : Over (Sp K)} (g : W ⟶ A.X) (hg : g ≫ f.hom = 1) : W ⟶ H :=
    GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift hp g hg
  have lift_comp {W : Over (Sp K)} (g : W ⟶ A.X) (hg : g ≫ f.hom = 1) :
      lift g hg ≫ i = g := GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift_comp hp g hg
  have kills (W : Over (Sp K)) (x : W ⟶ H) : (x ≫ i) ≫ f.hom = 1 := by
    rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]
  letI : GrpObj H :=
    { one := lift η[A.X] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
      mul := lift (fst H H ≫ i * snd H H ≫ i) (by
        rw [MonObj.mul_comp, kills, kills, _root_.mul_one])
      inv := lift (i ≫ ι[A.X]) (by
        have e : i ≫ f.hom = 1 := by simpa using kills H (𝟙 H)
        have h : (i⁻¹ * i) ≫ f.hom = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
        rw [MonObj.mul_comp, e, _root_.mul_one] at h
        exact h)
      one_mul := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [toUnit_unique (fst (𝟙_ (Over (Sp K))) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [toUnit_unique (snd H (𝟙_ (Over (Sp K)))) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        exact _root_.mul_assoc _ _ _
      left_inv := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [← Hom.one_def]
        exact inv_mul_cancel i
      right_inv := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [← Hom.one_def]
        exact mul_inv_cancel i }
  haveI : IsMonHom i := by
    refine { one_hom := lift_comp _ _, mul_hom := ?_ }
    refine (lift_comp _ _).trans ?_
    rw [Hom.mul_def]
    simp
  haveI : IsCommMonObj A.X := A.ab.comm
  haveI : IsCommMonObj H := by
    refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
    rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  have hHf : IsFinite H.hom := by
    have hl := hp.map (Over.forget _)
    have h1 : IsFinite (toUnit H).left := MorphismProperty.of_isPullback (P := @IsFinite) hl hf
    have h2 : H.hom = (toUnit H).left ≫ (𝟙_ (Over (Sp K))).hom := (Over.w _).symm
    rw [h2]
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 _))
  have hfl : Flat H.hom := flat_of_isFinite_field K H hHf
  obtain ⟨N, hN, h⟩ := GlobalTheory.FiniteFlatKilled.main K H hHf hfl
  refine ⟨N, hN, fun T x hx => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y : T ⟶ H, y ≫ i = x := ⟨_, GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift_comp hp x hx⟩
  rw [← MonObj.comp_pow, ← Category.id_comp i,
    ← MonObj.pow_comp, h, MonObj.one_comp, MonObj.comp_one]

end GlobalTheory.AV.KerKill
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVarProj

theorem strHom_eq_and_isProjOver : ∀ (K : Type) [Field K] (A : AbVar K),
    (letI := A.algΓ; GlobalTheory.strHom K A.X.left = A.X.hom) ∧ IsProjOver A.X.hom := by
  intro K _ A
  refine ⟨?_, ?_⟩
  · letI := A.algΓ
    exact GlobalTheory.strHom_eq fun _ => rfl
  · exact (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.X.hom).1
      (GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A.X A.ab)

end GlobalTheory.AV.AbVarProj
end
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.CovChar

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

variable {R} {X Y : Scheme.{0}} (f : Y ⟶ X)

end GlobalTheory.Et.CovChar

namespace GlobalTheory.AV.AbVar

open ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K]

abbrev geomX (A : AbVar K) : Scheme.{0} := GlobalTheory.Et.geom (AlgebraicClosure K) A.X.hom

abbrev geomOver (A : AbVar K) : Over (Sp K) :=
  Over.mk (pullback.fst A.X.hom (spMap (algebraMap K (AlgebraicClosure K))) ≫ A.X.hom)

def transl (A : AbVar K) (a : A.Pt) : geomX A ⟶ geomX A :=
  pullback.lift
    ((lift (Over.homMk (pullback.fst _ _) : geomOver A ⟶ A.X)
      (Over.homMk (pullback.snd _ _ ≫ a.left) (by
        rw [Category.assoc, Over.w a]; exact pullback.condition.symm) : geomOver A ⟶ A.X) ≫ μ[A.X]).left)
    (pullback.snd _ _) (by
      rw [Over.w]; exact pullback.condition)

end GlobalTheory.AV.AbVar
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleClsIff

theorem isAmpleCls_cls_iff : ∀ (K : Type) [Field K] (A : AbVar K) (L : LB A.X.left) (hL : L.IsLB),
    IsAmpleCls (cls L hL) ↔ IsAmpleLB L := by
  intro K _ A L hL
  have : IsProper A.X.hom := A.ab.proper
  constructor
  · rintro ⟨M, hM, hr, he⟩
    have hM' : IsAmpleLB M := (relAmple_iff_isAmpleLB_of_isAffine A.X hM).1 hr
    exact hM'.of_lbIso hL ((CechPic.cls_eq_iff hL hM).1 he.symm)
  · intro h
    exact ⟨L, hL, (relAmple_iff_isAmpleLB_of_isAffine A.X hL).2 h, rfl⟩

end GlobalTheory.AmpleClsIff
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isFinite_of_surjective_of_dim_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → Surjective f.hom.left → IsFinite f.hom.left := by
  intro K _ A B f hd hs
  have dB : SmoothOfRelativeDimension A.dim B.X.hom := hd ▸ B.smooth
  exact GlobalTheory.OntoFinite.isFinite_of_surjective A.ab B.ab A.smooth dB f.hom

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem comp_hom_eq_one_of_torsion_pts (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ)
    (hn : (n : K) ≠ 0) (hker : ∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1)
    (T : Over (Sp K)) (x : T ⟶ A.X) (hx : x ^ n = 1) : x ≫ f.hom = 1 := by
  have hA := A.ab
  have hC := C.ab
  have := hA.proper
  have := hC.proper
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨_, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion A.X hu
  have hι : torsion.ι A.X n ≫ mulN A.X n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ η[A.X]) (toUnit_unique _ _))
  set L := AlgebraicClosure K
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with ht
  let P := (Over.pullback t).obj (torsion A.X n)
  let C' := (Over.pullback t).obj C.X
  have hP : Etale P.hom := by
    change Etale (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hPf : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hC' : IsProper C'.hom := by
    change IsProper (pullback.snd C.X.hom t)
    infer_instance
  have hPr : IsReduced P.left := isReduced_of_smooth_of_isReduced P.hom
  have hfst : ∀ g : torsion A.X n ⟶ C.X, ((Over.pullback t).map g).left ≫ pullback.fst C.X.hom t =
      pullback.fst (torsion A.X n).hom t ≫ g.left := fun g => by
    simp
  have hEq : (Over.pullback t).map (torsion.ι A.X n ≫ f.hom) =
      (Over.pullback t).map (1 : torsion A.X n ⟶ C.X) := by
    refine TorsionDivisible.hom_ext_of_rationalPoints _ _ fun y => ?_
    let z : Sp L ⟶ (torsion A.X n).left := y.left ≫ pullback.fst (torsion A.X n).hom t
    have hz : z ≫ (torsion A.X n).hom = t := by
      have e1 : y.left ≫ P.hom = 𝟙 _ := by
        change y.left ≫ pullback.snd (torsion A.X n).hom t = _
        simpa using Over.w y
      simp only [z, Category.assoc, pullback.condition]
      rw [← Category.assoc]
      change (y.left ≫ P.hom) ≫ t = t
      rw [e1, Category.id_comp]
    let z' : ptOver K L ⟶ torsion A.X n := Over.homMk z hz
    have hw : (z' ≫ torsion.ι A.X n) ^ n = 1 := by
      rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
    have hk := hker (z' ≫ torsion.ι A.X n) hw
    have hk' : z' ≫ (torsion.ι A.X n ≫ f.hom) = z' ≫ (1 : torsion A.X n ⟶ C.X) := by
      rw [MonObj.comp_one, ← Category.assoc, hk]
    have hkl : z ≫ (torsion.ι A.X n ≫ f.hom).left = z ≫ (1 : torsion A.X n ⟶ C.X).left :=
      congrArg CommaMorphism.left hk'
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, hfst]
      simpa [z] using hkl
    · have w1 := Over.w (y ≫ (Over.pullback t).map (torsion.ι A.X n ≫ f.hom))
      have w2 := Over.w (y ≫ (Over.pullback t).map (1 : torsion A.X n ⟶ C.X))
      change _ ≫ pullback.snd C.X.hom t = _ at w1 w2
      rw [w1, w2]
  have hred : IsReduced (torsion A.X n).left := isReduced_of_smooth_of_isReduced (torsion A.X n).hom
  have hdom : IsDominant (pullback.fst (torsion A.X n).hom t) := inferInstance
  have h6 : torsion.ι A.X n ≫ f.hom = 1 := by
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated C.X.hom (by rw [Over.w, Over.w]) (pullback.fst (torsion A.X n).hom t) ?_
    rw [← hfst, ← hfst, hEq]
  have e : x ≫ mulN A.X n = toUnit T ≫ η[A.X] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
  obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion A.X n, y ≫ torsion.ι A.X n = x :=
    ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
  rw [← e', Category.assoc, h6, MonObj.comp_one]

end GlobalTheory.AV.AbVar

end
end
