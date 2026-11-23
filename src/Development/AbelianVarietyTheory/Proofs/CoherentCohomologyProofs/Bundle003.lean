module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.LocalRing.Length

@[expose] public section

section

namespace GlobalTheory.DoubleCosetSetoid

section Rep

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

def repStabilizer (ρ : Representation k G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]

end Rep

section Cont

variable {𝕜 G E : Type*} [NontriviallyNormedField 𝕜] [Group G] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]

def clmStabilizer (π : G →* (E →L[𝕜] E)) (v : E) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ContinuousLinearMap.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply]

end Cont

section DoubleCoset

variable {G : Type*} [Group G]

def doubleCosetSetoid (H K : Subgroup G) : Setoid G where
  r x y := ∃ h ∈ H, ∃ k ∈ K, y = h * x * k
  iseqv :=
    { refl := fun x => ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      symm := by
        rintro x y ⟨h, hh, k, hk, rfl⟩
        exact ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, by group⟩
      trans := by
        rintro x y z ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        exact ⟨h' * h, H.mul_mem hh' hh, k * k', K.mul_mem hk hk', by group⟩ }

end DoubleCoset

end GlobalTheory.DoubleCosetSetoid
end

section

open CategoryTheory Abelian Opposite Limits TopologicalSpace

universe w v u

namespace GlobalTheory
namespace Flasque

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

noncomputable abbrev freeSheaf (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J _).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

noncomputable abbrev freeSheafMap {V U : C} (i : V ⟶ U) : freeSheaf J V ⟶ freeSheaf J U :=
  (presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

instance mono_freeSheafMap {V U : C} (i : V ⟶ U) [Mono i] : Mono (freeSheafMap J i) := by
  infer_instance

variable {J}

noncomputable def freeSheafHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (freeSheaf J U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := ((sheafificationAdjunction J _).homEquiv _ _).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv)
  map_add' f g := by
    rfl

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] in
lemma _root_.GlobalTheory.Flasque.subsingleton_H'_of_injective (I : Sheaf J AddCommGrpCat.{v}) [Injective I]
    (n : ℕ) (U : C) : Subsingleton (Sheaf.H'.{w} I (n + 1) U) :=
  Ext.subsingleton_of_injective (_root_.GlobalTheory.Flasque.freeSheaf J U) I n

section Shift

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

end Shift

end Site

section Injective

variable {A : Type u} [Category.{v} A] [Abelian A]

noncomputable abbrev injectiveShortComplex [EnoughInjectives A] (F : A) : ShortComplex A :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {A : Type u} [Category.{v} A] [Abelian A] in
lemma _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact [EnoughInjectives A] (F : A) :
    (_root_.GlobalTheory.Flasque.injectiveShortComplex F).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)


open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {A : Type u} [Category.{v} A] [Abelian A] in
lemma _root_.GlobalTheory.Flasque.exists_hom_τ₁_eq {S T : ShortComplex A} (hS : S.ShortExact)
    [Injective T.X₂] (f : S.X₁ ⟶ T.X₁) : ∃ φ : S ⟶ T, φ.τ₁ = f := by
  have := hS.mono_f
  let τ₂ : S.X₂ ⟶ T.X₂ := Injective.factorThru (f ≫ T.f) S.f
  have h₂ : S.f ≫ τ₂ = f ≫ T.f := Injective.comp_factorThru _ _
  have hw : S.f ≫ τ₂ ≫ T.g = 0 := by
    rw [reassoc_of% h₂, T.zero, comp_zero]
  let τ₃ : S.X₃ ⟶ T.X₃ := hS.gIsCokernel.desc (CokernelCofork.ofπ _ hw)
  have h₃ : S.g ≫ τ₃ = τ₂ ≫ T.g :=
    hS.gIsCokernel.fac (CokernelCofork.ofπ _ hw) WalkingParallelPair.one
  exact ⟨{ τ₁ := f, τ₂ := τ₂, τ₃ := τ₃, comm₁₂ := h₂.symm, comm₂₃ := h₃.symm }, rfl⟩

end Injective

section Space

variable {X : TopCat.{u}}

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
private lemma freeSheafHomEquiv_eq_yonedaEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v})
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h = yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
        ((sheafificationAdjunction J _).homEquiv _ _ h)) := rfl

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
private lemma freeSheafHomEquiv_freeSheafMap_comp' {V U : C} (i : V ⟶ U) (F : Sheaf J AddCommGrpCat.{v})
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv V F (_root_.GlobalTheory.Flasque.freeSheafMap J i ≫ h) =
      F.obj.map i.op (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h) := by
  rw [freeSheafHomEquiv_eq_yonedaEquiv, freeSheafHomEquiv_eq_yonedaEquiv,
    Adjunction.homEquiv_naturality_left]
  erw [Adjunction.homEquiv_naturality_left]
  rw [← yonedaEquiv_naturality]
  rfl


open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {X : TopCat.{u}} in
theorem _root_.GlobalTheory.Flasque.isFlasque_of_injective (I : TopCat.Sheaf AddCommGrpCat.{u} X) [hI : Injective I] :
    I.IsFlasque := by
  let I' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := I
  haveI : Injective I' := hI
  refine ⟨fun {U V} i => ?_⟩
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let g : _root_.GlobalTheory.Flasque.freeSheaf _ (unop V) ⟶ I' :=
    (_root_.GlobalTheory.Flasque.freeSheafHomEquiv (unop V) I').symm s
  let h : _root_.GlobalTheory.Flasque.freeSheaf _ (unop U) ⟶ I' :=
    Injective.factorThru g (_root_.GlobalTheory.Flasque.freeSheafMap _ i.unop)
  refine ⟨_root_.GlobalTheory.Flasque.freeSheafHomEquiv (unop U) I' h, ?_⟩
  have key := freeSheafHomEquiv_freeSheafMap_comp' i.unop I' h
  rw [Injective.comp_factorThru] at key
  simpa [g] using key.symm

instance isFlasque_injectiveShortComplex_X₂ (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (injectiveShortComplex F).X₂.IsFlasque :=
  isFlasque_of_injective _

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
private lemma freeSheafHomEquiv_comp' (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) (f : F ⟶ G) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv U G (h ≫ f) =
      f.hom.app (op U) (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h) := by
  rw [freeSheafHomEquiv_eq_yonedaEquiv, freeSheafHomEquiv_eq_yonedaEquiv,
    Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_right]
  rw [yonedaEquiv_comp]
  rfl


open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {X : TopCat.{u}} in
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
theorem _root_.GlobalTheory.Flasque.subsingleton_H'_of_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [hF : F.IsFlasque] (n : ℕ) (U : Opens X) : Subsingleton (F.H' (n + 1) U) := by
  let Y : TopCat.Sheaf AddCommGrpCat.{u} X :=
    _root_.GlobalTheory.Flasque.freeSheaf (Opens.grothendieckTopology X) U
  letI : HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X) := ‹HasExt.{w} (Sheaf _ _)›
  suffices h : ∀ x : Ext.{w} Y F (n + 1), x = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  induction n generalizing F with
  | zero =>
    intro x
    have hS := _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact F
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ Y hS x (Ext.eq_zero_of_injective _) rfl
    obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective x₃
    have hepi := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS
    rw [AddCommGrpCat.epi_iff_surjective] at hepi
    obtain ⟨t, ht⟩ := hepi (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _ φ)
    let ψ : Y ⟶ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).X₂ :=
      (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _).symm t
    have hψ : ψ ≫ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).g = φ := by
      apply (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _).injective
      refine (freeSheafHomEquiv_comp' U ψ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).g).trans ?_
      simp only [ψ, AddEquiv.apply_symm_apply]
      exact ht
    rw [Ext.homEquiv₀_symm_apply, ← hψ, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by simp), hS.comp_extClass, Ext.comp_zero]
  | succ m ih =>
    intro x
    have hS := _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact F
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ Y hS x (Ext.eq_zero_of_injective _) rfl
    haveI : (_root_.GlobalTheory.Flasque.injectiveShortComplex F).X₃.IsFlasque :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    rw [ih _ x₃, Ext.zero_comp]

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {X : TopCat.{u}} in
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
theorem _root_.GlobalTheory.Flasque.subsingleton_H'_of_isFlasque_of_pos (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] {n : ℕ} (hn : 0 < n) (U : Opens X) : Subsingleton (F.H' n U) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact _root_.GlobalTheory.Flasque.subsingleton_H'_of_isFlasque F m U

end Space

end Flasque

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory.PointSupport


open TensorProduct in
open TensorProduct in
theorem _root_.GlobalTheory.PointSupport.exists_algHom_ker_eq (K : Type) [Field K] [IsAlgClosed K] (R : Type)
    [CommRing R] [Algebra K R] [Algebra.FiniteType K R] (M : Ideal R) [M.IsMaximal] :
    ∃ χ : R →ₐ[K] K, RingHom.ker χ = M := by
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  let e : K ≃ₐ[K] R ⧸ M :=
    AlgEquiv.ofBijective (Algebra.ofId K (R ⧸ M)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]


open TensorProduct in
open TensorProduct in
theorem _root_.GlobalTheory.PointSupport.finiteLength_and_finrank_eq_length :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R]
      [Algebra.FiniteType K R] (χ₀ : R →ₐ[K] K) (O : Type) [CommRing O] [Algebra R O]
      [(RingHom.ker χ₀).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ₀)]
      (H : Type) [AddCommGroup H] [Module R H] [Module K H] [IsScalarTower K R H]
      [Module.Finite R H],
      (∀ χ : R →ₐ[K] K, χ ≠ χ₀ → ∃ r : R, χ r ≠ 0 ∧ ∀ z : H, r • z = 0) →
      IsFiniteLength O (O ⊗[R] H) ∧ Module.Finite K H ∧
        (Module.finrank K H : ℕ∞) = Module.length O (O ⊗[R] H) := by
  intro K _ _ R _ _ _ χ₀ O _ _ _ _ H _ _ _ _ _ hsupp
  classical
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hχ₀ : Function.Surjective χ₀ := fun k => ⟨algebraMap K R k, χ₀.commutes k⟩
  haveI hP : (RingHom.ker χ₀).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ₀

  have hmax : ∀ M : Ideal R, M.IsMaximal → Module.annihilator R H ≤ M → M = RingHom.ker χ₀ := by
    intro M hM hle
    obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.PointSupport.exists_algHom_ker_eq K R M
    by_cases h : χ = χ₀
    · rw [← hχ, h]
    · obtain ⟨r, hr, hrz⟩ := hsupp χ h
      have hrM : r ∈ M := hle (Module.mem_annihilator.mpr hrz)
      rw [← hχ] at hrM
      exact absurd (RingHom.mem_ker.mp hrM) hr

  have hprime : ∀ Q : Ideal R, Q.IsPrime → Module.annihilator R H ≤ Q → Q = RingHom.ker χ₀ := by
    intro Q hQ hle
    rw [← IsJacobsonRing.out' Q hQ.isRadical]
    apply le_antisymm
    · obtain ⟨J, hJ, hQJ⟩ := Ideal.exists_le_maximal Q hQ.ne_top
      rw [← hmax J hJ (hle.trans hQJ)]
      exact sInf_le ⟨hQJ, hJ⟩
    · exact le_sInf fun J hJ => (hmax J hJ.2 (hle.trans hJ.1)).ge

  letI : Module (R ⧸ Module.annihilator R H) H := Module.quotientAnnihilator
  have hmk : ∀ (r : R) (z : H), (Ideal.Quotient.mk (Module.annihilator R H) r) • z = r • z :=
    fun _ _ => rfl
  haveI : IsScalarTower R (R ⧸ Module.annihilator R H) H :=
    ⟨fun r a z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, hmk, hmk, mul_smul]⟩
  haveI : IsScalarTower K (R ⧸ Module.annihilator R H) H :=
    ⟨fun k a z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hmk, hmk, ← Algebra.smul_def,
        smul_assoc]⟩
  haveI : Module.Finite (R ⧸ Module.annihilator R H) H :=
    Module.Finite.of_restrictScalars_finite R _ H
  have hprimeq : ∀ Q : Ideal (R ⧸ Module.annihilator R H), Q.IsPrime →
      Q.comap (Ideal.Quotient.mk _) = RingHom.ker χ₀ := fun Q hQ =>
    hprime _ (Ideal.comap_isPrime _ Q) fun r hr => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact Q.zero_mem
  haveI : Ring.KrullDimLE 0 (R ⧸ Module.annihilator R H) := Ring.KrullDimLE.mk₀ fun Q hQ => by
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, hprimeq Q hQ]
    refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker, ← hprimeq Q hQ]
    intro r hr
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact Q.zero_mem
  haveI : Module.Finite K (R ⧸ Module.annihilator R H) :=
    (Module.finite_iff_krullDimLE_zero K _).mpr inferInstance
  haveI hfin : Module.Finite K H := Module.Finite.trans (R ⧸ Module.annihilator R H) H

  have hunit : ∀ s : (RingHom.ker χ₀).primeCompl, IsUnit (algebraMap R (Module.End R H) s) := by
    intro s
    have ha : IsUnit (Ideal.Quotient.mk (Module.annihilator R H) (s : R)) := by
      by_contra h
      obtain ⟨I, hI, hsI⟩ := exists_max_ideal_of_mem_nonunits h
      have hsI' : (s : R) ∈ Ideal.comap (Ideal.Quotient.mk (Module.annihilator R H)) I := hsI
      rw [hprimeq I hI.isPrime] at hsI'
      exact s.2 hsI'
    rw [Module.End.isUnit_iff]
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    refine ⟨fun x y hxy => ?_, fun z => ⟨b • z, ?_⟩⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← hmk, ← hmk] at hxy
      exact ha.smul_left_cancel.mp hxy
    · rw [Module.algebraMap_end_apply, ← hmk, smul_smul, hb, one_smul]
  haveI : IsLocalizedModule (RingHom.ker χ₀).primeCompl (LinearMap.id : H →ₗ[R] H) :=
    IsLocalizedModule.mk hunit (fun y => ⟨⟨y, 1⟩, one_smul _ _⟩)
      (fun {x₁ x₂} h => ⟨1, by simpa using h⟩)
  let e : H ≃ₗ[R] O ⊗[R] H := IsLocalizedModule.linearEquiv (RingHom.ker χ₀).primeCompl
    LinearMap.id (TensorProduct.mk R O H 1)

  letI : Algebra K O := ((algebraMap R O).comp (algebraMap K R)).toAlgebra
  haveI : IsScalarTower K R O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eK : H ≃ₗ[K] O ⊗[R] H := e.restrictScalars K
  haveI : IsLocalRing O := IsLocalization.AtPrime.isLocalRing O (RingHom.ker χ₀)
  haveI : IsLocalHom (algebraMap K O) := ⟨fun k hk => by
    by_cases h0 : k = 0
    · rw [h0, map_zero] at hk
      exact absurd hk not_isUnit_zero
    · exact isUnit_iff_ne_zero.mpr h0⟩
  haveI : Module.Finite K (O ⊗[R] H) := Module.Finite.equiv eK

  have hsurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)) := by
    have hR : ∀ r : R, IsLocalRing.residue O (algebraMap R O r) ∈
        (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).fieldRange := by
      intro r
      refine ⟨IsLocalRing.residue K (χ₀ r), ?_⟩
      have hmem : algebraMap R O (r - algebraMap K R (χ₀ r)) ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O (RingHom.ker χ₀), RingHom.mem_ker,
          map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at hmem
      rw [hmem]
      exact IsLocalRing.ResidueField.map_residue (algebraMap K O) (χ₀ r)
    intro x
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (RingHom.ker χ₀).primeCompl o
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul]
    have hs : IsLocalRing.residue O (IsLocalization.mk' O (1 : R) s) =
        (IsLocalRing.residue O (algebraMap R O s))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, IsLocalization.mk'_spec, map_one, map_one]
    rw [hs]
    exact Subfield.mul_mem _ (hR r) (Subfield.inv_mem _ (hR s))
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O) = 1 := by
    let f := LinearEquiv.ofBijective
      (Algebra.linearMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O))
      ⟨(algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).injective, hsurj⟩
    rw [← f.length_eq, Module.length_eq_one_iff]
    infer_instance
  have hlen := IsLocalRing.length_restrictScalars K O (O ⊗[R] H)
  rw [hres, mul_one, Module.length_eq_finrank K] at hlen
  have hfr : Module.finrank K H = Module.finrank K (O ⊗[R] H) := eK.finrank_eq
  refine ⟨?_, hfin, ?_⟩
  · rw [← Module.length_ne_top_iff, ← hlen]
    exact ENat.coe_ne_top _
  · rw [hfr]
    exact hlen

end GlobalTheory.PointSupport
end
