module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open Filter Topology Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.HermFrame
open scoped Matrix ContDiff

namespace GlobalTheory.ChernCalc.FrameChange

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
variable {r : Type*} [Fintype r] [DecidableEq r] {H A B : E → Matrix r r ℂ} {z : E}

theorem conn_mul_mul (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 1 A z) (hAu : IsUnit (A z).det) (hB : MContDiffAt 1 B z) (hBu : IsUnit (B z).det)
    (hB0 : ∀ η, mdbar B z η = 0) (ξ : E) :
    conn (fun x => A x * H x * (B x)ᴴ) z ξ = (A z)ᵀ⁻¹ * (conn H z ξ * (A z)ᵀ + (mdel A z ξ)ᵀ) := by
  refine (eq_conn_of_compatible ?_ ?_).symm
  · simp only [det_mul, det_conjTranspose]
    exact (hAu.mul hu).mul hBu.star
  · rw [mdel_mul (hA.mul h) hB.conjTranspose, mdel_mul hA h, mdel_conjTranspose, hB0, ← conn_transpose_mul hu,
      transpose_mul, transpose_nonsing_inv]
    simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hAu, transpose_add, transpose_mul, Matrix.add_mul,
      conjTranspose_zero, transpose_transpose, Matrix.mul_zero, zero_add]

theorem curv_mul_mul (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 2 A z) (hAu : IsUnit (A z).det) (hA0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar A x η = 0)
    (hB : MContDiffAt 2 B z) (hBu : IsUnit (B z).det) (hB0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar B x η = 0) (ξ η : E) :
    curv (fun x => A x * H x * (B x)ᴴ) z ξ η = (A z)ᵀ⁻¹ * curv H z ξ η * (A z)ᵀ := by
  have he : (fun x => conn (fun x => A x * H x * (B x)ᴴ) x ξ) =ᶠ[𝓝 z]
      fun x => (A x)ᵀ⁻¹ * (conn H x ξ * (A x)ᵀ + (mdel A x ξ)ᵀ) := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, hA.eventually_two,
      hA.eventually_isUnit hAu, hB.eventually_two, hB.eventually_isUnit hBu, hB0] with x h1 h2 h3 h4 h5 h6 h7
    exact conn_mul_mul (h1.of_le one_le_two) h2 (h3.of_le one_le_two) h4 (h5.of_le one_le_two) h6 h7 ξ
  have hA1 : MContDiffAt 1 (fun x => (A x)ᵀ) z := (hA.of_le one_le_two).transpose
  have hAu' : IsUnit (A z)ᵀ.det := by rwa [det_transpose]
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have hd : MContDiffAt 1 (fun x => (mdel A x ξ)ᵀ) z := (hA.mdel (by norm_num) ξ).transpose
  have h0 : mddbar A z ξ η = 0 := by
    rw [← mdel_mdbar hA, mdel_congr (B := fun _ => 0) (hA0.mono fun x hx => hx η), mdel_const]
  rw [curv, mdbar_congr he, mdbar_mul (hA1.inv hAu') ((hc.mul hA1).add hd), mdbar_inv hA1 hAu',
    mdbar_add (hc.mul hA1) hd, mdbar_mul hc hA1, mdbar_transpose (fun x => mdel A x ξ), mdbar_mdel hA, h0,
    mdbar_transpose A, hA0.self_of_nhds, curv]
  simp [Matrix.mul_assoc]

end General

variable {n : ℕ} {r : Type} [Fintype r] {T : V n → Matrix r r ℂ} {v : V n}


omit [Fintype r] in
theorem two_of_holo (h : ∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) : MContDiffAt 2 T v :=
  fun a b => ((SCV.analyticAt_iff_eventually_differentiableAt.2 (h a b)).contDiffAt).restrict_scalars ℝ

theorem mdbar_zero_of_holo (h : ∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) :
    ∀ᶠ x in 𝓝 v, ∀ η, mdbar T x η = 0 :=
  (eventually_all.2 fun a => eventually_all.2 fun b => h a b).mono fun x hx η => by
    ext a b
    rw [mdbar_apply, dbar_eq_zero (hx a b)]
    rfl

theorem conn_curv_frame : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G₂ T K : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) → IsUnit (T v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K u a b) x) → IsUnit (K v).det → (∀ᶠ x in 𝓝 v, G₂ x = T x * G x * (K x)ᴴ) → (∀ ξ, conn G₂ v ξ = (T v)ᵀ⁻¹ * (conn G v ξ * (T v)ᵀ + (mdel T v ξ)ᵀ)) ∧ ∀ ξ η, curv G₂ v ξ η = (T v)ᵀ⁻¹ * curv G v ξ η * (T v)ᵀ := by
  intro n r _ _ G G₂ T K v hG hGu hT hTu hK hKu he
  have hG2 : MContDiffAt 2 G v := hG.of_le (by norm_cast)
  refine ⟨fun ξ => ?_, fun ξ η => ?_⟩
  · rw [conn_congr he]
    exact conn_mul_mul (hG2.of_le one_le_two) hGu ((two_of_holo hT).of_le one_le_two) hTu
      ((two_of_holo hK).of_le one_le_two) hKu (mdbar_zero_of_holo hK).self_of_nhds ξ
  · rw [curv_congr he]
    exact curv_mul_mul hG2 hGu (two_of_holo hT) hTu (mdbar_zero_of_holo hT) (two_of_holo hK) hKu
      (mdbar_zero_of_holo hK) ξ η

end GlobalTheory.ChernCalc.FrameChange
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ResBasic

variable {C : Type*} [Category C] [Abelian C] {X : C} (I : InjectiveResolution X)

end GlobalTheory.EtC.ResBasic

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private theorem injectiveResolution_cochainComplex_exact_and_exactAt {C : Type*} [Category C] [Abelian C]
    {X : C} (I : InjectiveResolution X) :
    (∀ n : ℤ, Injective (I.cochainComplex.X n)) ∧
    (∀ n : ℤ, n < 0 → IsZero (I.cochainComplex.X n)) ∧
    Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ∧
    (∃ w : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
        I.cochainComplex.d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧
    (∀ n : ℤ, n ≠ 0 → I.cochainComplex.ExactAt n) := by
  refine ⟨fun n => inferInstance, fun n hn => ?_, ?_, ?_, fun n hn => ?_⟩
  · exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
      have h : (ComplexShape.embeddingUpNat.f i : ℤ) = i := rfl
      omega)
  · rw [I.ι'_f_zero]
    erw [Iso.inv_hom_id_assoc]
    exact mono_comp (I.ι.f 0) _
  · have hw : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
        I.cochainComplex.d 0 1 = 0 := by
      rw [I.ι'_f_zero, I.cochainComplex_d 0 1 0 1 rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      erw [I.ι_f_zero_comp_complex_d_assoc, zero_comp]
    refine ⟨hw, ?_⟩
    refine (ShortComplex.exact_iff_of_iso ?_).mpr I.exact₀
    refine ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl)
      (I.cochainComplexXIso 1 1 rfl) ?_ ?_
    · dsimp only
      rw [I.ι'_f_zero]
      erw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, Iso.inv_hom_id_assoc]
    · dsimp only
      rw [I.cochainComplex_d 0 1 0 1 rfl rfl]
      simp
  · exact (quasiIsoAt_iff_exactAt I.ι' n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn)).mp
      inferInstance


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.res_basic : ∀ (R : Type) [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R), (∀ n : ℤ, Injective ((_root_.GlobalTheory.EtC.res R F).X n)) ∧
    (∀ n : ℤ, n < 0 → IsZero ((_root_.GlobalTheory.EtC.res R F).X n)) ∧ Mono (_root_.GlobalTheory.EtC.resι R F) ∧
    (∃ w : _root_.GlobalTheory.EtC.resι R F ≫ (_root_.GlobalTheory.EtC.res R F).d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧
    (∀ n : ℤ, n ≠ 0 → (_root_.GlobalTheory.EtC.res R F).ExactAt n) ∧
    ∀ (E : _root_.GlobalTheory.EtC.Spc) (n : ℤ), 0 < n → IsZero (((_root_.GlobalTheory.EtC.chains R).obj E).X n) := by
  intro R _ F
  unfold _root_.GlobalTheory.EtC.res _root_.GlobalTheory.EtC.resι _root_.GlobalTheory.EtC.chains
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := injectiveResolution_cochainComplex_exact_and_exactAt (injectiveResolution F)
  refine ⟨h₁, h₂, h₃, h₄, h₅, fun E n hn => ?_⟩
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
    have h : (ComplexShape.embeddingDownNat.f i : ℤ) = -i := rfl
    omega)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.SepCech

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

abbrev FinSub : Type := {L : IntermediateField K Ω // FiniteDimensional K L}

instance : IsDirected (FinSub K Ω) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, by haveI := a.2; haveI := b.2; infer_instance⟩, le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

instance : Nonempty (FinSub K Ω) := ⟨⟨⊥, inferInstance⟩⟩

def ringDiag : FinSub K Ω ⥤ CommRingCat.{0} where
  obj L := CommRingCat.of L.1
  map h := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom h)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

def ringCocone : Cocone (ringDiag K Ω) where
  pt := CommRingCat.of Ω
  ι := { app := fun L => CommRingCat.ofHom L.1.val.toRingHom, naturality := fun _ _ _ => rfl }

abbrev yArr (A : Type) [CommRing A] [Algebra K A] : Arrow PSh :=
  Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap K A))))

theorem ym {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) :
    yoneda.map (Spec.map g) ≫ yoneda.map (Spec.map f) = yoneda.map (Spec.map (f ≫ g)) := by
  rw [← Functor.map_comp, Spec.map_comp]

theorem spec_comm {L L' : FinSub K Ω} (h : L ⟶ L') :
    yoneda.map (Spec.map ((ringDiag K Ω).map h)) ≫ (yArr K L.1).hom = (yArr K L'.1).hom ≫ 𝟙 _ := by
  change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ 𝟙 _
  rw [Category.comp_id]
  refine (ym _ _).trans ?_
  congr 2 <;> (ext; rfl)

def arr : (FinSub K Ω)ᵒᵖ ⥤ Arrow PSh where
  obj L := yArr K L.unop.1
  map h := Arrow.homMk (yoneda.map (Spec.map ((ringDiag K Ω).map h.unop))) (𝟙 _) (spec_comm K Ω h.unop)
  map_id L := by
    refine Arrow.hom_ext _ _ ?_ ?_
    · change yoneda.map (Spec.map (𝟙 _)) = 𝟙 _
      rw [Spec.map_id, yoneda.map_id]
    · rfl
  map_comp f g := by
    refine Arrow.hom_ext _ _ ?_ ?_
    · change yoneda.map (Spec.map ((ringDiag K Ω).map (g.unop ≫ f.unop))) = _
      rw [Functor.map_comp]
      exact (ym _ _).symm
    · exact (Category.comp_id _).symm

def arrCone : Cone (arr K Ω) where
  pt := yArr K Ω
  π := { app := fun L => Arrow.homMk (yoneda.map (Spec.map ((ringCocone K Ω).ι.app L.unop))) (𝟙 _) (by
            change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ 𝟙 _
            rw [Category.comp_id]
            refine (ym _ _).trans ?_
            congr 2 <;> (ext; rfl))
         naturality := fun L L' h => by
            refine Arrow.hom_ext _ _ ?_ ?_
            · change 𝟙 _ ≫ yoneda.map (Spec.map _) = yoneda.map (Spec.map _) ≫ yoneda.map (Spec.map _)
              rw [Category.id_comp]
              refine Eq.trans ?_ (ym _ _).symm
              exact congrArg (fun x => yoneda.map (Spec.map x)) ((ringCocone K Ω).w h.unop).symm
            · exact (Category.comp_id _).symm }

def cechCone : Cone (arr K Ω ⋙ SimplicialObject.cechNerve) := SimplicialObject.cechNerve.mapCone (arrCone K Ω)

end GlobalTheory.SepCech
end
end

section

open GlobalTheory.EtC

namespace GlobalTheory

theorem field_finiteType_algClosed_SH : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B], IsField B → SH B := by
  intro k B _ _ _ _ _ hB
  letI : Field B := hB.toField
  haveI : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  have hbk : Function.Bijective (algebraMap k B) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed B := IsAlgClosed.of_ringEquiv k B
    (RingEquiv.ofBijective (algebraMap k B) hbk)
  refine ⟨Field.henselian B, ?_⟩
  have hbij : Function.Bijective (IsLocalRing.residue B) :=
    ⟨(IsLocalRing.residue B).injective, Ideal.Quotient.mk_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField B) :=
    IsAlgClosed.of_ringEquiv B _ (RingEquiv.ofBijective _ hbij)
  exact IsSepClosed.of_isAlgClosed _

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem aic_integralClosure_algebraicClosure :
    ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  intro D _ _ p hp hd
  have hmap : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).natDegree = p.natDegree := hp.natDegree_map _
  have hdeg : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hp.map _).ne_zero, hmap]; exact_mod_cast hd.ne'
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg
  have hrDp : IsIntegral (integralClosure D (AlgebraicClosure (FractionRing D))) r := ⟨p, hp, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  have hrD : IsIntegral D r := isIntegral_trans r hrDp
  refine ⟨⟨r, hrD⟩, ?_⟩
  apply Subtype.val_injective
  have key := Polynomial.eval₂_at_apply (p := p) (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D))) ⟨r, hrD⟩
  rw [← Polynomial.eval_map] at key
  have hr' : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).eval r = 0 := hr
  exact key.symm.trans hr'

end GlobalTheory
end

section

open GlobalTheory.EtC

namespace GlobalTheory.AICIff
open Polynomial

theorem root_mem_range {D K : Type} [CommRing D] [Nontrivial D] [CommRing K] [IsDomain K] [Algebra D K]
    (h : AIC D) : ∀ (n : ℕ) (p : D[X]), p.Monic → p.natDegree = n →
      ∀ x : K, aeval x p = 0 → ∃ y : D, algebraMap D K y = x := by
  intro n
  induction n with
  | zero =>
    intro p hp hn x hx
    rw [eq_one_of_monic_natDegree_zero hp hn] at hx
    simp at hx
  | succ n ih =>
    intro p hp hn x hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hfac : (X - C a) * (p /ₘ (X - C a)) = p := (mul_divByMonic_eq_iff_isRoot).2 ha
    have hq : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (hfac.symm ▸ hp)
    have hqn : (p /ₘ (X - C a)).natDegree = n := by
      have := (monic_X_sub_C a).natDegree_mul hq
      rw [hfac, natDegree_X_sub_C] at this
      omega
    rw [← hfac, map_mul] at hx
    rcases mul_eq_zero.1 hx with h0 | h0
    · refine ⟨a, ?_⟩
      simp only [map_sub, aeval_X, aeval_C] at h0
      exact (sub_eq_zero.1 h0).symm
    · exact ih _ hq hqn x h0

theorem aic_iff : ∀ (D : Type) [CommRing D] [IsDomain D],
    AIC D ↔ (IsIntegrallyClosed D ∧ IsAlgClosed (FractionRing D)) := by
  intro D _ _
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [isIntegrallyClosed_iff (FractionRing D)]
      rintro x ⟨p, hp, hx⟩
      exact root_mem_range h _ p hp rfl x (by rwa [aeval_def])
    · apply IsAlgClosed.of_exists_root
      intro f hf hirr
      have hdeg : 0 < f.natDegree :=
        hf.natDegree_pos.2 (fun h1 => hirr.not_isUnit (h1 ▸ isUnit_one))
      have hinj := IsFractionRing.injective D (FractionRing D)
      obtain ⟨b, hb0, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors D) f
      set g := IsLocalization.integerNormalization (nonZeroDivisors D) f with hg
      have hc : algebraMap D (FractionRing D) b ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb0
      have hgmap : g.map (algebraMap D (FractionRing D)) = C (algebraMap D (FractionRing D) b) * f := by
        rw [hb, Algebra.smul_def]; rfl
      have hgdeg : g.natDegree = f.natDegree := by
        rw [← natDegree_map_eq_of_injective hinj g, hgmap, natDegree_C_mul hc]
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, natDegree_zero] at hgdeg; omega
      obtain ⟨a, ha⟩ := h (integralNormalization g) (monic_integralNormalization hg0)
        (by rw [natDegree_integralNormalization]; omega)
      have hl : algebraMap D (FractionRing D) g.leadingCoeff ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap D (FractionRing D)), hinj.eq_iff]
        exact leadingCoeff_ne_zero.2 hg0
      refine ⟨algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) g.leadingCoeff, ?_⟩
      have key := integralNormalization_eval₂_leadingCoeff_mul (p := g) (by omega)
        (algebraMap D (FractionRing D))
        (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) g.leadingCoeff)
      rw [mul_div_cancel₀ _ hl, eval₂_at_apply, ha, map_zero, ← eval_map, hgmap, eval_mul, eval_C] at key
      have := key.symm
      simpa [hl, hc] using this
  · rintro ⟨h1, h2⟩ p hp hpos
    have hd : (p.map (algebraMap D (FractionRing D))).degree ≠ 0 := by
      refine ne_of_gt (natDegree_pos_iff_degree_pos.1 ?_)
      rw [hp.natDegree_map]; exact hpos
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
    have hint : IsIntegral D x := ⟨p, hp, by rwa [IsRoot, eval_map] at hx⟩
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨y, IsFractionRing.injective D (FractionRing D) ?_⟩
    rw [map_zero, ← eval₂_at_apply, ← eval_map]
    exact hx

end GlobalTheory.AICIff
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

lemma cechLev_π {f g : Arrow PSh} (F : f ⟶ g) (k : SimplexCategoryᵒᵖ) (j : Fin (k.unop.len + 1)) :
    ((evaluation _ PSh).obj k).map (Arrow.mapCechNerve F) ≫ WidePullback.π (fun _ => g.hom) j =
      WidePullback.π (fun _ => f.hom) j ≫ F.left := by
  simp only [evaluation_obj_map, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_π]

lemma cechLev_base {f g : Arrow PSh} (F : f ⟶ g) (k : SimplexCategoryᵒᵖ) :
    ((evaluation _ PSh).obj k).map (Arrow.mapCechNerve F) ≫
        WidePullback.base (fun _ : Fin (k.unop.len + 1) => g.hom) =
      WidePullback.base (fun _ => f.hom) ≫ F.right := by
  simp only [evaluation_obj_map, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_base]

theorem cech_level_limit (I : Type) [SmallCategory I] [IsCofiltered I] (A : I ⥤ Arrow PSh) (cA : Cone A)
    (hl : IsLimit (Arrow.leftFunc.mapCone cA)) (_hA : ∀ ⦃i j : I⦄ (f : i ⟶ j), IsIso (A.map f).right)
    (hR : ∀ i, IsIso (cA.π.app i).right) (k : SimplexCategoryᵒᵖ) :
    Nonempty (IsLimit (((evaluation _ PSh).obj k).mapCone (SimplicialObject.cechNerve.mapCone cA))) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  let L : ∀ (s : Cone ((A ⋙ SimplicialObject.cechNerve) ⋙ (evaluation _ PSh).obj k))
      (j : Fin (k.unop.len + 1)), s.pt ⟶ cA.pt.left := fun s j =>
    hl.lift
      { pt := s.pt
        π :=
          { app := fun i => s.π.app i ≫ WidePullback.π (fun _ => (A.obj i).hom) j
            naturality := by
              intro i i' f
              have h := s.w f
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                Functor.comp_obj, Arrow.leftFunc_obj, Functor.comp_map, Arrow.leftFunc_map] at h ⊢
              rw [← h]
              exact (Category.assoc _ _ _).trans
                ((congrArg (s.π.app i ≫ ·) (cechLev_π (A.map f) k j)).trans (Category.assoc _ _ _).symm) } }
  have hLfac : ∀ s j i, L s j ≫ (cA.π.app i).left =
      s.π.app i ≫ WidePullback.π (fun _ => (A.obj i).hom) j := by
    intro s j i
    exact hl.fac _ i
  have hLbase : ∀ s j i, L s j ≫ cA.pt.hom ≫ (cA.π.app i).right =
      s.π.app i ≫ WidePullback.base (fun _ : Fin (k.unop.len + 1) => (A.obj i).hom) := by
    intro s j i
    have hw : (cA.π.app i).left ≫ (A.obj i).hom = cA.pt.hom ≫ (cA.π.app i).right := Arrow.w (cA.π.app i)
    rw [← hw, ← Category.assoc, hLfac]
    exact (Category.assoc _ _ _).trans (congrArg (s.π.app i ≫ ·) (WidePullback.π_arrow _ j))
  refine ⟨{ lift := fun s => WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) (fun j => by
              rw [← cancel_mono (cA.π.app i₀).right, Category.assoc, Category.assoc, hLbase, hLbase])
            fac := ?_
            uniq := ?_ }⟩
  · intro s i
    apply WidePullback.hom_ext
    · intro j
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) _ ≫ ·) (cechLev_π (cA.π.app i) k j)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (cA.π.app i).left) (WidePullback.lift_π _ _ _ _ j)).trans ?_
      exact hLfac s j i
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) _ ≫ ·) (cechLev_base (cA.π.app i) k)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (cA.π.app i).right) (WidePullback.lift_base _ _ _ _)).trans ?_
      exact (Category.assoc _ _ _).trans (hLbase s 0 i)
  · intro s m hm
    have hmj : ∀ j, m ≫ WidePullback.π (fun _ => cA.pt.hom) j = L s j := by
      intro j
      apply hl.hom_ext
      intro i
      refine Eq.trans ?_ (hLfac s j i).symm
      refine Eq.trans ?_ (congrArg (· ≫ WidePullback.π (fun _ => (A.obj i).hom) j) (hm i))
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (m ≫ ·) (cechLev_π (cA.π.app i) k j).symm
    apply WidePullback.hom_ext
    · intro j
      exact (hmj j).trans (WidePullback.lift_π _ _ _ _ j).symm
    · refine Eq.trans ?_ (WidePullback.lift_base _ _ _ _).symm
      refine Eq.trans ?_ (congrArg (· ≫ cA.pt.hom) (hmj 0))
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (m ≫ ·) (WidePullback.π_arrow _ 0).symm

end GlobalTheory
end
