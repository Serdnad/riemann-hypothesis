module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinates
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjectiveCoordinateRepresentationClosedSubsch
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle079
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjDescendsToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle076
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
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem lift_mem_valuationSubring_iff {K L : Type*} [Field K] [Field L] (A : ValuationSubring L) (i : K →+* L)
    (h : Function.Injective (i.comp (A.comap i).subtype)) (x : FractionRing (A.comap i)) :
    IsFractionRing.lift (A := A.comap i) (K := FractionRing (A.comap i)) h x ∈ A ↔
      x ∈ Set.range (algebraMap (A.comap i) (FractionRing (A.comap i))) := by
  let f := FractionRing.algEquiv (A.comap i) K
  have hf : IsFractionRing.lift (A := A.comap i) (K := FractionRing (A.comap i)) h =
      i.comp f.toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (A.comap i)) (RingHom.ext fun a => ?_)
    refine (IsFractionRing.lift_algebraMap h a).trans ?_
    exact congrArg i (f.commutes a).symm
  rw [hf]
  refine ⟨fun hx => ⟨⟨f x, hx⟩, f.injective (f.commutes _)⟩, ?_⟩
  rintro ⟨v, rfl⟩
  rw [← hf, IsFractionRing.lift_algebraMap]
  exact v.2

theorem intRing_complete_dvr : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → IsDiscreteValuationRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ ∀ x : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K), ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K))) := by
  intro p _ K hK
  have hmem : ∀ x : K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := fun x => mem_OO_iff _
  let e : integralClosure ℤ_[p] K ≃+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K :=
    { toFun := fun x => ⟨x.1, (hmem _).2 ((mem_integralClosure_padicInt_iff K _).1 x.2)⟩
      invFun := fun x => ⟨x.1, (mem_integralClosure_padicInt_iff K _).2 ((hmem _).1 x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] (integralClosure ℤ_[p] K)
  refine ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_, fun x => ?_⟩
  · have := (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal _) e).2 hc
    rwa [IsLocalRing.map_ringEquiv_maximalIdeal] at this
  · rw [← mem_OO_iff]
    exact lift_mem_valuationSubring_iff (OO p) (algebraMap K (PadicAlgCl p))
      (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) x

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory.PowLie (sc zeroPt isTangent_iff)
noncomputable section
namespace GlobalTheory.KS.InvHom

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  have h₃ : O₂ ≤ (f ≫ g) ⁻¹ᵁ O₀ := h₂.trans (f.preimage_mono h₁)
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le _ h₃]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem pbT_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) :
    pbT f s (f ⁻¹ᵁ O₀) = (f.app O₀).hom s := by
  rw [pbT_of_le f le_rfl, Scheme.Hom.app_eq_appLE]

theorem constFn_spMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {Y : Scheme.{0}}
    (q : Y ⟶ Sp R') (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h1 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  refine h1.symm.trans ?_
  exact congrArg (fun t => (q.appLE ⊤ O (fun _ _ => trivial)).hom t) h2.symm

theorem constFn_mul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (O : Y.Opens) (a b : R) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp [constFn]

theorem constFn_zero {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (O : Y.Opens) :
    constFn q O (0 : R) = 0 := by
  simp [constFn]

variable {K : Type} [Field K]

def jA (A : Over (Sp K)) : A ⟶ epsR K ⊗ A := lift (toUnit A ≫ zeroPt K) (𝟙 A)

theorem thick (A : Over (Sp K)) :
    (∀ O : (epsR K ⊗ A).left.Opens, (snd (epsR K) A).left ⁻¹ᵁ ((jA A).left ⁻¹ᵁ O) = O) ∧
    ∀ (O : A.left.Opens) (F : Γ((epsR K ⊗ A).left, (snd (epsR K) A).left ⁻¹ᵁ O)),
      ∃! ab : Γ(A.left, O) × Γ(A.left, O), F = ((snd (epsR K) A).left.app O).hom ab.1 +
        constFn (R := DualNumber K) (fst (epsR K) A).left _ DualNumber.eps *
          ((snd (epsR K) A).left.app O).hom ab.2 := by
  have h := GlobalTheory.ConstThickening.structure_dualNumber K A.left (epsR K ⊗ A).left A.hom (fst (epsR K) A).left (snd (epsR K) A).left
    (jA A).left (IsPullback.of_hasPullback (epsR K).hom A.hom).flip
    (by rw [← Over.comp_left, jA, lift_snd]; rfl)
    (by
      have : jA A ≫ fst (epsR K) A = toUnit A ≫ zeroPt K := by rw [jA, lift_fst]
      exact congrArg CommaMorphism.left this)
  exact ⟨h.1, h.2.2⟩

abbrev tr {A : Over (Sp K)} [GrpObj A] (v : epsR K ⟶ A) : epsR K ⊗ A ⟶ A :=
  (fst (epsR K) A ≫ v) * snd (epsR K) A

variable {A : Over (Sp K)} [GrpObj A]

theorem tr_preimage {v : epsR K ⟶ A} (hv : IsTangent v) (W : A.left.Opens) :
    (tr v).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W := by
  have h : jA A ≫ tr v = 𝟙 A := by
    rw [MonObj.comp_mul, ← Category.assoc, jA, lift_fst, lift_snd, Category.assoc,
      (isTangent_iff v).1 hv]
    exact _root_.one_mul (𝟙 A)
  rw [← (thick A).1 ((tr v).left ⁻¹ᵁ W), ← Scheme.Hom.comp_preimage (jA A).left, ← Over.comp_left, h]
  rfl

theorem pull {v : epsR K ⟶ A} (hv : IsTangent v) {dd} (hd : IsInvDer v dd) {Z : Over (Sp K)}
    (S : Z ⟶ epsR K ⊗ A) (W : A.left.Opens) (f : Γ(A.left, W)) (O : Z.left.Opens)
    (hO : O ≤ (S ≫ snd (epsR K) A).left ⁻¹ᵁ W) :
    pbT (S ≫ tr v).left f O = pbT (S ≫ snd (epsR K) A).left f O +
      constFn (R := DualNumber K) (S ≫ fst (epsR K) A).left O DualNumber.eps *
        pbT (S ≫ snd (epsR K) A).left (dd W f) O := by
  have hO' : O ≤ S.left ⁻¹ᵁ ((snd (epsR K) A).left ⁻¹ᵁ W) := hO
  have h := congrArg (fun s => pbT S.left s O) (hd W f)
  simp only [pbT_add, pbT_mul] at h
  rw [pbT_pbT _ _ (tr_preimage hv W).ge hO', pbT_pbT _ _ le_rfl hO', pbT_pbT _ _ le_rfl hO',
    pbT_constFn _ _ hO'] at h
  exact h

theorem tan_one : IsTangent (1 : epsR K ⟶ A) := by
  rw [isTangent_iff, MonObj.comp_one]
  simp [Hom.one_def]

theorem tan_mul {u u' : epsR K ⟶ A} (hu : IsTangent u) (hu' : IsTangent u') : IsTangent (u * u') := by
  have e : (η[A] : _ ⟶ A) = 1 := by simp [Hom.one_def]
  rw [isTangent_iff] at *
  rw [MonObj.comp_mul, hu, hu', e, _root_.one_mul]

theorem tan_sc {v : epsR K ⟶ A} (hv : IsTangent v) (c : K) : IsTangent (sc c ≫ v) := by
  have e : zeroPt K ≫ sc c = zeroPt K := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [isTangent_iff] at *
  rw [← Category.assoc, e, hv]

theorem inv_one : IsInvDer (1 : epsR K ⟶ A) (fun _ _ => 0) := by
  intro W f
  rw [MonObj.comp_one, _root_.one_mul, pbT_zero, mul_zero, add_zero]

theorem inv_mul {u u' : epsR K ⟶ A} (hu : IsTangent u) (hu' : IsTangent u') {d d'}
    (hd : IsInvDer u d) (hd' : IsInvDer u' d') : IsInvDer (u * u') (fun W f => d W f + d' W f) := by
  intro W f
  have e : (fst (epsR K) A ≫ (u * u')) * snd (epsR K) A = lift (fst _ _) (tr u') ≫ tr u := by
    rw [MonObj.comp_mul, MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst, _root_.mul_assoc]
  have h := pull hu hd (lift (fst _ _) (tr u')) W f ((snd (epsR K) A).left ⁻¹ᵁ W)
    (by rw [lift_snd]; exact (tr_preimage hu' W).ge)
  rw [lift_snd, lift_fst, hd' W f, hd' W (d W f)] at h
  rw [e, h, pbT_add]
  have h2 : constFn (R := DualNumber K) (fst (epsR K) A).left ((snd (epsR K) A).left ⁻¹ᵁ W) DualNumber.eps *
      constFn (R := DualNumber K) (fst (epsR K) A).left ((snd (epsR K) A).left ⁻¹ᵁ W) DualNumber.eps = 0 := by
    rw [← constFn_mul, DualNumber.eps_mul_eps, constFn_zero]
  linear_combination (pbT (snd (epsR K) A).left (d' W (d W f)) ((snd (epsR K) A).left ⁻¹ᵁ W)) * h2

theorem inv_sc {v : epsR K ⟶ A} (hv : IsTangent v) {d} (hd : IsInvDer v d) (c : K) :
    IsInvDer (sc c ≫ v) (fun W f => constFn A.hom W c * d W f) := by
  intro W f
  have e : (fst (epsR K) A ≫ (sc c ≫ v)) * snd (epsR K) A = (sc c ▷ A) ≫ tr v := by
    rw [MonObj.comp_mul, whiskerRight_snd, whiskerRight_fst_assoc]
  have h := pull hv hd (sc c ▷ A) W f ((snd (epsR K) A).left ⁻¹ᵁ W) (by rw [whiskerRight_snd])
  rw [whiskerRight_snd, whiskerRight_fst] at h
  rw [e, h, pbT_mul, pbT_constFn _ _ le_rfl, ← _root_.mul_assoc]
  congr 2
  have w : (snd (epsR K) A).left ≫ A.hom = (fst (epsR K) A).left ≫ spMap (algebraMap K (DualNumber K)) :=
    (Over.w (snd (epsR K) A)).trans (Over.w (fst (epsR K) A)).symm
  have e2 : epsScaleR c (DualNumber.eps : DualNumber K) = DualNumber.eps * algebraMap K (DualNumber K) c := by
    ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [w]
  refine (constFn_spMap (epsScaleR c) (fst (epsR K) A).left _ _).trans ?_
  rw [e2]
  refine (constFn_mul _ _ _ _).trans ?_
  congr 1
  exact (constFn_spMap _ _ _ _).symm

theorem inv_prod : ∀ {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (d : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ i, IsTangent (u i)) →
    (∀ i, IsInvDer (u i) (d i)) →
      IsTangent (List.ofFn u).prod ∧ IsInvDer (List.ofFn u).prod (fun W f => ∑ i, d i W f) := by
  intro n
  induction n with
  | zero =>
    intro u d _ _
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨tan_one, inv_one⟩
  | succ n ih =>
    intro u d hu hd
    obtain ⟨h₁, h₂⟩ := ih (fun i => u i.succ) (fun i => d i.succ)
      (fun i => hu i.succ) (fun i => hd i.succ)
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨tan_mul (hu 0) h₁, inv_mul (hu 0) h₁ (hd 0) h₂⟩

theorem inv_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    {d : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)} (hv : ∀ i, IsTangent (v i))
    (hd : ∀ i, IsInvDer (v i) (d i)) (hw : IsLieComb c v w) :
    IsTangent w ∧ IsInvDer w (fun W f => ∑ i, constFn A.hom W (c i) * d i W f) := by
  obtain ⟨u, hu, rfl⟩ := hw
  have e : ∀ i, u i = sc (c i) ≫ v i := fun i => Over.OverMorphism.ext (hu i)
  exact inv_prod u (fun i W f => constFn A.hom W (c i) * d i W f) (fun i => e i ▸ tan_sc (hv i) _)
    (fun i => e i ▸ inv_sc (hv i) (hd i) _)

theorem inv_hom {A₁ : Over (Sp K)} [GrpObj A₁] (f : A₁ ⟶ A) [IsMonHom f] {w : epsR K ⟶ A₁}
    (hw : IsTangent w) (hwf : IsTangent (w ≫ f)) {dw D} (hdw : IsInvDer w dw) (hD : IsInvDer (w ≫ f) D)
    (W : A.left.Opens) (h : Γ(A.left, W)) :
    dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = (f.left.app W).hom (D W h) := by
  have e : (epsR K ◁ f) ≫ tr (w ≫ f) = tr w ≫ f := by
    rw [MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_snd, whiskerLeft_fst_assoc, Category.assoc]
  have h1 := pull hwf hD (epsR K ◁ f) W h ((snd (epsR K) A₁).left ⁻¹ᵁ (f.left ⁻¹ᵁ W))
    (by rw [whiskerLeft_snd]; exact le_rfl)
  rw [e, whiskerLeft_snd, whiskerLeft_fst, Over.comp_left, Over.comp_left,
    ← pbT_pbT _ _ le_rfl (tr_preimage hw _).ge, ← pbT_pbT _ _ le_rfl le_rfl h,
    ← pbT_pbT _ _ le_rfl le_rfl (D W h), pbT_app f.left, pbT_app f.left, pbT_app, pbT_app] at h1
  have h2 := hdw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h)
  rw [pbT_app, pbT_app] at h2
  have := ((thick A₁).2 (f.left ⁻¹ᵁ W) _).unique (y₁ := (_, _)) (y₂ := (_, _)) h2 h1
  exact congrArg Prod.snd this

theorem invDer_along_hom : ∀ (K : Type) [Field K] (A₁ A₀ : Over (Sp K)) [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (w : epsR K ⟶ A₁) (dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)) (c : Fin g → K), IsMonHom f → (∀ a, IsTangent (v a)) → IsTangent w → (∀ a, IsInvDer (v a) (dd a)) → IsInvDer w dw → IsLieComb c v (w ≫ f) → ∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)), dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = ∑ a, constFn A₁.hom _ (c a) * (f.left.app W).hom (dd a W h) := by
  intro K _ A₁ A₀ _ _ f g v dd w dw c hf hv hw hdd hdw hc W h
  obtain ⟨h₁, h₂⟩ := inv_comb hv hdd hc

  rw [inv_hom f hw h₁ hdw h₂, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, ← pbT_app f.left (constFn A₀.hom W (c a)), pbT_constFn _ _ le_rfl, Over.w f]

end GlobalTheory.KS.InvHom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.homogeneous_ideal_sections_of_line_bundle_power : ∀ (K σ : Type) [Field K] [Finite σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → (∀ F ∈ idealOf p M th (𝟙 X), ∀ e, MvPolynomial.homogeneousComponent e F ∈ idealOf p M th (𝟙 X)) ∧ (∀ F, (∀ i, MvPolynomial.X i * F ∈ idealOf p M th (𝟙 X)) → F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (d : ℕ) (F : MvPolynomial σ K), F.IsHomogeneous d → ∃ τ : (lbPow M d).Sec, (∀ j, τ.f j = MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F) ∧ ((∀ j, τ.f j = 0) ↔ F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (y : Sp K ⟶ X) (v : σ → K), y ≫ p = 𝟙 _ → SecCoord M th y v → (MvPolynomial.eval v F = 0 ↔ ¬ ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus τ) := by
  first | exact @GlobalTheory.ZV.FormSec.ideal_of_veryAmple | exact GlobalTheory.ZV.FormSec.ideal_of_veryAmple | (intros; apply GlobalTheory.ZV.FormSec.ideal_of_veryAmple <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.VertField

theorem differentiableAt_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (z₀ : E) (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀) :
    DifferentiableAt ℂ (fun z => (M z).det) z₀ := by
  simp only [Matrix.det_apply']
  fun_prop

private theorem differentiableAt_adjugate_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (z₀ : E) (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀)
    (i j : Fin g) : DifferentiableAt ℂ (fun z => (M z).adjugate i j) z₀ := by
  simp only [Matrix.adjugate_apply]
  refine differentiableAt_det (fun z => (M z).updateRow j (Pi.single i 1)) z₀ fun k l => ?_
  by_cases hk : k = j <;> simp [Matrix.updateRow_apply, hk, h k l]

theorem differentiableAt_of_mulVec {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (b w : E → Fin g → ℂ) (z₀ : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀) (hb : ∀ i, DifferentiableAt ℂ (fun z => b z i) z₀)
    (hdet : (M z₀).det ≠ 0) (hw : ∀ᶠ z in nhds z₀, (M z).mulVec (w z) = b z) :
    DifferentiableAt ℂ w z₀ := by
  have hd : DifferentiableAt ℂ (fun z => (M z).det) z₀ := differentiableAt_det M z₀ h
  have hne : ∀ᶠ z in nhds z₀, (M z).det ≠ 0 := hd.continuousAt.eventually_ne hdet
  have heq : w =ᶠ[nhds z₀] fun z => ((M z).det)⁻¹ • ((M z).adjugate.mulVec (b z)) := by
    filter_upwards [hne, hw] with z hz hzw
    rw [← hzw, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, inv_mul_cancel₀ hz, one_smul]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  rw [differentiableAt_pi]
  intro i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  have hadj := differentiableAt_adjugate_apply M z₀ h i
  have hi := hd.inv hdet
  fun_prop

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  have hpre : (x ≫ φ) ⁻¹ᵁ U = x ⁻¹ᵁ φ ⁻¹ᵁ U := by simp
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
  · rw [dite_eq_left (by rwa [hpre]), dite_eq_left h]
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · rw [dite_eq_right (by rwa [hpre]), dite_eq_right h]

theorem isOpen_dom_and_differentiableOn_fn {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left}
    (u : HolUnif A₀ L₀ g) {X : Scheme.{0}} (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    IsOpen (dom u m W) ∧ DifferentiableOn ℂ (fn u m W f) (dom u m W) := by
  have hcomp : ∀ z, ((u.ex z).left ≫ m) ⁻¹ᵁ W = (u.ex z).left ⁻¹ᵁ m ⁻¹ᵁ W := fun z => by simp
  have hdom : dom u m W = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ m ⁻¹ᵁ W} := by
    ext z
    simp only [dom, Set.mem_ofPred_eq, hcomp]
  have hfn : fn u m W f = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom f) := by
    funext z
    exact valAt'_comp _ _ _ _
  rw [hdom, hfn]
  exact u.8 (m ⁻¹ᵁ W) ((m.app W).hom f)

private theorem clm_apply_eq_sum_single_mul {g : ℕ} (L : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ) :
    L v = ∑ a, L (Pi.single a 1) * v a := by
  have hv : v = ∑ a, v a • (Pi.single a 1 : Fin g → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem exists_differentiableOn_vertical : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin P₀.g → ℂ)) (s : (Fin n → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ), IsOpen B → Differentiable ℂ G → (∀ z ∈ B, PtDer ((u.ex (G z)).left ≫ m) (s z) ∧ ∀ r, s z ⊤ (constFn p ⊤ r) = 0) → (∀ W f, DifferentiableOn ℂ (fun z => s z W f) {z ∈ B | G z ∈ dom u m W}) → ∃ w : (Fin n → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w B ∧ ∀ z ∈ B, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) (w z) := by
  intro P₀ u Hm χ hU R _ x₀ X p m hsm hpb n B G s hB hGd hs hhol
  have key : ∀ z ∈ B, ∃ v : Fin P₀.g → ℂ, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) v :=
    fun z hz => (GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hU R x₀ X p m hsm hpb (G z) (s z) (hs z hz).1 (hs z hz).2).exists
  choose! w hw using key
  refine ⟨w, fun z₁ hz₁ => ?_, hw⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨W, t, hW, hdet⟩ := exists_fibre_coords P₀ u Hm χ hU R x₀ X p m hsm hpb (G z₁)
  have hD : IsOpen (dom u m W) := (isOpen_dom_and_differentiableOn_fn u m W 0).1
  have hV : IsOpen {z ∈ B | G z ∈ dom u m W} := hB.inter (hD.preimage hGd.continuous)
  have hz₁V : z₁ ∈ {z ∈ B | G z ∈ dom u m W} := ⟨hz₁, hW⟩
  have hT : Matrix.transpose (Matrix.of fun b a => fderiv ℂ (fn u m W (t b)) (G z₁) (Pi.single a 1)) =
      Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) (G z₁) (Pi.single a 1) := by
    ext a b
    rfl
  refine differentiableAt_of_mulVec (fun z => Matrix.of fun b a => fderiv ℂ (fn u m W (t b)) (G z) (Pi.single a 1))
    (fun z b => s z W (t b)) w z₁ (fun b a => ?_) (fun b => ?_) ?_ ?_
  · have h1 := ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex P₀.g (dom u m W) (fn u m W (t b)) hD).2
      (isOpen_dom_and_differentiableOn_fn u m W (t b)).2).2 (Pi.single a 1)
    exact (h1.differentiableAt (hD.mem_nhds hW)).comp z₁ (hGd z₁)
  · exact (hhol W (t b)).differentiableAt (hV.mem_nhds hz₁V)
  · rw [← Matrix.det_transpose, hT]
    exact hdet
  · filter_upwards [hV.mem_nhds hz₁V] with z hz
    ext b
    exact ((hw z hz.1 W (t b) hz.2).trans (clm_apply_eq_sum_single_mul _ _)).symm

end GlobalTheory.KS.VertField
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_fibre_coords_det_fderiv_ne_zero_of_smooth : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z, ∃ (W : X.Opens) (t : Fin P₀.g → Γ(X, W)), z ∈ dom u m W ∧ (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)).det ≠ 0 := by
  first | exact @GlobalTheory.KS.exists_fibre_coords | exact GlobalTheory.KS.exists_fibre_coords | (intros; apply GlobalTheory.KS.exists_fibre_coords <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_scheme_map_of_projective_coordinates : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (sY : Y ⟶ Sp R) (M : LB Z) (N : LB Y) (th : σ → M.Sec) (ty : σ → N.Sec), ProjRep I s M th → N.IsLB → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R'), y ≫ sY = spMap β → SecCoord N ty y v → Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) → ∃ f : Y ⟶ Z, f ≫ s = sY ∧ LBIso N (M.pull f) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ f) v) ∧ ∀ f' : Y ⟶ Z, f' ≫ s = sY → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v → SecCoord M th (y ≫ f') v) → f' = f := by
  first | exact @GlobalTheory.ZM.RepMap.exists_map_of_coord | exact GlobalTheory.ZM.RepMap.exists_map_of_coord | (intros; apply GlobalTheory.ZM.RepMap.exists_map_of_coord <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.isProjectiveCoordinateRepresentation_closedSubscheme : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : Y ⟶ Z) (N : LB Y) (ty : σ → N.Sec), ProjRep I s M th → IsClosedImmersion i → N.IsLB → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ i) v) → ProjRep (idealOf (i ≫ s) N ty (𝟙 Y)) (i ≫ s) N ty := by
  first | exact @GlobalTheory.ZM.ClosedCoord.projRep_closed | exact GlobalTheory.ZM.ClosedCoord.projRep_closed | (intros; apply GlobalTheory.ZM.ClosedCoord.projRep_closed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.lineBundle_trivial_iso_descend_field : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), Smooth p₀ → IsProper p₀ → GeometricallyConnected p₀ → IsPullback φ p p₀ (spMap i) → (∀ M : LB X₀, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) ∧ ∀ M N : LB X₀, M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → LBIso M N := by
  first | exact @GlobalTheory.lb_gen_iso_descend_field | exact GlobalTheory.lb_gen_iso_descend_field | (intros; apply GlobalTheory.lb_gen_iso_descend_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_descent_of_morphisms_to_subfield : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀ := by
  first | exact @GlobalTheory.morphisms_descend_to_large_subfield | exact GlobalTheory.morphisms_descend_to_large_subfield | (intros; apply GlobalTheory.morphisms_descend_to_large_subfield <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.exists_fg_subalgebra_grpObj_model : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (X : Scheme.{0}) (p : X ⟶ Sp k) (φ : A.left ⟶ X) (F : Finset V), Smooth p → IsSeparated p → QuasiCompact p → IsPullback φ A.hom p (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (A₀ : Over (Sp R)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (ψ : A.left ⟶ A₀.left), (F : Set V) ⊆ R ∧ R.FG ∧ Smooth A₀.hom ∧ IsSeparated A₀.hom ∧ QuasiCompact A₀.hom ∧ IsGrpPullback A A₀ (spMap R.val.toRingHom) ψ := by
  first | exact @GlobalTheory.grpObj_descends_to_fg_subalgebra | exact GlobalTheory.grpObj_descends_to_fg_subalgebra | (intros; apply GlobalTheory.grpObj_descends_to_fg_subalgebra <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.exists_iso_pullback_over_fg_subalgebra : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (P Q T : Scheme.{0}) (p : P ⟶ Sp k) (q : Q ⟶ Sp k) (t : T ⟶ Sp V) (τ : T ⟶ P) (τ' : T ⟶ Q), Smooth p → IsSeparated p → QuasiCompact p → Smooth q → IsSeparated q → QuasiCompact q → IsPullback τ t p (spMap (algebraMap k V)) → IsPullback τ' t q (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (e : pullback p (spMap (algebraMap k R)) ≅ pullback q (spMap (algebraMap k R))), R.FG ∧ e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ ∀ σ : T ⟶ pullback p (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = τ → σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom → σ ≫ e.hom ≫ pullback.fst _ _ = τ' := by
  first | exact @GlobalTheory.smooth_models_iso_over_fg_subalgebra | exact GlobalTheory.smooth_models_iso_over_fg_subalgebra | (intros; apply GlobalTheory.smooth_models_iso_over_fg_subalgebra <;> assumption)
end
