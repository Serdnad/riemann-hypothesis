module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

theorem cotMap_list_prod {S : Scheme.{0}} {T G : Over S} [GrpObj G] [QuasiSeparated G.hom] {s : 𝟙_ (Over S) ⟶ T} :
    ∀ {m : ℕ} (z : Fin m → (T ⟶ G)) (hz : ∀ i, s ≫ z i = η) (h : s ≫ (List.ofFn z).prod = η),
      cotMap (List.ofFn z).prod h = ∑ i, cotMap (z i) (hz i)
  | 0, z, hz, h => by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact cotMap_eq_zero (by rw [List.ofFn_zero, List.prod_nil, Hom.one_def]) _
  | m + 1, z, hz, h => by
    have e : (List.ofFn z).prod = z 0 * (List.ofFn fun i : Fin m => z i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    have h₁ : (η : 𝟙_ (Over S) ⟶ G) = 1 := by rw [Hom.one_def]; simp
    have h' : s ≫ (List.ofFn fun i : Fin m => z i.succ).prod = η := by
      have := h
      rw [e, MonObj.comp_mul, hz 0, h₁, _root_.one_mul] at this
      exact this.trans h₁.symm
    rw [Fin.sum_univ_succ, ← cotMap_list_prod (fun i : Fin m => z i.succ) (fun i => hz _) h',
      ← cotMap_mul (hz 0) h' (e ▸ h)]
    congr 1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
variable {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X}
variable {G' : Over (Sp k)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}

theorem exists_fibre_vector (hp : IsGrpPullback G' t.G x φ) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ y : specO k (DualNumber k) ⟶ G', epsZero k ≫ y = η ∧ y.left ≫ φ = v := by
  refine ⟨Over.homMk (hp.1.lift v _ hv.1) (hp.1.lift_snd _ _ _), Over.OverMorphism.ext (hp.1.hom_ext ?_ ?_),
    hp.1.lift_fst _ _ _⟩
  · refine (Category.assoc _ _ _).trans ((congrArg (sec (epsZero k) ≫ ·) (hp.1.lift_fst _ _ _)).trans ?_)
    exact (epsZero_comp_of_isTanAtG t hv).trans (unitSec_comp hp).symm
  · exact (Over.w _).trans (Over.w _).symm

theorem tanForm_eq_fibre (hp : IsGrpPullback G' t.G x φ) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v)
    {y : specO k (DualNumber k) ⟶ G'} (hy : epsZero k ≫ y = η) (e : y.left ≫ φ = v) :
    tanForm t hv = omegaBase hp ≫ cotMap y hy ≫ (epsIso k).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso k).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_
  have k₁ := le_of_sq (unitSec_comp hp) (le_refl (unitSec t.G ⁻¹ᵁ W)) le_rfl
  have k₂ := le_of_sq (epsZero_comp_of_isTanAtG t hv) (le_refl (unitSec t.G ⁻¹ᵁ W)) le_rfl
  have k₃ := (le_preimage_of_comp e).2 (le_refl (v ⁻¹ᵁ W))
  refine (baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl
    k₂ le_rfl a).trans (Eq.symm ?_)
  refine (congrArg ((cotMap y hy).app _) (omegaBase_dUnit hp le_rfl le_rfl k₁ le_rfl a)).trans ?_
  exact (cotMap_d y hy k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE e _ _ _ a))

theorem tanEv_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V),
    ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i)) (cf : Fin m → k)
      (w : Sp (DualNumber k) ⟶ t.G.left) (hw : IsTanAtG t x w), IsCombAtG t x v cf w →
      ∀ s : Γ(GlobalTheory.LieVB.omega t.G, V), tanEv t hw h s = ∑ i, cf i * tanEv t (hv i) h s := by
  rintro E _ _ _ H X t k _ x V h m v hv cf w hw ⟨u, hu, hw'⟩ s
  have hp := isGrpPullback_pullback t.G x
  have := t.semi
  have : QuasiSeparated ((Over.pullback x).obj t.G).hom := MorphismProperty.of_isPullback hp.1 inferInstance
  choose y hy ey using fun i => exists_fibre_vector t hp (hv i)
  obtain ⟨yw, hyw, eyw⟩ := exists_fibre_vector t hp hw
  let z := fun i => ptMap (dualScale (cf i)) ≫ y i
  have hz (i : Fin m) : epsZero k ≫ z i = η := by
    rw [← Category.assoc, epsZero_dualScale, hy]
  have hu' : u = fun i => pushHom hp _ (z i) := funext fun i => Over.OverMorphism.ext <| by
    refine (hu i).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    rw [ey]
    rfl
  have hprod : yw = (List.ofFn z).prod := by
    refine Over.OverMorphism.ext (hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    refine eyw.trans (hw'.symm.trans ?_)
    rw [hu']
    exact (congrArg (fun q => q.left) ((map_list_prod (pushHom hp (specO k (DualNumber k))) (List.ofFn z)).trans
      (congrArg List.prod List.map_ofFn))).symm
  subst hprod
  let σ := (omegaBase hp).app ⊤ (pullbackSections x (omega t.G) h s)
  let F : (conormal (unitSec ((Over.pullback x).obj t.G)) ⟶ conormal (sec (epsZero k))) →+ k :=
    AddMonoidHom.mk' (fun α => (Scheme.ΓSpecIso (.of k)).hom ((epsIso k).hom.app ⊤ (α.app ⊤ σ))) fun α β =>
      (congrArg (Scheme.ΓSpecIso (.of k)).hom (map_add ((epsIso k).hom.app ⊤).hom (α.app ⊤ σ) (β.app ⊤ σ))).trans
        (map_add _ _ _)
  have hF {v' : Sp (DualNumber k) ⟶ t.G.left} (hv' : IsTanAtG t x v') {y'} (hy' : epsZero k ≫ y' = η)
      (e : y'.left ≫ pullback.fst t.G.hom x = v') : tanEv t hv' h s = F (cotMap y' hy') := by
    rw [tanEv, tanForm_eq_fibre t hp hv' hy' e]
    rfl

  rw [hF hw hyw eyw, cotMap_list_prod z hz, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := cotMap_comp (hy i) (epsZero_dualScale (cf i)) rfl (hz i)
  rw [cotMap_dualScale] at e
  rw [hF (hv i) (hy i) (ey i), ← e]
  refine (congrArg (Scheme.ΓSpecIso (.of k)).hom
    ((epsIso k).hom.app_smul (cst k (cf i)) ((cotMap (y i) (hy i)).app ⊤ σ))).trans ?_
  refine (map_mul _ _ _).trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

end GlobalTheory.LocM
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.LieMet
  GlobalTheory.LocM
open GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_self)
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.TanPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
  (h' : IsGrpPullback G' t.G x φ)

theorem toUnit_specO_left : (toUnit (specO R R)).left = 𝟙 (Sp R) := by
  rw [Over.toUnit_left]
  exact Spec.map_id _

include h'

theorem exists_lieG {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ p : LieG G', p.1.left ≫ φ = v := by
  let p : specO R (DualNumber R) ⟶ G' :=
    Over.homMk (h'.1.lift v (specO R (DualNumber R)).hom hv.1) (h'.1.lift_snd _ _ _)
  have hp : p.left ≫ φ = v := h'.1.lift_fst _ _ _
  refine ⟨⟨p, Over.OverMorphism.ext (h'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩, hp⟩
  rw [Over.comp_left, Over.comp_left, toUnit_specO_left, Category.assoc, hp, Category.assoc]
  exact (epsZero_comp_of_isTanAtG t hv).trans ((unitSec_comp h').symm.trans (Category.id_comp _).symm)

theorem isTanAtG_lieG (p : LieG G') : IsTanAtG t x (p.1.left ≫ φ) := by
  constructor
  · rw [Category.assoc, h'.1.w, ← Category.assoc]
    exact congrArg (· ≫ x) (Over.w p.1)
  · rw [← Category.assoc, Hom.one_def, Over.comp_left, Over.toUnit_left]
    exact (congrArg (· ≫ φ) (sec_epsZero_comp p)).trans (unitSec_comp h')

theorem tanForm_eq (p : LieG G') {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) (hp : p.1.left ≫ φ = v) :
    tanForm t hv = omegaBase h' ≫ cotMap p.1 (epsZero_comp p) ≫ (epsIso R).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso R).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_
  have k₁ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ unitSec G' ⁻¹ᵁ φ ⁻¹ᵁ W :=
    (le_preimage_of_comp (unitSec_comp h')).2 le_rfl
  have k₂ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ sec (epsZero R) ⁻¹ᵁ v ⁻¹ᵁ W :=
    (le_preimage_of_comp (epsZero_comp_of_isTanAtG t hv)).2 le_rfl
  have k₃ : v ⁻¹ᵁ W ≤ p.1.left ⁻¹ᵁ φ ⁻¹ᵁ W := (le_preimage_of_comp hp).2 le_rfl
  refine (baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero R)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl k₂
    le_rfl a).trans ?_
  refine Eq.symm ((congrArg ((cotMap p.1 (epsZero_comp p)).app _)
    (omegaBase_dUnit h' le_rfl le_rfl k₁ le_rfl a)).trans ?_)
  exact (cotMap_d p.1 (epsZero_comp p) k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE hp _ _ _ a))

theorem tanEv_eq (p : LieG G') {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) (hp : p.1.left ≫ φ = v)
    {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(omega t.G, V)) :
    tanEv t hv h s = (Scheme.ΓSpecIso (.of R)).hom
      (dualApp (tangent p) le_top ((omegaBase h').app ⊤ (pullbackSections x (omega t.G) h s))) := by
  rw [tanEv, tanForm_eq h' p hv hp]
  rfl

theorem exists_equiv_of_isGrpPullback {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} {s : Fin n → Γ(omega t.G, V)}
    (hs : VB.IsFrame s) : ∃ Φ : TanM x t.G ≃ₗ[R] (Fin n → R), ∀ v b, Φ v b = tanEv t (isTan_tv v) h (s b) := by
  have := t.semi
  have : QuasiSeparated G'.hom := MorphismProperty.of_isPullback h'.1 inferInstance
  let e : Fin n → Γ(omega G', ⊤) := fun b => (omegaBase h').app ⊤ (pullbackSections x (omega t.G) h (s b))
  have he : VB.IsFrame e := by
    have h₁ := ((hs.pullback x).res h).map_iso (omegaBase h')
    have h₂ (b : Fin n) : resM _ h (pullbackSections x (omega t.G) le_rfl (s b)) =
        pullbackSections x (omega t.G) h (s b) := QCoh.res_pullbackSections x _ _ _ _
    simpa only [h₂] using h₁
  have hc := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom
  let Φ : TanM x t.G →ₗ[R] (Fin n → R) :=
    { toFun := fun v b => tanEv t (isTan_tv v) h (s b)
      map_add' := fun v w => funext fun b => by
        obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
        obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
        have hpq : (p.1 * q.1).left ≫ φ = (tv (v + w)).left :=
          (h'.2 _ p.1 q.1 (tv v) (tv w) hp.symm hq.symm).symm
        rw [Pi.add_apply, tanEv_eq h' p _ hp, tanEv_eq h' q _ hq,
          tanEv_eq h' ⟨_, OmegaGlobal.fst_mul p q⟩ _ hpq, tangent_mul, dualApp_add, LinearMap.add_apply, map_add]
      map_smul' := fun a v => funext fun b => by
        obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
        have ha : (dualScale a).toRingHom = epsScaleR a := by
          ext y <;> simp [dualScale, epsScaleR]
        have hpq : (ptMap (dualScale a) ≫ p.1).left ≫ φ = (tv (a • v)).left := by
          rw [Over.comp_left, Category.assoc, hp]
          exact congrArg (fun r => spMap r ≫ (tv v).left) ha
        rw [Pi.smul_apply, tanEv_eq h' p _ hp, tanEv_eq h' ⟨_, OmegaGlobal.fst_scale a p⟩ _ hpq, tangent_scale]
        simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LB.resG_self,
          Iso.inv_hom_id_apply, RingHom.id_apply] }
  refine ⟨LinearEquiv.ofBijective Φ ⟨fun v w hvw => ?_, fun c => ?_⟩, fun _ _ => rfl⟩
  · obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
    obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
    obtain rfl : p = q := tangent_injective R G' (he.dual_ext le_rfl fun b => by
      rw [resM_self]
      exact hc.1 ((tanEv_eq h' p _ hp h (s b)).symm.trans
        ((congrFun hvw b).trans (tanEv_eq h' q _ hq h (s b)))))
    exact tan_ext (hp.symm.trans hq)
  · classical
    let coord (i : Fin n) : Γ(VB.dual (omega G'), ⊤) :=
      VB.homMk (fun _ h => (he.basis h).coord i) fun _ _ h h' s => he.repr_resM h h' s i
    have hcoord (i j : Fin n) : dualApp (coord i) le_rfl (e j) = if j = i then 1 else 0 := by
      change (he.basis le_rfl).repr (e j) i = _
      rw [← resM_self (F := omega G') (h := le_rfl) (e j), ← he.basis_apply le_rfl j,
        Module.Basis.repr_self, Finsupp.single_apply]
    let l : Γ(VB.dual (omega G'), ⊤) := ∑ i, cst R (c i) • coord i
    obtain ⟨p, hp⟩ := TangentSurj.tangent_surjective R G' l
    refine ⟨tanOf (isTanAtG_lieG h' p), funext fun b => (tanEv_eq h' p _ rfl h (s b)).trans ?_⟩
    rw [hp]
    have k : dualApp l le_rfl (e b) = cst R (c b) := by
      dsimp [l]
      rw [dualApp_sum, LinearMap.sum_apply]
      simp [dualApp_smul, hcoord]
    rw [k, Iso.inv_hom_id_apply]

omit h'

theorem exists_tanM_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (n : ℕ)
    (s : Fin n → Γ(omega t.G, V)) (hs : VB.IsFrame s) :
    ∃ Φ : TanM x t.G ≃ₗ[R] (Fin n → R), ∀ v b, Φ v b = tanEv t (isTan_tv v) h (s b) :=
  exists_equiv_of_isGrpPullback (isGrpPullback_pullback t.G x) h hs

end GlobalTheory.LocM.TanPair
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X} {v : Sp (DualNumber k) ⟶ t.G.left}

theorem preimage_le_of_isTanAtG (hv : IsTanAtG t x v) {V : X.Opens} {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) :
    (specO k (DualNumber k)).hom ⁻¹ᵁ T ≤ v ⁻¹ᵁ W := by
  intro y hy
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero y
  have h₁ : s ∈ (sec (epsZero k) ≫ (specO k (DualNumber k)).hom) ⁻¹ᵁ T := hy
  rw [sec_hom] at h₁
  have h₂ : s ∈ (x ≫ unitSec t.G) ⁻¹ᵁ W := hW (hT h₁)
  rw [← epsZero_comp_of_isTanAtG t hv] at h₂
  exact h₂

theorem tanForm_dUnit (hv : IsTanAtG t x v) {V : X.Opens} {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) (f : Γ(t.G.left, W))
    (a b : Γ(Sp k, T))
    (e : (v.appLE W _ (preimage_le_of_isTanAtG t hv hW hT) f :
        Γ((specO k (DualNumber k)).left, (specO k (DualNumber k)).hom ⁻¹ᵁ T)) =
      (specO k (DualNumber k)).hom.appLE T _ le_rfl a +
        (specO k (DualNumber k)).hom.appLE T _ le_rfl b * resG _ le_top (epsFn k)) :
    (tanForm t hv).app T (pullbackSections x (omega t.G) hT (dUnit t.G hW f)) = b := by
  have hV : T ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  have c := baseMap_d (sec_hom (MonObj.one (X := t.G))) (sec_hom (epsZero k)) hv.1
    (epsZero_comp_of_isTanAtG t hv) hW hT hV (preimage_le_of_isTanAtG t hv hW hT) f
  refine (congrArg ((epsIso k).hom.app T) c).trans ?_
  rw [e, map_add (f := _), d_base, zero_add, d_mul, d_base,
    smul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl, GlobalTheory.LB.resG_self, d_resG,
    ← resM_d _ (le_preimage_top _ ⊤) le_top, Scheme.Modules.Hom.app_smul, app_resM, epsIso_d]
  exact (congrArg (b * ·) (map_one (resG (Sp k) (le_top : T ≤ ⊤)))).trans (_root_.mul_one b)

variable {k' : Type} [CommRing k'] (φ : k →+* k')

theorem spMap_dualMap_comp : spMap (Formalism.L2.Pj.dualMap φ) ≫ (specO k (DualNumber k)).hom =
    (specO k' (DualNumber k')).hom ≫ spMap φ := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_dualMap_epsFn :
    (spMap (Formalism.L2.Pj.dualMap φ)).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn k) = epsFn k' := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Formalism.L2.Pj.dualMap φ))) DualNumber.eps).symm.trans ?_
  refine congrArg (Scheme.ΓSpecIso (.of (DualNumber k'))).inv.hom ?_
  change Formalism.L2.Pj.dualMap φ DualNumber.eps = _
  ext <;> simp [Formalism.L2.Pj.dualMap]

theorem tanForm_baseChange {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (hv : IsTanAtG t x v)
    (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V)
    (s : Γ(omega t.G, V)) :
    ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) =
      (spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) : Γ(Sp k, ⊤)) := by
  have := t.semi
  have key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧
      resG (Sp k') (le_top : T' ≤ ⊤) ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) =
      resG (Sp k') (le_top : T' ≤ ⊤) ((spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) : Γ(Sp k, ⊤))) := by
    obtain ⟨U, W, hU, hle, c⟩ := exists_isChart (sec_hom (MonObj.one (X := t.G))) (V := V)
      (x := x (spMap φ y.1)) (h trivial)
    obtain ⟨T, hT, hyT, hTU⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U) (spMap φ y.1) hU
    obtain ⟨f, hf⟩ := c.d_surjective (sec_hom (MonObj.one (X := t.G))) (resM _ hle s)
    have hf' : dUnit t.G c.le f = resM (omega t.G) hle s := hf
    have hTU' : spMap φ ⁻¹ᵁ T ≤ (spMap φ ≫ x) ⁻¹ᵁ U := (spMap φ).preimage_mono hTU
    obtain ⟨⟨a, b⟩, e⟩ := (bijective_add_mul_epsFn k T hT).2
      (v.appLE W _ (preimage_le_of_isTanAtG t hv c.le hTU) f)
    have e₁ := tanForm_dUnit t hv c.le hTU f a b e.symm
    have kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        spMap (Formalism.L2.Pj.dualMap φ) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
      (le_preimage_of_comp (spMap_dualMap_comp φ)).2 le_rfl
    have kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        ((specO k' (DualNumber k')).hom ≫ spMap φ) ⁻¹ᵁ T := le_rfl
    have n (z : Γ(Sp k, T)) : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk
        ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) =
        (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap φ).appLE T _ le_rfl z) :=
      (appLE_appLE (spMap_dualMap_comp φ) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm
    have n' : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk (resG _ le_top (epsFn k)) =
        resG _ le_top (epsFn k') :=
      (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans
        (congrArg _ (spMap_dualMap_epsFn φ)))
    have e₂ := tanForm_dUnit t hv' c.le hTU' f ((spMap φ).appLE T _ le_rfl a)
      ((spMap φ).appLE T _ le_rfl b) (by
        refine (appLE_appLE rfl (preimage_le_of_isTanAtG t hv c.le hTU) kk _ f).symm.trans ?_
        refine (congrArg ((spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk) e.symm).trans ?_
        refine (map_add _ _ _).trans ?_
        exact congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))
    rw [hf', QCoh.pullbackSections_res] at e₁ e₂
    refine ⟨spMap φ ⁻¹ᵁ T, hyT, ?_⟩
    refine (app_resM (tanForm t hv') le_top _).symm.trans ?_
    rw [QCoh.res_pullbackSections, e₂, ← e₁]
    refine .trans ?_ ((appLE_resG (spMap φ) (le_top : T ≤ ⊤) le_rfl _).trans
      (resG_appLE (spMap φ) le_top (le_preimage_top _ _) _).symm)
    refine congrArg _ ?_
    refine .trans ?_ (app_resM (tanForm t hv) le_top _)
    rw [QCoh.res_pullbackSections]
  choose T hT hs using key
  exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs

theorem tanEv_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (v : Sp (DualNumber k) ⟶ t.G.left) (hv : IsTanAtG t x v) (k' : Type) [CommRing k'] (φ : k →+* k') (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) (s : Γ(GlobalTheory.LieVB.omega t.G, V)), tanEv t hv' h' s = φ (tanEv t hv h s) := by
  intro E _ _ _ H X t k _ x V h v hv k' _ φ hv' h' s
  refine (congrArg (Scheme.ΓSpecIso (.of k')).hom (tanForm_baseChange t φ h hv hv' h' s)).trans ?_
  refine (congrArg (Scheme.ΓSpecIso (.of k')).hom (appLE_top (spMap φ) _)).trans ?_
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) _)

end GlobalTheory.LocM
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TraitOrder

theorem idlAlong_eq_map {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X)
    (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
    idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
  have hx : χ (closedPoint R) ∈ U.1 := hle trivial
  unfold idlAlong
  rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
  congr 2

theorem idlAlong_comp {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
  have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
  rw [idlAlong_eq_map J χ ⟨U, hU⟩ hle, idlAlong_eq_map J _ ⟨U, hU⟩ hle', Ideal.map_map]
  congr 1
  have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
  rfl

theorem map_injective {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Injective f) [IsLocalHom f] {I J : Ideal R}
    (h : I.map f = J.map f) : I = J := by
  letI := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Module.Flat R S := inferInstance
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) J]
  exact congrArg _ h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) (m : SABMap t' t f) (m' : SABMap t'' t' g) : Nonempty (SABMap t'' t h) :=
  e ▸ ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m').choose⟩

theorem cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) (m : SABMap t' t f) (n : SABMap t'' t h) : Nonempty (SABMap t'' t' g) := by
  subst e
  exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n).choose⟩

end GlobalTheory.TraitOrder
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

theorem exists_frPt_ptF_of_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z L _ φ z x g hs hx
  letI := φ.toAlgebra
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (Z := Z) z hs hx g
  refine ⟨y, pullback.hom_ext ?_ ?_, fun τ i => ⟨w τ i, (hw τ i).2⟩⟩
  · exact (pullback.lift_fst _ _ _).trans hy
  · exact (pullback.lift_snd _ _ _).trans hs.symm

end GlobalTheory.ShFam
end
end
