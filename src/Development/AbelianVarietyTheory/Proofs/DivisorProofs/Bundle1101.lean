module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle610
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.VB GlobalTheory.Conormal
open GlobalTheory.KS.DerMorK (deformHom hom_ext_appLE)

namespace GlobalTheory.LieVB.TangentSurj

section General

variable {S X T : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (p : T ⟶ S) (ε : Γ(T, ⊤)) (hε : ε * ε = 0)
  (D : Der π e (structureModule S))

def val {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : Γ(X, W) →+ Γ(S, V) := D.app h

theorem val_mul {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (f g : Γ(X, W)) :
    val D h (f * g) = e.appLE W V h f * val D h g + e.appLE W V h g * val D h f :=
  D.app_mul h f g

theorem val_base {W : X.Opens} {V U : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (k : W ≤ π ⁻¹ᵁ U) (a : Γ(S, U)) :
    val D h (π.appLE U W k a) = 0 := D.app_base h k a

theorem val_one {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : val D h 1 = 0 := by
  simpa using val_base D (U := ⊤) h le_top 1

theorem val_res {W W' : X.Opens} (k : W' ≤ W) (f : Γ(X, W)) :
    val D (le_refl (e ⁻¹ᵁ W')) (resG X k f) = resG S (e.preimage_mono k) (val D le_rfl f) :=
  (D.app_res _ k f).trans (D.res_app le_rfl (e.preimage_mono k) f).symm


include hε in
theorem res_sq (U : T.Opens) : resG T (le_top : U ≤ ⊤) ε * resG T (le_top : U ≤ ⊤) ε = 0 := by
  rw [← map_mul, hε, map_zero]

def psi (W : X.Opens) : Γ(X, W) →+* Γ(T, p ⁻¹ᵁ e ⁻¹ᵁ W) where
  toFun f := p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) +
    p.appLE _ _ le_rfl (val D le_rfl f) * resG T le_top ε
  map_one' := by simp only [val_one, map_one, map_zero, zero_mul, add_zero]
  map_mul' f g := by
    simp only [val_mul, map_mul, map_add (f := _)]
    linear_combination -(p.appLE _ _ le_rfl (val D le_rfl f) * p.appLE _ _ le_rfl (val D le_rfl g)) *
      res_sq ε hε (p ⁻¹ᵁ e ⁻¹ᵁ W)
  map_zero' := by simp only [map_zero, zero_mul, add_zero]
  map_add' f g := by
    simp only [map_add (f := _)]
    ring

theorem psi_apply (W : X.Opens) (f : Γ(X, W)) : psi p ε hε D W f =
    p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) +
      p.appLE _ _ le_rfl (val D le_rfl f) * resG T le_top ε := rfl

theorem psi_nat (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)) :
    psi p ε hε D W' (resG X h f) =
      resG T (p.preimage_mono (e.preimage_mono h)) (psi p ε hε D W f) := by
  rw [psi_apply, psi_apply, val_res, map_add (f := _), map_mul, resG_resG, resG_appLE, resG_appLE,
    appLE_resG e, appLE_resG p, ← resG_appLE e (e.preimage_mono h) le_rfl, appLE_resG p]

theorem psi_nil (W : X.Opens) (f : Γ(X, W)) :
    IsNilpotent (psi p ε hε D W f - p.appLE _ _ le_rfl (e.appLE W _ le_rfl f)) := by
  refine ⟨2, ?_⟩
  rw [psi_apply]
  linear_combination (p.appLE _ _ le_rfl (val D le_rfl f)) ^ 2 * res_sq ε hε (p ⁻¹ᵁ e ⁻¹ᵁ W)

def deform : T ⟶ X :=
  deformHom (p ≫ e) (psi p ε hε D) (psi_nat p ε hε D) fun W f => by
    have h : ((p ≫ e).app W).hom f = p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) := by
      rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app]; rfl
    rw [h]
    exact psi_nil p ε hε D W f

theorem deform_appLE (W : X.Opens) {U : T.Opens} (k : U ≤ p ⁻¹ᵁ e ⁻¹ᵁ W) (f : Γ(X, W)) :
    (deform p ε hε D).appLE W U k f = resG T k (psi p ε hε D W f) := rfl

theorem deform_comp (he : e ≫ π = 𝟙 S) : deform p ε hε D ≫ π = p := by
  have h₀ : p ≫ e ≫ π = p := by rw [he, Category.comp_id]
  refine hom_ext_appLE (congr(($h₀).base)) fun U k => ?_
  ext a
  have k' : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ e ⁻¹ᵁ π ⁻¹ᵁ U := k
  refine (appLE_appLE (f := deform p ε hε D) rfl le_rfl k' k a).symm.trans ?_
  rw [deform_appLE, psi_apply, val_base, map_zero, zero_mul, add_zero,
    appLE_base he _ _ ((le_preimage_iff he).1 le_rfl), appLE_resG, resG_appLE,
    Scheme.Hom.appLE_eq_app]

theorem comp_deform {z : S ⟶ T} (hz : z ≫ p = 𝟙 S) (h0 : z.appLE ⊤ ⊤ le_top ε = 0) :
    z ≫ deform p ε hε D = e := by
  have h₀ : z ≫ p ≫ e = e := by rw [reassoc_of% hz]
  refine hom_ext_appLE (congr(($h₀).base)) fun W k => ?_
  ext f
  have k' : e ⁻¹ᵁ W ≤ z ⁻¹ᵁ p ⁻¹ᵁ e ⁻¹ᵁ W := k
  refine (appLE_appLE (f := z) (g := deform p ε hε D) (V := p ⁻¹ᵁ e ⁻¹ᵁ W)
    rfl le_rfl k' k f).symm.trans ?_
  rw [deform_appLE, resG_self, psi_apply, map_add (f := _), map_mul, appLE_resG,
    ← resG_appLE z le_top le_top ε, h0, map_zero, mul_zero, add_zero,
    appLE_base hz _ _ le_rfl, resG_self, Scheme.Hom.appLE_eq_app]

end General

variable (O : Type) [CommRing O]

theorem epsFn_sq : epsFn O * epsFn O = 0 := by
  have h := map_mul (Scheme.ΓSpecIso (.of (DualNumber O))).inv.hom DualNumber.eps DualNumber.eps
  rw [DualNumber.eps_mul_eps, map_zero] at h
  exact h.symm

theorem epsZero_epsFn : (sec (epsZero O)).appLE ⊤ ⊤ le_top (epsFn O) = 0 := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O O).toRingHom)) DualNumber.eps).symm.trans ?_
  exact (congrArg (Scheme.ΓSpecIso (.of O)).inv.hom (DualNumber.fst_eps (R := O))).trans
    (map_zero _)

theorem tangent_surjective (O : Type) [CommRing O] (G : Over (Sp O)) [GrpObj G] :
    Function.Surjective (tangent : LieG G → Γ(Lie G, ⊤)) := by
  intro l
  let D := lieEquivDer G l
  let x : specO O (DualNumber O) ⟶ G :=
    Over.homMk (deform (specO O (DualNumber O)).hom (epsFn O) (epsFn_sq O) D)
      (deform_comp _ _ _ D (sec_hom η[G]))
  have hx : ptMap (TrivSqZeroExt.fstHom O O O) ≫ x = toUnit (specO O O) ≫ η[G] := by
    have h : (toUnit (specO O O)).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    ext1
    simp only [Over.comp_left, h]
    exact (comp_deform _ _ (epsFn_sq O) D (sec_hom (epsZero O)) (epsZero_epsFn O)).trans
      (Category.id_comp _).symm
  refine ⟨⟨x, hx⟩, (homGlobalEquiv _ _).injective (omega_hom_ext fun W f => ?_)⟩
  refine dualApp_tangent_dUnit ⟨x, hx⟩ le_rfl f
    ((le_preimage_iff (sec_hom (epsZero O))).2 le_rfl) le_rfl le_rfl
    ((unitSec G).appLE W _ le_rfl f) (val D le_rfl f) ?_
  exact (deform_appLE _ _ (epsFn_sq O) D W le_rfl f).trans (resG_self _ _)

end GlobalTheory.LieVB.TangentSurj
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.BigFieldChange

theorem isBig_pull_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k)
    (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q →
    topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB →
    ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  intro k E _ _ _ Y X p q π H hp hq hd L hL
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := hp
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hL' := LB.isLB_pull hL π
  have e : ∀ m : ℕ, lbH0 E (lbPow (L.pull π) m) = lbH0 k (lbPow L m) := fun m => by
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL' m) (LB.isLB_pull (isLB_lbPow hL m) π)
      (by rw [cls_lbPow hL', cls_pull hL, cls_pull (isLB_lbPow hL m), cls_lbPow hL, map_nsmul])]
    exact FieldChangeInter.hdim_pull H (isLB_lbPow hL m) 0
  constructor
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL, fun m => finite_coh_zero_twist_of_isProjOver (f := p) (fun _ => rfl) hp (isLB_lbPow hL m),
      D, hd.symm.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m))⟩
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL', fun m => finite_coh_zero_twist_of_isProjOver (f := q) (fun _ => rfl) hq (isLB_lbPow hL' m),
      D, hd.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m).symm)⟩

end GlobalTheory.BigFieldChange
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smooth_lifts_over_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B₀ _ _ hsm
  obtain ⟨C₀, _, _, i, r, hstd, hri⟩ := GlobalTheory.T.exists_standardSmooth_retract_of_smooth R₀ B₀ hsm
  obtain ⟨C, _, _, p', hs', hp', hker', hC⟩ := GlobalTheory.T.standardSmooth_lift_over_sqZero_thickening R R₀ I hI π hπ hk C₀ hstd
  exact GlobalTheory.T.exists_smoothLift_of_retract_squareZero R R₀ I hI π hπ hk C C₀ p' hs' hp' hker' B₀ i r hri

end GlobalTheory
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.TotFracAway

variable (R : Type) [CommRing R]

structure Idx where

  val : R
  mem : val ∈ nonZeroDivisors R

instance : Preorder (Idx R) where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

instance : IsDirected (Idx R) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.val * b.val, Submonoid.mul_mem _ a.mem b.mem⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance : Nonempty (Idx R) := ⟨⟨1, Submonoid.one_mem _⟩⟩

variable {R}

theorem isUnit_of_dvd {a b : R} (h : a ∣ b) : IsUnit (algebraMap R (Localization.Away b) a) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit b)

def tr {a b : R} (h : a ∣ b) : Localization.Away a →+* Localization.Away b :=
  Localization.awayLift (algebraMap R _) a (isUnit_of_dvd h)

theorem tr_comp {a b : R} (h : a ∣ b) : (tr h).comp (algebraMap R _) = algebraMap R _ :=
  IsLocalization.Away.lift_comp a (isUnit_of_dvd h)

theorem away_ext {a : R} {S : Type} [CommRing S] {f g : Localization.Away a →+* S}
    (h : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h


variable (R) in
def diag : Idx R ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away a.val)
  map {a b} h := CommRingCat.ofHom (tr (leOfHom h : a.val ∣ b.val))
  map_id a := by
    ext1
    refine away_ext ?_
    simp [tr_comp]
  map_comp {a b c} f g := by
    ext1
    refine away_ext ?_
    simp [RingHom.comp_assoc, tr_comp]

def toFrac (a : Idx R) : Localization.Away a.val →+* FractionRing R :=
  Localization.awayLift (algebraMap R _) a.val
    (IsLocalization.map_units (FractionRing R) (⟨a.val, a.mem⟩ : nonZeroDivisors R))

theorem toFrac_comp (a : Idx R) : (toFrac a).comp (algebraMap R _) = algebraMap R (FractionRing R) :=
  IsLocalization.Away.lift_comp a.val
    (IsLocalization.map_units (FractionRing R) (⟨a.val, a.mem⟩ : nonZeroDivisors R))


variable (R) in
def cocone : Cocone (diag R) where
  pt := CommRingCat.of (FractionRing R)
  ι :=
    { app := fun a => CommRingCat.ofHom (toFrac a)
      naturality := fun a b h => by
        ext1
        refine away_ext ?_
        simp [diag, RingHom.comp_assoc, tr_comp, toFrac_comp] }

def idx1 : Idx R := ⟨1, Submonoid.one_mem _⟩

theorem desc_unit (s : Cocone (diag R)) (y : nonZeroDivisors R) :
    IsUnit (((s.ι.app idx1).hom.comp (algebraMap R (Localization.Away (1 : R)))) y) := by
  let b : Idx R := ⟨y.1, y.2⟩
  have hw := s.w (homOfLE (show (idx1 : Idx R) ≤ b from one_dvd _))
  rw [← hw]
  change IsUnit ((s.ι.app b).hom ((tr (one_dvd y.1)) (algebraMap R _ y.1)))
  rw [← RingHom.comp_apply (tr _), tr_comp]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y.1) y.1).map (s.ι.app b).hom


variable (R) in
def isColim : IsColimit (cocone R) where
  desc s := CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) (desc_unit s))
  fac s a := by
    have hw := s.w (homOfLE (show (idx1 : Idx R) ≤ a from one_dvd _))
    ext1
    change (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) (desc_unit s)).comp (toFrac a) = (s.ι.app a).hom
    refine away_ext ?_
    rw [RingHom.comp_assoc, toFrac_comp, IsLocalization.lift_comp, ← hw]
    ext b
    exact congrArg (s.ι.app a).hom (DFunLike.congr_fun (tr_comp (one_dvd a.val)) b)
  uniq s m hm := by
    ext1
    change m.hom = IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) (desc_unit s)
    refine IsLocalization.ringHom_ext (S := FractionRing R) (nonZeroDivisors R) ?_
    rw [IsLocalization.lift_comp, ← hm idx1]
    ext b
    exact congrArg m.hom (DFunLike.congr_fun (toFrac_comp idx1) b).symm

theorem spMap_comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A') (g : A' →+* A'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory.EtC.TotFracAway


open GlobalTheory.EtC.TotFracAway in
theorem GlobalTheory.EtC.classVanishesAwayNZD : ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ (n i : ℤ)
    (z : Ht q (sp R) n i), pull _ (spMap (algebraMap R (FractionRing R))) _ _ z = 0 →
    ∃ g ∈ nonZeroDivisors R, pull _ (spMap (algebraMap R (Localization.Away g))) _ _ z = 0 := by
  intro q R _ hq n i x hx
  have hB1 := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag R) (cocone R) (isColim R) n i).2
  have hq1 : IsUnit (q : Localization.Away (idx1 : Idx R).val) := by
    have := hq.map (algebraMap R (Localization.Away (idx1 : Idx R).val))
    rwa [map_natCast] at this
  have h2 : pull _ (spMap (toFrac (idx1 : Idx R))) _ _
      (pull _ (spMap (algebraMap R (Localization.Away (idx1 : Idx R).val))) _ _ x) = 0 := by
    rw [← pull_comp, ← spMap_comp, toFrac_comp]
    exact hx
  obtain ⟨k, f, hk⟩ := hB1 idx1 (pull _ (spMap (algebraMap R (Localization.Away (idx1 : Idx R).val))) _ _ x) hq1 h2
  have hf : (idx1 : Idx R).val ∣ k.val := leOfHom f
  refine ⟨k.val, k.mem, ?_⟩
  have e : algebraMap R (Localization.Away k.val) =
      (tr hf).comp (algebraMap R (Localization.Away (idx1 : Idx R).val)) := by
    rw [tr_comp]
  rw [e, spMap_comp, pull_comp]
  exact hk
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.IntDescent

theorem isIntegral_algClosure_residue (A : Type) [CommRing A] [IsLocalRing A] :
    Algebra.IsIntegral A (AlgebraicClosure (IsLocalRing.ResidueField A)) := by
  haveI : Algebra.IsIntegral A (IsLocalRing.ResidueField A) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId A (IsLocalRing.ResidueField A)) IsLocalRing.residue_surjective
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)) :=
    Algebra.IsAlgebraic.isIntegral
  exact Algebra.IsIntegral.trans (IsLocalRing.ResidueField A)

theorem isIntegral_tensor (A C B : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B]
    [Algebra.IsIntegral A C] [Algebra.IsIntegral A B] : Algebra.IsIntegral A (C ⊗[A] B) := by
  constructor
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul x y =>
      have h1 : IsIntegral A (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := C) (B := B) x) :=
        (Algebra.IsIntegral.isIntegral x).map _
      have h2 : IsIntegral A (Algebra.TensorProduct.includeRight (R := A) (A := C) (B := B) y) :=
        (Algebra.IsIntegral.isIntegral y).map _
      have := h1.mul h2
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this
  | add x y hx hy => exact hx.add hy

theorem L1 : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)],
    IsUnit (q : A) → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
    Eqv (ZMod q) (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom) (tw q i) := by
  intro q i A _ _ _ hq B _ _ _
  have hSH : SH A := ⟨inferInstance, inferInstance⟩
  obtain ⟨ζ0⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A hSH hq
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) := ζ0.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i (Spec (CommRingCat.of A)) ζ
  haveI := isIntegral_algClosure_residue A
  haveI := isIntegral_tensor A (AlgebraicClosure (IsLocalRing.ResidueField A)) B
  have hfin := GlobalTheory.T.tateTwist_finitary q i
  have hU := GlobalTheory.T.integral_strictHenselian_acyclic_finitary (ZMod q) (tw q i) hfin A B hSH
  have hU' := GlobalTheory.T.integral_strictHenselian_acyclic_finitary (ZMod q) (tw q i) hfin A (AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B) hSH
  have hbij := GlobalTheory.T.bijective_locallyConstant_comap_algClosure_tensor_of_henselian (ZMod q) A B
  exact GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) _ _ hgen (Spec (CommRingCat.of B)) _
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) _ hU hU' hbij

end GlobalTheory.EtC.IntDescent

namespace GlobalTheory.EtC


open IntDescent in
theorem cechAug_eqv_of_isIntegralHom_of_strictlyHenselian : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)), IsIntegralHom g → Surjective g → Eqv _ (cechAug g) (tw q i) := by
  intro q i A _ hSH hq Y g hg hsurj
  obtain ⟨_, _⟩ := hSH
  set Ω := AlgebraicClosure (IsLocalRing.ResidueField A)
  set u : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ω)) with hu_def
  have hpb : IsPullback (pullback.fst g u) (pullback.snd g u) g u := IsPullback.of_hasPullback g u
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ (pullback.fst g u) (pullback.snd g u) g u hpb
  have hsq : ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of Ω)) (φ : Z' ⟶ Z),
      IsIntegralHom h → IsPullback φ h' h u → Eqv (ZMod q) (sch.map φ) (tw q i) :=
    GlobalTheory.T.etaleCohomologyEquivalence_pullback_integral_affine (ZMod q) (tw q i) A Ω (fun B _ _ _ => L1 q i A hq B)
  have hEm : Eqv (ZMod q) m (tw q i) :=
    GlobalTheory.T.levelwiseEquivalence_isEquivalence (ZMod q) m (tw q i) (GlobalTheory.T.cechNerve_levelwise_equivalence_integral_pullback (ZMod q) (tw q i) _ _ _ _ _ _ g u hpb hg hsq m hm)
  have hEu : Eqv (ZMod q) (sch.map u) (tw q i) :=
    hsq _ _ (𝟙 _) (𝟙 _) u inferInstance (IsPullback.id_vert u)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_point_algClosure_residueField_of_integral_surjective A Y g hg hsurj
  have hEs : Eqv (ZMod q) (cechAug (pullback.snd g u)) (tw q i) :=
    GlobalTheory.T.etaleCechAugmentation_equiv_of_section (ZMod q) (tw q i) _ _ (pullback.snd g u) (pullback.lift s (𝟙 _) (by rw [hs, Category.id_comp]))
      (pullback.lift_snd _ _ _)
  obtain ⟨-, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have h1 : Eqv (ZMod q) (cechAug (pullback.snd g u) ≫ sch.map u) (tw q i) :=
    (hcomp _ _ _ _ _).1 hEs hEu
  rw [← hm.w] at h1
  exact (hcomp _ _ _ _ _).2.1 hEm h1

end GlobalTheory.EtC
end
