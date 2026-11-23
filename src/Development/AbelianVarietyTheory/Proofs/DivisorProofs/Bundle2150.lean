module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjLineOpen
open GlobalTheory.ProjSpace

variable (R : Type) [CommRing R]

def vec (i : Fin 2) : Fin 2 → Polynomial R := fun j => if j = i then 1 else Polynomial.X

theorem span_vec (i : Fin 2) : Ideal.span (Set.range (vec R i)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, by simp [vec]⟩) isUnit_one

def cmap (i : Fin 2) : Sp (Polynomial R) ⟶ PSpace R 1 := pt Polynomial.C (vec R i) (span_vec R i)

def toPoly (i : Fin 2) : MvPolynomial {j : Fin 2 // j ≠ i} R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C fun _ => Polynomial.X

theorem ne_rev (i : Fin 2) : Fin.rev i ≠ i := by fin_cases i <;> decide

instance (i : Fin 2) : Subsingleton {j : Fin 2 // j ≠ i} :=
  ⟨fun a b => Subtype.ext (Fin.ext (by
    have h1 := Fin.val_ne_of_ne a.2; have h2 := Fin.val_ne_of_ne b.2
    have := a.1.2; have := b.1.2; have := i.2; omega))⟩

def fromPoly (i : Fin 2) : Polynomial R →+* MvPolynomial {j : Fin 2 // j ≠ i} R :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X ⟨Fin.rev i, ne_rev i⟩)

def polyEquiv (i : Fin 2) : MvPolynomial {j : Fin 2 // j ≠ i} R ≃+* Polynomial R :=
  RingEquiv.ofRingHom (toPoly R i) (fromPoly R i)
    (Polynomial.ringHom_ext (fun r => by simp [fromPoly, toPoly]) (by simp [fromPoly, toPoly]))
    (MvPolynomial.ringHom_ext (fun r => by simp [fromPoly, toPoly]) (fun t => by
      simp [fromPoly, toPoly]; exact congrArg _ (Subsingleton.elim _ _)))

instance (i : Fin 2) : IsIso (spMap (toPoly R i)) :=
  inferInstanceAs (IsIso (Spec.map (polyEquiv R i).toCommRingCatIso.hom))

theorem toPoly_dehom (i : Fin 2) :
    (toPoly R i).comp (RingHomClass.toRingHom (dehom R 1 i)) =
      MvPolynomial.eval₂Hom Polynomial.C (vec R i) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · simp [toPoly]
  · by_cases h : j = i
    · subst h; simp [vec]
    · have := dehom_X_of_ne R 1 i ⟨j, h⟩
      simp only [RingHom.comp_apply, RingHom.coe_coe] at this ⊢
      rw [this]; simp [toPoly, vec, h]

theorem chartι_eq (i : Fin 2) : spMap (toPoly R i) ≫ chartι R 1 i = cmap R i := by
  have hu : IsUnit (MvPolynomial.eval₂Hom Polynomial.C (vec R i) (MvPolynomial.X i)) := by
    simp [vec]
  rw [cmap, pt, ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem R 1 i) hu, chartι, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine ProjPoint.eq_awayLift _ _ hu (X_mem R 1 i) _ fun n a ha => ?_
  rw [RingHom.comp_apply, awayToPoly_mk R 1 i n a ha]
  have := congrArg (fun φ => φ a) (toPoly_dehom R i)
  simp only [RingHom.comp_apply, RingHom.coe_coe] at this
  rw [this]
  simp [vec]

instance (i : Fin 2) : IsOpenImmersion (cmap R i) := by
  rw [← chartι_eq]; infer_instance

theorem range_cmap (i : Fin 2) : Set.range (cmap R i) = (chart R 1 i : Set (PSpace R 1)) := by
  have e := congrArg (fun U : (PSpace R 1).Opens => (U : Set (PSpace R 1)))
    ((Scheme.Hom.opensRange_comp_of_isIso (spMap (toPoly R i)) (chartι R 1 i)).trans (opensRange_chartι R 1 i))
  simp only [Scheme.Hom.coe_opensRange] at e
  rwa [chartι_eq] at e

theorem cmap_str (i : Fin 2) : cmap R i ≫ PSpace.str R 1 = spMap (algebraMap R (Polynomial R)) := by
  rw [cmap, pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext fun r => by simp [Polynomial.algebraMap_eq]

theorem cmap_preimage (i : Fin 2) : cmap R i ⁻¹ᵁ chart R 1 (Fin.rev i) = spOpen (Polynomial.X : Polynomial R) := by
  rw [cmap, pt_preimage_chart]; simp [vec, ne_rev i]

theorem pt_congr {A : Type} [CommRing A] {c c' : R →+* A} (hc : c = c') {v v' : Fin 2 → A}
    (hv : Ideal.span (Set.range v) = ⊤) (hv' : Ideal.span (Set.range v') = ⊤) (u : Aˣ) (h : v' = u • v) :
    pt c v hv = pt c' v' hv' := by
  subst hc; exact (pt_eq_pt_iff c hv hv').2 ⟨u, h⟩

theorem overlap_eq :
    spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ cmap R 0 =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ cmap R 1 := by
  set L := Localization.Away (Polynomial.X : Polynomial R)
  set s : L := IsLocalization.Away.invSelf (Polynomial.X : Polynomial R)
  have hs : algebraMap (Polynomial R) L Polynomial.X * s = 1 := IsLocalization.Away.mul_invSelf _
  have hmap {B : Type} [CommRing B] (ψ : Polynomial R →+* B) (i : Fin 2) :
      spMap ψ ≫ pt Polynomial.C (vec R i) (span_vec R i) =
        pt (ψ.comp Polynomial.C) (ψ ∘ vec R i) (span_range_comp_eq_top _ (span_vec R i) ψ) := by
    refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun j => by simp)
  rw [cmap, cmap, hmap, hmap]
  refine pt_congr R (RingHom.ext fun r => ?_) _ _ (Units.mkOfMulEqOne s _ (by rw [mul_comm]; exact hs)) ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← Polynomial.algebraMap_eq]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply R (Polynomial R) L r).symm
  · refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp [vec, s, Units.smul_def]
    · have h1 : vec R 1 1 = 1 := by simp [vec]
      have h2 : vec R 0 1 = Polynomial.X := by simp [vec]
      simp only [Units.smul_def, Units.val_mkOfMulEqOne, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
        h1, h2, map_one]
      rw [mul_comm]; exact hs.symm

theorem exists_of_cmap_eq {x x' : Sp (Polynomial R)} (h : cmap R 0 x = cmap R 1 x') :
    ∃ u : Sp (Localization.Away (Polynomial.X : Polynomial R)),
      spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) u = x ∧
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom u = x' := by
  have h1 : cmap R 0 x ∈ (chart R 1 1 : Set (PSpace R 1)) := by
    rw [← range_cmap R 1, h]; exact ⟨x', rfl⟩
  have h2 : x ∈ cmap R 0 ⁻¹ᵁ chart R 1 (Fin.rev 0) := h1
  rw [cmap_preimage] at h2
  have h3 : (x : PrimeSpectrum (Polynomial R)) ∈
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) : Set (PrimeSpectrum (Polynomial R))) := h2
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (Polynomial.X : Polynomial R))] at h3
  obtain ⟨u, hu⟩ := h3
  refine ⟨u, hu, (cmap R 1).isOpenEmbedding.injective ?_⟩
  have e := congrArg (fun φ => φ u) (overlap_eq R)
  exact (e.symm.trans (congrArg (cmap R 0) hu)).trans h

theorem isClosedMap_str : IsClosedMap (PSpace.str R 1) := by
  haveI := isProper_str R 1
  exact (PSpace.str R 1).isClosedMap

theorem str_cmap (i : Fin 2) (x : Sp (Polynomial R)) :
    PSpace.str R 1 (cmap R i x) = spMap (algebraMap R (Polynomial R)) x :=
  congrArg (fun φ => φ x) (cmap_str R i)

end GlobalTheory.ProjLineOpen


open GlobalTheory.ProjLineOpen GlobalTheory.ProjSpace in
theorem GlobalTheory.isOpen_setOf_charts_mem (R : Type) [CommRing R] (Y : Scheme.{0}) (g₀ g₁ : Sp (Polynomial R) ⟶ Y)
    (hg : spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ g₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ g₁)
    (W : Y.Opens) :
    IsOpen {τ : Sp R | ∀ x : Sp (Polynomial R), spMap (algebraMap R (Polynomial R)) x = τ →
      g₀ x ∈ W ∧ g₁ x ∈ W} := by
  set O : Set (PSpace R 1) := cmap R 0 '' (g₀ ⁻¹ᵁ W : Set _) ∪ cmap R 1 '' (g₁ ⁻¹ᵁ W : Set _) with hOdef
  have hO : IsOpen O := ((cmap R 0).isOpenEmbedding.isOpenMap _ (g₀ ⁻¹ᵁ W).isOpen).union
    ((cmap R 1).isOpenEmbedding.isOpenMap _ (g₁ ⁻¹ᵁ W).isOpen)
  have hgu : ∀ u, g₀ (spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) u) =
      g₁ (spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom u) := fun u => congrArg (fun φ => φ u) hg
  have key : {τ : Sp R | ∀ x : Sp (Polynomial R), spMap (algebraMap R (Polynomial R)) x = τ →
      g₀ x ∈ W ∧ g₁ x ∈ W} = (PSpace.str R 1 '' Oᶜ)ᶜ := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro H q hq hτ
      obtain ⟨i, hi⟩ := _root_.GlobalTheory.ProjSpace.exists_mem_chart R 1 q
      rw [← SetLike.mem_coe, ← range_cmap R i] at hi
      obtain ⟨x, rfl⟩ := hi
      have hx := (str_cmap R i x).symm.trans hτ
      refine hq ?_
      fin_cases i
      · exact Or.inl ⟨x, (H x hx).1, rfl⟩
      · exact Or.inr ⟨x, (H x hx).2, rfl⟩
    · intro H x hx
      have c0 : cmap R 0 x ∈ O := by
        by_contra hc; exact H _ hc ((str_cmap R 0 x).trans hx)
      have c1 : cmap R 1 x ∈ O := by
        by_contra hc; exact H _ hc ((str_cmap R 1 x).trans hx)
      constructor
      · rcases c0 with ⟨x', hx', e⟩ | ⟨x', hx', e⟩
        · rw [← (cmap R 0).isOpenEmbedding.injective e]; exact hx'
        · obtain ⟨u, rfl, rfl⟩ := exists_of_cmap_eq R e.symm
          show _ ∈ W
          rw [hgu]; exact hx'
      · rcases c1 with ⟨x', hx', e⟩ | ⟨x', hx', e⟩
        · obtain ⟨u, rfl, rfl⟩ := exists_of_cmap_eq R e
          show _ ∈ W
          rw [← hgu]; exact hx'
        · rw [← (cmap R 1).isOpenEmbedding.injective e]; exact hx'
  rw [key]
  exact (isClosedMap_str R _ hO.isClosed_compl).isOpen_compl
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LinChange

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.QCoh.Qcqs (baseRingHom baseRingHom_res baseRingHom_top)

variable {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ}

def lin (f : X ⟶ Sp R) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : Fin (n + 1) → H.Sec) :
    Fin (n + 1) → H.Sec :=
  fun i => ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • s j

theorem cst_eq (f : X ⟶ Sp R) (W : X.Opens) (r : R) :
    GlobalTheory.AbLaw.cst f W r = (baseRingHom f W).hom r := by
  rw [← baseRingHom_res f (le_top : W ≤ ⊤), baseRingHom_top]
  rfl

theorem resG_cst (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (r : R) :
    resG X h (GlobalTheory.AbLaw.cst f U r) = GlobalTheory.AbLaw.cst f V r :=
  GlobalTheory.AbLaw.rs_cst f h r

theorem sum_f {m : ℕ} (s : Fin m → H.Sec) (k : H.ι) : (∑ j, s j).f k = ∑ j, (s j).f k :=
  map_sum ({ toFun := fun s : H.Sec => s.f k, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    H.Sec →+ Γ(X, H.U k)) s Finset.univ

theorem lin_f (f : X ⟶ Sp R) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : Fin (n + 1) → H.Sec)
    (i : Fin (n + 1)) (k : H.ι) :
    (lin f a s i).f k = ∑ j, GlobalTheory.AbLaw.cst f (H.U k) (a i j) * (s j).f k := by
  rw [lin, sum_f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.LB.smul_f, resG_cst]

theorem lin_lin (f : X ⟶ Sp R) (a b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : Fin (n + 1) → H.Sec) :
    lin f b (lin f a s) = lin f (b * a) s := by
  funext i

  simp only [lin, Finset.smul_sum, smul_smul, ← map_mul, Matrix.mul_apply, map_sum, Finset.sum_smul]
  exact Finset.sum_comm

theorem lin_one (f : X ⟶ Sp R) (s : Fin (n + 1) → H.Sec) : lin f 1 s = s := by
  funext i
  simp [lin, Matrix.one_apply, apply_ite]

end GlobalTheory.LinChange

namespace GlobalTheory.LinChange
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.QCoh.Qcqs (baseRingHom baseRingHom_res baseRingHom_top)
open GlobalTheory.ProjSpace (toProj toProj_str toProj_preimage_chart O1 coord coord_f chart pullRatio secRatio_on
  pullRatio_toProj_on iSup_nonzeroLocus_coord toProj_coord)

variable {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ}

theorem iSup_nonzeroLocus_lin (f : X ⟶ Sp R) {s : Fin (n + 1) → H.Sec} (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    {a : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (ha : IsUnit a.det) :
    ⨆ i, nonzeroLocus (lin f a s i) = ⊤ := by
  have hb : lin f a⁻¹ (lin f a s) = s := by rw [lin_lin, Matrix.nonsing_inv_mul a ha, lin_one]
  refine top_unique fun y _ => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨k, hk⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  by_contra hne
  have hnu : ∀ j, ¬ IsUnit (X.presheaf.germ (H.U k) y hk ((lin f a s j).f k)) := fun j hu =>
    hne (Opens.mem_iSup.2 ⟨j, (GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).2 ((X.mem_basicOpen _ y hk).2 hu)⟩)
  have hu := (X.mem_basicOpen _ y hk).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).1 hi)

  rw [← hb, lin_f, map_sum] at hu
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => ?_) hu
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu j))

theorem appLE_cst {Y : Scheme.{0}} (p : Y ⟶ Sp R) (g : X ⟶ Y) {U : Y.Opens} {W : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (r : R) :
    (g.appLE U W h).hom (GlobalTheory.AbLaw.cst p U r) = GlobalTheory.AbLaw.cst (g ≫ p) W r := by
  rw [cst_eq, cst_eq, ← GlobalTheory.ProjSpace.baseRingHom_appLE p g U W h]
  rfl

theorem toProj_lin (f : X ⟶ Sp R) {s : Fin (n + 1) → H.Sec} (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ht : ⨆ i, nonzeroLocus (lin f a s i) = ⊤)
    (hc : ⨆ i, nonzeroLocus (lin (PSpace.str R n) a (coord R n) i) = ⊤) :
    toProj f (lin f a s) ht =
      toProj f s hs ≫ toProj (PSpace.str R n) (lin (PSpace.str R n) a (coord R n)) hc := by
  have e := GlobalTheory.ProjSpace.toProj_eq_comp_of_locally (f := PSpace.str R n) hc (toProj f s hs)
    (t := lin f a s) ht ?_
  · rwa [toProj_str] at e
  intro z
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ z))
  obtain ⟨l, hl⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  have hW : nonzeroLocus (s i) ⊓ H.U l ≤ toProj f s hs ⁻¹ᵁ chart R n i :=
    inf_le_left.trans (toProj_preimage_chart f s hs i).ge
  refine ⟨nonzeroLocus (s i) ⊓ H.U l, ⟨hi, hl⟩, i, hW, l, inf_le_right, resG X inf_le_right ((s i).f l),
    fun j => ?_⟩

  rw [lin_f, lin_f (H := O1 R n) (PSpace.str R n) a (coord R n) j i, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_mul, resG_cst, coord_f]
  erw [appLE_cst (PSpace.str R n) (toProj f s hs) hW (a j m)]
  rw [toProj_str]
  change _ = _ * (_ * pullRatio (toProj f s hs) _ i hW m)
  generalize (GlobalTheory.AbLaw.cst f (nonzeroLocus (s i) ⊓ H.U l)) (a j m) = c
  rw [pullRatio_toProj_on, secRatio_on (s i) (s m) l inf_le_left inf_le_right]
  ring

end GlobalTheory.LinChange

namespace GlobalTheory.LinChange
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj coord iSup_nonzeroLocus_coord toProj_coord)

variable {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ}

theorem toProj_congr (f : X ⟶ Sp R) {s t : Fin (n + 1) → H.Sec} (h : s = t) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) : toProj f s hs = toProj f t ht := by
  subst h
  rfl

def linAut (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsUnit a.det) : PSpace R n ⟶ PSpace R n :=
  toProj (PSpace.str R n) (lin (PSpace.str R n) a (coord R n))
    (iSup_nonzeroLocus_lin _ (iSup_nonzeroLocus_coord R n) ha)

theorem linAut_comp (a b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hba : IsUnit (b * a).det) : linAut a ha ≫ linAut b hb = linAut (b * a) hba :=
  (toProj_lin (PSpace.str R n) _ b
    (iSup_nonzeroLocus_lin _ (iSup_nonzeroLocus_lin _ (iSup_nonzeroLocus_coord R n) ha) hb) _).symm.trans (toProj_congr _ (lin_lin _ a b _) _ _)

theorem linAut_one (h : IsUnit (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).det) : linAut 1 h = 𝟙 (PSpace R n) :=
  (toProj_congr _ (lin_one _ _) _ _).trans (toProj_coord R n)

instance isIso_linAut (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsUnit a.det) : IsIso (linAut a ha) := by
  have hb : IsUnit a⁻¹.det := Matrix.isUnit_nonsing_inv_det a ha
  refine ⟨⟨linAut a⁻¹ hb, ?_, ?_⟩⟩
  · rw [linAut_comp a a⁻¹ ha hb (by rw [Matrix.nonsing_inv_mul a ha, Matrix.det_one]; exact isUnit_one)]
    simp only [Matrix.nonsing_inv_mul a ha]
    exact linAut_one _
  · rw [linAut_comp a⁻¹ a hb ha (by rw [Matrix.mul_nonsing_inv a ha, Matrix.det_one]; exact isUnit_one)]
    simp only [Matrix.mul_nonsing_inv a ha]
    exact linAut_one _

end GlobalTheory.LinChange

theorem GlobalTheory.veryAmpleBy_linChange : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (n : ℕ)
    (s : Fin (n + 1) → H.Sec) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R), IsUnit a.det → H.IsLB →
    GlobalTheory.AbLaw.VeryAmpleBy f H s → GlobalTheory.AbLaw.VeryAmpleBy f H (fun i => ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • s j) := by
  intro R _ X f H n s a ha _ hv
  obtain ⟨hs, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hv
  refine (GlobalTheory.ProjSpace.veryAmpleBy_iff f (GlobalTheory.LinChange.lin f a s)).2
    ⟨GlobalTheory.LinChange.iSup_nonzeroLocus_lin f hs ha, ?_⟩
  rw [GlobalTheory.LinChange.toProj_lin f hs a _ (GlobalTheory.LinChange.iSup_nonzeroLocus_lin _
    (GlobalTheory.ProjSpace.iSup_nonzeroLocus_coord R n) ha)]
  exact (inferInstance : IsClosedImmersion (GlobalTheory.ProjSpace.toProj f s hs ≫ GlobalTheory.LinChange.linAut a ha))
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_unipotent_embeddings_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW (t.comp σ)) = 0 ∧ (uT Y).map (piW t) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW t) = 0 ∧ GlobalTheory.LinWAt.coW G t (uM z) = z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinWAt.coW G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinWAt.coW G t x i j * (u.map (piW t)) i j) := by
  first | exact @GlobalTheory.LinWCoords.exists_split_coords | exact GlobalTheory.LinWCoords.exists_split_coords | (intros; apply GlobalTheory.LinWCoords.exists_split_coords <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_inertPlace_transversal_of_localCore : (∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ Z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z ∧ (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  first | exact @GlobalTheory.TransvChoose.exists_transversal | exact GlobalTheory.TransvChoose.exists_transversal | (intros; apply GlobalTheory.TransvChoose.exists_transversal <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.diagonalStabilizer_doubledVacuum_eigenvalue_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegel.eigen_eq_one_of_diag | exact GlobalTheory.DblVacSiegel.eigen_eq_one_of_diag | (intros; apply GlobalTheory.DblVacSiegel.eigen_eq_one_of_diag <;> assumption)
end
