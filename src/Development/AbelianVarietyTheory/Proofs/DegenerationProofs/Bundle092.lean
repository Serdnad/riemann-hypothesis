module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle083
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

noncomputable section
namespace GlobalTheory.ZH.LinFrame
open GlobalTheory.ProjSpace

variable {o : Type} [CommRing o] {m : ℕ} {T : Scheme.{0}}

def chartLB (p : T ⟶ PSpace o m) : LB T :=
  ⟨Fin (m + 1), fun i => p ⁻¹ᵁ chart o m i, fun i j =>
    ⟨pullRatio p _ i inf_le_left j, pullRatio p _ j inf_le_right i,
      pullRatio_mul_pullRatio.trans pullRatio_self, pullRatio_mul_pullRatio.trans pullRatio_self⟩⟩

theorem lin_compat (p : T ⟶ PSpace o m) (b : Fin (m + 1) → Γ(T, ⊤)) (i j : Fin (m + 1)) :
    resG T (inf_le_left : p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j ≤ _)
        (∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m i) i le_rfl k) =
      pullRatio p (p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j) i inf_le_left j *
        resG T (inf_le_right : p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j ≤ _)
          (∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m j) j le_rfl k) := by

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, resG_pullRatio, resG_pullRatio, mul_left_comm, pullRatio_mul_pullRatio]
  congr 1
  exact (DVR.SecOps.resTop_res _ _).trans (DVR.SecOps.resTop_res _ _).symm

def linSec (p : T ⟶ PSpace o m) (b : Fin (m + 1) → Γ(T, ⊤)) : (chartLB p).Sec where
  f l := ∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m l) l le_rfl k
  compat i j := lin_compat p b i j

variable {K : Type} [Field K]

theorem crd_iff (x : Sp K ⟶ PSpace o m) (v : Fin (m + 1) → K) : Crd (O1 o m) (coord o m) x v ↔
    ∃ (l : Fin (m + 1)) (c : Kˣ), ⊤ ≤ x ⁻¹ᵁ chart o m l ∧
      ∀ j, v j = (c : K) * valR x (chart o m l) (ratio o m l j) := Iff.rfl

theorem valR_pullRatio (x : Sp K ⟶ T) (p : T ⟶ PSpace o m) {W : T.Opens} {l : Fin (m + 1)}
    (hl : W ≤ p ⁻¹ᵁ chart o m l) (h : ⊤ ≤ x ⁻¹ᵁ W) (k : Fin (m + 1)) :
    valR x W (pullRatio p W l hl k) = valR (x ≫ p) (chart o m l) (ratio o m l k) :=
  Points.valR_appLE x p hl h _

theorem valR_linSec (x : Sp K ⟶ T) (p : T ⟶ PSpace o m) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤))
    {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l) (i : Fin (m + 1)) :
    valR x (p ⁻¹ᵁ chart o m l) ((linSec p (b i)).f l) =
      (b.map (valR x ⊤)).mulVec (fun k => valR (x ≫ p) (chart o m l) (ratio o m l k)) i := by
  change valR x (p ⁻¹ᵁ chart o m l) (∑ k, resG T le_top (b i k) * pullRatio p (p ⁻¹ᵁ chart o m l) l le_rfl k) =
    ∑ k, valR x ⊤ (b i k) * valR (x ≫ p) (chart o m l) (ratio o m l k)

  rw [CrdCalc.valR_eq x _ h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← CrdCalc.valR_eq x _ h, CrdCalc.valR_mul x _ h, CrdCalc.valR_res x _ h, valR_pullRatio x p _ h]

theorem valR_ratio_self (x : Sp K ⟶ PSpace o m) {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ chart o m l) :
    valR x (chart o m l) (ratio o m l l) = 1 := by
  rw [ratio, ratioOn_self, Points.valR_one x _ h]

theorem exists_isUnit_valR_linSec (x : Sp K ⟶ T) (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det)
    {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l) :
    ∃ i, IsUnit (valR x (p ⁻¹ᵁ chart o m l) ((linSec p (b i)).f l)) := by
  by_contra hn
  have e : b.map (valR x ⊤) = (CrdCalc.valHom x ⊤ le_top).mapMatrix b := by
    ext i j
    exact CrdCalc.valR_eq x ⊤ le_top _
  have hd : (b.map (valR x ⊤)).det ≠ 0 := by
    rw [e, ← RingHom.map_det]
    exact (hb.map _).ne_zero
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hd
    (v := fun k => valR (x ≫ p) (chart o m l) (ratio o m l k)) (funext fun i => by
      rw [← valR_linSec x p b h]
      by_contra hi
      exact hn ⟨i, Ne.isUnit hi⟩)
  have h1 := congrFun h0 l
  rw [valR_ratio_self (x ≫ p) h] at h1
  exact one_ne_zero h1

theorem iSup_nonzeroLocus_linSec (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det) :
    ⨆ i, nonzeroLocus (linSec p (b i)) = ⊤ := by
  refine top_le_iff.1 fun y _ => ?_
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 ((iSup_chart o m).ge (Set.mem_univ (p y)))
  let x : Sp (T.residueField y) ⟶ T := T.fromSpecResidueField y
  have hx : ∀ z, x z = y := fun z => T.fromSpecResidueField_apply y z
  have h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l := fun z _ => by
    change p (x z) ∈ chart o m l
    rw [hx]; exact hl
  obtain ⟨i, hi⟩ := exists_isUnit_valR_linSec x p hb h
  have h2 : x (IsLocalRing.closedPoint _) ∈ T.basicOpen ((linSec p (b i)).f l) :=
    (CrdCalc.isUnit_valR_iff x _ h _).1 hi (Set.mem_univ _)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨l, (congrArg (· ∈ T.basicOpen ((linSec p (b i)).f l)) (hx _)).mp h2⟩⟩

theorem crd_toProj_linSec {A : Type} [CommRing A] (c : T ⟶ Sp A) (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det) (x : Sp K ⟶ T) {v : Fin (m + 1) → K}
    (hv : Crd (O1 o m) (coord o m) (x ≫ p) v) :
    Crd (O1 A m) (coord A m) (x ≫ toProj c (fun i => linSec p (b i)) (iSup_nonzeroLocus_linSec p hb))
      ((b.map (valR x ⊤)).mulVec v) := by
  obtain ⟨l, u, hl, hv⟩ := (crd_iff _ _).1 hv
  have h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l := hl
  obtain ⟨i, hi⟩ := exists_isUnit_valR_linSec x p hb h
  set g := toProj c (fun i => linSec p (b i)) (iSup_nonzeroLocus_linSec p hb) with hg
  have h₁ : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ chart A m i := by
    rw [hg, toProj_preimage_chart]
    exact ((CrdCalc.isUnit_valR_iff x _ h _).1 hi).trans
      (x.preimage_mono (le_iSup (fun k => T.basicOpen ((linSec p (b i)).f k)) l))
  have h₂ : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ chart A m i ⊓ p ⁻¹ᵁ chart o m l) := fun z hz => ⟨h₁ hz, h hz⟩
  refine (crd_iff _ _).2 ⟨i, u * hi.unit, h₁, fun j => ?_⟩
  have e := congrArg (valR x _) (sec_eq_pullRatio_toProj_mul c (fun i => linSec p (b i))
    (iSup_nonzeroLocus_linSec p hb) i j l (W := g ⁻¹ᵁ chart A m i ⊓ p ⁻¹ᵁ chart o m l) inf_le_left inf_le_right)
  have r : ∀ t : (chartLB p).Sec, _ = valR x (p ⁻¹ᵁ chart o m l) (t.f l) := fun t =>
    CrdCalc.valR_res x inf_le_right h₂ (t.f l)
  replace e := (r _).symm.trans (e.trans ((CrdCalc.valR_mul x _ h₂ _ _).trans
    (congrArg₂ (· * ·) (valR_pullRatio x _ _ h₂ _) (r _))))
  have ev : v = (u : K) • fun k => valR (x ≫ p) (chart o m l) (ratio o m l k) := funext hv
  rw [ev, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← valR_linSec x p b h, Units.val_mul, IsUnit.unit_spec,
    _root_.mul_assoc]
  exact congrArg (_ * ·) (e.trans (mul_comm _ _))

theorem eq_of_crd {x x' : Sp K ⟶ PSpace o m} (hs : x ≫ PSpace.str o m = x' ≫ PSpace.str o m)
    {w : Fin (m + 1) → K} (h : Crd (O1 o m) (coord o m) x w) (h' : Crd (O1 o m) (coord o m) x' w) : x = x' := by
  obtain ⟨l, c, hl, hw⟩ := (crd_iff _ _).1 h
  obtain ⟨l', c', hl', hw'⟩ := (crd_iff _ _).1 h'
  have h1 : w l = c := by rw [hw, valR_ratio_self x hl, mul_one]
  have h2 : ⊤ ≤ x' ⁻¹ᵁ chart o m l := by
    have hu : IsUnit (valR x' (chart o m l') (ratio o m l' l)) :=
      (Units.isUnit_units_mul c' _).1 ((hw' l).symm.trans h1 ▸ c.isUnit)
    refine ((CrdCalc.isUnit_valR_iff x' _ hl' _).1 hu).trans (x'.preimage_mono ?_)
    rw [ratio, basicOpen_ratioOn]
    exact inf_le_right
  obtain ⟨u, hu⟩ := CrdCalc.exists_unit_charts (O1 o m) x' l' l hl' h2
  have hw'' : ∀ j, w j = (c' : K) * u * valR x' (chart o m l) (ratio o m l j) := fun j => by
    rw [hw', _root_.mul_assoc]
    exact congrArg (_ * ·) (hu (coord o m j))
  have h3 : (c' : K) * u = c := by rw [← h1, hw'', valR_ratio_self x' h2, mul_one]
  refine hom_ext hs fun _ => ⟨⊤, trivial, l, hl, h2, fun j => ?_⟩
  have e := (hw j).symm.trans (hw'' j)
  rw [h3, Units.mul_right_inj, CrdCalc.valR_eq x _ hl, CrdCalc.valR_eq x' _ h2] at e
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e

theorem isImmersion_lift_of_linear_change : ∀ (o : Type) [CommRing o] (Y Z : Scheme.{0}) [IsReduced Y] (s : Z ⟶ Sp o) (f : Y ⟶ Z) (m : ℕ) (π : Y ⟶ PSpace o m) (h : π ≫ PSpace.str o m = f ≫ s), (∀ y : Y, ∃ (W : Z.Opens) (A : Type) (_ : CommRing A) (c : W.toScheme ⟶ Sp A) (ψ : (f ⁻¹ᵁ W).toScheme ⟶ PSpace A m) (a : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(Z, W)) (K : Type) (_ : Field K) (η : Sp K ⟶ (f ⁻¹ᵁ W).toScheme) (v : Fin (m + 1) → K), f y ∈ W ∧ IsImmersion ψ ∧ ψ ≫ PSpace.str A m = (f ∣_ W) ≫ c ∧ IsUnit a.det ∧ IsDominant η ∧ Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (η ≫ (f ⁻¹ᵁ W).ι ≫ π) v ∧ Crd (ProjSpace.O1 A m) (ProjSpace.coord A m) (η ≫ ψ) ((a.map (valF (η ≫ (f ⁻¹ᵁ W).ι ≫ f) W)).mulVec v)) → IsImmersion (pullback.lift π f h) := by
  intro o _ Y Z _ s f m π h H
  choose W A iA c ψ a K iK η v hy hψ hc ha hη h₁ h₂ using H
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  have hj : pullback.lift π f h ≫ pullback.snd (PSpace.str o m) s = f := pullback.lift_snd _ _ _
  have hπ : pullback.lift π f h ≫ pullback.fst (PSpace.str o m) s = π := pullback.lift_fst _ _ _
  generalize pullback.lift π f h = j at hj hπ ⊢
  generalize pullback.fst (PSpace.str o m) s = q at hπ
  generalize pullback.snd (PSpace.str o m) s = r at hj
  subst hj hπ
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (fun y => r ⁻¹ᵁ W y) ?_ fun y => ?_
  · rintro _ ⟨y, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩
  have := hψ y
  have := hη y
  have hT : (⊤ : (r ⁻¹ᵁ W y).toScheme.Opens) ≤ ((r ⁻¹ᵁ W y).ι ≫ r) ⁻¹ᵁ W y := (r ⁻¹ᵁ W y).ι_preimage_self.ge
  let b := (((r ⁻¹ᵁ W y).ι ≫ r).appLE (W y) ⊤ hT).hom.mapMatrix (a y)
  have hb : IsUnit b.det := by
    rw [← RingHom.map_det]
    exact (ha y).map _
  let j' : ((j ≫ r) ⁻¹ᵁ W y).toScheme ⟶ (r ⁻¹ᵁ W y).toScheme := j ∣_ (r ⁻¹ᵁ W y)
  have hj' : j' ≫ (r ⁻¹ᵁ W y).ι = ((j ≫ r) ⁻¹ᵁ W y).ι ≫ j := morphismRestrict_ι j _
  let g := toProj ((r ∣_ W y) ≫ c y) (fun i => linSec ((r ⁻¹ᵁ W y).ι ≫ q) (b i)) (iSup_nonzeroLocus_linSec _ hb)
  have hs : (j' ≫ g) ≫ PSpace.str (A y) m = ψ y ≫ PSpace.str (A y) m := by
    rw [Category.assoc, toProj_str, hc, morphismRestrict_comp]
    exact (Category.assoc _ _ _).symm
  have e : j' ≫ g = ψ y := by
    refine ext_of_isDominant_of_isSeparated _ hs (η y) (eq_of_crd ?_ ?_ (h₂ y))
    · rw [Category.assoc, hs, Category.assoc]
    · have k := crd_toProj_linSec ((r ∣_ W y) ≫ c y) ((r ⁻¹ᵁ W y).ι ≫ q) hb (η y ≫ j') (v := v y) (by
        rw [Category.assoc, reassoc_of% hj']
        exact h₁ y)
      have eb : b.map (valR (η y ≫ j') ⊤) = (a y).map (valF (η y ≫ ((j ≫ r) ⁻¹ᵁ W y).ι ≫ j ≫ r) (W y)) := by
        ext i k
        refine (Points.valR_appLE (η y ≫ j') _ hT le_top (a y i k)).trans ?_
        rw [Category.assoc, reassoc_of% hj']
        rfl
      rw [eb, Category.assoc] at k
      exact k
  have : IsImmersion (j' ≫ g) := e ▸ hψ y
  exact IsImmersion.of_comp j' g

end GlobalTheory.ZH.LinFrame
end
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.CosetCrit

theorem posDef_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] {q : QuadraticMap ℤ X ℝ}
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) : q.PosDef := by
  intro x hx
  by_contra h
  have hinj : Function.Injective fun k : ℤ => k • x := smul_left_injective ℤ hx
  have h1 := (hq.comp hinj.tendsto_cofinite).eventually_gt_atTop 0
  obtain ⟨k, hk⟩ := h1.exists
  simp only [Function.comp, QuadraticMap.map_smul, zsmul_eq_mul] at hk
  have : (0 : ℝ) ≤ ((k * k : ℤ) : ℝ) := by exact_mod_cast mul_self_nonneg k
  nlinarith [not_lt.1 h]

theorem tendsto_class {X : Type} [AddCommGroup X] [Module.Free ℤ X] {q : QuadraticMap ℤ X ℝ}
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (y : X) {m : ℕ} (hm : m ≠ 0) :
    Filter.Tendsto (fun χ => q (y + m • χ)) Filter.cofinite Filter.atTop := by
  have hinj : Function.Injective fun χ : X => y + m • χ := fun a b h => by
    have h1 : (m : ℤ) • a = (m : ℤ) • b := by simpa using h
    exact smul_right_injective X (by exact_mod_cast hm : (m : ℤ) ≠ 0) h1
  exact hq.comp hinj.tendsto_cofinite

theorem exists_char_pow {C X : Type} [Field C] [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X]
    (t : Multiplicative X →* Cˣ) {k : ℕ} (hk : 0 < k) : ∃ t' : Multiplicative X →* Cˣ, t' ^ k = t := by
  have hroot : ∀ u : Cˣ, ∃ v : Cˣ, v ^ k = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : C) hk
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk.ne'] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose r hr using hroot
  let e := Module.Free.chooseBasis ℤ X
  let f : X →ₗ[ℤ] Additive Cˣ :=
    e.constr ℤ fun i => Additive.ofMul (r (t (Multiplicative.ofAdd (e i))))
  have hf : k • f = (MonoidHom.toAdditiveRight t).toIntLinearMap := e.ext fun i => by
    simp only [f, LinearMap.smul_apply, Module.Basis.constr_basis, ← ofMul_pow, hr]
    rfl
  refine ⟨AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hf x.toAdd)

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}


omit [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] in
theorem norm_txT_le (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    ‖N.txT m p χ‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) := by
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p χ]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)


omit [CompleteSpace C] [IsAlgClosed C] in
theorem norm_tx_le (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + m • χ₀) ≤ q (p.1.1.toAdd + m • χ)) :
    ‖N.tx m p‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ₀) / (m : ℝ) ^ 2)) := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (Real.exp_pos _).le fun χ => ?_
  refine (norm_txT_le hI hm p χ).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
  exact div_le_div_of_nonneg_right (h₀ χ) (by positivity)


omit [IsUltrametricDist C] [CompleteSpace C] in
theorem exists_lift {n g : ℕ} (hn : (n : C) ≠ 0) (hT : N.Tors n g) (j : ℕ) {t : N.A} (ht : t ^ n = 1) :
    ∃ γ : N.Gt, γ ^ n ^ (j + 1) = 1 ∧ γ.b ^ n ^ j = t := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hn hT j
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  obtain ⟨γ₀, rfl⟩ := h1 t
  obtain ⟨s, hs⟩ := (N.exists_tor_iff (γ₀ ^ n)).2 (by rw [NumD.Gt.pow_b, ht])
  obtain ⟨s', rfl⟩ := exists_char_pow s hn0
  obtain ⟨γ, hγ⟩ := h2 (γ₀ * (N.tor s')⁻¹)
  refine ⟨γ, ?_, ?_⟩
  · rw [pow_succ, pow_mul, hγ, mul_pow, inv_pow, ← N.tor_pow, hs, mul_inv_cancel]
  · rw [← NumD.Gt.pow_b, hγ]
    simp

theorem exists_norm_tx_ge (hI : N.Int q) {n g : ℕ} (hp : n.Prime) (ho : Odd n) (hn : ‖(n : C)‖ = 1)
    (hT : N.Tors n g) {j : ℕ} (hj : 1 ≤ j) (p : N.QT ((n ^ j) ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + n ^ j • χ₀) ≤ q (p.1.1.toAdd + n ^ j • χ)) :
    ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧
      Real.exp (-(q (p.1.1.toAdd + n ^ j • χ₀) / ((n ^ j : ℕ) : ℝ) ^ 2)) ≤ ‖N.tx (n ^ j) (p * h)‖ := by
  have hn0 : (n : C) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hm : Odd (n ^ j) := ho.pow
  have hm0 : 0 < n ^ j := hm.pos
  have hP := posDef_of_tendsto hI.pos
  have hQ : ∀ γ : N.Gt, γ ^ n ^ (j + 1) = 1 → (1, γ) ∈ N.QT ((n ^ j) ^ 2) := fun γ hγ => by
    obtain ⟨c, hc⟩ : n ^ (j + 1) ∣ (n ^ j) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow n (by omega)
    rw [NumD.mem_QT, hc, pow_mul, hγ, one_pow]
    exact N.io_zero.symm
  obtain ⟨t, ht, hth⟩ := hT.good (N.c χ₀ * p.1.2.b ^ n ^ j)
  obtain ⟨γ, hγ, hγb⟩ := exists_lift hn0 hT j ht
  set p₁ : N.QT ((n ^ j) ^ 2) := p * ⟨(1, γ), hQ γ hγ⟩ with hp₁
  have hy : p₁.1.1 = p.1.1 := mul_one _
  have hb : p₁.1.2 = p.1.2 * γ := rfl
  haveI : NeZero (n : C) := ⟨hn0⟩
  haveI : NeZero n := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C n
  have hr : ∀ x : ℝ, Real.exp (-1) ^ x = Real.exp (-x) := fun x => by
    rw [← Real.exp_mul, neg_one_mul]
  have hsq : (0 : ℝ) < ((n ^ j : ℕ) : ℝ) ^ 2 := by positivity
  obtain ⟨s, hs, hle⟩ := GlobalTheory.exists_torsion_twist_tsum_norm_ge C N.X n ζ hp.pos hn hζ
    (N.txT (n ^ j) p₁) (fun χ => q (p.1.1.toAdd + n ^ j • χ) / ((n ^ j : ℕ) : ℝ) ^ 2) (Real.exp (-1))
    (Real.exp_pos _) (by simpa using Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num))
    ((tendsto_class hI.pos _ hm0.ne').atTop_div_const hsq)
    (fun χ => by rw [hr, ← hy]; exact norm_txT_le hI hm p₁ χ) χ₀
    (by rw [hr, (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 _ hm p₁ χ₀, hy, hb, NumD.Gt.mul_b, mul_pow, hγb, ← mul_assoc, hth,
          mul_one])
    (fun μ hμ => by
      refine div_lt_div_of_pos_right ?_ hsq
      have := GlobalTheory.ClassMin.lt_of_min_class_of_ne_zero hP (N := ((n ^ j : ℕ) : ℤ)) (n := (n : ℤ))
        (a := p.1.1.toAdd + n ^ j • χ₀) (by exact_mod_cast hm0.ne') (by exact_mod_cast hp.two_le)
        (fun w => by rw [natCast_zsmul, add_assoc, ← smul_add]; exact h₀ _) hμ
      rwa [mul_comm, mul_smul, natCast_zsmul, natCast_zsmul, add_assoc, ← smul_add] at this)
  obtain ⟨s', rfl⟩ := exists_char_pow s hm0
  have hs' : s' ^ n ^ (j + 1) = 1 := by rw [pow_succ, pow_mul, hs]
  have hγ' : (γ * N.tor s') ^ n ^ (j + 1) = 1 := by
    rw [mul_pow, hγ, ← N.tor_pow, hs', N.tor_one, mul_one]
  refine ⟨⟨(1, γ * N.tor s'), hQ _ hγ'⟩, rfl, hγ', ?_⟩
  set p₂ : N.QT ((n ^ j) ^ 2) := p * ⟨(1, γ * N.tor s'), hQ _ hγ'⟩ with hp₂
  have hone : ∀ x, ‖(s' x : C)‖ = 1 := fun x => by
    have h1 : ‖(s' x : C)‖ ^ n ^ (j + 1) = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hs', MonoidHom.one_apply,
        Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).1 h1
  have hterm : ∀ χ, N.txT (n ^ j) p₂ χ =
      ((s' p₁.1.1 : C) ^ (((n ^ j) ^ 2 - 1) / 2) * (s' p₁.1.1 : C)) *
        (N.txT (n ^ j) p₁ χ * ((s' ^ n ^ j) (Multiplicative.ofAdd χ) : C)) := fun χ => by
    rw [(GlobalTheory.T.thetaConstantTerm_representative_dependence C N (n ^ j) hm p₁ p₂ χ).2 s' ((mul_one _).trans hy.symm) (mul_assoc _ _ _).symm,
      ofAdd_add, ofAdd_nsmul, map_mul, map_pow, ofAdd_toAdd, MonoidHom.pow_apply]
    push_cast
    ring
  rw [NumD.tx, funext hterm, tsum_mul_left, norm_mul, norm_mul, norm_pow, hone, one_pow, one_mul, one_mul,
    ← hr]
  exact hle

end GlobalTheory.CosetCrit

theorem GlobalTheory.tx_coset_criterion : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ n g : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n g → ∀ j : ℕ, 1 ≤ j → (∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 ∧ (‖N.tx (n ^ j) p‖ = 1 → ∃ z, p.1.1.toAdd = n ^ j • z)) ∧ (∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ ‖N.tx (n ^ j) (p * h)‖ = 1) ∧ ∀ p : N.QT ((n ^ j) ^ 2), ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ N.tx (n ^ j) (p * h) ≠ 0 := by
  intro C _ _ _ _ N q hI n g hp ho hn hT j hj
  have hm : Odd (n ^ j) := ho.pow
  have hP := GlobalTheory.CosetCrit.posDef_of_tendsto hI.pos
  have hsq : (0 : ℝ) < ((n ^ j : ℕ) : ℝ) ^ 2 := by have := hm.pos; positivity
  have hmin : ∀ p : N.QT ((n ^ j) ^ 2), ∃ χ₀, ∀ χ,
      q (p.1.1.toAdd + n ^ j • χ₀) ≤ q (p.1.1.toAdd + n ^ j • χ) := fun p =>
    (GlobalTheory.CosetCrit.tendsto_class hI.pos _ hm.pos.ne').exists_forall_le
  have h1 : ∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 := fun p => by
    obtain ⟨χ₀, h₀⟩ := hmin p
    refine (GlobalTheory.CosetCrit.norm_tx_le hI hm p h₀).trans (Real.exp_le_one_iff.2 (neg_nonpos.2 ?_))
    exact div_nonneg (hP.nonneg _) hsq.le
  refine ⟨fun p => ⟨h1 p, fun h => ?_⟩, fun p hp1 => ?_, fun p => ?_⟩
  · obtain ⟨χ₀, h₀⟩ := hmin p
    have h2 := GlobalTheory.CosetCrit.norm_tx_le hI hm p h₀
    rw [h, Real.one_le_exp_iff, neg_nonneg] at h2
    refine ⟨-χ₀, ?_⟩
    rw [smul_neg, eq_neg_iff_add_eq_zero]
    by_contra h3
    exact (div_pos (hP _ h3) hsq).not_ge h2
  · obtain ⟨h, ha, hb, hc⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge hI hp ho hn hT hj p (χ₀ := 0) (fun χ => by
      rw [hp1, toAdd_one, smul_zero, add_zero, map_zero]
      exact hP.nonneg _)
    refine ⟨h, ha, hb, le_antisymm (h1 _) ?_⟩
    simpa [hp1] using hc
  · obtain ⟨χ₀, h₀⟩ := hmin p
    obtain ⟨h, ha, hb, hc⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge hI hp ho hn hT hj p h₀
    exact ⟨h, ha, hb, norm_pos_iff.1 ((Real.exp_pos _).trans_le hc)⟩
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

theorem _root_.GlobalTheory.T.span_translates_multiplicationPullback_theta : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) (m N : ℕ), N = m ^ 2 → 1 ≤ m → IsUnit (m : Γ(S, ⊤)) → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ (κ : Type) [Fintype κ] (b : κ → SecM P.A P.L N (baseOver S)), UnivBasis P N b → ∀ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left] ![(N : ℤ), -1])), α.IsGen → ∀ s₀ : LB.Sec (LPow P.A P.L N (baseOver S)), IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀ → ∀ (I : Type) (U : I → ThetaGrp P.A P.L N (baseOver S)) (t : I → LB.Sec (LPow P.A P.L N (baseOver S))), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ N = 1 → ∃ i, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ (U i).pt = z) → (∀ i, IsActOf P.A P.L N (U i) s₀ (t i)) → Submodule.span Γ((baseOver S).left, ⊤) (Set.range fun i => (SecM.ofSec P.A (t i) : SecM P.A P.L N (baseOver S))) = ⊤ := by
  first | exact @GlobalTheory.ThetaReal.span_translates_mulPull | exact GlobalTheory.ThetaReal.span_translates_mulPull | (intros; apply GlobalTheory.ThetaReal.span_translates_mulPull <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_glue_sections_same_theta_multiple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (c : Ω), (∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N'), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j)) → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ N ≤ W ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.ThMul c N σ ∧ Q.FibNe N σ) → ∃ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ W), Q.ThMul c W σ ∧ Q.FibNe W σ := by
  first | exact @GlobalTheory.ZH.GlueTheta.exists_glue | exact GlobalTheory.ZH.GlueTheta.exists_glue | (intros; apply GlobalTheory.ZH.GlueTheta.exists_glue <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.theta_section_restriction_unit_twist : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (c f : Ω), N' ≤ N → (∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) → σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → Q.FibNe N σ → ∃ σ' : Q.SecFam N', σ' ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N') ∧ Q.ThMul (f * c) N' σ' ∧ Q.FibNe N' σ' := by
  first | exact @GlobalTheory.ZH.ZHPre.exists_scale_section | exact GlobalTheory.ZH.ZHPre.exists_scale_section | (intros; apply GlobalTheory.ZH.ZHPre.exists_scale_section <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_localThetaSection_fibreNonzero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), Q.LocTheta → ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.FibNe N σ := by
  first | exact @GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe | exact GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe | (intros; apply GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe <;> assumption)
end
