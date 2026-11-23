module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.CommonEqnOpen

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_pow {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem exists_pow_mul_eq {U : X.Opens} (hU : IsAffineOpen U) (hg : genericPoint X ∈ U) (t : Γ(X, U))
    (ht : genericPoint X ∈ X.basicOpen t) {f : X.functionField}
    (h : ∀ z ∈ X.basicOpen t, RegAt z f) :
    ∃ (n : ℕ) (a : Γ(X, U)), fnOf U hg t ^ n * f = fnOf U hg a := by
  obtain ⟨b, rfl⟩ := exists_fnOf_eq ht h
  have := hU.isLocalization_basicOpen t
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj t b
  refine ⟨n, a, ?_⟩
  have e' := congrArg (fnOf _ ht) e
  rw [map_mul, map_pow] at e'
  have k (c : Γ(X, U)) : fnOf _ ht (algebraMap Γ(X, U) Γ(X, X.basicOpen t) c) =
      fnOf U hg c := fnOf_resG (X.basicOpen_le t) ht c
  rw [k, k] at e'
  rw [← e', mul_comm]

theorem exists_regularAt {U : X.Opens} (hU : IsAffineOpen U) {D : CartierDiv X} {x : X}
    (hxU : x ∈ U) {g : X.functionFieldˣ} (hg : D.IsEqn x g) {y : X} (hyU : y ∈ U) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      D.RegularAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) := by
  obtain ⟨W, hW, hgW⟩ := hg.exists_nhds
  obtain ⟨V, hV, g', hgV⟩ := D.exists_isEqn_nhds y
  obtain ⟨t, htW, ht⟩ := hU.exists_basicOpen_le ⟨x, hW⟩ hxU
  obtain ⟨t', htV, ht'⟩ := hU.exists_basicOpen_le ⟨y, hV⟩ hyU
  have hgen : genericPoint X ∈ X.basicOpen (t * t') := by
    rw [X.basicOpen_mul]; exact ⟨gen_mem ht, gen_mem ht'⟩
  obtain ⟨n, a, e⟩ := exists_pow_mul_eq hU (gen_mem hxU) (t * t') hgen
    (f := (g' : X.functionField) / g) fun z hz => by
      rw [X.basicOpen_mul] at hz
      exact ((hgW z (htW hz.1)).iff_unitAt.1 (hgV z (htV hz.2))).regAt
  have hu : UnitAt y (fnOf U (gen_mem hxU) (t' ^ n)) := by
    rw [map_pow]; exact unitAt_pow ((unitAt_fnOf_iff hyU _ _).2 ht') n
  refine ⟨t ^ n, (unitAt_fnOf_iff hxU (gen_mem hxU) _).1 (by
    rw [map_pow]; exact unitAt_pow ((unitAt_fnOf_iff hxU _ _).2 ht) n), g', hgV y hV, ?_⟩
  have := (regAt_fnOf hyU (gen_mem hxU) a).mul hu.inv.regAt
  rw [← e] at this
  convert this using 1
  have h0 := hu.ne_zero
  rw [map_pow] at h0
  rw [map_mul, map_pow, map_pow, mul_pow]
  field_simp

theorem exists_vanishesAt {U : X.Opens} (hU : IsAffineOpen U) {D : CartierDiv X} {x : X}
    (hxU : x ∈ U) {g : X.functionFieldˣ} (hg : D.IsEqn x g) {y : X} (hyU : y ∈ U)
    (hxy : x ∉ closure ({y} : Set X)) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) := by
  obtain ⟨s, hs, hreg⟩ := exists_regularAt hU hxU hg hyU
  obtain ⟨t, htU, ht⟩ := hU.exists_basicOpen_le
    (V := ⟨(closure ({y} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩) ⟨x, hxy⟩ hxU
  have hz : ZeroAt y (fnOf U (gen_mem hxU) t) := zeroAt_iff.2 ⟨regAt_fnOf hyU _ _,
    fun h => htU ((unitAt_fnOf_iff hyU _ _).1 h) (subset_closure rfl)⟩
  refine ⟨t * s, by rw [X.basicOpen_mul]; exact ⟨ht, hs⟩, ?_⟩
  obtain ⟨g', hg', hr⟩ := hreg
  refine ⟨g', hg', ?_⟩
  rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (fnOf U (gen_mem hxU) s)]
  exact hz.mul hr

theorem exists_generatesAt_vanishesAt : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U →
    ∀ (D : CartierDiv X) (x : X), x ∈ U →
    ∀ (T : Finset X), (∀ y ∈ T, y ∈ U) → (∀ y ∈ T, y ≠ x → x ∉ closure ({y} : Set X)) →
    ∃ f : X.functionField, D.GeneratesAt x f ∧ ∀ y ∈ T, y ≠ x → D.VanishesAt y f := by
  intro X _ U hU D x hxU T hTU hT
  classical
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  suffices ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧ ∀ y ∈ T, y ≠ x →
      D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) by
    obtain ⟨s, hs, h⟩ := this
    refine ⟨_, ⟨g, hg, ?_⟩, h⟩
    rw [mul_assoc, inv_mul_cancel₀ g.ne_zero, mul_one]
    exact (unitAt_fnOf_iff hxU _ _).2 hs
  have key (y : X) (hyU : y ∈ U) (s t : Γ(X, U))
      (h : D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹)) :
      D.VanishesAt y (fnOf U (gen_mem hxU) (s * t) * (g : X.functionField)⁻¹) := by
    obtain ⟨g', hg', hr⟩ := h
    refine ⟨g', hg', ?_⟩
    have := hr.mul (regAt_fnOf hyU (gen_mem hxU) t)
    convert this using 1
    rw [map_mul]; ring
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simpa using hxU, by simp⟩
  | insert y T _ ih =>
    obtain ⟨s, hs, h⟩ := ih (fun z hz => hTU z (Finset.mem_insert_of_mem hz))
      fun z hz => hT z (Finset.mem_insert_of_mem hz)
    by_cases hyx : y = x
    · refine ⟨s, hs, fun z hz hzx => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact (hzx hyx).elim
      · exact h z hz hzx
    have hyU := hTU y (Finset.mem_insert_self _ _)
    obtain ⟨t, ht, h'⟩ := exists_vanishesAt hU hxU hg hyU (hT y (Finset.mem_insert_self _ _) hyx)
    refine ⟨s * t, by rw [X.basicOpen_mul]; exact ⟨hs, ht⟩, fun z hz hzx => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [mul_comm s]; exact key _ hyU _ _ h'
    · exact key _ (hTU z (Finset.mem_insert_of_mem hz)) _ _ (h z hz hzx)

end GlobalTheory.Cartier.CommonEqnOpen
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.Cartier.RatSecDiv

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_mul_unit_iff {x : X} {a u : X.functionField} (hu : UnitAt x u) :
    UnitAt x (a * u) ↔ UnitAt x a := by
  refine ⟨fun h => ?_, fun h => h.mul hu⟩
  have e : a = a * u * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one]
  rw [e]; exact h.mul hu.inv

theorem local_of {D D' : CartierDiv X} {V : X.Opens} {h : X.functionField}
    (H : ∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V))
    {x : X} {gi rk : X.functionFieldˣ} (hi : D.IsEqn x gi) (hk : D'.IsEqn x rk) :
    RegAt x (h * (gi : X.functionField) / (rk : X.functionField)) ∧
      (UnitAt x (h * (gi : X.functionField) / (rk : X.functionField)) ↔ x ∈ V) := by
  obtain ⟨g, g', hg, hg', hr, hu⟩ := H x
  have u : UnitAt x (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) :=
    (hg.iff_unitAt.1 hi).mul (hk.iff_unitAt.1 hg')
  have e : h * (gi : X.functionField) / (rk : X.functionField) =
      h * (g : X.functionField) / (g' : X.functionField) *
        (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) := by
    have := g.ne_zero; have := g'.ne_zero; have := rk.ne_zero
    field_simp
  rw [e, unitAt_mul_unit_iff u]
  exact ⟨hr.mul u.regAt, hu⟩

end GlobalTheory.Cartier.RatSecDiv


open GlobalTheory.Cartier.RatSecDiv in
theorem GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq :
    ∀ {X : Scheme.{0}} [IsIntegral X] (D D' : CartierDiv X) (L : LB X) (r : L.ι → X.functionFieldˣ),
    Presents D' L r → ∀ (V : X.Opens) (h : X.functionField),
    (∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V)) →
    ∃ θ : (LB.div (toLB D) L).Sec, nonzeroLocus θ = V := by
  intro X _ D D' L r hP V h H
  have key (p : (LB.div (toLB D) L).ι) : ∃ a : Γ(X, (LB.div (toLB D) L).U p), ∀ hp,
      fnOf _ hp a = h * (p.1.1.2 : X.functionField) / (r p.2 : X.functionField) := by
    by_cases hp : genericPoint X ∈ (LB.div (toLB D) L).U p
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hp fun x hx =>
        (local_of H (p.1.2.2 x hx.1) (hP.isEqn p.2 x hx.2)).1
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (hp h').elim⟩
  choose a ha using key
  refine ⟨⟨a, fun p q => fn_ext fun hpq => ?_⟩, ?_⟩
  · have hp : genericPoint X ∈ (LB.div (toLB D) L).U p := hpq.1
    have hq : genericPoint X ∈ (LB.div (toLB D) L).U q := hpq.2
    refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg _ (fnOf_resG _ hpq _))).symm)
    rw [ha p hp, ha q hq]
    have eL := hP.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2)
    have e1 : fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val =
        (p.1.1.2 : X.functionField) / (q.1.1.2 : X.functionField) := fnOf_toLB_g _ _ _
    have eg : fnOf _ hpq ((LB.div (toLB D) L).g p q).val =
        fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val *
          (fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val)⁻¹ := by
      change fnOf _ hpq ((res _ ((toLB D).g p.1 q.1) * (res _ (L.g p.2 q.2))⁻¹ : Γ(X, _)ˣ).val) = _
      erw [Units.val_mul, map_mul, map_units_inv]
      exact congrArg₂ (· * ·) (fnOf_resG _ _ _) (congrArg _ (fnOf_resG _ _ _))
    have eL' : fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val =
        (r p.2 : X.functionField) / (r q.2 : X.functionField) :=
      (eq_div_of_mul_eq (r q.2).ne_zero eL.symm)
    rw [eg, e1, eL']
    have := (p.1.1.2).ne_zero; have := (q.1.1.2).ne_zero
    have := (r p.2).ne_zero; have := (r q.2).ne_zero
    field_simp
  · have hmem (p : (LB.div (toLB D) L).ι) (y : X) (hy : y ∈ (LB.div (toLB D) L).U p) :
        y ∈ X.basicOpen (a p) ↔ y ∈ V := by
      rw [← unitAt_fnOf_iff hy (gen_mem hy), ha p (gen_mem hy)]
      exact (local_of H (p.1.2.2 y hy.1) (hP.isEqn p.2 y hy.2)).2
    refine le_antisymm (iSup_le fun p y hy => (hmem p y (X.basicOpen_le _ hy)).1 hy) fun y hy => ?_
    obtain ⟨i, hi⟩ := exists_chart (isLB_toLB D) y
    obtain ⟨k, hk⟩ := exists_chart hP.isLB y
    exact Opens.mem_iSup.2 ⟨(i, k), (hmem (i, k) y ⟨hi, hk⟩).2 hy⟩
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharIndepAt

variable {X : Scheme.{0}} [IsIntegral X] {x : X}

def liftStalk (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f)) :
    X.presheaf.stalk x →+* X.presheaf.stalk x where
  toFun s := (h _ ⟨s, rfl⟩).choose
  map_one' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_one, map_one])
  map_mul' s t := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_mul, map_mul, map_mul, (h _ ⟨s, rfl⟩).choose_spec,
      (h _ ⟨t, rfl⟩).choose_spec])
  map_zero' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_zero, map_zero])
  map_add' s t := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_add (f := _), map_add (f := _), map_add (f := _), (h _ ⟨s, rfl⟩).choose_spec,
      (h _ ⟨t, rfl⟩).choose_spec])

theorem algebraMap_liftStalk (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f))
    (s : X.presheaf.stalk x) :
    algebraMap _ X.functionField (liftStalk σ h s) = σ (algebraMap _ X.functionField s) :=
  (h _ ⟨s, rfl⟩).choose_spec

theorem residue_liftStalk_eq_iff (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f)) :
    (IsLocalRing.residue (X.presheaf.stalk x)).comp (liftStalk σ h) = IsLocalRing.residue (X.presheaf.stalk x) ↔
      ∀ f, RegAt x f → ZeroAt x (σ f - f) := by
  constructor
  · rintro e f ⟨s, rfl⟩
    refine ⟨liftStalk σ h s - s, ?_, by rw [map_sub, algebraMap_liftStalk]⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact RingHom.congr_fun e s
  · intro H
    ext s
    obtain ⟨m, hm, e⟩ := H _ ⟨s, rfl⟩
    have : m = liftStalk σ h s - s := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
      rw [e, map_sub, algebraMap_liftStalk])
    subst this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
    exact hm

end GlobalTheory.CharIndepAt


open GlobalTheory.CharIndepAt in
theorem GlobalTheory.CharIndepAt.main : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U → ∀ (x : X) (hx : x ∈ U)
    (ι : Type) [Fintype ι] (σ : ι → X.functionField →+* X.functionField) (u : ι → X.functionField),
    (∀ i f, RegAt x f → RegAt x (σ i f)) → (∀ i f, ZeroAt x f → ZeroAt x (σ i f)) →
    (∀ i, RegAt x (u i)) →
    (∀ i, (∀ f, RegAt x f → ZeroAt x (σ i f - f)) → ZeroAt x (u i - 1)) →
    (∀ n : ℕ, n ≠ 0 → UnitAt x (n : X.functionField)) →
    (∃ i, ∀ f, RegAt x f → ZeroAt x (σ i f - f)) →
    ∃ a : Γ(X, U), UnitAt x (∑ i, σ i (fnOf U (gen_mem hx) a) * u i) := by

  intro X _ U hU x hx ι _ σ u h1 h2 h3 h4 h5 h6
  classical
  let R := X.presheaf.stalk x
  let res := IsLocalRing.residue R
  let g : Γ(X, U) →+* R := (X.presheaf.germ U x hx).hom
  let ψ : ι → (R →+* IsLocalRing.ResidueField R) := fun i => res.comp (liftStalk (σ i) (h1 i))
  let χ : ι → (Γ(X, U) →* IsLocalRing.ResidueField R) := fun i => ((ψ i).comp g : Γ(X, U) →+* _)
  let χ₀ : Γ(X, U) →* IsLocalRing.ResidueField R := (res.comp g : Γ(X, U) →+* _)
  letI : Algebra Γ(X, U) R := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hl : IsLocalization.AtPrime R (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have hext : ∀ i, χ i = χ₀ → ψ i = res := by
    intro i e
    refine IsLocalization.ringHom_ext (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl ?_
    ext a
    exact DFunLike.congr_fun e a
  choose t ht using h3
  have hone : ∀ j, χ j = χ₀ → res (t j) = 1 := by
    intro j e
    obtain ⟨m, hm, em⟩ := h4 j ((residue_liftStalk_eq_iff (σ j) (h1 j)).1 (hext j e))
    have : m = t j - 1 := IsFractionRing.injective R X.functionField (by rw [em, map_sub, map_one, ht])
    subst this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at hm
    exact hm
  obtain ⟨i₀, hi₀⟩ := h6
  have h0 : χ i₀ = χ₀ := by
    have := (residue_liftStalk_eq_iff (σ i₀) (h1 i₀)).2 hi₀
    ext a
    exact RingHom.congr_fun this (g a)
  by_contra hne
  push_neg at hne
  have hsum : ∀ a : Γ(X, U), ∑ i, res (t i) * χ i a = 0 := by
    intro a
    by_contra hz
    refine hne a ⟨∑ i, liftStalk (σ i) (h1 i) (g a) * t i, ?_, ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
      intro h
      apply hz
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, mul_comm]
      rfl
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, algebraMap_liftStalk, ht]
      congr 2
      exact algebraMap_germ hx a
  have hli := linearIndependent_monoidHom Γ(X, U) (IsLocalRing.ResidueField R)
  rw [linearIndependent_iff'] at hli
  let c : (Γ(X, U) →* IsLocalRing.ResidueField R) → IsLocalRing.ResidueField R :=
    fun φ => ∑ i ∈ Finset.univ.filter (fun i => χ i = φ), res (t i)
  have hcomb : ∑ φ ∈ Finset.univ.image χ, c φ • (φ : Γ(X, U) → IsLocalRing.ResidueField R) = 0 := by
    ext a
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hsum a, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image χ) (g := χ)
      (fun i _ => Finset.mem_image_of_mem χ (Finset.mem_univ i))]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hc := hli _ c hcomb χ₀ (by rw [← h0]; exact Finset.mem_image_of_mem χ (Finset.mem_univ i₀))
  have hc' : c χ₀ = ((Finset.univ.filter fun i => χ i = χ₀).card : IsLocalRing.ResidueField R) := by
    change ∑ i ∈ Finset.univ.filter (fun i => χ i = χ₀), res (t i) = _
    rw [Finset.sum_congr rfl fun i hi => hone i (Finset.mem_filter.1 hi).2, Finset.sum_const, nsmul_one]
  have hn : (Finset.univ.filter fun i => χ i = χ₀).card ≠ 0 :=
    (Finset.card_pos.2 ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩).ne'
  obtain ⟨s, hs, es⟩ := h5 _ hn
  have : s = ((Finset.univ.filter fun i => χ i = χ₀).card : R) :=
    IsFractionRing.injective R X.functionField (by rw [es, map_natCast])
  subst this
  have := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hs
  rw [map_natCast, ← hc'] at this
  exact this hc
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.PullCartier

theorem fnOf_app {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    {U : W.Opens} (h : genericPoint M ∈ f ⁻¹ᵁ U) (a : Γ(W, U)) :
    fnOf (f ⁻¹ᵁ U) h ((f.app U).hom a) =
      GlobalTheory.functionFieldMap f (fnOf U (gen_mem (x := f (genericPoint M)) h) a) := by
  have hx : f (genericPoint M) ∈ U := h
  rw [← algebraMap_germ hx a, GlobalTheory.functionFieldMap_algebraMap, Scheme.Hom.germ_stalkMap_apply f U _ hx a]
  exact (algebraMap_germ (X := M) (U := f ⁻¹ᵁ U) (x := genericPoint M) h _).symm

theorem cls_toLB_pull : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    (D₀ : CartierDiv W) (D₁ : CartierDiv M),
    (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) →
      cls (toLB D₁) (isLB_toLB D₁) = CechPic.pull f (cls (toLB D₀) (isLB_toLB D₀)) := by
  intro M W _ _ f _ D₀ D₁ hD
  have hP : Presents D₁ ((toLB D₀).pull f)
      fun J => Units.map (GlobalTheory.functionFieldMap f).toMonoidHom (J PUnit.unit).1.2 := by
    refine ⟨pull_isLB (isLB_toLB D₀) f, fun J K h => ?_,
      fun J x hx => hD x _ ((J PUnit.unit).2.2 _ (mem_pull.1 hx))⟩
    have hle : ((toLB D₀).pull f).U J ⊓ ((toLB D₀).pull f).U K ≤
        f ⁻¹ᵁ ((toLB D₀).U (J PUnit.unit) ⊓ (toLB D₀).U (K PUnit.unit)) :=
      fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
    have e0 : ((toLB D₀).pull f).g J K =
        res hle (pullU f _ ((toLB D₀).g (J PUnit.unit) (K PUnit.unit))) :=
      by dsimp only [LB.pull, LB.LinComb]; rw [Fintype.prod_unique, zpow_one]; rfl
    have e : fnOf _ h (((toLB D₀).pull f).g J K).val =
        fnOf _ (hle h) ((f.app _).hom ((toLB D₀).g (J PUnit.unit) (K PUnit.unit)).val) := by
      rw [e0, LB.val_res, fnOf_resG]
      rfl
    rw [e, fnOf_app, fnOf_toLB_g]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [← map_mul, div_mul_cancel₀ _ (Units.ne_zero _)]
  rw [← cls_pull (isLB_toLB D₀) f hP.isLB, ← toPic_apply, hP.toPic_eq]

end GlobalTheory.PullCartier
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

theorem _root_.GlobalTheory.T.exists_bump_shintani_alt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) ∧ ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w) := by
  first
  | exact @GlobalTheory.JSW.BumpShintani.exists_bump_shintani
  | exact GlobalTheory.JSW.BumpShintani.exists_bump_shintani
  | (intros; apply GlobalTheory.JSW.BumpShintani.exists_bump_shintani <;> assumption)
end
