module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqMulOfContinuousOnQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle984
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle528
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private lemma smul_dlog_mem_forms {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (y : X)
    (g : X.functionFieldˣ) (hg : _root_.GlobalTheory.LogDR.LogUnit Z y g) (b : X.functionField)
    (hb : b ∈ _root_.GlobalTheory.LogDR.locRing y) :
    ExteriorAlgebra.ι X.functionField (b • _root_.GlobalTheory.LogDR.dlog g) ∈
      _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
        (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1 := by
  unfold _root_.GlobalTheory.DI.forms
  refine AddSubgroup.subset_closure ⟨b, hb, fun _ => _root_.GlobalTheory.LogDR.dlog g,
    fun _ => ⟨g, hg, rfl⟩, ?_⟩
  rw [map_smul, ExteriorAlgebra.ιMulti_apply]
  simp

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private lemma logUnit_of_isUnit_stalk {X : Scheme.{0}} [IsIntegral X] (Z : Set X)
    (y : X) (g : X.functionFieldˣ) (a : X.presheaf.stalk y) (ha : IsUnit a)
    (hg : algebraMap (X.presheaf.stalk y) X.functionField a = g) :
    _root_.GlobalTheory.LogDR.LogUnit Z y g := by
  intro z hz _
  refine ⟨X.presheaf.stalkSpecializes hz a, ha.map (X.presheaf.stalkSpecializes hz).hom, ?_⟩
  rw [← hg]
  change (X.presheaf.stalkSpecializes _) ((X.presheaf.stalkSpecializes hz) a) =
    (X.presheaf.stalkSpecializes _) a
  rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.dK_dlog_mem_forms_one : ∀ {X : Scheme.{0}} [IsIntegral X]
    (Z : Set X) (y : X), (∀ w ∈ _root_.GlobalTheory.LogDR.locRing y,
      ExteriorAlgebra.ι X.functionField (_root_.GlobalTheory.LogDR.dK w) ∈
        _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
          (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1) ∧
      ∀ g, _root_.GlobalTheory.LogDR.LogUnit Z y g → ExteriorAlgebra.ι X.functionField (_root_.GlobalTheory.LogDR.dlog g) ∈
        _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
          (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1 := by
  intro X _ Z y
  refine ⟨fun w hw => ?_, fun g hg => ?_⟩
  · obtain ⟨a, rfl⟩ := _root_.GlobalTheory.LogDR.mem_locRing.mp hw
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with ha | ha
    · set U := (ha.map (algebraMap (X.presheaf.stalk y) X.functionField)).unit with hU
      have hUv : (U : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField a := rfl
      have key := smul_dlog_mem_forms Z y U
        (logUnit_of_isUnit_stalk Z y U a ha hUv.symm) _ hw
      convert key using 2
      unfold _root_.GlobalTheory.LogDR.dlog _root_.GlobalTheory.LogDR.dK
      rw [smul_smul, ← hUv, Units.mul_inv, one_smul]
    · set U := (ha.map (algebraMap (X.presheaf.stalk y) X.functionField)).unit with hU
      have hUv : (U : X.functionField) =
          algebraMap (X.presheaf.stalk y) X.functionField (1 - a) := rfl
      have hmem : -(U : X.functionField) ∈ _root_.GlobalTheory.LogDR.locRing y :=
        neg_mem (_root_.GlobalTheory.LogDR.mem_locRing.mpr ⟨1 - a, hUv.symm⟩)
      have key := smul_dlog_mem_forms Z y U
        (logUnit_of_isUnit_stalk Z y U (1 - a) ha hUv.symm) _ hmem
      convert key using 2
      unfold _root_.GlobalTheory.LogDR.dlog _root_.GlobalTheory.LogDR.dK
      rw [smul_smul, neg_mul, Units.mul_inv, neg_smul, one_smul, hUv, map_sub, map_one,
        map_sub, Derivation.map_one_eq_zero, zero_sub, neg_neg]
  · simpa using smul_dlog_mem_forms Z y g hg 1 (one_mem _)

end GlobalTheory.DI
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LogDR.isExtD_extD : ∀ (K : Type) [Field K], IsExtD ℤ K (extD K) := by
  intro K _
  refine { mul := ?_, sq := ?_, alg := ?_ }
  ·
    intro x y
    rw [extD_apply, extD_apply, extD_apply, CechDR.dDR_mul, add_comm]
    rfl
  · intro x
    rw [extD_apply, extD_apply, CechDR.dDR_dDR]
  · intro a
    rw [extD_apply, CechDR.dDR_algebraMap]
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

namespace LatTwist

open GlobalTheory.Twist

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M M' : X → AddSubgroup V} {F : X.Modules} {L : LB X} {r : L.ι → X.functionFieldˣ}

theorem sec_eq_of_not_gen {W : X.Opens} (hW : genericPoint X ∉ W) (s t : Γ(F, W)) : s = t :=
  sec_ext_of_cover (ι := PEmpty.{1}) (fun k => k.elim) (fun k => k.elim)
    (by intro x hx; exact (hW (gen_mem hx)).elim) (fun k => k.elim)

theorem val_resM (hM : LatModel M F) {U W : X.Opens} (e : W ≤ U) (h : genericPoint X ∈ W)
    (s : Γ(F, U)) : hM.val W h (resM F e s) = hM.val U (e h) s :=
  hM.res U W e h s


variable (r) in
def tval (hM : LatModel M F) (i : L.ι) (hi : genericPoint X ∈ L.U i) (U : X.Opens)
    (h : genericPoint X ∈ U) : Γ(twist F L, U) →+ V where
  toFun s := (r i)⁻¹ • hM.val (U ⊓ L.U i) (memInf h hi) (coord s i)
  map_zero' := by rw [coord_zero, map_zero, smul_zero]
  map_add' s t := by rw [coord_add, map_add (f := _), smul_add]

theorem tval_apply (hM : LatModel M F) (i : L.ι) (hi : genericPoint X ∈ L.U i) (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(twist F L, U)) :
    tval r hM i hi U h s = (r i)⁻¹ • hM.val (U ⊓ L.U i) (memInf h hi) (coord s i) := rfl

theorem val_coord_rel (hM : LatModel M F) {U : X.Opens} (s : Γ(twist F L, U)) (i j : L.ι)
    (hU : genericPoint X ∈ U) (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j) :
    hM.val (U ⊓ L.U i) (memInf hU hi) (coord s i) =
      fnOf (L.U i ⊓ L.U j) (memInf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) •
        hM.val (U ⊓ L.U j) (memInf hU hj) (coord s j) := by
  have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j := memInf (memInf hU hi) hj
  have e := coord_rel s i j (W := U ⊓ L.U i ⊓ L.U j) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_inf_right _ inf_le_right)
  have e1 := val_resM hM (inf_le_left : U ⊓ L.U i ⊓ L.U j ≤ U ⊓ L.U i) hW (coord s i)
  have e2 := val_resM hM (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    U ⊓ L.U i ⊓ L.U j ≤ U ⊓ L.U j) hW (coord s j)
  rw [← e1, ← e2, e, hM.smul, fnOf_resG]

theorem tval_eq (hM : LatModel M F) (hr : IsRatSec L r) {U : X.Opens} (h : genericPoint X ∈ U)
    (i j : L.ι) (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j)
    (s : Γ(twist F L, U)) : tval r hM i hi U h s = tval r hM j hj U h s := by
  rw [tval_apply, tval_apply, val_coord_rel hM s i j h hi hj, Units.smul_def, Units.smul_def,
    smul_smul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hr i j (memInf hi hj)]
  congr 1
  have hg : fnOf (L.U i ⊓ L.U j) (memInf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) ≠ 0 :=
    ((L.g i j).isUnit.map (fnOf (L.U i ⊓ L.U j) (memInf hi hj))).ne_zero
  have hrj : (r j : X.functionField) ≠ 0 := (r j).ne_zero
  field_simp

end LatTwist

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR

namespace LatTwist

open GlobalTheory.Twist

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M M' : X → AddSubgroup V} {F : X.Modules} {D : CartierDiv X} {L : LB X}
  {r : L.ι → X.functionFieldˣ}

theorem mem_of_mem_latSec {N : X → AddSubgroup V} {U : X.Opens} {v : V} (hv : v ∈ latSec N U)
    {y : X} (hy : y ∈ U) : v ∈ N y :=
  AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv y) hy

theorem mem_latSec {N : X → AddSubgroup V} {U : X.Opens} {v : V} (hv : ∀ y ∈ U, v ∈ N y) :
    v ∈ latSec N U :=
  AddSubgroup.mem_iInf.2 fun y => AddSubgroup.mem_iInf.2 fun hy => hv y hy

def twistModel (hP : Presents D L r)
    (hE : ∀ y (g : X.functionFieldˣ) (v : V), D.IsEqn y g → (v ∈ M' y ↔ (g : X.functionField) • v ∈ M y))
    (hM : LatModel M F) (i₀ : L.ι) (hi₀ : genericPoint X ∈ L.U i₀) :
    LatModel M' (twist F L) where
  val U h := tval r hM i₀ hi₀ U h
  inj U h := by
    intro s t e
    refine sec_ext fun i => ?_
    by_cases hi : genericPoint X ∈ L.U i
    · have e' : tval r hM i hi U h s = tval r hM i hi U h t := by
        rw [← tval_eq hM hP.isRatSec h i₀ i hi₀ hi, ← tval_eq hM hP.isRatSec h i₀ i hi₀ hi]
        exact e
      rw [tval_apply, tval_apply] at e'
      exact hM.inj (U ⊓ L.U i) (memInf h hi) (MulAction.injective _ e')
    · exact sec_eq_of_not_gen (fun hh : genericPoint X ∈ U ⊓ L.U i => hi hh.2) _ _
  range U h := by
    ext v
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨s, rfl⟩
      refine mem_latSec fun y hy => ?_
      obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hP.isLB y
      have hgi : genericPoint X ∈ L.U i := gen_mem hi
      rw [tval_eq hM hP.isRatSec h i₀ i hi₀ hgi, hE y (r i) _ (hP.isEqn i y hi), tval_apply,
        ← Units.smul_def, smul_inv_smul]
      have hw : hM.val (U ⊓ L.U i) (memInf h hgi) (coord s i) ∈ (hM.val (U ⊓ L.U i) (memInf h hgi)).range :=
        AddMonoidHom.mem_range.2 ⟨_, rfl⟩
      rw [hM.range] at hw
      exact mem_of_mem_latSec hw (memInf hy hi)
    · intro hv
      have key : ∀ i, ∃ t : Γ(F, U ⊓ L.U i),
          ∀ hi : genericPoint X ∈ L.U i, hM.val (U ⊓ L.U i) (memInf h hi) t = r i • v := by
        intro i
        by_cases hi : genericPoint X ∈ L.U i
        · have hm : r i • v ∈ latSec M (U ⊓ L.U i) := mem_latSec fun y hy => by
            rw [Units.smul_def, ← hE y (r i) v (hP.isEqn i y hy.2)]
            exact mem_of_mem_latSec hv hy.1
          rw [← hM.range (U ⊓ L.U i) (memInf h hi)] at hm
          obtain ⟨t, ht⟩ := hm
          exact ⟨t, fun _ => ht⟩
        · exact ⟨0, fun h' => (hi h').elim⟩
      choose t ht using key
      have hmem : t ∈ Twist.secGroup F L U := by
        intro i j
        by_cases hij : genericPoint X ∈ L.U i ⊓ L.U j
        · have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j := (memInf (memInf h hij.1) hij.2)
          apply hM.inj (U ⊓ L.U i ⊓ L.U j) hW
          rw [hM.smul, val_resM, val_resM, fnOf_resG, ht i hij.1, ht j hij.2, Units.smul_def,
            Units.smul_def, smul_smul, hP.isRatSec i j hij]
        · exact sec_eq_of_not_gen (fun hh : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j => hij (memInf hh.1.2 hh.2)) _ _
      exact ⟨mkSec t hmem, by rw [tval_apply, coord_mkSec, ht i₀ hi₀, inv_smul_smul]⟩
  res U W e h s := by
    change tval r hM i₀ hi₀ W h (resM (twist F L) e s) = tval r hM i₀ hi₀ U (e h) s
    rw [tval_apply, tval_apply, coord_resM, val_resM]
  smul U h a s := by
    change tval r hM i₀ hi₀ U h (a • s) = fnOf U h a • tval r hM i₀ hi₀ U h s
    rw [tval_apply, tval_apply, coord_smul, hM.smul, fnOf_resG, Units.smul_def, Units.smul_def,
      smul_smul, smul_smul, mul_comm]

end LatTwist

theorem nonempty_latModel_twist : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M M' : X → AddSubgroup V) (F : X.Modules) (D : CartierDiv X)
    (L : LB X) (r : L.ι → X.functionFieldˣ), Presents D L r →
    (∀ y (g : X.functionFieldˣ) (v : V), D.IsEqn y g → (v ∈ M' y ↔ (g : X.functionField) • v ∈ M y)) →
    LatModel M F → Nonempty (LatModel M' (twist F L)) := by
  intro X _ V _ _ M M' F D L r hP hE hM
  obtain ⟨i₀, hi₀⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hP.isLB (genericPoint X)
  exact ⟨LatTwist.twistModel hP hE hM i₀ hi₀⟩

end GlobalTheory.LogDR
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory


open AffinePoints in
theorem exists_eq_of_continuous_quotient_algHom {A : Type} [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [IsIntegrallyClosed A] {ψ : (A →ₐ[ℂ] ℂ) → ℂ} (hψ : Continuous ψ)
    {a b : A} (hb : b ≠ 0) (hab : ∀ e : A →ₐ[ℂ] ℂ, e b * ψ e = e a) :
    ∃ c : A, ∀ e : A →ₐ[ℂ] ℂ, e c = ψ e := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have key (s r : A) (h : b * s = a * r) (e : A →ₐ[ℂ] ℂ) : e s = ψ e * e r := by
    refine congrFun (Continuous.ext_on (dense_nonvanishing hb) (continuous_eval s)
      (hψ.mul (continuous_eval r)) fun w hw => mul_left_cancel₀ hw ?_) e
    have h1 := congrArg w h
    rw [map_mul, map_mul, ← hab w] at h1
    exact h1.trans (_root_.mul_assoc _ _ _)
  by_cases H : b ∣ a
  · obtain ⟨c, hc⟩ := H
    exact ⟨c, fun e => by rw [key c 1 (by rw [hc, _root_.mul_one]) e, map_one, _root_.mul_one]⟩
  obtain ⟨p, hp, s, r, hs, hr, h⟩ := ContinuousQuotient.exists_prime_of_not_dvd hb H
  have h0 : Ideal.Quotient.mkₐ ℂ p s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨e, he⟩ := not_forall.mp fun h => h0 (eq_zero_of_forall_algHom_complex _ h)
  refine (he ((key s r h (e.comp (Ideal.Quotient.mkₐ ℂ p))).trans ?_)).elim
  change _ * e (Ideal.Quotient.mk p r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, mul_zero]

theorem isIntegrallyClosed_sections_of_isDomain {Y : Scheme.{0}}
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(Y, U)] : IsIntegrallyClosed Γ(Y, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp ↦ ?_
  let P : Spec Γ(Y, U) := ⟨p, hp.isPrime⟩
  have hy : hU.fromSpec P ∈ U := hU.range_fromSpec.le ⟨P, rfl⟩
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk (hU.fromSpec P)) :=
    Y.presheaf.algebra_section_stalk (U := U) ⟨_, hy⟩
  have h : IsLocalization p.primeCompl (Y.presheaf.stalk (hU.fromSpec P)) :=
    hU.isLocalization_stalk' P hy
  have := hY (hU.fromSpec P)
  exact IsIntegrallyClosed.of_equiv (R := Y.presheaf.stalk (hU.fromSpec P))
    (IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk (hU.fromSpec P))
      (Localization.AtPrime p)).toRingEquiv


open AffinePoints in
theorem exists_ev_eq_of_continuousOn_quotient :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ (V : Y.Opens), IsAffineOpen V → IsDomain Γ(Y, V) → ∀ φ : CxPts p (RingHom.id ℂ) → ℂ, ContinuousOn φ (ptsIn p (RingHom.id ℂ) V) → ∀ a b : Γ(Y, V), b ≠ 0 → (∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V b y * φ y = ev p (RingHom.id ℂ) V a y) → ∃ c : Γ(Y, V), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V c y = φ y := by
  intro Y p D hp U hU hdom φ hφ a b hb hab
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hN := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hsm).2.1
  have := isIntegrallyClosed_sections_of_isDomain (fun y => (hN y).2) hU
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  let : Algebra ℂ Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType ℂ Γ(Y, U) := hc
  let s (e : Γ(Y, U) →ₐ[ℂ] ℂ) : CxPts p (RingHom.id ℂ) := ofHom hU e.toRingHom fun c => e.commutes c
  have hm (e) : s e ∈ ptsIn p (RingHom.id ℂ) U := ofHom_mem _ _ _
  have hv (e) (f) : ev p (RingHom.id ℂ) U f (s e) = e f := ev_ofHom _ _ _ _
  have hs : Continuous s := continuous_iff_continuousAt.2 fun e => tendsto_subtype_rng.2
    (Points.tendsto_of_isAffineOpen hU (hm e) (Filter.Eventually.of_forall hm) fun f => by
      have h : Continuous fun w => ev p (RingHom.id ℂ) U f (s w) := by
        simp only [hv]; exact continuous_eval f
      exact h.continuousAt)
  obtain ⟨c, hc⟩ := exists_eq_of_continuous_quotient_algHom (hφ.comp_continuous hs hm) (a := a) hb
    fun e => by rw [← hv, ← hv]; exact hab _ (hm e)
  refine ⟨c, fun y hy => ?_⟩
  let e : Γ(Y, U) →ₐ[ℂ] ℂ :=
    { evHom hy with commutes' := fun t => (ev_eq hy _).symm.trans (ev_algX hy t) }
  have he : s e = y := Subtype.ext (Points.ext_of_valR hU (hm e) hy fun f =>
    (hv e f).trans (ev_eq hy f).symm)
  rw [← he, hv]
  exact hc e

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem spread_le_at {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (hW : W.Hyp) (hD : W.IsDiv) (τ : ι)
    (j : ℕ) (hj : j ≤ N - W.kc) :
    (j : ℝ) * ((⨆ i, reWt W.u' τ i) - ⨅ i, reWt W.u' τ i) ≤ 6 * ∑ i, |(W.u' τ i : ℝ)| := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.T.dividedWeight_nodes_far_and_spread ι N W hW hD τ
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hW.p_lt
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite (f := reWt W.u' τ)
  obtain ⟨b, hb⟩ := exists_eq_ciInf_of_finite (f := reWt W.u' τ)
  have hsp : (⨆ i, reWt W.u' τ i) - ⨅ i, reWt W.u' τ i ≤ 3 / 2 * W.w τ / W.T := by
    rw [← ha, ← hb]; exact h2 a b
  have h0 : 0 ≤ 3 / 2 * W.w τ / W.T := by simpa using h2 a a
  have hkN : W.kc < N := hW.kc_lt.trans hW.p_lt
  set s : Finset (Fin N) := Finset.Ici (⟨W.kc, hkN⟩ : Fin N) with hs
  have hcard : s.card = N - W.kc := by simp [hs]
  have hsum : (s.card : ℝ) * (W.w τ / (4 * W.T)) ≤ ∑ i ∈ s, |(W.u' τ i : ℝ)| := by
    have := Finset.card_nsmul_le_sum s (fun i => |(W.u' τ i : ℝ)|) (W.w τ / (4 * W.T))
      (fun i hi => (h1 i (by simpa [hs, Fin.le_def] using hi)).2)
    simpa [nsmul_eq_mul] using this
  have hsub : ∑ i ∈ s, |(W.u' τ i : ℝ)| ≤ ∑ i, |(W.u' τ i : ℝ)| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)
  have hjc : (j : ℝ) ≤ s.card := by rw [hcard]; exact_mod_cast hj
  have he : 3 / 2 * W.w τ / W.T = 6 * (W.w τ / (4 * W.T)) := by ring
  calc (j : ℝ) * ((⨆ i, reWt W.u' τ i) - ⨅ i, reWt W.u' τ i) ≤ j * (3 / 2 * W.w τ / W.T) :=
        mul_le_mul_of_nonneg_left hsp (Nat.cast_nonneg _)
    _ ≤ s.card * (3 / 2 * W.w τ / W.T) := mul_le_mul_of_nonneg_right hjc h0
    _ = 6 * (s.card * (W.w τ / (4 * W.T))) := by rw [he]; ring
    _ ≤ _ := by linarith

end GlobalTheory.MeanTop
end

section

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog



theorem exists_series_of_cobOne_dvd : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 ∧ (∀ α, (p : O) ∣ coeff α (cob2 c.μ κ)) ∧ (∀ α, (p : O) ∣ coeff α (Katz.swap κ - κ)) ∧ (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) ∧ c.ev 1 B = b + (p : O) • y := by
  intro p _ O _ G d c b z hbz
  let I : Ideal O := Ideal.span {(p : O)}
  have hpI : (p : O) ^ 1 ∈ I := by rw [pow_one]; exact Ideal.subset_span rfl
  obtain ⟨c', hlaw, hev, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 hpI
  have hmkp : (algebraMap O (O ⧸ I)) (p : O) = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  have hb' : cobOne (O ⧸ I) ((G.baseChange (O ⧸ I)).A 1) ((G.toBase (O ⧸ I)).app 1 b) = 0 := by
    rw [← SemiBialgHom.two_cobOne, hbz, map_smulₛₗ, hmkp, zero_smul]
  obtain ⟨κ', B', hcoc, hκ0, hcob, hev1⟩ := GlobalTheory.T.exists_series_of_additive_function_first_level p (O ⧸ I) d _ c' _ hlaw _ hb'
  obtain ⟨hl2, hz2, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I
  obtain ⟨hl1, hz1, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ (Fin d ⊕ Fin d)) I
  obtain ⟨hl0, -, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I
  obtain ⟨κ, hκ, hκc⟩ := hl2 κ'
  obtain ⟨B, hB, -⟩ := hl0 B'
  have hdiv : ∀ x : O, x ∈ I ↔ (p : O) ∣ x := fun x => Ideal.mem_span_singleton
  have hμ := c.isLaw.const
  obtain ⟨hm1, hm2, hsw, -, hpull⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hμ (O ⧸ I) (Ideal.Quotient.mk I)
  obtain ⟨-, hn⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d c.μ c.isLaw (O ⧸ I) (Ideal.Quotient.mk I)
  have hnm : (fun i => map (Ideal.Quotient.mk I) (nmul c.μ p i)) =
      nmul (fun i => map (Ideal.Quotient.mk I) (c.μ i)) p := funext fun i => (hn p i).2
  obtain ⟨hpl, -⟩ := hpull (nmul c.μ p) fun i => (hn p i).1
  have hy : ∃ y : G.A 1, c.ev 1 B = b + (p : O) • y := by
    have h1 : (G.toBase (O ⧸ I)).app 1 (c.ev 1 B) = (G.toBase (O ⧸ I)).app 1 b := by
      rw [← hev, hB, hev1]
    rw [toBase_app, toBase_app] at h1
    have h2 : (1 : O ⧸ I) ⊗ₜ[O] (c.ev 1 B - b) = 0 := by rw [tmul_sub, h1, sub_self]
    obtain ⟨-, hq, hs⟩ := GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A 1) I
    obtain ⟨y, hy⟩ := (hs (p : O) _).1 ((hq _).1 h2)
    exact ⟨y, by rw [← hy]; abel⟩
  obtain ⟨y, hy⟩ := hy
  refine ⟨κ, B, y, hκc hκ0, ?_, ?_, ?_, hy⟩
  · intro α
    refine (hdiv _).1 ((hz1 _).1 ?_ α)
    rw [hm2, hκ]; exact hcoc.1
  · intro α
    refine (hdiv _).1 ((hz2 _).1 ?_ α)
    rw [map_sub, hsw, hκ, hcoc.2, sub_self]
  · intro α
    refine (hdiv _).1 ((hz2 _).1 ?_ α)
    rw [map_sub, hm1, hpl, hκ, hB, hnm, hcob, sub_self]

end GlobalTheory.QLog
end
