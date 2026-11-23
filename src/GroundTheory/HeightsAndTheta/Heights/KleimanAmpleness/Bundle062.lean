module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockComp
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle052
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecMul
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle058
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

theorem twistVanishAll_closed : Kleiman.TwistVanishAll.Statement.{0, 0} :=
  Kleiman.TwistVanishAll.proof Kleiman.Extension.full Kleiman.SerreVanish.full Kleiman.TwistSplit.proof

theorem lineBundle_twist_vanish {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (Q : Kleiman.LineBundle F x) :
    ∃ c₀ : ℤ, ∀ (i : ℕ) (c : ℤ), 1 ≤ i → c₀ ≤ c →
      Subsingleton ((Q.twist (Kleiman.twistSys F x c)).H i) := by
  obtain ⟨c₀, hc₀⟩ := twistVanishAll_closed F Ω N x Q (Kleiman.twistBundle F x 1) N x
    Kleiman.mem_secs_twistBundle_one Kleiman.span_range_eq_twistMod_one
  refine ⟨c₀, fun i c hi hc => ?_⟩
  have h := hc₀ i 0 c hi hc
  have e : Q.twist ((Kleiman.twistBundle F x 1).pow 0) = Q.toSubSystem :=
    Kleiman.SubSystem.twist_twistSys_zero _
  rwa [e] at h

theorem RayVanish.proof (hMC : ModelCechTwist.Statement) : RayVanish.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ hM β
  have : Nonempty (ι k₀) := let ⟨i, _⟩ := hM.1 k₀; ⟨i⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : ι k₀ ≃ Fin (N + 1) := (Fintype.equivFin _).trans (finCongr hN)
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hM β
  obtain ⟨c₀, hc₀⟩ := lineBundle_twist_vanish Q
  rw [Filter.eventually_atTop]
  refine ⟨c₀.toNat, fun c hc i hi => ?_⟩
  obtain ⟨φ⟩ := hMC F K ι Ω y k₀ N e hM β Q hQ 1 1 0 c i
  have hdeg : (1 : ℕ) • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β 1 0 + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ =
      β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    simp [IndefiniteRowSideFullHecke.Kleiman2.stepL]
  have hsys : (Kleiman.twistMul Q.toSubSystem 1 0).pow 1 = Q.toSubSystem := by
    change (Kleiman.twistSys _ _ 0).twist (Kleiman.twistMul Q.toSubSystem 1 0) = _
    rw [Kleiman.twistSys_zero_twist, Kleiman.twistMul]
    change ((Kleiman.twistSys _ _ 0).twist Q.toSubSystem).twist (Kleiman.twistSys _ _ 0) = _
    rw [Kleiman.twistSys_zero_twist, Kleiman.SubSystem.twist_twistSys_zero]
  rw [hdeg, hsys] at φ
  have := hc₀ i c hi (by omega)
  exact φ.symm.toEquiv.subsingleton

theorem RayVanish.proof_of_ties (hLoc : CellLocEval.Statement) (hRef : ModelCechRefine.Statement) :
    RayVanish.Statement :=
  RayVanish.proof (ModelCechTwist.proof (ChartSecMul.proof BundleOfDeg.full) BaseRealises.proof hLoc hRef)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelChangeVeryAmple.proof (hGen : ModelChangeGen.Statement) : ModelChangeVeryAmple.Statement := by
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hy hy' hx β β' hs
  exact veryAmple_change hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

noncomputable section

section Ratio

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def ResidueGen.ratioMon (β : K → ℤ) (c d : ∀ k, ι k) : MRingOver F ι :=
  ∏ k, (X ⟨k, d k⟩ ^ (β k).toNat * X ⟨k, c k⟩ ^ (-β k).toNat)

theorem ResidueGen.ratioMon_homog (β : K → ℤ) :
    ∃ a : K → ℕ, ∀ c d : ∀ k, ι k,
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (ResidueGen.ratioMon (F := F) β c d) a := by
  classical
  refine ⟨_, fun c d => ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_prod _ _ _ fun k _ =>
    ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_mul
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_pow (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k (d k)) _)
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_pow (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k (c k)) _)⟩

omit [∀ k, Fintype (ι k)] in
theorem ResidueGen.aeval_ratioMon {L : Type} [Field L] [Algebra F L] (z : (Σ k, ι k) → L) (β : K → ℤ)
    (c d : ∀ k, ι k) :
    aeval z (ResidueGen.ratioMon (F := F) β c d) =
      ∏ k, (z ⟨k, d k⟩ ^ (β k).toNat * z ⟨k, c k⟩ ^ (-β k).toNat) := by
  simp [ResidueGen.ratioMon, map_prod]


omit [∀ k, Fintype (ι k)] in
theorem ResidueGen.ratio_eval {L : Type} [Field L] [Algebra F L] (z : (Σ k, ι k) → L) (β : K → ℤ)
    (c d : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hd : ∀ k, z ⟨k, d k⟩ ≠ 0) :
    aeval z (ResidueGen.ratioMon (F := F) β c d) / aeval z (ResidueGen.ratioMon (F := F) β d c) =
      (∏ k, z ⟨k, c k⟩ ^ (-β k)) / ∏ k, z ⟨k, d k⟩ ^ (-β k) := by
  rw [ResidueGen.aeval_ratioMon, ResidueGen.aeval_ratioMon, ← Finset.prod_div_distrib,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hck := hc k
  have hdk := hd k
  conv_rhs => rw [← Int.toNat_sub_toNat_neg (β k)]
  rw [neg_sub, zpow_sub₀ hck, zpow_sub₀ hdk]
  simp only [zpow_natCast]
  field_simp

end Ratio

theorem ResidueGen.proof : ResidueGen.Statement := by
  intro F _ K _ ι _ Ω _ _ y K' _ _ y' _ R σ hσ hchart β hgen d₀ hd₀
  classical

  have hne : ∀ p : Σ k, ι k, y' p ≠ 0 → y p ≠ 0 := by
    rintro ⟨k, a⟩ hp h0
    obtain ⟨hm, he⟩ := hσ (X ⟨k, a⟩) (X ⟨k, a⟩) _ (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k a)
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k a) (by simpa [aeval_X] using hp)
    have h0' : (⟨_, hm⟩ : R) = 0 := Subtype.ext (by simp [aeval_X, h0])
    rw [h0', map_zero, aeval_X, div_self hp] at he
    exact zero_ne_one he
  have hy0 : ∀ k, y ⟨k, d₀ k⟩ ≠ 0 := fun k => hne _ (hd₀ k)
  have hG0' : (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hd₀ k)
  have hG0 : (∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hy0 k)
  obtain ⟨ext, ext_eq⟩ : ∃ e : Ω → K', ∀ z (hz : z ∈ R), e z = σ ⟨z, hz⟩ :=
    ⟨fun z => if hz : z ∈ R then σ ⟨z, hz⟩ else 0, fun z hz => dif_pos hz⟩
  obtain ⟨a, ha⟩ := ResidueGen.ratioMon_homog (F := F) (ι := ι) β

  have key : ∀ h ∈ secOver F y β, ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
      ∃ hh : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) ∈ R,
        σ ⟨_, hh⟩ = ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) *
          ∏ k, y' ⟨k, c k⟩ ^ (-β k) := by
    intro h hH c hc'
    have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hne _ (hc' k)
    obtain ⟨h0R, -⟩ := hchart d₀ hd₀ _ ((PowRealises.mem_secOver y β h).mp hH d₀ hy0)
    obtain ⟨hrR, hr⟩ := hσ (ResidueGen.ratioMon β c d₀) (ResidueGen.ratioMon β d₀ c) a (ha c d₀) (ha d₀ c)
      (by
        rw [ResidueGen.aeval_ratioMon]
        exact Finset.prod_ne_zero_iff.mpr fun k _ =>
          mul_ne_zero (pow_ne_zero _ (hc' k)) (pow_ne_zero _ (hd₀ k)))
    have eqΩ := ResidueGen.ratio_eval (F := F) y β c d₀ hc hy0
    have eqK := ResidueGen.ratio_eval (F := F) y' β c d₀ hc' hd₀
    have hprod : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) = (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) *
        (aeval y (ResidueGen.ratioMon (F := F) β c d₀) / aeval y (ResidueGen.ratioMon (F := F) β d₀ c)) := by
      rw [eqΩ]
      field_simp
    have hmem : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) ∈ R := by
      rw [hprod]
      exact mul_mem h0R hrR
    refine ⟨hmem, ?_⟩
    have hsplit : (⟨_, hmem⟩ : R) = ⟨_, h0R⟩ * ⟨_, hrR⟩ := Subtype.ext hprod
    rw [hsplit, map_mul, hr, eqK, ext_eq _ h0R]
    ring
  refine ⟨fun h => ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)),
    fun h hH => key h hH d₀ hd₀, ?_⟩
  intro c hc'
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hne _ (hc' k)
  have hGc' : (∏ k, y' ⟨k, c k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc' k)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨h, hH, rfl⟩
    rw [SetLike.mem_coe, PowRealises.mem_span_inv_iff _ hGc']
    obtain ⟨hh, he⟩ := key h hH c hc'
    obtain ⟨_, hin⟩ := hchart c hc' _ ((PowRealises.mem_secOver y β h).mp hH c hc)
    beta_reduce
    rw [← he]
    exact hin
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    obtain ⟨m, s, hs, hg⟩ := hgen
    obtain ⟨u, hu, hsum⟩ := hg c hc
    choose hUR hUc using fun j => hchart c hc' _ (hu j)
    choose hWR hW using fun j => key (s j) (hs j) c hc'
    have hsumR : (∑ j, (⟨u j, hUR j⟩ : R) * ⟨_, hWR j⟩) = 1 := by
      apply Subtype.ext
      push_cast
      exact hsum
    have hone := congrArg σ hsumR

    rw [map_sum, map_one] at hone
    have h2 : (∑ j, σ ⟨u j, hUR j⟩ *
        (ext (s j * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)))) *
          (∏ k, y' ⟨k, c k⟩ ^ (-β k)) = 1 := by
      rw [Finset.sum_mul, ← hone]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hW j]
      ring
    rw [← eq_inv_of_mul_eq_one_left h2]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hj := Submodule.smul_mem
      (Submodule.span (chartRingOver F y' c)
        ((fun h => ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k))) ''
          (secOver F y β : Set Ω)))
      (⟨_, hUc j⟩ : chartRingOver F y' c) (Submodule.subset_span (Set.mem_image_of_mem _ (hs j)))
    rwa [Subalgebra.smul_def, smul_eq_mul] at hj

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

section Block

variable {F : Type} [Field F] {K : Type} {ι : K → Type} {L : Type} [Field L] [Algebra F L]

theorem comap_mIdealOver_block (y : (Σ k, ι k) → L) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    (mIdealOver F y).comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) := by
  have h1 : (mConeMapOver F y).comp (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      ((Polynomial.aeval (X k₀ : MvPolynomial K L)).restrictScalars F).comp
        (Kleiman.cone (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have h2 : ∀ q : Polynomial L,
      aeval (fun _ : K => (Polynomial.X : Polynomial L)) (Polynomial.aeval (X k₀ : MvPolynomial K L) q) = q :=
    fun q => by rw [← Polynomial.aeval_algHom_apply, aeval_X, Polynomial.aeval_X_left_apply]
  ext f
  rw [Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  change mConeMapOver F y (rename _ f) = 0 ↔ _
  have h := AlgHom.congr_fun h1 f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  constructor
  · intro h0
    rw [← h2 (Kleiman.cone (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f), h0, map_zero]
  · intro h0
    rw [h0, map_zero]

theorem mIdealOver_oneBlock_block (y : (Σ k, ι k) → L) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) =
      baseComap F k₀ e (mIdealOver F y) := by
  have hcomp : (mConeMapOver F y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := L) fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  ext f
  rw [baseComap, Ideal.mem_comap]
  change mConeMapOver F _ f = 0 ↔ mConeMapOver F y (rename _ f) = 0
  have h := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    exact rename_injective _ (fun a b _ => Subsingleton.elim a b) (h0.trans (map_zero _).symm)

end Block

theorem CurveNumModel.proof (hMP : ModelPoint.Statement) (hRR : RealiseRestrict.Statement)
    (hIR : Kleiman.InterNumRestrict.Statement.{0, 0}) (hNM : NumModel.Statement) (hMC : ModelCurves.Statement) :
    CurveNumModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hm Q β hQ W hW hle hrel
  classical
  have := hW.isPrime
  have hWy : mIdealOver F (genPtOf W) = W := mIdealOver_genPtOf W hW.multiHomog
  have hzero : ∀ p, genPtOf W p = 0 ↔ (X p : NumbersDVR.MRing ι F) ∈ W := fun p => by
    rw [← X_mem_mIdealOver_iff (k := F), hWy]
  have hy' : ∀ k, ∃ i, genPtOf W ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hW.relevant k
    exact ⟨i, fun h => hi ((hzero _).mp h)⟩
  have hleW : mIdealOver F y ≤ mIdealOver F (genPtOf W) := hWy.symm ▸ hle
  have hm' := hMP F K ι Ω y k₀ hm _ (genPtOf W) hy' hleW
  have hxy : ∀ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) i ≠ 0 → x i ≠ 0 := fun i h h0 => by
    rw [hx] at h0
    exact h ((hzero ⟨k₀, e.symm i⟩).mpr (hle ((X_mem_mIdealOver_iff y ⟨k₀, e.symm i⟩).mpr h0)))
  obtain ⟨Q', r, hR, hQ'⟩ := hRR F K ι Ω y k₀ N e x hx hm Q β hQ _ (genPtOf W) hm' hleW hxy
  have hpp : Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) =
      W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) := by
    rw [← comap_mIdealOver_block, hWy]
  have hsub : Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm)
      (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm)) 1 := by
    refine (isSubvar_iff_relDim _ 1).mpr ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := hy' k₀
      exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
    · rw [mIdealOver_oneBlock_block, hWy]
      exact ((hMC F K ι Ω y k₀ N e x hx hm 1).1 W hW hle hrel).2.2
  have hxx : Kleiman.primeOf (S := F) x ≤
      Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) := by
    rw [hx, ← comap_mIdealOver_block, ← comap_mIdealOver_block]
    exact Ideal.comap_mono hleW
  have h1 := hIR F Ω N x _ _ hxy hxx _ 1 hsub ![Q] ![Q'] (fun _ => r) (fun i => by fin_cases i; exact hR)
  have h2 := hNM F K ι _ (genPtOf W) k₀ N e _ rfl hm' 1 ![Q'] ![β] (fun i => by fin_cases i; exact hQ') hsub
  rw [hWy] at h2
  have e1 : (fun i => (![Q] i).toSubSystem) = ![Q.toSubSystem] := by
    funext i; fin_cases i; rfl
  have e2 : (fun i => (![Q'] i).toSubSystem) = ![Q'.toSubSystem] := by
    funext i; fin_cases i; rfl
  rw [e1, e2] at h1
  rw [e2] at h2
  rw [← h2, h1, hpp]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

noncomputable section

section Fold

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

def foldTensor {n : ℕ} (L : Fin n → Kleiman.LineBundle S x) (l : List (Fin n)) (Q : Kleiman.LineBundle S x) :
    Kleiman.LineBundle S x :=
  l.foldl (fun P i => P.tensor (L i)) Q

theorem foldTensor_toSubSystem {n : ℕ} (L : Fin n → Kleiman.LineBundle S x) (l : List (Fin n))
    (Q : Kleiman.LineBundle S x) :
    (foldTensor L l Q).toSubSystem = l.foldl (fun P i => P.twist (L i).toSubSystem) Q.toSubSystem := by
  induction l generalizing Q with
  | nil => rfl
  | cons a l ih =>
    rw [foldTensor, List.foldl_cons, List.foldl_cons, ← Kleiman.LineBundle.tensor_toSubSystem]
    exact ih _

end Fold

theorem realises_foldTensor (hT : TensorRealises.Statement)
    {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) {n : ℕ}
    (L : Fin n → Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (δ : Fin n → K → ℤ)
    (hL : ∀ i, BundleRealises y k₀ (L i) (δ i)) (l : List (Fin n)) :
    ∀ (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (β : K → ℤ),
      BundleRealises y k₀ Q β → BundleRealises y k₀ (foldTensor L l Q) (β + (l.map δ).sum) := by
  induction l with
  | nil => intro Q β hQ; simpa [foldTensor] using hQ
  | cons a l ih =>
    intro Q β hQ
    have h := ih (Q.tensor (L a)) (β + δ a) (hT F K ι Ω y k₀ N e hmod Q (L a) β (δ a) hQ (hL a))
    rw [List.map_cons, List.sum_cons, ← add_assoc]
    exact h

theorem TensorRealise.proof (hT : TensorRealises.Statement) : TensorRealise.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n L δ hL T
  subst hx
  refine Filter.Eventually.of_forall fun c => ?_
  have h0 := BaseRealises.proof F K ι Ω y k₀ N e _ rfl hmod 0
  have h := realises_foldTensor hT hmod L δ hL ((List.finRange n).filter (· ∈ T)) _ _ h0 (c : ℤ)
  rw [foldTensor_toSubSystem, Kleiman.twistBundle_toSubSystem] at h
  have hsum : (((List.finRange n).filter (· ∈ T)).map δ).sum = ∑ i ∈ T, δ i := by
    rw [← List.sum_toFinset δ ((List.nodup_finRange n).filter _)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp
  rw [hsum, zero_smul, zero_add] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
