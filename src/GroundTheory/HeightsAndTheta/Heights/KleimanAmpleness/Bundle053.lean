module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle044
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelPoint.proof (hgen : BlockGenOfModel.Statement) (htr : BlockGenTransfer.Statement)
    (hmod : ModelOfBlockGen.Statement) : ModelPoint.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ hy K' _ _ y' hy' hle
  exact hmod F K ι K' y' k₀ hy' (htr F K ι Ω y k₀ (hgen F K ι Ω y k₀ hy) K' y' hy' hle)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem ModelChangeNef.proof (hC : ModelCurves.Statement) (hN : ModelCurveNum.Statement) :
    ModelChangeNef.Statement := by
  have key : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
      (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
      IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
      ∀ (β : K → ℤ) (β' : K' → ℤ),
        (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
            secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
        IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β → IndefiniteRowSideFullHecke.Kleiman2.IsNef F y' β' := by
    intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs hnef W' hW' hle' hrel'
    obtain ⟨hP, hPle, hPrel⟩ := (hC F K' ι' Ω y' k₀' N e' _ hx hm' 1).1 W' hW' hle' hrel'
    obtain ⟨W, hW, hle, hrel, hWP⟩ := (hC F K ι Ω y k₀ N e _ rfl hm 1).2 _ hP hPle hPrel
    rw [← hN F Ω N K ι y k₀ e K' ι' y' k₀' e' hm hm' hx β β' hs W W' hW hle hrel hW' hle' hrel' hWP]
    exact hnef W hW hle hrel
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs
  exact ⟨key F Ω N K ι y k₀ e K' ι' y' k₀' e' hm hm' hx β β' hs,
    key F Ω N K' ι' y' k₀' e' K ι y k₀ e hm' hm hx.symm β' β fun c => (hs c).symm⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

noncomputable section

namespace ModelTwistGenerated

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {K : Type} [Fintype K] {ι : K → Type}

theorem secOver_mul (y : (Σ k, ι k) → Ω) {β γ : K → ℤ} {a b : Ω} (ha : a ∈ secOver S y β)
    (hb : b ∈ secOver S y γ) : a * b ∈ secOver S y (β + γ) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule] at ha hb ⊢
  intro c hc
  have : a * b * ∏ k, y ⟨k, c k⟩ ^ (-(β + γ) k) =
      (a * ∏ k, y ⟨k, c k⟩ ^ (-β k)) * (b * ∏ k, y ⟨k, c k⟩ ^ (-γ k)) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.add_apply, neg_add, zpow_add₀ (hc k)]
  rw [this]
  exact Subalgebra.mul_mem _ (ha c hc) (hb c hc)

theorem one_mem_secOver (y : (Σ k, ι k) → Ω) : (1 : Ω) ∈ secOver S y 0 := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply]
  intro c _
  simp only [Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
  exact Subalgebra.one_mem _

theorem pow_mem_secOver (y : (Σ k, ι k) → Ω) {δ : K → ℤ} {a : Ω} (ha : a ∈ secOver S y δ) (m : ℕ) :
    a ^ m ∈ secOver S y ((m : ℤ) • δ) := by
  induction m with
  | zero => simpa using one_mem_secOver (S := S) y
  | succ m ih =>
    have h := secOver_mul y ih ha
    rw [pow_succ]
    convert h using 2
    push_cast
    rw [add_smul, one_smul]

variable [DecidableEq K]

theorem coord_mem_secOver (y : (Σ k, ι k) → Ω) (k₀ : K) (i : ι k₀) :
    y ⟨k₀, i⟩ ∈ secOver S y (IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule, IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  intro c _
  rw [Fintype.prod_eq_single k₀ fun k hk => by rw [Pi.single_eq_of_ne hk]; simp]
  rw [Pi.single_eq_same, zpow_neg_one, ← div_eq_mul_inv]
  exact Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩

theorem prod_coord_mem_secOver (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (s : Finset (Fin (N + 1))) :
    ∏ j ∈ s, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) j ∈
      secOver S y ((s.card : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_secOver (S := S) y
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have h := secOver_mul y (coord_mem_secOver (S := S) y k₀ (e.symm j)) ih
    convert h using 2 <;> first | rfl | (push_cast; rw [add_smul, one_smul, add_comm])

variable {N : ℕ} {y : (Σ k, ι k) → Ω} {k₀ : K} (e : ι k₀ ≃ Fin (N + 1))

theorem twist_sub_eq_chartSecOver (β : K → ℤ)
    (Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (hQ : ∀ c : ℤ, (Q.twist (Kleiman.twistSys S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
      secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    (c : ℕ) (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) :
    ((Q.twist (Kleiman.twistSys S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (c : ℤ))).sub I : Set Ω) =
      chartSecOver S y k₀ e (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) I := by
  have hsubQ : (Q.sub I : Set Ω) = chartSecOver S y k₀ e β I := by
    refine Set.ext fun t => ?_
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hQ]
  let X := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : X i ≠ 0 := (Kleiman.mem_support _).mp (I.2.2 hi)
  have hcard := Finset.card_erase_add_one hi
  have hxI : Kleiman.xProd I = X i * ∏ j ∈ I.1.erase i, X j := (Finset.mul_prod_erase I.1 _ hi).symm
  have hxic : X i ^ c ∈ secOver S y ((c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) :=
    pow_mem_secOver y (coord_mem_secOver y k₀ (e.symm i)) c
  have hP : (∏ j ∈ I.1.erase i, X j) ^ c ∈
      secOver S y ((c : ℤ) • (((I.1.erase i).card : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) :=
    pow_mem_secOver y (prod_coord_mem_secOver y k₀ e _) c
  ext t
  rw [SetLike.mem_coe, twist_sub_eq_mul]
  change t ∈ Kleiman.twistMod S X (c : ℤ) I * Q.sub I ↔ _
  rw [Kleiman.twistMod_eq_span (c : ℤ) I hi, Submodule.mem_span_singleton_mul, zpow_natCast]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb' : b ∈ chartSecOver S y k₀ e β I := by rw [← hsubQ]; exact hb
    obtain ⟨n, hn⟩ := hb'
    refine ⟨n, ?_⟩
    have h := secOver_mul y hxic hn
    rw [show Kleiman.xProd I ^ n * (X i ^ c * b) = X i ^ c * (Kleiman.xProd I ^ n * b) by ring]
    convert h using 2
    abel
  · rintro ⟨n, hn⟩
    refine ⟨(X i ^ c)⁻¹ * t, ?_, ?_⟩
    · rw [← SetLike.mem_coe, hsubQ]
      refine ⟨n + c, ?_⟩
      have h := secOver_mul y hP hn
      rw [show Kleiman.xProd I ^ (n + c) * ((X i ^ c)⁻¹ * t) =
          (∏ j ∈ I.1.erase i, X j) ^ c * (Kleiman.xProd I ^ n * t) by
        rw [hxI]; field_simp; ring]
      convert h using 2
      funext k
      rw [← hcard]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    · change X i ^ c * ((X i ^ c)⁻¹ * t) = t
      field_simp

end ModelTwistGenerated


open ModelTwistGenerated in
theorem ModelTwistGenerated.proof (hCG : ChartSecGen.Statement) : ModelTwistGenerated.Statement := by
  classical
  intro S _ K _ _ ι _ Ω _ _ y k₀ hS hM β
  obtain ⟨i₀, -⟩ := hM.1 k₀
  have hpos : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
  set N := Fintype.card (ι k₀) - 1
  have hcard : Fintype.card (ι k₀) = N + 1 := by omega
  let e : ι k₀ ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  set x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm with hx
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full S K ι Ω y k₀ N e hM β
  obtain ⟨c₀, hc₀⟩ := GroundTheory.Heights₂.Heights.Kleiman.Generated.full S Ω N x Q
  refine ⟨max c₀ 0, fun c hc => ?_⟩
  lift c to ℕ using le_trans (le_max_right _ _) hc with m
  set L := Q.twist (Kleiman.twistSys S x (m : ℤ)) with hL
  have hgen : L.Generated := hc₀ m (le_trans (le_max_left _ _) hc)
  have hfin : ∀ I : Kleiman.Chart x, ∃ T : Finset Ω, (T : Set Ω) ⊆ L.secs ∧
      Submodule.span (Kleiman.chartRing S x I) (T : Set Ω) = L.sub I := by
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hfg : (L.sub I).FG := by
      rw [hL, twist_sub_eq_mul]
      change (Kleiman.twistMod S x (m : ℤ) I * Q.sub I).FG
      rw [Kleiman.twistMod_eq_span (m : ℤ) I hi]
      exact (Submodule.fg_span_singleton _).mul (Q.fg I)
    rw [← hgen I] at hfg ⊢
    obtain ⟨T, hT, hTs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
    exact ⟨T, hT, hTs.symm⟩
  choose T hTsub hTspan using hfin
  let _ : Fintype (Kleiman.Chart x) := Fintype.ofFinite _
  let U : Finset Ω := Finset.univ.biUnion T
  have hUsub : (U : Set Ω) ⊆ L.secs := by
    intro z hz
    obtain ⟨I, -, hzI⟩ := Finset.mem_biUnion.mp hz
    exact hTsub I hzI
  have hUspan : ∀ I, Submodule.span (Kleiman.chartRing S x I) (U : Set Ω) = L.sub I := by
    intro I
    apply le_antisymm
    · rw [← hgen I]
      exact Submodule.span_mono hUsub
    · rw [← hTspan I]
      exact Submodule.span_mono fun z hz => Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, hz⟩
  have hsecs : L.secs = secOver S y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := hQ m
  let η : Fin U.card → Ω := fun j => (U.equivFin.symm j : Ω)
  have hrange : Set.range η = (U : Set Ω) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact (U.equivFin.symm j).2
    · intro hz
      exact ⟨U.equivFin ⟨z, hz⟩, by simp [η]⟩
  have hη : ∀ j, η j ∈ secOver S y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro j
    rw [← hsecs]
    exact hUsub (U.equivFin.symm j).2
  refine ⟨U.card, η, hη, (hCG S K ι Ω y k₀ N e hM _ U.card η hη).mpr fun I => ?_⟩
  rw [hrange, hUspan I]
  exact twist_sub_eq_chartSecOver e β Q hQ m I

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver cechHc cechZc cechBc quotPart GlobalSectionsComparisonStatement)

noncomputable section

theorem altSum_eq_of_vanish (f : ℕ → ℕ) (B : ℕ) (h : ∀ i, 1 ≤ i → f i = 0) :
    ∑ i ∈ Finset.range (B + 1), (-1 : ℚ) ^ i * (f i : ℚ) = f 0 := by
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun i _ => by rw [h (i + 1) (by omega)]; simp]
  simp

theorem finrank_sectionsOver_eq_H0 (hB : GlobalSectionsComparisonStatement) {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K]
    {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (n : K → ℤ) :
    Module.finrank F (secOver F y n) = Module.finrank F (cechHc ι (quotPart F (mIdealOver F y)) n 0) := by
  obtain ⟨φ, hinj, hrange, -⟩ := hB F K ι Ω y n hy
  let e1 : ↥(cechZc ι (quotPart F (mIdealOver F y)) n 0) ≃ₗ[F] secOver F y n :=
    (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hbot : (cechBc ι (quotPart F (mIdealOver F y)) n 0).comap
      (cechZc ι (quotPart F (mIdealOver F y)) n 0).subtype = ⊥ := by
    rw [cechBc, Submodule.comap_bot, Submodule.ker_subtype]
  let e2 : cechHc ι (quotPart F (mIdealOver F y)) n 0 ≃ₗ[F] ↥(cechZc ι (quotPart F (mIdealOver F y)) n 0) :=
    Submodule.quotEquivOfEqBot _ hbot
  rw [← e1.finrank_eq, e2.finrank_eq]

theorem SectionsPoly.proof (hB : GlobalSectionsComparisonStatement) (hE : EulerPoly.Statement) (hM : MultiSerre.Statement)
    (hR : RayVanish.Statement) : SectionsPoly.Statement := by
  intro F _ K _ dK ι _ Ω _ _ y k₀ hmod
  let lo : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain rfl : dK = @LinearOrder.toDecidableEq K lo := Subsingleton.elim _ _
  have hV : NumbersDVR.IsMultiHomogIdeal (mIdealOver F y) := isMultiHomogIdeal_mIdealOver y
  obtain ⟨B, χ, -, -, hχ⟩ := hE F K ι (mIdealOver F y) hV
  have key : ∀ m : K → ℤ, (∀ i : ℕ, 1 ≤ i → Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) m i)) →
      (Module.finrank F (secOver F y m) : ℚ) = eval (fun k => (m k : ℚ)) χ := by
    intro m hm
    rw [← hχ m, finrank_sectionsOver_eq_H0 hB y hmod.1 m]
    refine (altSum_eq_of_vanish (fun i => Module.finrank F (cechHc ι (quotPart F (mIdealOver F y)) m i)) B
      fun i hi => ?_).symm
    have := hm i hi
    exact Module.finrank_zero_of_subsingleton
  refine ⟨χ, ?_, fun β => ?_⟩
  · filter_upwards [hM F K ι (mIdealOver F y) hV] with m hm
    rw [← hm.2, ← key m hm.1, finrank_sectionsOver_eq_H0 hB y hmod.1 m]
    push_cast
    rfl
  · filter_upwards [hR F K ι Ω y k₀ hmod β] with c hc
    exact key _ hc

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

noncomputable section

namespace SegreFibreIdeal

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type}

def thetaVal (ι : K → Type) (R : Type) [CommRing R] : (Σ k, segreIdx ι k) → Polynomial (MRing ι R)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (∏ k, X ⟨k, c k⟩)
  | ⟨Sum.inr k, i⟩ => Polynomial.C (X ⟨k, i⟩)

def theta (ι : K → Type) (R : Type) [CommRing R] : MRing (segreIdx ι) R →+* Polynomial (MRing ι R) :=
  eval₂Hom (Polynomial.C.comp C) (thetaVal ι R)

def chi (K : Type) [Fintype K] : MvPolynomial (Unit ⊕ K) Ω →+* Polynomial (MvPolynomial K Ω) :=
  eval₂Hom (Polynomial.C.comp C)
    (Sum.elim (fun _ => Polynomial.X * Polynomial.C (∏ k, X k)) (fun k => Polynomial.C (X k)))

theorem map_cone_theta (y : (Σ k, ι k) → Ω) :
    (Polynomial.mapRingHom (mConeMapOver O y).toRingHom).comp (theta ι O) =
      (chi K).comp (mConeMapOver O (segreJoin y)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [theta, chi, mConeMapOver]
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec,
        IndefiniteRowSideFullHecke.Kleiman2.oneBlock, NumbersDVR.segreVec, Polynomial.map_prod, Finset.prod_mul_distrib]
      ring
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]

theorem segreLiftMap_map (F : Type) [Field F] (φ : O →+* F) (W : Ideal (MRing ι F)) :
    (segreLiftMap ι F W).toRingHom.comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom ((Ideal.Quotient.mk W).comp (MvPolynomial.map φ))).comp (theta ι O) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [theta, segreLiftMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coe_eval₂Hom, eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C, map_C, aeval_C]
    rfl
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal, Polynomial.map_prod]
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal]

end SegreFibreIdeal

open SegreFibreIdeal in
theorem SegreFibreIdeal.proof : SegreFibreIdeal.Statement := by
  intro O _ Ω _ _ F _ φ K _ _ ι _ y
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨c, d, rfl⟩
    have hm : (segreY c * segreMon d - segreY d * segreMon c : MRing (segreIdx ι) O) ∈
        mIdealOver O (segreJoin y) := by
      simp only [mIdealOver, RingHom.mem_ker, map_sub, map_mul, map_prod, segreY, segreMon,
        mConeMapOver, aeval_X, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.oneBlock,
        NumbersDVR.segreVec, Sum.elim_inr, Finset.prod_mul_distrib]
      ring
    have := Ideal.mem_map_of_mem (MvPolynomial.map φ) hm
    rw [SetLike.mem_coe]
    convert this using 1
    simp [segreY, segreMon, map_prod]
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    simp only [Ideal.mem_comap]
    have hr : segreIncl ι F (MvPolynomial.map φ f) = MvPolynomial.map φ (segreIncl ι O f) := by
      simp [segreIncl, MvPolynomial.map_rename]
    rw [hr]
    refine Ideal.mem_map_of_mem _ ?_
    have key : (mConeMapOver O (segreJoin y)).toRingHom.comp (segreIncl ι O).toRingHom =
        (rename (R := Ω) (Sum.inr : K → Unit ⊕ K)).toRingHom.comp (mConeMapOver O y).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [segreIncl, mConeMapOver]
      · rintro ⟨k, i⟩
        simp [segreIncl, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]
    have hc : mConeMapOver O (segreJoin y) (segreIncl ι O f) =
        rename Sum.inr (mConeMapOver O y f) := by
      simpa using congrArg (fun g => g f) key
    rw [mIdealOver, RingHom.mem_ker] at hf ⊢
    rw [hc, hf, map_zero]
  · intro W hW
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, segreLift, RingHom.mem_ker]
    have h1 := congrArg (fun g => g f) (segreLiftMap_map F φ W)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
    rw [h1]
    have h2 := congrArg (fun g => g f) (map_cone_theta (O := O) y)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
    rw [mIdealOver, RingHom.mem_ker] at hf
    rw [hf, map_zero] at h2
    ext n
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero,
      RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    apply hW
    apply Ideal.mem_map_of_mem
    rw [mIdealOver, RingHom.mem_ker]
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) h2
    simpa [Polynomial.coeff_map] using this

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelRowExact.proof (hSub : RowSub.Statement) (hZ : CellZeroConst.Statement)
    (hGlue : RowSecGlue.Statement) (hC : CellContract.Statement) (hL : CellLocGlue.Statement)
    (hAct : RowChartAct.Statement) (hCov : RowLocCover.Statement) : ModelRowExact.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ J
  refine ⟨fun I hne hI => Submodule.span_le.mpr (hSub F K ι Ω y k₀ N e γ J I hne hI), ?_, ?_⟩
  · intro s hs hd
    choose c₀ hc₀ using hM.1

    let cell : (∀ k, ι k) → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 := fun c =>
      ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩
    have hmeet : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → CellMeets y (cell c).1 := by
      intro c hc k i hi
      rw [Finset.mem_singleton.mp hi]
      exact hc k
    refine ⟨s (cell c₀), Submodule.subset_span (hGlue F K ι Ω y k₀ N e γ J _ fun c hc => ?_),
      fun c hc => hZ F K ι Ω y s hd c (cell c₀) hc (hmeet c₀ hc₀)⟩
    rw [← hZ F K ι Ω y s hd (cell c) (cell c₀) (hmeet c hc) (hmeet c₀ hc₀)]
    exact hs (cell c) (Set.mem_univ _)
  · obtain ⟨m, f, u, hf, hu, hsum, hloc⟩ := hCov F K ι Ω y k₀ N e hM γ J
    refine hL F K ι Ω y _ (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J).toSubring m f u hf hu hsum
      (fun I r hr a ha => hAct F K ι Ω y k₀ N e γ J I r a hr ha) fun l => ?_
    obtain ⟨c, hc, h0, hmono, hinv⟩ := hloc l
    exact hC F K ι Ω y _ c hc h0 hmono hinv

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
