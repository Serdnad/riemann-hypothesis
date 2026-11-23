module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
public import Development.AutomorphicArithmetic.BlochKatoExtensions.BkExtHolds
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle024
public import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle030
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle036
import Formalism.SharpRestriction.LevelLetterCocycles.LocalInputsFromLiterature
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing

def levBOfSit {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
    {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (finrank ℚ_[l] ↥(K0 K))} {E : EtSit P AI K s LL h W}
    (S : CmpSit P AI K s LL h E) : LevB W where
  levB := S.tie.levB
  mem := S.tie.levB_mem
  supp := S.tie.levB_supp



theorem local_theorem_of_inputs (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (C : ℝ)
    (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F)
    (hP6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (hPr2a : Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F)
    (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F)
    (h3 : adm3 D HW F) (h4 : ArchimedeanSignatureMatching D HW F C) (h7 : adm7 D HW F Cm)
    (h8 : adm8 D HW F) (h9a : adm9 D HW F) (h10 : adm10 D HW F) (h14 : adm14 D)
    (hDdR : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1)
    (h9 : Formalism.MainNotions.LocalSituation.adm9 D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hUG : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, UnitGen ((HW l).W K 1 LL h.2.2) e) : Conclusion1 D 800 := by
  refine local_theorem_of_cyclotomic_lift D.loc id (fun l _ K LL h => (HW l).W K 1 LL h.2.2)
    (fun l _ K LL h _ h5 hz => ?_) (Formalism.MainNotions.UnusedSlot80.base_change_every_theory D.loc)
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
  refine crystalline_lifting_second_form (brHyp2_of_rec (D.loc l) h h5 _ ((HW l).W_s K 1 LL h.2.2)
    (hP5 l K 1 LL h.2.2) (hP6 l K 1 LL h.2.2) (hP9 l K 1 LL h.2.2) (hPr2a l K 1 LL h.2.2)
    (h3.1 l K 1 LL h.2.2) (h4 l K 1 LL h.2.2)
    (h7 l K LL h h5).1 (h9a l K LL h h5) (h10 l K LL h h5) (h14 l K LL) ?_)
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨e, he⟩ := hUG l K LL h h5
  refine ⟨e, he, UpperTheory.Prune.bkExt_holds D HW F h9 hFont l K LL h h5 e he, fun hR => ?_⟩
  have hV := valRing_rec (D.loc l) LL
  have hpl := (D.loc l).PD_p K
  have : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  have : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac LL
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) :=
    (mem_maximalIdeal _).2 (not_isUnit_p ((HW l).W K 1 LL h.2.2) hV)
  have hpm' : ((l : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) := by
    have h' := hpm
    rwa [hpl] at h'
  have hp0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have h0' := congrArg (algebraMap ↥(OL LL) ↥LL.1) h0
    rw [map_natCast, map_zero] at h0'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h0'
  have : IsAdicComplete (maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.N.Ln03.Pf.complMax_holds ↥(OL LL) l hpm' hp0 (complete_OL LL)
  obtain ⟨uZ, huZ, hutie⟩ := Formalism.MainNotions.N.Ln03.Pf.uTieRec_holds D HW l K LL h h5
  have hrich : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ finrank ℚ_[l] ↥(K0 K)) := by
    obtain ⟨ζ, hζ⟩ := hz
    exact ⟨ζ, by rw [hpl]; exact hζ⟩
  have h5' : 5 ≤ ((D.loc l).PD K).p := by rw [hpl]; exact h5
  refine realised2_pf (K := ↥K.1) (W := (HW l).W K 1 LL h.2.2) (levBOfSit ((Cm l).C K 1 LL h.2.2)) hR e uZ
    (ιZrec (D.loc l) K LL)
    ?_ ?_ ?_ ?_ ?_ ?_ ((HW l).W_s K 1 LL h.2.2) (hP4 l K 1 LL h.2.2) ?_ ?_ (hP3 l K 1 LL h.2.2)
    (hP9 l K 1 LL h.2.2) (hP5 l K 1 LL h.2.2) ?_ ?_ ?_ hV (unram_of_caseA h) hpm hrich huZ hutie he ?_ h5'
  · exact ((Cm l).C K 1 LL h.2.2).tie.levN_eq
  · exact ((Cm l).C K 1 LL h.2.2).tie.cmp_eq
  · exact ((Cm l).C K 1 LL h.2.2).tie.levB_φ
  · exact ((Cm l).C K 1 LL h.2.2).tie.levB_Γ
  · exact ((Cm l).C K 1 LL h.2.2).tie.lev_Γ
  · exact ((Cm l).C K 1 LL h.2.2).tie.lev_φ
  · exact (h7 l K LL h h5).2
  · exact h8 l K LL h h5
  · exact hLem3 l K 1 LL h.2.2
  · exact hDdR l K LL h
  · exact (h14 l K LL).1
  · exact Formalism.MainNotions.LiftingTheory.gen_one_crys _

theorem logb_nat_nonneg_sk (p h : ℕ) (hp : 11 ≤ p) : 0 ≤ Real.logb p (h : ℝ) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  · apply Real.logb_nonneg
    · have : (11 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    · exact_mod_cast hh

theorem corollary_monotone_in_constant (D : D7) (C C' : ℝ) (h : C ≤ C') (H : Conclusion2 D C) : Conclusion2 D C' := by
  intro l _ K LL n _ emb
  have H' := H l K LL n emb
  intro hL h11 T₁ T₂ F hG h1 h2 hF r b w S η j typ sz hr hj hn hJ hT hb hC
  obtain ⟨mm, k, e1, e2, e3⟩ := H' hL h11 T₁ T₂ F hG h1 h2 hF r b w S η j typ sz hr hj hn hJ hT
    (le_trans (by gcongr) hb) hC
  refine ⟨mm, k, e1, e2, le_trans e3 ?_⟩
  have hp : (11 : ℝ) ≤ ((D.loc l).PD K).p := by exact_mod_cast h11
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h ?_) ?_) ?_) ?_
  · positivity
  · positivity
  · have := logb_nat_nonneg_sk ((D.loc l).PD K).p (hCor b w S η sz) h11
    have h3 : (0 : ℝ) ≤ (((D.loc l).PD K).p : ℝ) - 1 := by linarith
    positivity
  · positivity

theorem corollary_local_exists_constant : ∃ C₀ : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (C : ℝ),
    Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F →
    Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F → Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F → Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F → Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F →
    adm3 D HW F → ArchimedeanSignatureMatching D HW F C → adm7 D HW F Cm → adm8 D HW F → adm9 D HW F →
    adm10 D HW F → adm12 D → adm14 D →
    (∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1) →
    Formalism.MainNotions.LocalSituation.adm9 D HW F → Formalism.MainNotions.InvariantsGenerators.LitFont D HW F →
    (∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, UnitGen ((HW l).W K 1 LL h.2.2) e) →
    Conclusion1 D 800 ∧ ∀ C₂ : ℝ, C₀ ≤ C₂ → Conclusion2 D C₂ := by
  obtain ⟨C', h1', h'⟩ := corollary_of_Theorem_E
  refine ⟨max C' (4 * 800), fun D HW F Cm C hP3 hP4 hP5 hP6 hP9 hPr2a hLem3 h3 h4 h7 h8 h9a h10 h12 h14
    hDdR h9 hFont hUG => ?_⟩
  have hp1 := local_theorem_of_inputs D HW F Cm C hP3 hP4 hP5 hP6 hP9 hPr2a hLem3 h3 h4 h7 h8 h9a h10 h14 hDdR h9 hFont hUG
  refine ⟨hp1, fun C₂ h2 => ?_⟩
  refine corollary_monotone_in_constant D _ C₂ h2 ?_
  refine h' D 800 (by norm_num) hp1 h12 ?_
  intro l _ K LL n _ emb T₁ T₂ F h1 h2 hF i A hA' τ hτ a ha
  exact hA' τ hτ a ((h14 l K LL).1 T₁ T₂ F h1 h2 hF τ a ha)

end Formalism.MainNotions.N.Ln03
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03 PowerSeries

section Div

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem isUnit_of_mk {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {x : R}
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : x * y' - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, map_one, sub_self]
  have h2 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot I h1) 1
  rw [mul_one, sub_add_cancel] at h2
  exact isUnit_of_mul_isUnit_left h2

theorem aeval_X_coe {R : Type} [CommRing R] (r : Polynomial R) :
    Polynomial.aeval (PowerSeries.X : PowerSeries R) r = (r : PowerSeries R) := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), hp, hq, Polynomial.coe_add]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.coe_monomial, PowerSeries.monomial_eq_mk]
    ext m
    simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, eq_comm]

theorem map_aeval {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : PowerSeries R) (P : Polynomial R) :
    PowerSeries.map f (Polynomial.aeval x P) = Polynomial.aeval (PowerSeries.map f x) (P.map f) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext c : 1
  simp [PowerSeries.algebraMap_eq]

variable [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem wdiv_ps (W : LocWach PD LL O v n) (hR : ToolsR.RingP W) (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ) (f : PowerSeries O) :
    ∃ (H : PowerSeries O) (r : Polynomial O), r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) ∧
      f = ps W s a * H + (r : PowerSeries O) := by
  set I : Ideal O := Ideal.span {((PD.p : ℕ) : O)} with hIdef
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, hIdef, Ideal.span_singleton_eq_top]; exact hpu)
  set N : ℕ := (PD.p - 1) * PD.p ^ s with hN
  set D : PowerSeries O := ps W s a with hDdef
  obtain ⟨u, P, hu, hPm, hPd, hPc, hps⟩ := hT.2.1 s
  obtain ⟨w, hw, hπw⟩ := ToolsR.π₀_comp hR
  have hD : D = u a * Polynomial.aeval W.π₀₁ P := by
    have h1 := congrFun hps a
    rw [Pi.mul_apply] at h1
    rw [hDdef, show ps W s = Formalism.MainNotions.WachCoordinates.pS W s from rfl, h1]
    congr 1
    exact (Polynomial.aeval_algHom_apply (Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) a) W.π₀ P).symm
  have hPmap : P.map (Ideal.Quotient.mk I) = Polynomial.X ^ (PD.p ^ s) := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
    rcases lt_trichotomy k (PD.p ^ s) with hk | rfl | hk
    · rw [if_neg hk.ne, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton.2 (hPc k hk)
    · rw [if_pos rfl, ← hPd, hPm.coeff_natDegree, map_one]
    · rw [if_neg hk.ne', Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  set V : PowerSeries (O ⧸ I) := PowerSeries.map (Ideal.Quotient.mk I) (u a) *
    PowerSeries.map (Ideal.Quotient.mk I) w ^ (PD.p ^ s) with hV
  have hmapD : PowerSeries.map (Ideal.Quotient.mk I) D = V * PowerSeries.X ^ N := by
    rw [hD, map_mul, map_aeval, hPmap, Polynomial.aeval_X_pow, hπw, map_mul, map_pow, PowerSeries.map_X, hV, hN,
      mul_pow, ← pow_mul, mul_comm (PD.p - 1) (PD.p ^ s)]
    ring
  have huV : IsUnit (PowerSeries.constantCoeff V) := by
    rw [hV, map_mul, map_pow]
    refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
    · have := ((hu.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)).map
        (PowerSeries.map (Ideal.Quotient.mk I))).map PowerSeries.constantCoeff
      simpa using this
    · exact (hw.map (PowerSeries.map (Ideal.Quotient.mk I))).map PowerSeries.constantCoeff
  have hcN : PowerSeries.coeff N (PowerSeries.map (Ideal.Quotient.mk I) D) = PowerSeries.constantCoeff V := by
    rw [hmapD, PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff]
  have hord : (PowerSeries.map (Ideal.Quotient.mk I) D).order.toNat = N := by
    have : (PowerSeries.map (Ideal.Quotient.mk I) D).order = N := by
      refine PowerSeries.order_eq_nat.2 ⟨by rw [hcN]; exact huV.ne_zero, fun i hi => ?_⟩
      rw [hmapD, PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
    rw [this, ENat.toNat_natCast]
  have hdiv : D.IsWeierstrassDivisorAt I := by
    unfold PowerSeries.IsWeierstrassDivisorAt
    rw [hord]
    refine isUnit_of_mk I ?_
    rw [← PowerSeries.coeff_map, hcN]
    exact huV
  have HD := hdiv.isWeierstrassDivisionAt_div_mod f
  refine ⟨hdiv.div f, hdiv.mod f, ?_, HD.eq_mul_add⟩
  have := HD.degree_lt
  rwa [hord] at this

theorem ev_aeval {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (hB : LevBasics W a s) (ζ : Rs hB.F PD.p s)
    (r : Polynomial O) : hB.ev ζ (Polynomial.aeval (letπ : LetA O n) r) = Polynomial.aeval ((ζ : hB.F) - 1) r := by
  let evA : LetA O n →ₐ[O] hB.F := { hB.ev ζ with commutes' := hB.ev_O ζ }
  rw [← hB.ev_π ζ]
  exact (Polynomial.aeval_algHom_apply evA letπ r).symm

theorem card_Rs {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (hB : LevBasics W a s) :
    Fintype.card (Rs hB.F PD.p s) = (PD.p - 1) * PD.p ^ s := by
  obtain ⟨ζ₀, hζ₀⟩ := hB.root
  rw [Fintype.card_coe, hζ₀.card_primitiveRoots, Nat.totient_prime_pow_succ PD.hp, mul_comm]

theorem poly_eq_zero {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (hB : LevBasics W a s) (r : Polynomial hB.F)
    (hdeg : r.natDegree < (PD.p - 1) * PD.p ^ s) (h : ∀ ζ : Rs hB.F PD.p s, Polynomial.eval ((ζ : hB.F) - 1) r = 0) :
    r = 0 :=
  Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun ζ : Rs hB.F PD.p s => (ζ : hB.F) - 1)
    (fun x y hxy => Subtype.ext (sub_left_injective hxy)) h (by rw [card_Rs hB]; exact hdeg)

theorem levDiv_of (W : LocWach PD LL O v n) (hR : ToolsR.RingP W) (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ) (hB : LevBasics W a s) : LevDiv W a s hB.F hB.ev := by
  intro g hg hev
  have hNpos : 0 < (PD.p - 1) * PD.p ^ s := Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
  obtain ⟨H, r, hdeg, heq⟩ := wdiv_ps W hR hT hpu a s (g a)
  set wH : LetA O n := Pi.single a H with hwH
  have hRr : (fun _ : ZMod n => (r : PowerSeries O)) = Polynomial.aeval (letπ : LetA O n) r := by
    funext i
    show (r : PowerSeries O) = Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) i (Polynomial.aeval letπ r)
    rw [← Polynomial.aeval_algHom_apply]
    exact (aeval_X_coe r).symm
  have key : (letE a : LetA O n) * g = ps W s * wH + letE a * Polynomial.aeval (letπ : LetA O n) r := by
    rw [← hRr]
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_same, one_mul, heq]
    · simp [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_of_ne hi]
  have hroots : ∀ ζ : Rs hB.F PD.p s, Polynomial.eval ((ζ : hB.F) - 1) (r.map (algebraMap O hB.F)) = 0 := by
    intro ζ
    have h1 := congrArg (hB.ev ζ) key
    rw [map_mul, hB.ev_letE, one_mul, hev ζ, map_add (f := _), map_mul, hB.ev_ps, zero_mul, zero_add, map_mul,
      hB.ev_letE, one_mul, ev_aeval hB] at h1
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact h1.symm
  have hr0 : r.map (algebraMap O hB.F) = 0 := by
    refine poly_eq_zero hB _ (lt_of_le_of_lt Polynomial.natDegree_map_le ?_) hroots
    by_cases hr : r = 0
    · rw [hr, Polynomial.natDegree_zero]; exact hNpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hr).2 hdeg
  have hr : r = 0 := Polynomial.map_injective _ hB.inj (by rw [hr0, Polynomial.map_zero])
  rw [hr, map_zero, mul_zero, add_zero] at key
  have hpsΔ : ps W s ∈ W.AΔ := RatW.ps_mem W hR.1 s
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hB.hp
    rw [← map_natCast (algebraMap O hB.F), h, map_zero]
  have hps0 : ∀ i, ps W s i ≠ 0 := by
    intro i h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hT.2.2.1 s)
    have h1 := congrFun hc i
    have h2 := congrArg PowerSeries.constantCoeff h1
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.natCast_apply, map_mul, map_sub, map_natCast, LocWach.π₀,
      ToolsR.π₀₁_cc hR, mul_zero] at h2
    rw [show Formalism.MainNotions.WachCoordinates.pS W s i = ps W s i from rfl, h, map_zero, zero_sub, eq_comm, neg_eq_zero] at h2
    exact hp0 h2
  refine ⟨0, wH, ToolsR.cancel_AΔ hpsΔ hps0 ?_, by rw [pow_zero, one_mul, key]⟩
  rw [← key]
  exact W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) hg

end Div

end Formalism.MainNotions.UnusedSlot80.InvW
end
end
