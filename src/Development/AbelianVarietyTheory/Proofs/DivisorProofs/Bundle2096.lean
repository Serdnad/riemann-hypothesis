module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle811
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
open Formalism.DivisionValues (vw)

namespace GlobalTheory.RhoLowProof

theorem meanVal_lower {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {β : ℂ} {p : K[X]}
    (hp : IsMinPol σ β p) (hβ : β ≠ 0) {c : K} (hc : c ≠ 0) {l : ℕ} (hl : l.Prime)
    {w : Formalism.PairingDivisionLocalBalance.Pl K} (hw : (l : 𝓞 K) ∈ w.asIdeal) {m : ℕ}
    (h : IntAt l ((l : ℂ) ^ m * (σ c * β))) :
    -((m : ℝ) * (vw w (l : K) : ℝ)) ≤ (vw w c : ℝ) + meanVal_vw w p :=
  GlobalTheory.T.meanValuation_ge_of_integral_at_prime σ hp hβ hc hl hw h

theorem classZetaVals_unique {E : Type} [Field E] [NumberField E] {k : ℕ} (hk : 2 ≤ k) {z z' : ClassGroup (OF E) → ℚ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z) (h' : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z') : z = z' :=
  GlobalTheory.T.partialZeta_values_at_neg_int_unique hk h h'

section Twist
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)


open Classical in
theorem twist_val {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j) :
    IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl)
      ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) (nuH G t i j) :=
  GlobalTheory.T.square_nu_twisted_tuple_isCMValueHeckeCharacter G hL t i j hs


open Classical in
theorem squareTopTwistPlaces_coprime_splitPlaces {μ₀ : T} (hL : L.Is μ₀) (t : T) :
    IsFinSetSplitPlacesCoprimeConductor (condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) :=
  GlobalTheory.T.isFinSetSplitPlacesCoprimeConductor_twPl_under G hL t

theorem twist_ram {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) :
    ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (nuH G t i j).UnrAt P :=
  GlobalTheory.T.square_nu_twisted_tuple_ramified_at_twist_place G hL t i j


open Classical in
theorem twist_prime (t : T) {l : ℕ} (hl : l.Prime) {w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL} (hlw : (l : 𝓞 D.what₂.LL) ∈ w.asIdeal)
    (hQ : (GlobalTheory.SqTop.Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal) :
    ∀ q ∈ (GlobalTheory.SqTop.twPl G t).image (fun P => P.under (𝓞 D.host.F)), (l : 𝓞 D.host.F) ∉ q.asIdeal :=
  GlobalTheory.T.twist_places_under_prime_not_mem_of_norm_coprime G t hl hlw hQ

end Twist

theorem vw_pow {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {z : K} (hz : z ≠ 0) (n : ℕ) :
    vw w (z ^ n) = n * vw w z := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

theorem over_under {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Over P (P.under (OF E)) := rfl


open Classical in
theorem core (hTD : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator) {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} {μ₀ : T}
    (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E) (hab : IsAbelianGalois ℚ D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl))
    (i j : Fin D.R.m) (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ halfRank D i j)
    (t : T) (Λ Λ₀ : ℂ → ℂ) (z : D.what₂.LL) (zd : Bool → D.what₂.LL) (g : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → ℤ) (n : ℕ → ℝ)
    (hΛ : IsHeckeL (nuH G t i j) Λ) (hΛ₀ : IsHeckeL (nuH G μ₀ i j) Λ₀) (hz : D.what₂.embLL z * Λ₀ s = Λ s)
    (htv : IsTorVal G μ₀ i j s zd g) (hden : IsDenom G i j s n)
    (w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL) (l : ℕ) (hl : l.Prime) (hlw : (l : 𝓞 D.what₂.LL) ∈ w.asIdeal)
    (hQw : (GlobalTheory.SqTop.Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal) :
    -(n l * (vw w (l : D.what₂.LL) : ℝ)) ≤ ((vw w z + g w : ℤ) : ℝ) := by
  haveI := hcm
  haveI := hab
  obtain ⟨x, hx, hx0, -, Λl, p, hΛl, hp, hg⟩ := htv
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (cmPhi D) := hfd.2.2.2.2.2.2.1

  have e0 : x = Λ₀ s := by
    have h := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
      (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) (fun _ => G.pl.w G.pl.v0) Λ₀ hU hs1 hbc
      (fun q hq => absurd hq (Finset.notMem_empty q)) hx.1 (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ₀
    simp only [condQ, Finset.prod_empty, mul_one, Finset.filter_empty] at h
    exact hx.2.unique h

  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset (HeightOneSpectrum (OF D.host.E)),
      Q = (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := ⟨_, rfl⟩
  have hQval := twist_val G hL t i j hs2
  have hQaux := squareTopTwistPlaces_coprime_splitPlaces G hL t
  have hQram := twist_ram G hL t i j
  have hQpr := twist_prime G t hl hlw hQw
  rw [← hQdef] at hQval hQaux hQpr
  have hex : ∀ q ∈ Q, ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q := fun q hq => by
    rw [hQdef] at hq
    exact Finset.mem_image.1 hq
  let Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun q =>
    if h : ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q then h.choose else G.pl.w G.pl.v0
  have hPq : ∀ q ∈ Q, Pq q ∈ GlobalTheory.SqTop.twPl G t ∧ (Pq q).under (𝓞 D.host.F) = q := fun q hq => by
    have h := hex q hq
    simp only [Pq, dif_pos h]
    exact h.choose_spec
  have hov : ∀ q ∈ Q, Over (Pq q) q := fun q hq =>
    (over_under (Pq q)).trans (congrArg HeightOneSpectrum.asIdeal (hPq q hq).2)
  have htor := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) Pq Λ hU hs1 hbc hQaux hQval
    hov hΛ
  rw [Finset.filter_false_of_mem (fun q hq => hQram _ (hPq q hq).1), Finset.prod_empty, mul_one] at htor

  have hnu : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
    rw [nuH, nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]
  have hpic : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsPicChar (condQ (condF G.pl) Q) (Lc.xiH t) := by
    obtain ⟨k, hk, hko⟩ := hL.xi_fin t
    refine ⟨fun y => GlobalTheory.TypeValues.inf_eq_one _ hk hko y, fun u hu => ?_⟩
    have a := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) Q (nuH G t i j) hU hbc hQaux hQval u hu
    have hle : condQ (condF G.pl) Q ≤ condQ (condF G.pl) ∅ := by
      simp only [condQ, Finset.prod_empty, mul_one]
      exact Ideal.mul_le_left
    have b := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) ∅ (nuH G μ₀ i j) hU hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hx.1 u
      (hatOUnits_mono hle hu)
    rw [hnu, finPart_mul, b, one_mul] at a
    exact a

  obtain ⟨zc, hzc, H⟩ := hTD D.host.E D.what₂.Tau D.host.d (cmPhi D) s hfd hs1
  have hV := ((H (kap D sc.cGap i j s) (condF G.pl) Λl (nuH G μ₀ i j) hbc hΛl hx.1) l hl Q hQaux hQpr).2
    (Lc.xiH t) (Λ s) hpic (hnu ▸ htor)
  obtain ⟨zc', hzc', hn⟩ := hden
  obtain rfl : zc = zc' := classZetaVals_unique (by omega) hzc hzc'
  set B := GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D sc.cGap i j s) (condF G.pl) zc l with hB
  set N := ⌈B / 12⌉₊ with hN
  have hnl : n l = N := by rw [hn l hl]
  have hInt := hV (12 * N : ℕ) 1 one_pos (by
    push_cast
    have := Nat.le_ceil (B / 12)
    linarith)

  have hv0 : G.pl.v0 ∉ Q := fun h => by
    obtain ⟨P, hP, e⟩ := hex _ h
    have hP' : P ∈ Lc.Q t := by
      simp only [GlobalTheory.SqTop.twPl, Finset.mem_filter, locPl, Finset.mem_union] at hP
      exact hP.1.resolve_left hP.2
    exact G.pl.levelPlace_ne_basePlace t P hP' e
  have hram0 : ¬ (nuH G t i j).UnrAt (G.pl.w G.pl.v0) := by
    have h1 := (hQval.2.2.2 G.pl.v0 (G.pl.w G.pl.v0) ((over_under _).trans (congrArg HeightOneSpectrum.asIdeal (G.pl.w_over _ (Finset.mem_insert_self _ _))))).2 hv0
    rw [GlobalTheory.FunObj.SqNum.Model.expIn_condF, if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)), condExp, if_pos rfl] at h1
    exact h1.not_unrAt one_ne_zero
  have hΛs : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hQval.1
    (GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt hram0) hΛ (by simpa using (by exact_mod_cast hs1 : (1 : ℝ) ≤ s))
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hΛs (by rw [← hz, map_zero, zero_mul])

  have hbeta : beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl (Λ s) =
      D.what₂.embLL (z ^ 12) * beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl x := by
    rw [← hz, ← e0, beta, beta, map_pow]
    ring
  have hβ0 : beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl x ≠ 0 := by
    rw [beta]
    refine div_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ hx0)) (pow_ne_zero _ (latDisc_ne_zero Λl))
    exact_mod_cast (cmValueConst_pos D.host.E (hfd.1.pos) (by omega) _).ne'
  rw [hbeta, pow_one, zpow_natCast] at hInt
  have key := meanVal_lower D.what₂.embLL hp hβ0 (pow_ne_zero 12 hz0) hl hlw hInt
  rw [vw_pow w hz0] at key
  have h2 : ((-(N * vw w (l : D.what₂.LL)) : ℤ) : ℝ) ≤ (vw w z : ℝ) + meanVal_vw w p / 12 := by
    push_cast at key ⊢
    linarith
  have h3 := GlobalTheory.FunObj.SqNum.le_add_truncZero h2
  rw [hnl, hg w]
  have h4 : ((-(N * vw w (l : D.what₂.LL)) : ℤ) : ℝ) ≤ ((vw w z + GlobalTheory.LeafRestExamples.truncZero (meanVal_vw w p / 12) : ℤ) : ℝ) := by
    exact_mod_cast h3
  push_cast at h4 ⊢
  linarith

theorem rhoLow_holds : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.TorEx → GlobalTheory.SqTop.RhoLow := by
  intro hTD hF _
  obtain ⟨CF0, hF⟩ := hF
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, hF⟩ := hF ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hcm, hab, hfd, hbc, -⟩ := hF C hC D large₂ he hx hR T Lc μ₀ hL G
  intro i j s hs1 hs2 t Λ Λ₀ z zd g n hΛ hΛ₀ hz htv hden w l hl hlw hQw
  exact core hTD hL G hcm hab hfd hbc i j s hs1 hs2 t Λ Λ₀ z zd g n hΛ hΛ₀ hz htv hden w l hl hlw hQw

end GlobalTheory.RhoLowProof

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise


theorem _root_.GlobalTheory.T.gridLocalTensorPlaces_coprime_two_q_d : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.SqTop.Rec large₂ → ∀ {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T), ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  first | exact @GlobalTheory.StdPairPlaces.natCast_two_q_d_notMem | exact GlobalTheory.StdPairPlaces.natCast_two_q_d_notMem | (intros; apply GlobalTheory.StdPairPlaces.natCast_two_q_d_notMem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.bilinearFockPairing_sq_le_hermitianNorms : ∀ {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x y : VV ℂ w),
    ‖pairBK w x y‖ ^ 2 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  first | exact @GlobalTheory.FockCauchySchwarz.pairBK_sq_le | exact GlobalTheory.FockCauchySchwarz.pairBK_sq_le | (intros; apply GlobalTheory.FockCauchySchwarz.pairBK_sq_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.dualLattice_embedded_lastCoordinate_sum : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n N : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 E) (Fin n → E))
    (L : Submodule (𝓞 E) (Fin N → E)),
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ τ : ι, dualFr (tauLat emb τ L) = Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) 1 := by
  first | exact @GlobalTheory.dualFr_tauLat_sumLat | exact GlobalTheory.dualFr_tauLat_sumLat | (intros; apply GlobalTheory.dualFr_tauLat_sumLat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isLattice_of_lastCoordinate_extension : ∀ {E : Type} [Field E] [NumberField E] {n N : ℕ} (hN : N = n + 1)
    (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    Submodule.IsLattice E L := by
  first | exact @GlobalTheory.latLast_isLattice | exact GlobalTheory.latLast_isLattice | (intros; apply GlobalTheory.latLast_isLattice <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MvPolynomial
open scoped Matrix

namespace GlobalTheory.CoefSchur

theorem polyAction_ten (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (h : ι → GL (Fin n) K) (f : ι → MvPolynomial (Fin n × Fin n) K) :
    actP lam h (ten f) = ten fun τ => sqAct K n (lam τ) (h τ) (f τ) := by
  have hb := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)).1
  simp only [actP, ten, detTwK, trAct, sqAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod, hb, map_smul]
  rw [Finset.prod_smul]

theorem natW_anti {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  omega

theorem ten_ext_mem (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    (ten fun τ => extremal K n (lam τ)) ∈ VV K lam :=
  Submodule.subset_span ⟨fun τ => extremal K n (lam τ),
    fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (natW_anti (lam τ)), rfl⟩

theorem endo_scalar : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g : Module.End K (VV K lam)),
    (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∃ a : K, ∀ v, g v = a • v := by
  intro K _ _ ι _ n lam g hg
  set v0 : VV K lam := ⟨_, ten_ext_mem K lam⟩ with hv0
  have hw0 := (GlobalTheory.T.weightSpace_coefficientSpace_eq_extremalTensorLine K lam).1
  have hgw := GlobalTheory.T.weylTensorCoefSpace_endomorphism_preserves_torus_weight K lam g hg v0 hw0
  obtain ⟨a, ha⟩ := (GlobalTheory.T.weightSpace_coefficientSpace_eq_extremalTensorLine K lam).2 _ (g v0).2 hgw
  have ha' : g v0 = a • v0 := Subtype.ext ha
  refine ⟨a, ?_⟩
  let W : Submodule K (Pol K ι n) := Submodule.map (VV K lam).subtype (LinearMap.ker (g - a • LinearMap.id))
  have hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (Set.range fun x : GL (Fin n) K => sqAct K n (lam τ) x (extremal K n (lam τ))) :=
    fun τ => GlobalTheory.T.dualWeylModule_le_span_extremalTranslates K n (lam τ)
  have hle := GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors K lam _ hS
  have hW : VV K lam ≤ W := by
    refine hle.trans (Submodule.span_le.2 ?_)
    rintro P ⟨f, hf, rfl⟩
    choose h hh using hf
    have e : ten f = ten fun τ => sqAct K n (lam τ) (h τ) (extremal K n (lam τ)) := by
      congr 1; funext τ; exact (hh τ).symm
    refine ⟨rhoK lam h v0, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hg, ha', map_smul, sub_self]
    · rw [e, ← polyAction_ten]; rfl
  intro v
  obtain ⟨w, hw, hwv⟩ := hW v.2
  have : w = v := Subtype.ext hwv
  subst this
  simpa [sub_eq_zero] using hw

end GlobalTheory.CoefSchur
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.BaseId

variable {D : D7}

section Row

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

theorem tie_baseChange {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r n : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {Γ : Type} [Group Γ]
    {act : Γ → Rul Xo c →ₗ[c.F] Rul Xo c} {act' : Γ → Rul Xo c' →ₗ[c'.F] Rul Xo c'}
    {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs] {Tup : Type} {dδ : Tup → DeltaDat Xo c' n}
    {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
    {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat D.host.E n} {Nc : ∀ t, Cl' t → ℕ}
    {gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
    {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
    {cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ} {ph : ℂ}
    (htie : OneMapTieC hle LL U σ' V dict mu xr a act act' dδ Cl' w La Nc gam vol ep io thAd Pl cc ph) (t : Tup) :
    ∃ z ∈ Subgroup.center Γ, ∃ ze ∈ LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      ∃ (f' : Rul Xo c') (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), f' ∈ sec Xo c' a n ∧
        IsThClsD Xo c' (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f' ∧ (∀ k, fs k ∈ cusp Xo c U a n) ∧
        IsBC hle f' as fs ∧ ∀ q : AutQ V, ph * thAd t x q = ∑ k, ze * σ' (as k) * ((lieFac Dw xr a : ℂ) *
          adel V dict (muPin V dict mu cc) (rdU (U (σ'.comp (incF c c' hle))) (act z (fs k))) q.out) := by
  obtain ⟨-, hC, hA, -, -, z, hz, hrow⟩ := htie
  obtain ⟨ze, hze, hroot, hrow⟩ := hrow t
  refine ⟨z, hz, ze, hze, hroot, fun x hx => ?_⟩
  obtain ⟨⟨f', hf', hcl⟩, hall⟩ := hrow x hx
  have hf's := cusp_le_sec _ _ _ _ _ hf'
  obtain ⟨m, as, fs, hfs, hBC⟩ := hC a n f' hf'
  have hBCz := hA a n z m as fs f' hf's (fun k => cusp_le_sec _ _ _ _ _ (hfs k)) hBC
  refine ⟨f', m, as, fs, hf's, hcl, hfs, hBC, fun q => ?_⟩
  have h1 := hall f' hf's hcl q
  have h2 := GlobalTheory.PhaseRational.rdU_of_isBC hle U σ' hBCz (dict q.out).1 (dict q.out).2
  have h3 : jFn V σ' (rdU (unfBC hle U σ')) dict mu (act' z f') q = mu q.out * ∑ k, σ' (as k) *
      rdU (U (σ'.comp (incF c c' hle))) (act z (fs k)) (dict q.out).1 (dict q.out).2 :=
    congrArg (mu q.out * ·) h2
  rw [h1, h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adel_muPin]
  change ze * cc (dict q.out).1 * _ * _ = _
  ring

end Row

theorem phiC_congr (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem proj_model {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {X G : Type} [AddCommGroup X] [Module ℂ X] [Fintype G]
    (e : X →ₗ[ℂ] MMap M) (he : Function.Injective e) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (c : G → ℂ)
    (ρ : G → X →ₗ[ℂ] X) (hρ : ∀ g x, e (ρ g x) = postOn M (L g) (e x)) (ph : ℂ) (y y' w : X)
    (hy : e y' = postOn M (∑ g, c g • L g) (e y)) (hw : ph • y = w) : ph • y' = ∑ g, c g • ρ g w := by
  have h1 : y' = ∑ g, c g • ρ g y := by
    apply he

    rw [hy, map_sum]
    simp only [map_smul, hρ]
    ext v x
    simp [postOn, LinearMap.sum_apply, Finset.sum_apply]
  rw [h1, ← hw, Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, smul_comm]

theorem eq_of_reps {V : HSp D} {S : D.what₂.Tau → SPar} {θ} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] MMap M) (hr : LinearMap.range e = Mult.Mult θ M J χ) (v : M.Vec)
    (hinj : Function.Injective fun x => e x v) (ph : ℂ) (y : X) {n : ℕ} (b : Fin n → ℂ) (u : Fin n → X)
    (h : ∀ q : AutQ V, ph * e y v q.out = ∑ k, b k * e (u k) v q.out) : ph • y = ∑ k, b k • u k := by
  apply hinj
  funext g
  refine GlobalTheory.PhaseRational.eq_of_out
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v)
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v) (fun q => ?_) g

  simpa [map_sum, Finset.sum_apply] using h q

end GlobalTheory.GalLift.BaseId

end
end
