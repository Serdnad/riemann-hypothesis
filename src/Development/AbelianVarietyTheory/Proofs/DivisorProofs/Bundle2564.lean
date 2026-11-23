module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIntZSqNonnegOfSqDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle816
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle702
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle498
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.thetaLift_eq_integral_routeKernel_fubini : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  first | exact @GlobalTheory.BigRoute.lift_eq_integral_kerBig | exact GlobalTheory.BigRoute.lift_eq_integral_kerBig | (intros; apply GlobalTheory.BigRoute.lift_eq_integral_kerBig <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovInt


set_option maxHeartbeats 1000000 in
theorem integral_smul_thLa : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ [StarRing (𝓞 D.host.E)] (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∃ Na : ℕ, 0 < Na ∧ Real.log Na ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n ∧ ∀ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F), La.Unimod → La.TrivAt (GlobalTheory.CovGmin.badC Y) → La.TrivAt Y.d.l₂.M → La.LevOK N Y.d.l₂.M → P ∈ harmL Y.d.c₂ La a → ∀ y : Y.V (wtZ a n), (∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R), thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')) → ∀ s : Y.d.c₂.F, Submodule.span (𝓞 Y.d.c₂.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.Ln τ ^ (T.Q.Dw j).mult τ ≤ ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.La τ ^ (T.Q.Dw j).mult τ → ∀ y₁ : Y.V (wtZ a n), (y₁ : Rul Y.d.Xo₂ Y.d.c₂) = s • (y : Rul Y.d.Xo₂ Y.d.c₂) → Na • y₁ ∈ AllWt.latW Y.U (wtZ a n) := by
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.log_shortThetaSeriesDenominatorBound_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro D T j Y e o Lb a n hH _ nab hnab
  obtain ⟨hpos, hlog⟩ := hC D T j Y e o Lb a n hH
  refine ⟨intZ D (T.Q.Dw j) Y.d.l₂ n a ^ 2, pow_pos hpos 2, ?_, ?_⟩
  · rw [Nat.cast_pow, Real.log_pow]
    push_cast
    nlinarith
  · intro x0 La N P hU hTb hTM hN hP y hval s hs y₁ hy₁
    choose x0' hx0' using fun b => Submodule.Quotient.mk_surjective _ (x0 b)
    have hx : x0 = fun b => (Submodule.Quotient.mk (x0' b) : LevQc (T.Q.Dw j) Y.d.l₂) := funext fun b => (hx0' b).symm
    subst hx
    rw [GlobalTheory.RawSpan.phiHat_indPhi_mk] at hval
    have hsec : (y : Rul Y.d.Xo₂ Y.d.c₂) ∈ sec Y.d.Xo₂ Y.d.c₂ a n := by
      have := GlobalTheory.AllWt.cuspW_le_secZ (U := Y.U) (wtZ a n) y.2
      rwa [GlobalTheory.AllWt.exZ_wtZ, GlobalTheory.AllWt.secZ_nat] at this
    have hR := GlobalTheory.RawSpan.isShortRule_of_raw nab hnab hU hTM hN hP x0' _ hsec hval
    obtain ⟨-, hp1, -, hfr, -, -, -, -, -, -, -, -, -, hn8, -, -⟩ := hH
    have hM0 : Y.d.l₂.M ≠ 0 := by
      intro h0
      have hc := GlobalTheory.PlaceInt.card_fun_levQ _ _ (T.Q.Dw j) Y.d.l₂ n
      have hex : Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by omega)
      rw [h0, zero_pow hex] at hc
      have : intZ D (T.Q.Dw j) Y.d.l₂ n a = 0 := by unfold intZ; rw [hc]; simp
      omega
    have hβ : betaH (Dw := T.Q.Dw j) Y.d.c₂ La ≠ 0 := GlobalTheory.RawSpan.betaH_ne_zero La
    have hg := Submodule.smul_mem _ (betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ hsec
    have hlevI := GlobalTheory.RawSpan.idCover_isLev nab n
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = intZ D (T.Q.Dw j) Y.d.l₂ n a := ⟨_, rfl⟩
    rw [← hZ]
    refine GlobalTheory.AllWt.mem_supLat.2 ?_
    intro la v hv
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul Y.d.c₂.F, hy₁]
    have hV := isVal_valSet la v hv
    have hZ0 : Z ≠ 0 := by rw [hZ]; exact hpos.ne'
    by_cases hb : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 Y.d.c₂.F) ∈ la.asIdeal ∧ ℓ ∣ Y.d.l₂.M
    · obtain ⟨ℓ₀, hℓ₀, hm₀, hd₀⟩ := hb
      have hsI := GlobalTheory.T.intersectedLattice_detIdeal_integral_trivAt_prime D.host.E _ (T.Q.Dw j) _ Y.d.c₂ n La ℓ₀ hℓ₀ (GlobalTheory.IntCuspLat.trivAt_of_dvd hTM hd₀) la hm₀ s hs
      rw [smul_comm]
      refine GlobalTheory.IdemInt.nonneg_smul hV hsI ?_
      have hyZ : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (y : Rul Y.d.Xo₂ Y.d.c₂) =
          ((Z : Y.d.c₂.F)) • ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La * (Z : Y.d.c₂.F)) •
            ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂))) := by
        rw [smul_smul, smul_smul]
        congr 1
        field_simp
        push_cast
        ring
      have hyZ2 : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (y : Rul Y.d.Xo₂ Y.d.c₂) =
          (betaH (Dw := T.Q.Dw j) Y.d.c₂ La * ((Z ^ 2 : ℕ) : Y.d.c₂.F)) •
          ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂)) := by
        rw [smul_smul]
        congr 1
        field_simp
      by_cases h : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 Y.d.c₂.F) ∈ la.asIdeal ∧ ℓ ^ 2 ∣ Y.d.l₂.M
      · obtain ⟨ℓ, hℓ, hm, hsq⟩ := h
        have htr : La.TrivAt ℓ := GlobalTheory.IntCuspLat.trivAt_of_dvd hTM
          (dvd_trans (dvd_pow_self ℓ two_ne_zero) hsq)
        rw [hyZ2, hZ]
        exact GlobalTheory.CovInt.SqLev.smul_intZ_sq_nonneg_of_sq_dvd D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
          (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
          la ℓ hℓ hm hsq htr v hv
      · push_neg at h
        rw [hyZ, hV.smul _ _ (by exact_mod_cast hZ0)]
        have h1 := vAdd_int_nonneg la (a := (Z : 𝓞 Y.d.c₂.F)) (by exact_mod_cast hZ0)
        refine add_nonneg (by exact_mod_cast h1) ?_
        rw [hZ]
        exact GlobalTheory.CovInt.smul_intZ_nonneg_away D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
          (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
          la h v hv
    · push_neg at hb
      have hyZ : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (s • (y : Rul Y.d.Xo₂ Y.d.c₂)) =
          ((Z : Y.d.c₂.F)) • ((s * betaH (Dw := T.Q.Dw j) Y.d.c₂ La * (Z : Y.d.c₂.F)) •
            ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂))) := by
        rw [smul_smul, smul_smul, smul_smul]
        congr 1
        field_simp
        push_cast
        ring
      rw [hyZ, hV.smul _ _ (by exact_mod_cast hZ0)]
      have h1 := vAdd_int_nonneg la (a := (Z : 𝓞 Y.d.c₂.F)) (by exact_mod_cast hZ0)
      refine add_nonneg (by exact_mod_cast h1) ?_
      rw [hZ]
      exact GlobalTheory.T.clearingInteger_shortSeries_integral_coprimeLevel D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
        (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
        la hb s hs v hv

end GlobalTheory.CovInt
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BaseCmp
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem unitOff_inv_mul' {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v)⁻¹ := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨inv_ne_zero (mul_ne_zero hu0 hv0), n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by
      rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹⁻¹ = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by
      rw [inv_inv, pow_add]; ring
    rw [e]; exact hn1.mul hm1

theorem exists_unif' (E : Type) [Field E] [NumberField E] (Q : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :
    ∃ ϖ : 𝓞 E, ϖ ≠ 0 ∧ ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2 := by
  have hx : ∀ PP : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ∃ x ∈ PP.asIdeal, x ∉ PP.asIdeal ^ 2 := fun PP => by
    simpa using Ideal.exists_mem_pow_notMem_pow_succ PP.asIdeal PP.ne_bot PP.isPrime.ne_top 1
  choose x hx1 hx2 using hx
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Q)
    (fun PP => PP.asIdeal) (fun _ => 2) (fun PP _ => Ideal.prime_of_isPrime PP.ne_bot PP.isPrime)
    (fun PP _ PP' _ h e => h (IsDedekindDomain.HeightOneSpectrum.ext e)) (fun PP => x PP.1)
  have key : ∀ PP ∈ Q, y ∈ PP.asIdeal ∧ y ∉ PP.asIdeal ^ 2 := fun PP hPP => by
    have h1 := hy PP hPP
    have hle : PP.asIdeal ^ 2 ≤ PP.asIdeal := Ideal.pow_le_self (by norm_num)
    refine ⟨?_, fun h => hx2 PP ?_⟩
    · have := PP.asIdeal.add_mem (hle h1) (hx1 PP)
      simpa using this
    · have := (PP.asIdeal ^ 2).sub_mem h h1
      simpa using this
  by_cases hQ : Q.Nonempty
  · obtain ⟨PP, hPP⟩ := hQ
    refine ⟨y, fun h0 => (key PP hPP).2 (h0 ▸ Ideal.zero_mem _), key⟩
  · refine ⟨1, one_ne_zero, fun PP hPP => absurd ⟨PP, hPP⟩ hQ⟩

theorem flatKer_holds : FlatKer := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV B hBg hB ξ ξR ω φ hK hQt N hN hNQ
  obtain ⟨eg, eQ, fg, heg, heQ, hfg, hflat⟩ := GlobalTheory.BaseCmp.flatTwoStep_holds D G Pl0 T0 A Ks R F hC i ξ B.de.chi ξR ω φ B hBg hB hK hK.chr
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_unif' D.host.E B.de.Q
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, hz, hzm⟩ := GlobalTheory.CentScal.exists_isCentAt_scalar D i B.de.Q eQ heQ (ϖ : D.host.E) hϖE
  obtain ⟨κ, hκ, hact⟩ := GlobalTheory.T.central_uniformiser_acts_by_dilation_tame_kernel D G Pl0 T0 A Ks R F hC hQG i hV ξ B.de.chi ξR B.de.Q ω φ hK hQt N hN hNQ
    eg eQ fg heg heQ hfg ϖ hϖE hϖ z hzm
  obtain ⟨Gc, hG, hSB, hφ⟩ := GlobalTheory.T.tameKernel_vector_unit_mul_dilated_flat D G Pl0 T0 A Ks R F hC hQG i hV ξ B.de.chi ξR B.de.Q ω φ hK hQt N hN hNQ
    eg eQ fg heg heQ hfg ϖ hϖ0 hϖ
  obtain ⟨Tm, hTm⟩ := hflat.1
  have hvT := hflat.2 Tm hTm
  have hφT := hφ Tm hTm
  have hne : κ * Gc ≠ 0 := mul_ne_zero hκ.1 hG.1
  have hcomp : ∀ x : WO (Vc D i) (Wc D i), dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ x) = x := by
    intro x
    show Matrix.map (Matrix.map x fun w => incA D ((ϖ : D.host.E)⁻¹) * w) (fun w => incA D (ϖ : D.host.E) * w) = x
    ext a b
    simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  have hvec : (princ B).vecBase = (κ * Gc)⁻¹ • ω (z, 1) φ := by
    rw [hφT, hact Tm hTm _ hSB]
    simp only [hcomp]
    have hsm : (fun x : WO (Vc D i) (Wc D i) => Gc * flatDat R i B.de.Q ξR eQ x) = Gc • flatDat R i B.de.Q ξR eQ := rfl
    rw [hsm, map_smul, ← hvT, smul_smul, smul_smul, mul_assoc (κ * Gc)⁻¹, inv_mul_cancel₀ hne, one_smul]
  refine ⟨z, (κ * Gc)⁻¹, hz, unitOff_inv_mul' hκ hG, fun h P => ?_⟩
  have hθ : IsInfFam R.θ := hK.vec.1.2.inf
  have hth := GlobalTheory.VecTheta.isThetaFunO_thPVec hK.vec
  funext g
  rw [hvec, Pi.smul_apply, series_apply, series_apply, hB.fock_eq, hB.fock_eq, GlobalTheory.FiniteFock.pureTensorO_smul,
    ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hK.weil R.θ hθ z hz.2.1 1 (one_mem _) _ _ _ _ φ _ hth,
    map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

end GlobalTheory.BigOn.Exp.SerBase
end
end

section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumNorm

theorem vacNorm_ne_zero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ →
    Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) t0 → ∀ a d : ℕ, vacNorm D cc δ t0 a d ≠ 0 :=
  fun D cc δ t0 hc ht _ _ =>
    pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ t0 hc ht)

end GlobalTheory.VacuumNorm
end

section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NormRatio

theorem conj_smul_le {D : D7} {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : D.host.conj • I ≤ D.host.conj • J :=
  EigUnit.conj_smul_mono D h

theorem exists_conj_place {D : D7} (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
      w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ∧
      ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w'' = w ∨ w'' = w' := by
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hp := w.isPrime
  have hpr : (D.host.conj • w.asIdeal).IsPrime := inferInstance
  have hnb : D.host.conj • w.asIdeal ≠ ⊥ := by
    intro h0
    apply w.ne_bot
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  let w' : HeightOneSpectrum (𝓞 D.host.E) := ⟨D.host.conj • w.asIdeal, hpr, hnb⟩
  have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv w w' := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
    rw [hy]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  have hiff := GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) w
  refine ⟨w', rfl, (hiff w').2 (Or.inr hc), fun w'' h => ?_⟩
  rcases (hiff w'').1 h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h1 hc)

theorem eq_top_of_eq_conj {D : D7} {𝔪 A B : Ideal (𝓞 D.host.E)} (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hA : 𝔪 ≤ A)
    (hB : 𝔪 ≤ B) (h : A = D.host.conj • B) : A = ⊤ :=
  top_le_iff.1 (hcop ▸ sup_le hA (h ▸ conj_smul_le hB))

theorem prod_Ioc_shift {M : Type} [CommMonoid M] (g : ℕ → M) (a a' : ℕ) :
    ∏ n ∈ Finset.Ioc a' (a + a'), g n = ∏ i ∈ Finset.Icc 1 a, g (a' + i) := by
  have e : Finset.Ioc a' (a + a') = (Finset.Icc 1 a).image (a' + ·) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro h; exact ⟨n - a', by omega, by omega⟩
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩; omega
  rw [e, Finset.prod_image fun x _ y _ h => by simpa using h]

theorem locIdx_mul_locNorm_mul_dSfun : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf →
    ∀ a a' : ℕ, 1 ≤ a' →
    (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) =
      GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) := by
  intro D 𝔪 Sf hG a a' ha'
  classical
  obtain ⟨hne, hcop, -, hS⟩ := hG
  set s : ℂ := (a' : ℂ) / 2 with hs_def
  have hs : 0 < s.re := by
    have : (1 : ℝ) ≤ a' := by exact_mod_cast ha'
    simp only [hs_def, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  set f : HeightOneSpectrum (𝓞 D.host.F) → ℂ := fun v => GlobalTheory.LFun.dv D.host.E a (a + a') v s with hf
  have h0 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (∅ : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (∅ : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') hs).multipliable.hasProd
  have h1 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') hs).multipliable.hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))) (f := f)).1
    (Finset.hasProd Sf f)
  have hsplitf : Set.mulIndicator {v | v ∉ (∅ : Set (HeightOneSpectrum (𝓞 D.host.F)))} f =
      Set.mulIndicator {v | v ∉ (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))} f * Set.mulIndicator (Sf : Set _) f := by
    funext v
    simp only [Pi.mul_apply, Set.mulIndicator_apply, Set.mem_setOf_eq, Finset.mem_coe, Set.mem_empty_iff_false]
    by_cases hv : v ∈ Sf <;> simp [hv]
  rw [hsplitf] at h0
  have key : GlobalTheory.LFun.dSfun D.host.E (∅ : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s =
      GlobalTheory.LFun.dSfun D.host.E (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s * ∏ v ∈ Sf, f v :=
    h0.unique (h1.mul h2)
  set P := (normalizedFactors 𝔪).toFinset with hP
  have hw : ∀ I ∈ P, I.IsPrime ∧ I ≠ ⊥ ∧ 𝔪 ≤ I := by
    intro I hI
    obtain ⟨hp, hle⟩ := (Ideal.mem_normalizedFactors_iff hne).1 (Multiset.mem_toFinset.1 hI)
    exact ⟨hp, fun h => hne (le_bot_iff.1 (h ▸ hle)), hle⟩
  let W : P → HeightOneSpectrum (𝓞 D.host.E) := fun x => ⟨x.1, (hw x.1 x.2).1, (hw x.1 x.2).2.1⟩
  have hbij : ∏ v ∈ Sf, f v = ∏ x ∈ P.attach, f ((W x).under (𝓞 D.host.F)) := by
    symm
    refine Finset.prod_bij (fun x _ => (W x).under (𝓞 D.host.F)) (fun x _ => (hS _).2 ⟨W x, (hw x.1 x.2).2.2, rfl⟩)
      (fun x _ y _ hxy => ?_) (fun v hv => ?_) (fun x _ => rfl)
    · obtain ⟨w', hw', -, hall⟩ := exists_conj_place (W x)
      rcases hall (W y) hxy.symm with h | h
      · exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal h).symm
      · have h' : y.1 = D.host.conj • x.1 := (congrArg HeightOneSpectrum.asIdeal h).trans hw'
        exact absurd (eq_top_of_eq_conj hcop (hw y.1 y.2).2.2 (hw x.1 x.2).2.2 h') (hw y.1 y.2).1.ne_top
    · obtain ⟨w, hmw, rfl⟩ := (hS v).1 hv
      have hmem : w.asIdeal ∈ P := Multiset.mem_toFinset.2 ((Ideal.mem_normalizedFactors_iff hne).2 ⟨w.isPrime, hmw⟩)
      exact ⟨⟨w.asIdeal, hmem⟩, Finset.mem_attach _ _, rfl⟩
  have hloc : ∀ x : P, ((blockIdx (Ideal.absNorm x.1 : ℝ) ((normalizedFactors 𝔪).count x.1) a a' : ℝ) : ℂ) *
      ((((Ideal.absNorm x.1 : ℝ) ^ ((normalizedFactors 𝔪).count x.1 * a * a'))⁻¹ * glVol (Ideal.absNorm x.1 : ℝ) a : ℝ) : ℂ) *
      f ((W x).under (𝓞 D.host.F)) = 1 := by
    intro x
    obtain ⟨w', hw', hu, -⟩ := exists_conj_place (W x)
    have hne' : W x ≠ w' := by
      intro h
      have h' : x.1 = D.host.conj • x.1 := (congrArg HeightOneSpectrum.asIdeal h).trans hw'
      exact (hw x.1 x.2).1.ne_top (eq_top_of_eq_conj hcop (hw x.1 x.2).2.2 (hw x.1 x.2).2.2 h')
    have hsp : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) ((W x).under (𝓞 D.host.F)) :=
      ⟨W x, w', hne', rfl, congrArg HeightOneSpectrum.asIdeal hu⟩
    have hN : Ideal.absNorm ((W x).under (𝓞 D.host.F)).asIdeal = Ideal.absNorm x.1 :=
      GlobalTheory.ChainTw.TwPlaces.absNorm_under_of_ne hu.symm hne'
    have hq : (1 : ℝ) < (Ideal.absNorm x.1 : ℝ) := by
      have h1 : Ideal.absNorm x.1 ≠ 1 := fun h => (hw x.1 x.2).1.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      have h2 : Ideal.absNorm x.1 ≠ 0 := fun h => (hw x.1 x.2).2.1 (Ideal.absNorm_eq_zero_iff.1 h)
      exact_mod_cast (by omega : 1 < Ideal.absNorm x.1)
    have hd := GlobalTheory.ChainTw.dv_center_of_isSplit D.sp.cm.deg2 hsp a a'
    have hst := congrArg (fun r : ℝ => (r : ℂ)) (GlobalTheory.StdLoc.stdLoc_product hq ((normalizedFactors 𝔪).count x.1) a a')
    simp only [hf, hs_def, hd, hN, prod_Ioc_shift (fun n => (1 - (((Ideal.absNorm x.1 : ℕ) : ℂ) ^ n)⁻¹)) a a']
    push_cast at hst ⊢
    linear_combination hst
  rw [key]
  have hmain : (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * ∏ v ∈ Sf, f v = 1 := by
    rw [hbij, locIdx, locNorm, Complex.ofReal_prod, Complex.ofReal_prod, ← Finset.prod_attach P,
      ← Finset.prod_attach P, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ => hloc x
  linear_combination (GlobalTheory.LFun.dSfun D.host.E (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s) * hmain

end GlobalTheory.NormRatio
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem fockIp_self_re_pos {ι : Type} {p : MvPolynomial ι ℂ} (hp : p ≠ 0) :
    0 < (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp p p).re := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp
  rw [Complex.re_sum]
  refine Finset.sum_pos (fun k hk => ?_) (MvPolynomial.support_nonempty.2 hp)
  rw [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  refine mul_pos (Complex.normSq_pos.2 (MvPolynomial.mem_support_iff.1 hk)) ?_
  exact Nat.cast_pos.2 (Finset.prod_pos fun _ _ => Nat.factorial_pos _)

theorem fockSum_ne_zero : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ), a ≤ d → fockSum D a d n ≠ 0 := by
  intro D a d n had h0
  have hpos : 0 < (fockSum D a d n).re := by
    unfold fockSum
    rw [Complex.re_sum]
    haveI : Nonempty (GlobalTheory.NormSum.Tup D a d n) := ⟨fun _ _ => ⟨Fin.castLE had, fun _ _ h => h⟩⟩
    exact Finset.sum_pos (fun T _ => fockIp_self_re_pos (GlobalTheory.NormAdelic.minorPol_ne_zero T)) (by
      classical exact ⟨fun _ _ => ⟨Fin.castLE had, fun _ _ h => h⟩, by simp⟩)
  rw [h0] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.NormRatio
end
end
