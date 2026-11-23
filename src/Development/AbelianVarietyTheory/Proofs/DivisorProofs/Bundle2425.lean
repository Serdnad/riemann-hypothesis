module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle109
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle038
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitLevel

theorem level_halfSplit : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D), ∃ π π' : 𝓞 D.host.E, HalfSplit T.Q.l (D.host.g 0) (D.host.g 1) π π' := by
  intro D T h EX
  have hp : ∀ i, piOf T EX i * T.Q.H.bar (piOf T EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [bar_core]; exact piOf_mul_barE T EX i
  have hM : T.Q.l.Mb = Ideal.span {piOf T EX 0 * piOf T EX 1} := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_piOf T h, span_piOf T h, Mb_eq T h]
  exact ⟨piOf T EX 0, piOf T EX 1, D.host.g_prime 0, D.host.g_prime 1, D.host.g_ne,
    by rw [level_M T h, mul_comm], hp 0, hp 1, hM,
    GlobalTheory.LevelSplit.splitsIn_level_prime D 0, GlobalTheory.LevelSplit.splitsIn_level_prime D 1⟩

end GlobalTheory.SplitLevel
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaLow
open GlobalTheory.ThetaBound GlobalTheory.PlaceInt

theorem finite_vLa_ne_zero {K : Type} [Field K] [NumberField K] (x : K) :
    {w : HeightOneSpectrum (𝓞 K) | vLa w x ≠ 0}.Finite := by
  by_cases hx : x = 0
  · subst hx
    simpa [vLa] using (Set.finite_empty : (∅ : Set (HeightOneSpectrum (𝓞 K))).Finite)
  · refine (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 x hx)).subset fun w hw h1 => hw ?_
    simp only [Units.val_mk0] at h1
    simp [vLa, h1]

theorem vLa_natCast_eq_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {g p : ℕ}
    (hg : ((g : ℕ) : 𝓞 K) ∈ w.asIdeal) (hc : Nat.Coprime g p) : vLa w ((p : ℕ) : K) = 0 := by
  have hp : ((p : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    intro hp
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 K))
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hg) (Ideal.mul_mem_left _ _ hp)
  have h1 : w.valuation K ((p : ℕ) : K) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) p, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hp
  simp [vLa, h1]

theorem thetaRule_bounded_below : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (g g' : ℕ) (π π' : 𝓞 D.host.E), HalfSplit l g g' π π' → Nat.Coprime (g * g') (D.host.QS * D.host.q * D.host.d) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∃ m : HeightOneSpectrum (𝓞 c.F) → ℝ, (Function.support m).Finite ∧ (∀ f ∈ thGen Xo c nab a n, ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) ∧ ∀ w : HeightOneSpectrum (𝓞 c.F), (((g : ℕ) : 𝓞 c.F) ∈ w.asIdeal ∨ ((g' : ℕ) : 𝓞 c.F) ∈ w.asIdeal) → m w = -((vLa w (nrm Dw c a (star π * star π')) : ℤ) : ℝ) := by
  intro D H Dw l Xo c
  letI := H.starRing
  intro nab hnab g g' π π' hs hcop a n
  have hstar : ∀ x : 𝓞 D.host.E, star x = H.bar x := hnab.1
  obtain ⟨hg, hg', hne, hM, hπ, hπ', hMb, -, -⟩ := hs
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hπ
    exact hg.ne_zero (by exact_mod_cast hπ.symm)
  have hπ0' : π' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hπ'
    exact hg'.ne_zero (by exact_mod_cast hπ'.symm)
  have hb0 : star π * star π' ≠ 0 := by
    rw [hstar, hstar]
    refine mul_ne_zero (fun h => hπ0 ?_) (fun h => hπ0' ?_)
    · rw [← TorsFac.bar_bar (H := H) π, h, map_zero]
    · rw [← TorsFac.bar_bar (H := H) π', h, map_zero]
  let ρ : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ p ∈ D.host.condN.primeFactors, ((vLa w ((p : ℕ) : c.F) : ℤ) : ℝ) *
      D.host.vdH p * (Formalism.L2.Pj.DF Dw a : ℝ) / 2
  refine ⟨fun w => -(ρ w + ((vLa w (nrm Dw c a (star π * star π')) : ℤ) : ℝ)), ?_, ?_, ?_⟩
  ·
    have hfin : ((⋃ p ∈ D.host.condN.primeFactors,
        {w : HeightOneSpectrum (𝓞 c.F) | vLa w ((p : ℕ) : c.F) ≠ 0}) ∪
        {w | vLa w (nrm Dw c a (star π * star π')) ≠ 0}).Finite :=
      (Set.Finite.biUnion (Finset.finite_toSet _) fun p _ => finite_vLa_ne_zero _).union (finite_vLa_ne_zero _)
    refine hfin.subset fun w hw => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_not] at hn
    apply hw
    have h0 : ρ w = 0 := Finset.sum_eq_zero fun p hp => by rw [hn.1 p hp]; simp
    simp [h0, hn.2]
  · intro f hf w v hv
    obtain ⟨y, rfl⟩ := hv
    obtain ⟨T, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
    have hv : vAtV y f = nval T.V e (evI yI f) := by
      show y.1.1 f = _
      rw [hq]
      rfl
    rw [hv]
    refine bound_of_chBound Xo c (star π * star π') hb0 ?_ nab hnab w a n (ρ w) ?_ T io e ho yI hy f hf
    · intro ℓ hp hd
      rw [hM] at hd ⊢
      rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hg').1 h1
        refine ⟨fun h2 => hne ?_, star π', star π, _root_.mul_comm _ _, ?_, ?_⟩
        · rw [pow_two] at h2
          exact ((Nat.prime_dvd_prime_iff_eq hg' hg).1 (Nat.dvd_of_mul_dvd_mul_left hg'.pos h2)).symm
        · rw [hstar, TorsFac.bar_bar, _root_.mul_comm]; exact hπ'
        · rw [hMb, hstar, TorsFac.bar_bar, Ideal.span_singleton_le_span_singleton]
          exact Dvd.intro_left _ rfl
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hg).1 h1
        refine ⟨fun h2 => hne ?_, star π, star π', rfl, ?_, ?_⟩
        · rw [pow_two] at h2
          exact (Nat.prime_dvd_prime_iff_eq hg hg').1 (Nat.dvd_of_mul_dvd_mul_right hg.pos h2)
        · rw [hstar, TorsFac.bar_bar, _root_.mul_comm]; exact hπ
        · rw [hMb, hstar, TorsFac.bar_bar, Ideal.span_singleton_le_span_singleton]
          exact Dvd.intro _ rfl
    · intro T' io' y' C' e' ho'
      have hc := HostChart.chBound_host D H Dw l Xo c hstar T' io' y' C' e' ho'.1 a n
        (Formalism.L2.Pj.DF Dw a) le_rfl
      convert hc using 1
      refine Finset.sum_congr rfl fun p _ => ?_
      have h1 := ho'.2 ((p : ℕ) : c.F)
      rw [map_natCast] at h1
      have he : (e' : ℝ) ≠ 0 := by exact_mod_cast ho'.1.ne'
      rw [h1]
      push_cast
      rw [mul_div_cancel_left₀ _ he]
  · intro w hw
    have h0 : ρ w = 0 := Finset.sum_eq_zero fun p hp => by
      have hcp : Nat.Coprime (g * g') p := Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_primeFactors hp) hcop
      rcases hw with hw | hw
      · rw [vLa_natCast_eq_zero w hw (Nat.Coprime.coprime_dvd_left (dvd_mul_right g g') hcp)]; simp
      · rw [vLa_natCast_eq_zero w hw (Nat.Coprime.coprime_dvd_left (dvd_mul_left g' g) hcp)]; simp
    show -(ρ w + _) = _
    rw [h0, zero_add]
end GlobalTheory.ThetaLow
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

theorem _root_.GlobalTheory.T.freeLowerBlockVector_multiple_kernelTranslate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∃ φ₁, VecOf R i Q (omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0)) φ₁ ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ₁ = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  first | exact @GlobalTheory.FreeBlockTwist.vecFree_base_translate | exact GlobalTheory.FreeBlockTwist.vecFree_base_translate | (intros; apply GlobalTheory.FreeBlockTwist.vecFree_base_translate <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem growthOn_le_compDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G G' : WTZ E), Even G.2 → Even G'.2 → growthOn U Z G ≠ ⊤ → BirOn U Z G → ValMult U Z G G' → growthOn U Z G' ≤ (compDeg U Z G : ℝ≥0∞) := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro E _ _ _ H Dw l Xo c r U hU Z G G' hG hG' hfin hB hM
    rcases eq_or_ne (growthOn U Z G') 0 with h0 | h0
    · rw [h0]; exact bot_le
    obtain ⟨a, θ, ha, hθ, hmul⟩ := hM
    letI : FiniteDimensional c.F (cuspOn U Z G) :=
      GlobalTheory.DegTop.finiteDimensional_of_growthOn (U := U) (Z := Z) hG hfin
    have hR := GlobalTheory.T.cuspFormsRatioOnComponent_of_birational E H Dw l Xo c r U Z G hB
    have hFG := GlobalTheory.T.flagSpaceComponent_functionField_fg E H Dw l Xo c r U hU Z
    set ev := genPoint Z (cuspOn U Z G) with hev
    let S : ℕ → Submodule c.F (Om Z) := fun k =>
      if k = 0 then ⊥ else (cuspOn U Z ((a * k) • G')).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (θ ^ k))
    have h1 := GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.2.1 c.F _ _ ev (dimFlag Dw) a ha S (by
      intro k t ht
      by_cases hk : k = 0
      · simp only [S, hk, if_true, Submodule.mem_bot] at ht
        subst ht
        refine ⟨?_, ⟨0, 1, by simp [Submodule.one_eq_span], one_ne_zero, by simp⟩⟩
        rw [IsIntDeg, map_zero, mul_zero]
        exact isIntegral_zero
      · simp only [S, hk, if_false] at ht
        obtain ⟨f, hf, rfl⟩ := ht
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
        obtain ⟨hc, hv⟩ := hmul k hk1 f hf
        exact ⟨GlobalTheory.T.isIntegralInConeDegree_of_valuativeBound c.F _ _ ev inferInstance inferInstance hFG _ _ hv, hR _ _ hc⟩)
    have hθk : ∀ k : ℕ, genVal Z (θ ^ k) ≠ 0 := fun k => by rw [map_pow]; exact pow_ne_zero _ hθ
    have h2 : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G')))) ≤
        growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (S k))) :=
      GlobalTheory.DegTop.growth_mono _ fun k hk => by
        have hk0 : k ≠ 0 := by omega
        show _ ≤ Cardinal.toENat (Module.rank c.F (S k))
        have hS : S k = (cuspOn U Z ((a * k) • G')).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (θ ^ k)) := if_neg hk0
        rw [hS, GlobalTheory.DegTop.rank_map_mul (U := U) (G := (a * k) • G') (hθk k)]
    have hmulG : ∀ G₀ : WTZ E, growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G₀)))) =
        growthOn U Z (a • G₀) := fun G₀ => by
      rw [growthOn]
      congr 1
      funext k
      rw [mul_nsmul]
    have h3 : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G')))) =
        (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G' := by
      rw [hmulG, GlobalTheory.T.cuspFormGrowthOnComponent_nsmul E H Dw l Xo c r U hU Z G' hG' a ha]
    have h4 : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≤ (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
      rw [← GlobalTheory.T.cuspFormGrowthOnComponent_nsmul E H Dw l Xo c r U hU Z G hG a ha, ← hmulG]
      exact GlobalTheory.DegTop.growth_mono _ fun k hk => GlobalTheory.DegTop.hilb_le hG (Nat.mul_pos ha hk)
    have haD0 : (a : ℝ≥0∞) ^ dimFlag Dw ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
    have haDT : (a : ℝ≥0∞) ^ dimFlag Dw ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
    have hlow : (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G' ≤ growth (dimFlag Dw) (fun k => hilb ev (a * k)) :=
      h3 ▸ h2.trans h1
    have hne0 : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≠ 0 :=
      ne_bot_of_le_ne_bot (mul_ne_zero haD0 h0) hlow
    have hneT : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top haDT hfin) h4
    obtain ⟨δ, hδ⟩ := GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.1 c.F _ _ ev (dimFlag Dw) a ha hne0 hneT
    rw [GlobalTheory.T.cone_degree_growth_chowForm_integrality.1 c.F _ _ ev (dimFlag Dw) a ha δ hδ] at hlow
    rw [compDeg, ← hev, hδ.imageDeg_eq]
    first | exact (ENNReal.mul_le_mul_iff_right haD0 haDT).1 hlow | exact (ENNReal.mul_le_mul_iff_left haD0 haDT).1 hlow

end GlobalTheory.DegVal
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.rational_isotropicStabiliser_splitLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν → ν DN = 1 → ∃ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), SemiLat (unipRad σ J X) (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) ν π DN DM := by
  first | exact @GlobalTheory.ResidueEisenstein.semiLat_frameGrp | exact GlobalTheory.ResidueEisenstein.semiLat_frameGrp | (intros; apply GlobalTheory.ResidueEisenstein.semiLat_frameGrp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

theorem _root_.GlobalTheory.T.primePowerLatticeInclusion_of_localModels : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι), NumOk P W → (Formalism.EigenvalueLevelCeiling.plc w).Prime → W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam), Covers B ℓ Z w X → (∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) → LIncl B ℓ Z w (W.coarseWeightBound P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  first | exact @GlobalTheory.ExpTie.lIncl_of_models | exact GlobalTheory.ExpTie.lIncl_of_models | (intros; apply GlobalTheory.ExpTie.lIncl_of_models <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

theorem _root_.GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ), LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  first | exact @GlobalTheory.ExpTie.jexpU_le_of_lIncl | exact GlobalTheory.ExpTie.jexpU_le_of_lIncl | (intros; apply GlobalTheory.ExpTie.jexpU_le_of_lIncl <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.twoLevelCuspForms_directSum_components : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C] [DecidableEq C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → ∃ A : C → Submodule ℂ (M.cusp ka), DirectSum.IsInternal A ∧ ∀ (h : U) (c : C), ∀ v ∈ A c, ρ h v ∈ A (h • c) := by
  first | exact @GlobalTheory.ShareOn.cusp_decomp | exact GlobalTheory.ShareOn.cusp_decomp | (intros; apply GlobalTheory.ShareOn.cusp_decomp <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.Over.ord_fnPull_of_bijective : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g := by
  intro k _ X Y _ _ p s _ hs E' E h g
  let φ : E.ring →+* E'.ring :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict E'.ring fun a => (h _).1 a.2
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b e => Subtype.ext (hs.1 (congrArg Subtype.val e)), fun b => ?_⟩
    obtain ⟨a, ha⟩ := hs.2 (b : Y.functionField)
    exact ⟨⟨a, (h a).2 (ha ▸ b.2)⟩, Subtype.ext ha⟩
  let e : E.ring ≃+* E'.ring := RingEquiv.ofBijective φ hφ
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, u, eg⟩ := exists_eq_unit_mul_zpow ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := X.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := Y.functionField) (ht.map e)
    (Units.map e.toMonoidHom u) m
  rw [← eg, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have eg' : ((fnPull s g : Y.functionFieldˣ) : Y.functionField) =
      algebraMap E'.ring Y.functionField (Units.map e.toMonoidHom u : E'.ringˣ) *
        algebraMap E'.ring Y.functionField (e t) ^ m := by
    change functionFieldMap s (g : X.functionField) = _
    rw [eg, map_mul, map_zpow₀]
    rfl
  rw [← eg', ordTop_vw_of_ne_zero _ (fnPull s g).ne_zero, WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.Discrepancy
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem IsSncChart.neg_one_lt_formOrd_sub_sum : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (E : DivOver q), E.Through y → ∀ a : Fin n → ℚ, ((∀ j ∈ J, a j < 1) → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) ∧ ((∀ j ∈ J, a j ≤ 1) → -1 ≤ ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) := by
  intro k _ _ Y _ _ q n _ B y U hy z J w u hc E hE a
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen k _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  have h0 : formOf U (gen_mem hy) (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hc.frame).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).2 (by rw [hc.val j hj]; exact hE _ (regAt_fnOf hy _ (z j)))
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy hE z h0 (J := {j // j ∈ J})
    Subtype.val Subtype.val_injective (fun j => u j.1) fun j => hc.val j.1 j.2
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hA
  have hF := DivOver.formOrd_formOf_nonneg hn hy hE (dOn q z) h0
  set F := E.formOrd (formOf U (gen_mem hy) (dOn q z))
  have hAq : ∑ j ∈ J, (E.ord (u j) : ℚ) - 1 ≤ F := by exact_mod_cast hA
  have hFq : (0 : ℚ) ≤ F := by exact_mod_cast hF
  have hnq : ∀ j ∈ J, (0 : ℚ) ≤ E.ord (u j) := fun j hj => by exact_mod_cast hnn j hj
  have hle : (∀ j ∈ J, a j ≤ 1) → ∀ j ∈ J, a j * (E.ord (u j) : ℚ) ≤ E.ord (u j) :=
    fun ha j hj => by nlinarith [ha j hj, hnq j hj]
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · change -1 < (F : ℚ) - ∑ j ∈ J, a j * E.ord (u j)
    by_cases hz : ∀ j ∈ J, (E.ord (u j) : ℚ) = 0
    · rw [Finset.sum_eq_zero fun j hj => by rw [hz j hj, mul_zero]]
      linarith
    · push Not at hz
      obtain ⟨j, hj, hj0⟩ := hz
      have hpos : (0 : ℚ) < E.ord (u j) := lt_of_le_of_ne (hnq j hj) hj0.symm
      have := Finset.sum_lt_sum (hle fun j hj => (ha j hj).le)
        ⟨j, hj, by nlinarith [ha j hj]⟩
      linarith
  · change -1 ≤ (F : ℚ) - ∑ j ∈ J, a j * E.ord (u j)
    have := Finset.sum_le_sum (hle ha)
    linarith

end GlobalTheory.Discrepancy
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over_of_bijective : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E := by
  intro k _ X Y _ _ p s _ hb E'
  have e := GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p s
  have hc : ∀ a, Cartier.constFn p a ∈ E'.ring.comap (functionFieldMap s) := fun a => by
    show functionFieldMap s (Cartier.constFn p a) ∈ E'.ring
    rw [← RingHom.comp_apply, e]; exact E'.const_mem a
  let ψ : E'.ring.comap (functionFieldMap s) →+* E'.ring :=
    (functionFieldMap s).restrict _ E'.ring fun _ hx => hx
  have hψb : Function.Bijective ψ := by
    refine ⟨fun x y h => Subtype.ext (hb.1 (congrArg Subtype.val h)), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hb.2 (y : Y.functionField)
    exact ⟨⟨x, show functionFieldMap s x ∈ E'.ring from hx ▸ y.2⟩, Subtype.ext hx⟩
  let eq : E'.ring.comap (functionFieldMap s) ≃+* E'.ring := RingEquiv.ofBijective ψ hψb
  have hdvr : IsDiscreteValuationRing (E'.ring.comap (functionFieldMap s)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eq.symm
  have hcomp : eq.symm.toRingHom.comp
      ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem) =
      (Cartier.constFn p).codRestrict _ hc := by
    refine RingHom.ext fun a => eq.injective ?_
    rw [RingHom.comp_apply]
    erw [RingEquiv.apply_symm_apply]
    exact Subtype.ext (RingHom.congr_fun e a).symm
  have hess : ((Cartier.constFn p).codRestrict _ hc).EssFiniteType := by
    rw [← hcomp]
    have h1 := E'.essFiniteType
    letI := ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem).toAlgebra
    letI := (eq.symm.toRingHom.comp
      ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem)).toAlgebra
    haveI : Algebra.EssFiniteType k E'.ring := h1
    let f : E'.ring →ₐ[k] E'.ring.comap (functionFieldMap s) :=
      { eq.symm.toRingHom with commutes' := fun _ => rfl }
    exact Algebra.EssFiniteType.of_surjective f eq.symm.surjective
  exact ⟨⟨E'.ring.comap (functionFieldMap s), hc, hdvr, hess⟩, fun _ => Iff.rfl⟩

end GlobalTheory.Discrepancy
end
end
