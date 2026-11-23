module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle033
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle032
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle037
public import Formalism.PairingDivisors.StatementA
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle017
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Mathlib.Topology.UniformSpace.Uniformizable
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF


theorem _root_.GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, σ ξ₀ = -ξ₀ → ∀ x y : WOF F E nS nT,
      symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  first | exact @GlobalTheory.SymplSkew.symplOF_swap | exact GlobalTheory.SymplSkew.symplOF_swap | (intros; apply GlobalTheory.SymplSkew.symplOF_swap <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.exists_haar_fundamentalDomain_rationalMatrices_tower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    ∃ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν := by
  first | exact @GlobalTheory.TowerFD.exists_fd_any | exact GlobalTheory.TowerFD.exists_fd_any | (intros; apply GlobalTheory.TowerFD.exists_fd_any <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF


theorem _root_.GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    IsTopologicalAddGroup (WOF F E nS nT) ∧ LocallyCompactSpace (WOF F E nS nT) ∧
    SecondCountableTopology (WOF F E nS nT) ∧ T2Space (WOF F E nS nT) ∧ DiscreteTopology (ratLF F E nS nT) ∧
    ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  first | exact @GlobalTheory.AdelicMatrixLatticeF.lattice | exact GlobalTheory.AdelicMatrixLatticeF.lattice | (intros; apply GlobalTheory.AdelicMatrixLatticeF.lattice <;> assumption)
end

section

open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.PeriodicPositiveIntegral

theorem integral_ne_zero_of_cocompact {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (Γ : AddSubgroup G) [Countable Γ] {K : Set G}
    (hK : IsCompact K) (hKc : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K)
    (I : G → ℂ) (hI : Continuous I) (hper : ∀ γ ∈ Γ, ∀ u, I (γ + u) = I u)
    (hnn : ∀ u, 0 ≤ (I u).re) (h0 : 0 < (I 0).re) (ν : Measure G) [ν.IsAddHaarMeasure] (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 ν) (hfin : ν 𝓕 < ⊤) : ∫ u in 𝓕, I u ∂ν ≠ 0 := by
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hI.continuousOn
  have hint : Integrable I (ν.restrict 𝓕) := by
    refine Integrable.of_bound hI.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hper γ hγ w]
    exact hC _ h
  have hcre : Continuous fun u => (I u).re := Complex.continuous_re.comp hI
  have hO : IsOpen (Function.support fun u => (I u).re) := hcre.isOpen_support
  have hpos : ν (Function.support fun u => (I u).re) ≠ 0 := hO.measure_ne_zero ν ⟨0, h0.ne'⟩
  intro hz
  have hre : ∫ u in 𝓕, (I u).re ∂ν = 0 := by
    have := integral_re (𝕜 := ℂ) hint
    rw [hz] at this
    simpa using this
  have hlt : 0 < ∫ u in 𝓕, (I u).re ∂ν := by
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint.re,
      Measure.restrict_apply hO.measurableSet, pos_iff_ne_zero]
    intro hm
    refine hpos (h𝓕.measure_zero_of_invariant _ (fun g => ?_) hm)
    ext u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    show (I (((-g : Γ) : G) + u)).re ≠ 0 ↔ (I u).re ≠ 0
    rw [hper _ (-g).2]
  exact hlt.ne' hre

theorem integral_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (I : WOF F E nS nT → ℂ), Continuous I → (∀ γ ∈ ratLF F E nS nT, ∀ u, I (γ + u) = I u) →
    (∀ u, 0 ≤ (I u).re) → 0 < (I 0).re →
    ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν → ∫ u in 𝓕, I u ∂ν ≠ 0 := by
  intro F E _ _ _ _ _ nS nT I hI hper hnn h0 ν 𝓕 hν h𝓕
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  exact integral_ne_zero_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc I hI hper hnn h0 ν 𝓕 h𝓕
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕)

end GlobalTheory.PeriodicPositiveIntegral
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory



theorem lastPos_wtA_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j,
    w.LastPos → Formalism.L2.Pj.LastPos (Q.Dw j) (wtA w) := by
  intro D Q h j hj w hw τ hτ hm
  obtain ⟨t, rfl⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q h.1 τ hτ
  have hmult : (Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
    have hτ' : (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    rw [if_pos hτ']
    exact (h.2.2.2 j hj).1
  rw [hmult] at hm ⊢
  have h1 : 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ :=
    hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  have h2 : ext0 (w.aP t) ((D.R.sigW j).1 - 1) = w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := by
    unfold ext0
    rw [dite_eq_left (by omega)]
  unfold wtA
  classical
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  simp only [if_true]
  omega

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.FramePower

theorem exists_nabValN_eq_of_map {R K O : Type} [CommRing R] [Algebra ℚ R] [CommRing K] [Algebra ℚ K] [Algebra R K]
    [CommRing O] [StarRing O] {d : ℕ} (B : FB R d O) (h : PS R 2 d) (hc : MvPowerSeries.constantCoeff h = 0)
    (w0 : O) (k k' : ℕ) {n : ℕ} (g : PS R n d) :
    ∃ g' : PS R n d, ∀ {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → K) (P : MvPolynomial Ix K),
      nabValN B K (FB.toK K h) w0 k (FB.toK K g) cp u P = nabValN B K (FB.toK K h) w0 k' (FB.toK K g') cp u P := by
  have gC : GP (comp1 (B.actK R w0) (pt R (n := 1) d 0)) :=
    gp_comp1 _ _ (GlobalTheory.GaugeBaseChange.gp_actK B w0) (gp_pt 0)
  have cL : MvPowerSeries.constantCoeff (B.hL R h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map (algebraMap R K) (B.hL R h w0) = B.hL K (FB.toK K h) w0 := by
    unfold FB.hL
    rw [GlobalTheory.GaugeBaseChange.map_ev_two _ _ _ (gp_pt _) gC, GlobalTheory.QuadDeriv.baseChange_comp1 _ _ _ (gp_pt _),
      GlobalTheory.QuadDeriv.baseChange_pt]
    have := GlobalTheory.GaugeBaseChange.baseChange_actK B (Algebra.ofId R K) w0
    exact congrArg (fun t => ev (n := 1) ![pt K d 0, comp1 t (pt K d 0)] (FB.toK K h)) this
  set S : PS R n d := ∑ b : Fin n, ev (n := n) ![pt R d b] (B.hL R h w0) with hS
  have gp : ∀ b : Fin n, ∀ j : Fin 1, GP ((![pt R d b] : Fin 1 → Pt R n d) j) := by
    intro b j; fin_cases j; exact gp_pt b
  have cS : MvPowerSeries.constantCoeff S = 0 := by

    rw [hS, map_sum]
    exact Finset.sum_eq_zero fun b _ => gt_const_ev _ (gp b) _ cL
  have eS : MvPowerSeries.map (algebraMap R K) S =
      ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K (FB.toK K h) w0) := by

    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.QuadDeriv.map_ev _ _ (gp b), eL]
    congr 1
    funext j; fin_cases j
    exact GlobalTheory.QuadDeriv.baseChange_pt _ _
  have cm : ∀ m : ℕ, MvPowerSeries.constantCoeff ((m : R) • S) = 0 := fun m => by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cS, mul_zero]
  have em : ∀ m : ℕ, FB.expS K ((m : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K (FB.toK K h) w0)) =
      FB.toK K (FB.expS R ((m : R) • S)) := fun m => by
    rw [FB.toK.eq_1 K (FB.expS R _), GlobalTheory.GaugeBaseChange.map_expS _ _ (cm m), MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul,
      map_mul, MvPowerSeries.map_C, map_natCast (algebraMap R K), eS]
  refine ⟨g * FB.expS R ((k : R) • S - (k' : R) • S), fun cp u P => ?_⟩
  unfold nabValN
  rw [em, em, FB.toK, FB.toK, FB.toK, FB.toK, ← map_mul, ← map_mul, _root_.mul_assoc,
    ← gt_expS_add _ _ (by rw [map_sub, cm, cm, sub_zero]) (cm k'), sub_add_cancel]

end GlobalTheory.FramePower


open GlobalTheory.FramePower in
theorem GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n k k' : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∃ f' : PS T.Fr n (chD C.ch), IsIntPS T f' ∧ nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) = nabValN C.ch.B T.Fr C.ch.h H.w0 k' f' (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  intro T io y C hchar
  letI := io.toAlgebra
  intro a n k k' P hP f hf
  obtain ⟨B, hBT, hB⟩ := GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C
  obtain ⟨hg, -, heig, -⟩ := hB B hBT
  obtain ⟨hF, hA, -⟩ := C.gen.1
  obtain ⟨e1, e2, -⟩ := hBT
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [GlobalTheory.ChartBiext.toK_self, hF, e1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [GlobalTheory.ChartBiext.toK_self, hA, e2]
  letI : Algebra ℚ T.V := (IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) (g := Int.castRingHom T.V) (by
    rintro ⟨z, hz⟩
    have h0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
    rw [← residue_ne_zero_iff_isUnit]
    simpa using h0)).toAlgebra
  obtain ⟨h0, hh0⟩ := GlobalTheory.canonGauge_exists T.V (chD C.ch) (𝓞 E) T.V B
  have hh1 : B.IsCanonGauge T.Fr (FB.toK T.Fr h0) :=
    GlobalTheory.GaugeBaseChange.isCanonGauge_map B (Algebra.ofId T.V T.Fr) hh0
  choose g hg' using hf
  have ef : f = FB.toK T.Fr (g : PS T.V n (chD C.ch)) := by
    ext m
    exact (hg' m).symm.trans (MvPowerSeries.coeff_map (algebraMap T.V T.Fr) m (g : PS T.V n (chD C.ch))).symm
  obtain ⟨g', hgg⟩ := exists_nabValN_eq_of_map (K := T.Fr) B h0 (GlobalTheory.GaugeBaseChange.const_of_axis hh0.ax0)
    H.w0 k k' (g : PS T.V n (chD C.ch))
  have key := GlobalTheory.nabValN_harmonic_gauge_independent T.V (chD C.ch) (𝓞 E) T.Fr B (gaugeOf C) (FB.toK T.Fr h0) hg hh1
    (E →+* ℂ) Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ => io.comp (embK c τ)) (fun τ => by ext x; simp)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H)
    (fun τ a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hstar]
      congr 1
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])
    (fun σ τ hne => by
      have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))
      obtain ⟨a, ha⟩ := hex
      refine ⟨a, ?_⟩
      have h0 : embK c σ a - embK c τ a ≠ 0 := by
        rw [sub_ne_zero]
        intro h1
        apply ha
        rw [← embK_coe c, ← embK_coe c, h1]
      rw [RingHom.comp_apply, RingHom.comp_apply, ← map_sub]
      exact (Ne.isUnit h0).map _)
    C.ch.uvec heig n (MvPolynomial.map io P) (ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map io hP.1.1) H.w0
  refine ⟨FB.toK T.Fr g', fun m => ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩, ?_⟩
  rw [← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA, ← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA]
  refine (key k f).trans (Eq.trans ?_ (key k' _).symm)
  rw [ef]
  exact hgg _ _ _
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.ObjModel

namespace GlobalTheory.ToricSumValue

theorem cpow_pos_eq {r : ℝ} (hr : 0 < r) (z : ℂ) : (r : ℂ) ^ z = Complex.exp ((Real.log r : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log hr.le]

theorem term_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E} (h : HasInf χ φ fun i => (κ i : ℤ) + s) (σ : ℂ) (k : Eˣ) :
    term φ (2 * s) κ σ k = (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) *
      ((modF (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℝ) : ℂ) ^ ((s : ℂ) + σ) := by
  have hpos : ∀ i, 0 < ‖φ i (k : E)‖ := fun i => by simp
  have hN : 0 < ∏ i, ‖φ i (k : E)‖ ^ 2 := Finset.prod_pos fun i _ => pow_pos (hpos i) 2
  rw [modF_princ k, ← prod_normSq hφ k,
    Complex.cpow_add _ _ (by exact_mod_cast (inv_pos.2 hN).ne'), Complex.cpow_natCast]
  have h1 : term φ (2 * s) κ σ k = term φ (2 * s) κ 0 k * ∏ i, ((‖φ i (k : E)‖ : ℝ) : ℂ) ^ (-2 * σ) := by
    unfold term
    rw [← Finset.prod_mul_distrib]
    simp
  have h2 : ∏ i, ((‖φ i (k : E)‖ : ℝ) : ℂ) ^ (-2 * σ) = (((∏ i, ‖φ i (k : E)‖ ^ 2)⁻¹ : ℝ) : ℂ) ^ σ := by
    rw [cpow_pos_eq (inv_pos.2 hN), Real.log_inv, Real.log_prod (fun i _ => (pow_pos (hpos i) 2).ne')]
    simp only [cpow_pos_eq (hpos _)]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_pow]
    push_cast
    ring
  have h3 := term_mul_inf h k
  have h4 : ∏ i, (φ i k * starRingEnd ℂ (φ i k)) ^ s = (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ^ s := by
    rw [Finset.prod_pow]
    congr 1
    push_cast
    exact Finset.prod_congr rfl fun i _ => Complex.mul_conj' _
  have h5 : (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) * (χ.inf k : ℂ) = 1 := by
    rw [← Units.val_mul, finPart_mul_inf, Units.val_one]
  rw [h4] at h3
  have hN' : (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [h1, h2, ← mul_assoc]
  congr 1
  rw [Complex.ofReal_inv, inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hN')]
  linear_combination (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) * h3 -
    (term φ (2 * s) κ 0 k * (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ^ s) * h5

def twistFin {E : Type} [Field E] [NumberField E] (χ : HChar E) (S : ℂ) : (Af E)ˣ →* ℂ where
  toFun y := (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S
  map_one' := by
    have : modF (1 : (Af E)ˣ) = 1 := modF_unit (c := ⊤) (one_mem _)
    simp [this]
  map_mul' y y' := by
    rw [map_mul, modF_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (modF_pos y).le (modF_pos y').le,
      Units.val_mul]
    ring

theorem twistFin_apply {E : Type} [Field E] [NumberField E] (χ : HChar E) (S : ℂ) (y : (Af E)ˣ) :
    twistFin χ S y = (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S := rfl

theorem hasSum_classes {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E} (h : HasInf χ φ fun i => (κ i : ℤ) + s)
    {𝔣 c : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣) (hd : 𝔣 ∣ c) (hc : c ≠ ⊥) (hχ : ∀ y ∈ hatOUnits c, finPart χ y = 1)
    {σ T : ℂ} {S : PicO c → ℂ}
    (hS : ∀ q, HasSum (fun x : modUnits (lattice c q.out) => term φ (2 * s) κ σ x.1.out) (S q))
    (hT : HasSum (fun z : {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ,
      (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c} => twistFin χ (s + σ) z.1.out) T) :
    HasSum (fun q : PicO c => (twistFin χ (s + σ) q.out)⁻¹ * S q) T := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_latticePoints_integralIdeles_equiv E 𝔣 c h𝔣 hd hc
  rw [← e.hasSum_iff] at hT
  refine HasSum.sigma hT fun q => ?_
  refine ((hS q).mul_left (twistFin χ (s + σ) q.out)⁻¹).congr_fun fun x => ?_
  let k : Eˣ := Units.mk0 x.1.out (out_mem_lattice x).2
  have h1 := he ⟨q, x⟩ (Units.map (algebraMap E (Af E)).toMonoidHom k * (q.out)⁻¹) rfl
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (hatOUnits c)
    (Units.map (algebraMap E (Af E)).toMonoidHom k * (q.out)⁻¹)
  have h2 : twistFin χ (s + σ) u = 1 := by
    rw [twistFin_apply, hχ u u.2, modF_unit u.2]; simp
  have h3 : term φ (2 * s) κ σ x.1.out = twistFin χ (s + σ) (Units.map (algebraMap E (Af E)).toMonoidHom k) :=
    term_eq hφ h σ k
  show twistFin χ (s + σ) (e ⟨q, x⟩).1.out = _
  rw [h1, hu, map_mul, map_mul, h2, h3, mul_one, mul_comm, map_inv]

theorem toricSum_eq : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (Λ : ℂ → ℂ), UnramFin E → 1 ≤ s → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → IsHeckeL χ Λ → open Classical in IsToricSum φ s κ (condQ 𝔣 Q) χ (Λ s * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), Formalism.PairingDivisionLocalBalance.eq (Ideal.absNorm q.asIdeal) s (val χ (Pq q) : ℂ)) := by
  intro hH E _ _ _ I _ φ hφ s κ 𝔣 Q χ Pq Λ hU hs h𝔣 hQ hχ hP hΛ
  classical
  have hc : condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hd : 𝔣 ∣ condQ 𝔣 Q := dvd_mul_right _ _
  have htriv := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hU h𝔣 hQ hχ
  have hfin := GlobalTheory.T.finite_ringClassGroup_of_conductor_ne_zero E _ hc
  choose S hS using fun q : PicO (condQ 𝔣 Q) =>
    GlobalTheory.T.exists_entire_latticeSum_of_heckeL_continuation hH E I φ hφ s κ 𝔣 _ χ hU hs h𝔣 hd hc hχ.1 hχ.2.2.1 htriv q.out
  refine ⟨hfin, S, hS, ?_⟩
  have := Fintype.ofFinite (PicO (condQ 𝔣 Q))
  have key : (fun σ : ℂ => ∑ q : PicO (condQ 𝔣 Q), (twistFin χ (s + σ) q.out)⁻¹ * S q σ) = fun σ : ℂ =>
      Λ (s + σ) * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)),
        ((1 - (val χ (Pq q) : ℂ) * (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) *
          (1 - (val χ (Pq q) : ℂ)⁻¹ * (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) +
          ((Ideal.absNorm q.asIdeal : ℂ) - 1) * ((Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) ^ 2) := by
    refine entire_eq_of_halfPlane ?_ ?_ (1 - s) fun σ hσ => ?_
    · refine Differentiable.fun_sum fun q _ => Differentiable.mul ?_ (hS q).1
      simp only [twistFin_apply, mul_inv, ← Complex.cpow_neg]
      refine Differentiable.const_mul ?_ _
      exact Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast (modF_pos _).ne'))
    · refine (hΛ.1.comp (by fun_prop)).mul (Differentiable.fun_finsetProd fun q _ => ?_)
      have h0 : Differentiable ℂ fun σ : ℂ => (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ)) := by
        refine Differentiable.const_cpow (by fun_prop) (Or.inl ?_)
        rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
        exact q.ne_bot
      fun_prop
    · have h1 : 1 < ((s : ℂ) + σ).re := by simp; linarith
      have h2 := GlobalTheory.T.hasSum_integralIdeles_eulerProduct E I φ hφ s κ 𝔣 Q χ Pq (s + σ) _ hU h𝔣 hQ hχ hP h1 (hΛ.2 _ h1)
      exact (hasSum_fintype _).unique (hasSum_classes hφ hχ.2.2.1 h𝔣 hd hc htriv
        (fun q => (hS q).2 σ (by push_cast; linarith)) h2)
  have h0 := congrFun key 0
  simp only [add_zero, twistFin_apply, Complex.cpow_neg, Complex.cpow_natCast] at h0
  rw [finsum_eq_sum_of_fintype]
  simp only [Formalism.PairingDivisionLocalBalance.eq, Complex.ofReal_pow]
  exact h0.symm

end GlobalTheory.ToricSumValue
end
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.compactRaising_word_mem_span_higherWords : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (w : V) (c d : Fin n), c < d → ε c = ε d → E c d w = 0 → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → E c d ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) ∈ Submodule.span ℂ {y : V | ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ (l.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum < (l'.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum ∧ y = (l'.map fun p : Fin n × Fin n => E p.1 p.2).prod w} := by
  first | exact @GlobalTheory.HolDS.compactRaise_word_higher | exact GlobalTheory.HolDS.compactRaise_word_higher | (intros; apply GlobalTheory.HolDS.compactRaise_word_higher <;> assumption)
end
