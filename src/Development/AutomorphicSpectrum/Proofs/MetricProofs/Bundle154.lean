module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.AdaptedChartsRegularization
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle140
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle077
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle042
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle036
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquarePolarIntegralIdentity
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle153
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle152
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle112
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
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
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.lowerBound_height_on_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal x) ∩ mcPts bd) : Set (mcPts (mCoordIdeal x))) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → ∃ (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Rb.X), IsPotential Rb.A L ∧ IsSection Rb.A L s ∧ IsSNC Rb.A L s m W ∧ (∀ p, logNormSec L s p ≤ 0) ∧ (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ mcPts bd) ∧ ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → rW L s p' = rW L s p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary | exact GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary | (intros; apply GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_potential_from_snc_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)), Adapted M P S → FromSnc M P → ∃ (r : M.Xc → ℝ) (f : Fin P.N → (Fin D.n → ℂ) → ℝ) (Bf : ℝ), (∀ z ∈ D.Xo, 1 ≤ r (M.proj z)) ∧ (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j) (P.chart j).target ∧ ∀ y ∈ (P.chart j).target, |f j y| ≤ Bf) ∧ ∀ j, ∀ y ∈ (P.chart j).target \ ReciprocityTheory.AnForm.A.coordDiv (S j), r ((P.chart j).symm y) = Real.exp 1 + f j y + ∑ i ∈ S j, Real.log (‖y i‖ ^ 2)⁻¹ := by
  first | exact @LevelTowerAlt.adapted_charts_regularization | exact LevelTowerAlt.adapted_charts_regularization
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tendsto_polar {σ : Type} [Fintype σ] {n : ℕ} {α : Type} {l : Filter α} {f : α → (Fin n → σ) → ℝ}
    {a : (Fin n → σ) → ℝ} (c : Fin n → σ → ℝ) (h : ∀ w, Tendsto (fun t => f t w) l (𝓝 (a w))) :
    Tendsto (fun t => polar n (f t) c) l (𝓝 (polar n a c)) := by
  unfold polar
  exact tendsto_finsetSum _ fun w _ => (h w).const_mul _

theorem Realis.limNum_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type}
    {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) {II : IntersectionSystem}
    (hII : IsFullIntersectionSystem II) (hpos : 0 < S.t₀) (π : Equiv.Perm (Fin (D + 1)))
    (w : Fin (D + 1) → σ) : Re.limNum II (w ∘ π) = Re.limNum II w := by
  have hev : (fun t => Re.num II t (w ∘ π)) =ᶠ[𝓝[>] 0] fun t => Re.num II t w := by
    filter_upwards [Ioc_mem_nhdsGT hpos] with t ht
    have h := (hII.1 K ι).1 P (D + 1) (fun j => Re.line (w j) t) π Re.arith
      fun j => Re.line_smooth _ t ht.1 ht.2
    unfold Realis.num
    exact congrArg (· / (Re.deg : ℝ)) h
  unfold Realis.limNum limUnder
  rw [Filter.map_congr hev]

theorem AnSys.degNum_perm {e : ℕ} {σ : Type} (S : AnSys e σ) (π : Equiv.Perm (Fin e)) (w : Fin e → σ) :
    S.degNum (w ∘ π) = S.degNum w :=
  ReciprocityTheory.AnForm.M.mIntSymm S.A (fun j => S.th (w j)) π fun _ => 1

theorem thmA_limit : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (Re.PB II) + eval (fun x => c x + u / 2 * ε x) (Re.PB II) = (tsgPoly (d + 1) kappa (linePoly c ε SY.degPoly)).eval u := by
  intro hI hF II hII K _ ι _ d σ _ SY P Re a₀ ε Q c hc u
  have hpos : 0 < SY.t₀ := (SY.reg a₀).1
  have hposW : 0 < Q.an.SW.t₀ := (Q.an.SW.reg none).1
  obtain ⟨C₃, s₀, -, hAg⟩ := GlobalTheory.T.agreement_positive hI (d + 1) σ SY 0 hpos
  have hlim := (hAg II hII K ι P Re).1
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ Q.an.SW.t₀ := by
    filter_upwards [Ioc_mem_nhdsGT hposW] with t ht using ⟨ht.1, ht.2⟩
  refine GlobalTheory.T.polar_identity_from_symmetric_forms σ (d + 1) (Re.limNum II) SY.degNum kappa ε a₀ (Re.limNum_perm hII hpos)
    SY.degNum_perm (fun n hn => ?_) c hc u
  have hsq := GlobalTheory.T.square_system_polar_vanishing hI II hII K ι d σ SY P Re a₀ ε Q n hn
  refine ⟨?_, fun k hk hk2 => ?_⟩
  · have h1 := tendsto_polar (fun _ (x : σ) => (n x : ℝ)) hlim
    have h2 : Tendsto (fun t => polar (d + 2) (Re.num II t) fun _ (x : σ) => (n x : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).1.symm)
    exact tendsto_nhds_unique h1 h2
  · have h1 := tendsto_polar (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ)) hlim
    have h2 : Tendsto (fun t => -∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t))
          (Q.an.wcoef (fun a => (n a : ℝ)) k i)) (𝓝[>] 0)
        (𝓝 (-∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potH (w r)) Q.an.gH)
          (Q.an.wcoef (fun a => (n a : ℝ)) k i))) :=
      (tendsto_finsetSum _ fun i _ => tendsto_polar _ fun w =>
        (GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε Q.an w).2).neg
    have h3 := tendsto_nhds_unique (h1.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).2 k hk hk2)) h2
    let square := Q.an
    let coeff : σ → ℝ := fun a => (n a : ℝ)
    have hcoeff : coeff a₀ = 0 := by simp [coeff, hn]
    have hIntegralIdentity :
        ∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt square.SW.A (fun r => square.SW.potH (w r)) square.gH)
          (square.wcoef coeff k i) =
        2 * kappa k * polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) := by
      have hSquareLim :=
        GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε square
      obtain ⟨-, hnW, hC2W, -, -⟩ := anSys_open_basics (d + 2) (Option σ) square.SW
      obtain ⟨-, hnY, hC2Y, -, -⟩ := anSys_open_basics (d + 1) σ SY
      have hhom (w : Fin (d + 1) → σ) :
          MIntegrable SY.A (fun i => SY.potH (w i)) (fun _ => 1) ∧
            mInt SY.A (fun i => SY.potH (w i)) (fun _ => 1) = SY.degNum w := by
        let : MeasurableSpace SY.X := borel SY.X
        have : BorelSpace SY.X := ⟨rfl⟩
        have hlim := hI.convergenceSigned SY.A SY.Θ SY.L SY.s SY.m SY.W
          SY.potΘ SY.posΘ SY.potL SY.sec SY.snc SY.norm_le
          (fun i => SY.th (w i)) (fun i => SY.ph (w i)) (fun i => SY.phT (w i)) SY.C₅ SY.C SY.t₀
          (fun i => SY.sing (w i)) (fun i => SY.reg (w i)) (fun i => SY.c2 (w i))
          (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
          (fun _ y _ => SY.abs_one_le_log_rW y)
          (TendstoUniformlyOn.tendstoLocallyUniformlyOn (by
            refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
            exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε))
        refine ⟨hlim.1, ?_⟩
        have hDegree : Tendsto (fun t => mInt SY.A (fun i => SY.potT (w i) t) (fun _ => 1))
            (𝓝[>] 0) (𝓝 (SY.degNum w)) :=
          tendsto_const_nhds.congr' (by
            filter_upwards [Ioc_mem_nhdsGT hpos] with t ht
            exact (ReciprocityTheory.AnForm.M.massIndep SY.A (fun i => SY.th (w i))
              (fun i => SY.phT (w i) t) (fun i => (SY.sing (w i)).1)
              (fun i => ((SY.reg (w i)).2.2 t ht.1 ht.2).1)).symm)
        exact tendsto_nhds_unique hlim.2 hDegree

      have hexW := fun i => mInt_sumPot_expand (d + 2) square.SW.X square.SW.A (Option σ) square.SW.open' square.SW.potH
        (square.wcoef coeff k i) square.gH hnW hC2W fun w => (hSquareLim w).1
      have hexY := mInt_sumPot_expand (d + 1) SY.X SY.A σ SY.open' SY.potH
        (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) (fun _ => 1) hnY hC2Y fun w => (hhom w).1
      have hpolW : ∀ i, polar (d + 2) (fun w => mInt square.SW.A (fun r => square.SW.potH (w r)) square.gH) (square.wcoef coeff k i) =
          mInt square.SW.A (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH := fun i => (hexW i).2.symm
      have hpolY : polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) =
          mInt SY.A (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (fun _ => 1) := by
        rw [hexY.2]
        exact Finset.sum_congr rfl fun w _ => by rw [(hhom w).2]

      have hoW : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ square.U n → square.ΦW n z ∈ square.SW.open' := by
        intro n z hz
        rw [square.bdry_eq 0, Set.mem_preimage, square.first_projection_chart_compat n z hz]
        exact square.ΦY_open n _ (by simpa using hz)

      have hcW := fun i => integrableOn_hasSum_paramCover (d + 2) square.SW.X square.SW.A _ _ square.ΦW
        (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH square.coverW
        (fun n z hz r => SqFubini.isC2At_sumPot _ _ _ _ fun a => hC2W a _ (hoW n z (square.B_meas n |>.2 hz)))
        (hexW i).1
      have hcY := integrableOn_hasSum_paramCover (d + 1) SY.X SY.A _ _ square.ΦY
        (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (fun _ => 1) square.coverY
        (fun n z hz r => SqFubini.isC2At_sumPot _ _ _ _ fun a => hC2Y a _ (square.ΦY_open n z (square.B_meas n |>.2 hz)))
        hexY.1

      have hFibreIntegral : ∀ n, ∑ i ∈ Finset.range k,
          ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n},
          square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z =
          2 * kappa k * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n},
            (fun _ => (1 : ℝ)) (square.ΦY n z) * paramDens
              (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z := by
        intro n
        let α : (Fin d → ℂ) → ℝ := fun y => ∑ a, coeff a * square.α n a y
        have hd := GlobalTheory.T.square_parametrized_density_formula d σ SY a₀ ε square coeff hcoeff n k hk hk2
        have hmW : MeasurableSet {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n} := (square.coverW.2.1 n).1
        have hmY : MeasurableSet {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n} := (square.coverY.2.1 n).1
        let F : ℕ → (Fin (d + 2) → ℂ) → ℝ := fun i z =>
          logSin (square.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) * maDens (SqFubini.EW (square.G n) α k i) z
        have hae : ∀ i < k, ∀ᵐ z ∂(volume.restrict {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n}),
            square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z = F i z := by
          intro i hi
          filter_upwards [ae_restrict_of_ae (SqFubini.ae_ne d), ae_restrict_mem hmW] with z hne hz
          have hU : Fin.tail (Fin.tail z) ∈ square.U n := (square.B_meas n).2 hz
          have h1 : square.gH (square.ΦW n z) = logSin (square.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) :=
            square.norm_hom n z hU hne
          have h2 : paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z =
              maDens (SqFubini.EW (square.G n) α k i) z := hd.2 i hi z hU
          rw [h1, h2]
        have hH : ∀ z ∈ {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n},
            (fun _ => (1 : ℝ)) (square.ΦY n z) * paramDens
              (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z =
            maDens (SqFubini.EY (square.G n) α k) z := by
          intro z hz
          have h2 : paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z =
              maDens (SqFubini.EY (square.G n) α k) z := hd.1 z ((square.B_meas n).2 hz)
          rw [h2, one_mul]
        have hFint : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n} :=
          fun i hi => ((hcW i).1 n).congr (hae i hi)
        have hHint : IntegrableOn (maDens (SqFubini.EY (square.G n) α k)) {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n} :=
          (integrableOn_congr_fun hH hmY).1 (hcY.1 n)
        have hpt : ∀ y ∈ square.B n, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
            (2 * kappa k) * ∫ a : ℂ, maDens (SqFubini.EY (square.G n) α k) (Fin.cons a y) := by
          intro y hy
          have hyU : y ∈ square.U n := (square.B_meas n).2 hy
          have hnh : square.U n ∈ 𝓝 y := (square.U_open n).mem_nhds hyU
          have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := ENat.LEInfty.out
          exact GlobalTheory.T.log_sine_monge_ampere_integral hF d k hk hk2 (square.G n) α y
            (by filter_upwards [hnh] with y' hy' using square.G_pos n y' hy')
            (fun p q => ((square.G_smooth n p q).contDiffAt hnh).of_le h2)
            (ContDiffAt.sum fun a _ => contDiffAt_const.mul (((square.α_smooth n a).contDiffAt hnh).of_le h2))
        rw [Finset.sum_congr rfl fun i hi => integral_congr_ae (hae i (Finset.mem_range.1 hi)),
          setIntegral_congr_fun hmY hH]
        exact SqFubini.fibre_sum (square.B n) F _ _ hFint hHint hpt (square.B_meas n).1
      have hsW : HasSum (fun n => ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n},
          square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z)
          (∑ i ∈ Finset.range k, mInt square.SW.A (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH) :=
        hasSum_sum fun i _ => (hcW i).2
      rw [funext hFibreIntegral] at hsW
      rw [Finset.sum_congr rfl fun i _ => hpolW i, hpolY]
      exact hsW.unique (hcY.2.mul_left _)
    rw [h3, hIntegralIdentity]
    ring

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 3) ∧ IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) (d + 2) ∧ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0) ∧ imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y ∧ ∀ v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀)), (∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩) → (∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) → imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic | exact GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic <;> assumption)
end

section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def IsImg {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (z : (Σ k, ι' k) → ℂ) (w : (Σ k, ι k) → ℂ) : Prop :=
  ∀ z₁, SameOrbit z₁ z → ∀ F' F, M'.IsFrame F' → M.IsFrame F →
    M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) →
    ∀ h, M'.IsFlagOf F' z₁ h → ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) ∧
      M.IsFlagOf F z₀ fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ

theorem IsImg.orbit {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {Cv : FlagCover M' M}
    {z z₁ : (Σ k, ι' k) → ℂ} {w w₁ : (Σ k, ι k) → ℂ} (h : IsImg Cv z w) (hz : SameOrbit z₁ z)
    (hw : SameOrbit w₁ w) : IsImg Cv z₁ w₁ := by
  intro z₂ h2 F' F hF' hF hg' hg hh hfl
  obtain ⟨z₀, a, b, c⟩ := h z₂ (Cj.sameOrbit_trans h2 hz) F' F hF' hF hg' hg hh hfl
  exact ⟨z₀, Cj.sameOrbit_trans a (Cj.sameOrbit_symm hw), b, c⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt

theorem eq_on_block {K : Type} {ι : K → Type} {Kk : Type} {ιk : Kk → Type} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {a b : (Σ k, ι k) → ℂ} (h : a ∘ v = b ∘ v)
    {k : K} (hk : k ∈ Set.range κ) (m : ι k) : a ⟨k, m⟩ = b ⟨k, m⟩ := by
  obtain ⟨q, hq⟩ := hb.2.2.2 ⟨k, m⟩ hk
  rw [← hq]
  exact congrFun h q

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ (x y' : R.X) (z : (Σ k, ι k) → ℂ), y' ∈ R.U x → pr y' ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z ∘ v = R.lift x y' → stepPh M BM p v R pr y' = stepGap M BM p z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr H x y' z hy' hpr hz hzv
  obtain ⟨hb, hr, -, H1⟩ := H
  obtain ⟨z₀, hz₀, hz₀v, hz₀o⟩ := H1 y'
  have hex : pr y' ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift y' y' :=
    ⟨hpr, z₀, hz₀, hz₀v⟩
  have hph : stepPh M BM p v R pr y' = stepGap M BM p hex.2.choose := by
    unfold stepPh
    rw [dite_eq_left hex]
  obtain ⟨hz₁, hz₁v⟩ := hex.2.choose_spec
  rw [hph]
  generalize hex.2.choose = z₁ at hz₁ hz₁v

  have hbase : ∀ {a b : (Σ k, ι k) → ℂ}, a ∘ v = b ∘ v → basePart M.blk a = basePart M.blk b := by
    intro a b hab
    funext q
    exact eq_on_block hb hab (hr q.1.1 (Or.inl q.1.2)) q.2
  have hz₁o : SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr y') (pr y')) := by
    rw [hbase (hz₁v.trans hz₀v.symm)]
    exact hz₀o

  obtain ⟨c, hc, hcl⟩ := R.compat x y' y' ⟨hy', R.mem_U y'⟩
  set c' : K → ℂ := Function.extend κ c 1 with hc'
  have hc'0 : ∀ k, c' k ≠ 0 := by
    intro k
    by_cases hk : ∃ a, κ a = k
    · obtain ⟨a, rfl⟩ := hk
      rw [hc', hb.1.extend_apply]
      exact hc a
    · rw [hc', Function.extend_apply' _ _ _ hk]
      exact one_ne_zero
  set z₂ : (Σ k, ι k) → ℂ := fun q => c' q.1 * z₁ q with hz₂
  have hz₂m : z₂ ∈ mcPts (mCoordIdeal y) :=
    ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z₁ c' hc'0).2 hz₁).1
  have hz₂v : z₂ ∘ v = z ∘ v := by
    rw [hzv, hcl]
    funext q
    have h1 : z₁ (v q) = R.lift y' y' q := congrFun hz₁v q
    have h2 : c' (v q).1 = c q.1 := by
      rw [hb.2.2.1 q, hc', hb.1.extend_apply]
    simp only [Function.comp, hz₂, h1, h2]
  have ht : stepGap M BM p z₂ = stepGap M BM p z₁ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus K ι Φ y Ψ N j M n BM p z₁ c' hc'0 hz₁.1
  have hz₂o : SameOrbit (basePart M.blk z₂) (BM.Rb.lift (pr y') (pr y')) := by
    obtain ⟨d, hd, hdl⟩ := hz₁o
    refine ⟨fun k => c' k.1 * d k, fun k => mul_ne_zero (hc'0 _) (hd k), ?_⟩
    funext q
    have h1 : basePart M.blk z₁ q = d q.1 * BM.Rb.lift (pr y') (pr y') q := congrFun hdl q
    have h2 : basePart M.blk z₂ q = c' q.1.1 * basePart M.blk z₁ q := rfl
    rw [h2, h1, mul_assoc]
  have hg : stepGap M BM p z₂ = stepGap M BM p z :=
    GlobalTheory.T.flag_gap_same_base_orbit K ι Φ y Ψ N j M n BM p (pr y') z₂ z hpr hz₂m hz hz₂o (hbase hz₂v)
      (fun k hk m => eq_on_block hb hz₂v (hr k (Or.inr hk)) m)
  rw [← ht, hg]

end GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem sameOrbit_basePart {M : FlagModel y Ψ N j} {BM : BaseMetric M n} {p : Ψ × Fin N} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e} {pr : R.X → BM.Rb.X}
    (hS : IsStepHyp M BM p κ v R pr) (x : R.X) {z : (Σ k, ι k) → ℂ} (hz : z ∘ v = R.lift x x) :
    SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)) := by
  obtain ⟨hbm, hcov, -, hall⟩ := hS
  obtain ⟨z₁, -, h1, h2⟩ := hall x
  have e : basePart M.blk z = basePart M.blk z₁ := by
    funext q
    obtain ⟨r, hr⟩ := hbm.2.2.2 ⟨q.1.1, q.2⟩ (hcov _ (Or.inl q.1.2))
    have h3 : z (v r) = z₁ (v r) := congrFun (hz.trans h1.symm) r
    rw [hr] at h3
    exact h3
  rw [e]
  exact h2

theorem exists_base_const {L : Type} {μ : L → Type} {b₁ b₂ b : (Σ k, μ k) → ℂ} (h₁ : SameOrbit b₁ b)
    (h₂ : SameOrbit b₂ b) : ∃ c : L → ℂ, (∀ k, c k ≠ 0) ∧ ∀ q, b₁ q = c q.1 * b₂ q := by
  obtain ⟨c₁, hc₁, rfl⟩ := h₁
  obtain ⟨c₂, hc₂, rfl⟩ := h₂
  refine ⟨fun k => c₁ k / c₂ k, fun k => div_ne_zero (hc₁ k) (hc₂ k), fun q => ?_⟩
  have := hc₂ q.1
  field_simp

theorem exists_coord {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hbm : IsBlockMap κ v) (k : Kk) (i : ι (κ k)) :
    ∃ m : ιk k, v ⟨k, m⟩ = ⟨κ k, i⟩ := by
  obtain ⟨r, hr⟩ := hbm.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
  have h1 : κ r.1 = κ k := by rw [← hbm.2.2.1 r, hr]
  have h2 : r.1 = k := hbm.1 h1
  obtain ⟨r1, m⟩ := r
  obtain rfl : r1 = k := h2
  exact ⟨m, hr⟩

theorem stepGap_eq {M : FlagModel y Ψ N j} [Fintype Ψ] [DecidableEq Ψ] {BM : BaseMetric M n} {p : Ψ × Fin N} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e} {pr : R.X → BM.Rb.X}
    (hS : IsStepHyp M BM p κ v R pr) {x x' : R.X} (hpr : pr x = pr x') (hb : pr x ∉ bdry BM.s)
    (hblk : ∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k,
      R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩)
    {z z' : (Σ k, ι k) → ℂ} (hzm : z ∈ mcPts (mCoordIdeal y)) (hz'm : z' ∈ mcPts (mCoordIdeal y))
    (hz : z ∘ v = R.lift x x) (hz' : z' ∘ v = R.lift x' x') :
    stepGap M BM p z = stepGap M BM p z' := by
  have so := sameOrbit_basePart hS x hz
  have so' := sameOrbit_basePart hS x' hz'
  rw [← hpr] at so'
  obtain ⟨cb, hcb, hcbq⟩ := exists_base_const so so'
  obtain ⟨hbm, hcov, -, -⟩ := hS
  have e1 : ∀ r, z (v r) = R.lift x x r := congrFun hz
  have e2 : ∀ r, z' (v r) = R.lift x' x' r := congrFun hz'
  have ha : ∃ a : ℂ, a ≠ 0 ∧ ∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = a * z' ⟨k, m⟩ := by
    rcases hp : M.blk p with _ | k₀
    · exact ⟨1, one_ne_zero, fun k hk => by simp at hk⟩
    · obtain ⟨k', rfl⟩ := hcov k₀ (Or.inr hp)
      obtain ⟨i, hi⟩ := hzm.1 (κ k')
      obtain ⟨m, hm⟩ := exists_coord hbm k' i
      obtain ⟨a, ha⟩ := hblk k' m hp
      refine ⟨a, fun h0 => hi ?_, fun k hk m' => ?_⟩
      · rw [← hm, e1, ha, h0, zero_mul]
      · obtain rfl : κ k' = k := Option.some.inj hk
        obtain ⟨m'', hm''⟩ := exists_coord hbm k' m'
        rw [← hm'', e1, e2, ha]
  obtain ⟨a, ha0, ha⟩ := ha
  let c : K → ℂ := fun k =>
    if h : ∀ p', M.blk p' ≠ some k then cb ⟨k, h⟩ else if M.blk p = some k then a else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    simp only [c]
    split_ifs
    · exact hcb _
    · exact ha0
    · exact one_ne_zero
  have hT := GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z' c hc
  have h1 : stepGap M BM p (fun q => c q.1 * z' q) = stepGap M BM p z' :=
    GlobalTheory.T.flag_gap_torus_invariant K ι Φ y Ψ N j M n BM p z' c hc hz'm.1
  rw [← h1]
  refine GlobalTheory.T.flag_gap_same_base_orbit K ι Φ y Ψ N j M n BM p (pr x) z _ hb hzm (hT.2 hz'm).1 so ?_ ?_
  · funext q
    have : c q.1.1 = cb q.1 := dif_pos q.1.2
    show basePart M.blk z q = c q.1.1 * z' ⟨q.1.1, q.2⟩
    rw [this, hcbq]
    rfl
  · intro k hk m
    have : c k = a := (dif_neg fun h => h p hk).trans (if_pos hk)
    show z ⟨k, m⟩ = c k * z' ⟨k, m⟩
    rw [this, ha k hk]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → stepPh M BM p v R pr x = stepPh M BM p v R pr x' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hS x x' hpr hblk
  by_cases hb : pr x ∈ bdry BM.s
  · have hb' : pr x' ∈ bdry BM.s := hpr ▸ hb
    rw [stepPh, stepPh, dif_neg fun h => h.1 hb, dif_neg fun h => h.1 hb']
  · have hb' : pr x' ∉ bdry BM.s := hpr ▸ hb
    obtain ⟨z₁, hz₁, hv₁, -⟩ := hS.2.2.2 x
    obtain ⟨z₂, hz₂, hv₂, -⟩ := hS.2.2.2 x'
    have h1 : pr x ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x := ⟨hb, z₁, hz₁, hv₁⟩
    have h2 : pr x' ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x' x' := ⟨hb', z₂, hz₂, hv₂⟩
    rw [stepPh, stepPh, dif_pos h1, dif_pos h2]
    exact stepGap_eq hS hpr hb hblk h1.2.choose_spec.1 h2.2.choose_spec.1 h1.2.choose_spec.2 h2.2.choose_spec.2

end GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp
end
end
