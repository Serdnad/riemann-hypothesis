module

public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupTranslateAutomorphismAndMatrixKernel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle047
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle035
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

def letterEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ) :
    Lt1 Dw × Fin n ≃ LtN Dw n where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun ℓ := (⟨ℓ.1, ℓ.2.1⟩, ℓ.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem toK_prod_evV (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] (K : Type) [CommRing K] [Algebra V K] {d n : ℕ}
    (f : Fin n → PS V 1 d) :
    FB.toK K (∏ b, evV (n := n) ![pt V d b] (f b)) =
      GlobalTheory.PowGerm.boxSer (fun b => MvPowerSeries.map (algebraMap V K) (f b)) := by
  have key : ∀ b : Fin n, evV (n := n) ![pt V d b] (f b) =
      MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) (f b) := by
    intro b
    have hX : ∀ j : Fin 1 × Fin d,
        MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d))
          (MvPowerSeries.X j : MvPowerSeries (Fin 1 × Fin d) V) =
        (fun p : Fin 1 × Fin d => (![pt V d b] : Fin 1 → Pt V n d) p.1 p.2) j := by
      rintro ⟨i, j⟩
      rw [Fin.fin_one_eq_zero i, MvPowerSeries.rename_X]
      simp [pt]
    show evC _ (f b) = _
    exact evC_eq_algHom _ (fun j => by
      have h := (hX j).symm
      simp only at h
      rw [h, MvPowerSeries.rename_X]
      simp) _ hX (f b)
  simp only [FB.toK, key, map_prod, GlobalTheory.PowGerm.boxSer, MvPowerSeries.rename_map]

theorem nabValN_boxSer_eq_chartVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {S : Type} [Field S] [Algebra c.F S] [Algebra ℚ S]
    {y : FrPt Xo c S} (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (g : Fin n → PS S 1 C.d)
    (P : MvPolynomial (LtN Dw n) c.F) :
    chartVal C k g P = nabValN C.B S C.h H.w0 k (GlobalTheory.PowGerm.boxSer g) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map (algebraMap c.F S) P) := by
  classical
  have hcc : MvPowerSeries.constantCoeff C.h = 0 := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.11
  have hcol : ∀ (m : LtN Dw n →₀ ℕ) (b : Fin n),
      ReciprocityTheory.ChartRestriction.G.TB.colM (Finsupp.mapDomain (letterEquiv Dw n).symm m) b = colOf m b := by
    intro m b
    unfold ReciprocityTheory.ChartRestriction.G.TB.colM colOf
    congr 1
    funext ℓ
    have hℓ : ((ℓ, b) : Lt1 Dw × Fin n) = (letterEquiv Dw n).symm ⟨ℓ.1, (ℓ.2, b)⟩ := rfl
    rw [hℓ, Finsupp.mapDomain_apply_of_injective (letterEquiv Dw n).symm.injective]
  have hP : MvPolynomial.map (algebraMap c.F S) P = MvPolynomial.rename (letterEquiv Dw n)
      (MvPolynomial.rename (letterEquiv Dw n).symm (MvPolynomial.map (algebraMap c.F S) P)) := by
    rw [MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id_apply]
  rw [hP, GlobalTheory.nabValN_boxSer S C.d (𝓞 E) C.B S C.h H.w0 hcc k n g (Lt1 Dw) (LtN Dw n) (letterEquiv Dw n)
    (fun ℓ => ℓ.2.2) C.uvec (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (fun _ => rfl) (fun _ => rfl),
    GlobalTheory.NabCol.sum_support_rename]
  unfold chartVal
  rw [MvPolynomial.support_map_of_injective _ (algebraMap c.F S).injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  simp only [hcol]

theorem hv_eq_nabValN : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (k n : ℕ) (F : Fin n → SecN Xo (xOf y) k) (f : Fin n → PS T.V 1 (chD C.ch)), (∀ b, GermIs C k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → letI := io.toAlgebra; hv Xo c nab y.1 k F P = nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C nab hnab B hB k n F f hF w P hP
  letI := io.toAlgebra
  obtain ⟨hG, hAct, -⟩ := hB
  have hgen := C.gen.1
  have hFK : B.FK T.Fr = C.ch.B.FK T.Fr := by
    unfold FB.FK FGLaw.mapF
    funext i
    simp [hG, hgen.1 i]
  have hAK : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    unfold FB.actK
    funext i
    simp [hAct, hgen.2.1 a i]
  have h1 := GlobalTheory.T.harmonicValue_eq_chart_value E H Dw l Xo c hstar nab hnab T.Fr y.1 C.ch k n F
    (fun b => MvPowerSeries.map (algebraMap T.V T.Fr) (f b)) (fun b => hF b) w P hP
  rw [h1, nabValN_boxSer_eq_chartVal C.ch k _ P, ← toK_prod_evV T.V T.Fr f]
  exact GlobalTheory.ChartCmp.nabValN_congr_FK C.ch.B B T.Fr hFK hAK _ _ _ _ _ _ _

end GlobalTheory.PlaceInt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p p' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → p' * p = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin n × Fin d → PS (ResidueField V) n d)) ^ M ≤ Ideal.span (Set.range fun s : Fin n × Fin d => MvPowerSeries.map (residue V) (matV B p (fun j => pt V (n := n) d j) s.1 s.2)) := by
  first | exact @GlobalTheory.PlaceInt.exists_pow_span_X_le_span_matV | exact GlobalTheory.PlaceInt.exists_pow_span_X_le_span_matV | (intros; apply GlobalTheory.PlaceInt.exists_pow_span_X_le_span_matV <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.formalGroupTranslate_automorphism_and_matrixKernel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (p : Matrix (Fin n) (Fin n) O), (0 ∈ kerM B p) ∧ (∀ f : PS V n d, shift B.G.F 0 f = f) ∧ ∀ α β : Fin n → Fin d → V, (∀ b, Small (α b)) → (∀ b, Small (β b)) → (∃ ψ : PS V n d ≃ₐ[V] PS V n d, ∀ f, shift B.G.F α f = ψ f) ∧ (α ∈ kerM B p ↔ ∀ f, shift B.G.F α (pullM B p f) = pullM B p f) ∧ ((∀ f, shift B.G.F α f = shift B.G.F β f) → α = β) ∧ ∃ δ : Fin n → Fin d → V, (∀ b, Small (δ b)) ∧ (∀ b, (cpt (δ b) : Pt V 0 d) = addV B.G.F (cpt (α b)) (cpt (β b))) ∧ (∀ f, shift B.G.F α (shift B.G.F β f) = shift B.G.F δ f) ∧ (α ∈ kerM B p → β ∈ kerM B p → δ ∈ kerM B p) := by
  first | exact @GlobalTheory.PlaceInt.shift_kerM | exact GlobalTheory.PlaceInt.shift_kerM | (intros; apply GlobalTheory.PlaceInt.shift_kerM <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.connectionValueLevel_kappa_mul_pullback : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O), MvPowerSeries.constantCoeff h = 0 → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d), IsKappa B K h w0 mu N κ → ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → ∀ (P : MvPolynomial (Letter Ty r n) K) (g : PS V n d), nabValN B K h w0 N (FB.toK K (κ * pullM B mu g)) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B K h w0 1 (FB.toK K g) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.aeval (fun ℓ : Letter Ty r n => ∑ b, MvPolynomial.C (σ ℓ.1 (mu b ℓ.2.2)) * MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter Ty r n)) P) := by
  first | exact @GlobalTheory.PlaceInt.nabValN_kappa_mul_pullM | exact GlobalTheory.PlaceInt.nabValN_kappa_mul_pullM | (intros; apply GlobalTheory.PlaceInt.nabValN_kappa_mul_pullM <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain

theorem _root_.GlobalTheory.T.harmonicValuationLowerBound_hostField_all_places : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n DFw : ℕ), Formalism.L2.Pj.DF Dw w ≤ DFw → ChBound C e (∑ p ∈ D.host.condN.primeFactors, (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * (DFw : ℝ) / 2) w n := by
  first | exact @GlobalTheory.PlaceInt.HostChart.chBound_host | exact GlobalTheory.PlaceInt.HostChart.chBound_host | (intros; apply GlobalTheory.PlaceInt.HostChart.chBound_host <;> assumption)
end
