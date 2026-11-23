module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isGramPair_of_isMetricFr : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H H' : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → IsMetricFr E H' → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (gramAt E H' τ) := by
  intro F _ σ X ι _ m k E H H' hH hH' τ
  have hA (y : CxPts X.str σ) := (E.nonempty (under y)).choose_spec
  refine ⟨fun y => ⟨(GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y _ (hA y) τ).1,
    (GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H' hH' y _ (hA y) τ).1⟩, fun y => ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E y _ (hA y)] with z hz
  have hP := (Fr.mem_iff hz).1 (hA z) τ
  have hT := GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X (m τ) _ z (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)
  refine ⟨_, _, _, hT, hT, hT, ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E z _ hz, GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E z _ (hA z)] with w h1 h2
  exact ⟨hH.trans w _ h1 _ h2 τ, hH'.trans w _ h1 _ h2 τ⟩

end GlobalTheory.ChernCalc
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem ratVal_zero_var {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (y : CxPts X.str σ) :
    ratVal (0 : X.Fn) y = 0 := by
  have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial (0 : Γ(X.X, ⊤))
  rw [map_zero, ev_eq mem_ptsIn_top, map_zero] at e
  exact e

theorem isGramPair_ldPart (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (hH : IsMetricFr E H) (τ : ι) :
    IsGramPair (atlas X σ) (gramAt E H τ) (fun y z => ldPart (gramAt E H τ y z)) := by
  have hA : ∀ y : CxPts X.str σ, (E.nonempty (under y)).choose ∈ E.S (under y) :=
    fun y => (E.nonempty (under y)).choose_spec
  have hsm := fun y => GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H hH y _ (hA y) τ
  have hT : ∀ (A B : Mat m X.Fn) (w : CxPts X.str σ), A ∈ E.S (under w) → B ∈ E.S (under w) →
      HolUnitAt (atlas X σ) (fun z => ((B * A⁻¹) τ).map (ratVal · z)) w ∧
      ∀ i j : Fin (m τ), i < j → ((B * A⁻¹) τ).map (ratVal · w) i j = 0 := by
    intro A B w hAw hBw
    have hp := ((Fr.mem_iff hAw).1 hBw) τ
    refine ⟨GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X (m τ) ((B * A⁻¹) τ) w (fun i j => mem_O_ratOf.1 (hp.1 i j)) hp.2.1
      (mem_O_ratOf.1 hp.2.2.1), fun i j hij => ?_⟩
    rw [Matrix.map_apply, hp.2.2.2 i j i.2 hij]
    exact ratVal_zero_var w
  refine ⟨fun y => ⟨(hsm y).1, ?_⟩, fun y => ?_⟩
  · refine ⟨(GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ (hH.posDef y _ (hA y) τ)).2.2.2, fun c hc => ?_⟩
    filter_upwards [(hsm y).2 c hc] with v hv
    exact (GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth _ _ _ v hv.1 hv.2).1
  · have h1 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E y _ (hA y)
    filter_upwards [h1, h1.eventually_nhds] with z hz hz'
    have h2 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ (hA z)
    obtain ⟨hol, tri⟩ := hT _ _ z hz (hA z)
    refine ⟨_, _, fun w => Matrix.diagonal fun i =>
      (((E.nonempty (under z)).choose * (E.nonempty (under y)).choose⁻¹) τ).map (ratVal · w) i i,
      hol, hol, ⟨?_, fun c hc a b => ?_⟩, ?_⟩
    · rw [Matrix.det_diagonal, ← Matrix.det_of_lowerTriangular _ (fun i j hij => tri i j hij)]
      exact hol.1
    · by_cases hab : a = b
      · subst hab
        filter_upwards [hol.2 c hc a a] with v hv
        simpa only [Matrix.diagonal_apply_eq] using hv
      · exact Eventually.of_forall fun v => by
          simp only [Matrix.diagonal_apply_ne _ hab]
          exact differentiableAt_const _
    · filter_upwards [hz', h2] with w hwA hwB
      obtain ⟨holw, triw⟩ := hT _ _ w hwA hwB
      have e := hH.trans w _ hwA _ hwB τ
      change gramAt E H τ z w = _ * gramAt E H τ y w * _ at e
      refine ⟨e, ?_⟩
      rw [e]
      exact (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ (hH.posDef w _ hwA τ) triw holw.1).1

end GlobalTheory.ChernCalc
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem trace_mul_mul_eq_sum_entries {R : Type} [CommRing R] {r : Type} [Fintype r] (P M Q : Matrix r r R) :
    (P * M * Q).trace = ∑ p, ∑ q, (Q * P) q p * M p q := by
  rw [Matrix.trace_mul_cycle, Matrix.trace, Finset.sum_comm (f := fun p q => (Q * P) q p * M p q)]
  exact Finset.sum_congr rfl fun q _ => Matrix.mul_apply

theorem dbarAt_transAt (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n)
    (hG : MContDiffAt ∞ G v) (hGu : IsUnit (G v).det) (hG' : MContDiffAt ∞ G' v)
    (hG'u : IsUnit (G' v).det) (k : ℕ) :
    dbarAt (fun x => transAt G G' x k) v = (powAt G v k : Alt n) - powAt G' v k := by
  obtain ⟨_, hsum, hsmul, _, hleib⟩ := GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v
  obtain ⟨sconst, ssum, ssmul, smul⟩ := GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := le_of_eq (by simp)
  have hdiff : ∀ α : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v :=
    fun α h S => (h S).differentiableAt (by simp)
  obtain ⟨W, hW⟩ : ∃ W : ℕ → V n → Matrix r r (Ev n),
      W = fun i x => curvEv G' x ^ (k - 1 - i) * curvEv G x ^ i := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : r → r → V n → Alt n, β = fun p q x =>
      (∑ a, conn G x (coordVec a) p q • dz a) - ∑ a, conn G' x (coordVec a) p q • dz a := ⟨_, rfl⟩

  have hWs : ∀ i p q, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((W i x q p : Ev n) : Alt n) S) v := by
    intro i p q; subst hW; exact (GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).1
  have hWc : ∀ i p q, dbarAt (fun x => ((W i x q p : Ev n) : Alt n)) v = 0 := by
    intro i p q; subst hW; exact (GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).2

  have hcs : ∀ (H : V n → Matrix r r ℂ), MContDiffAt ∞ H v → IsUnit (H v).det → ∀ p q,
      ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ a, conn H x (coordVec a) p q • dz a) S) v := by
    intro H hH hHu p q
    exact ssum (Fin n) Finset.univ (fun a x => conn H x (coordVec a) p q • dz a) fun a _ =>
      ssmul (fun x => conn H x (coordVec a) p q) (fun _ => dz a)
        (hH.conn hHu hinf (coordVec a) p q) (sconst (dz a))
  have hβs : ∀ p q, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β p q x) S) v := by
    intro p q S; subst hβ
    simpa only [map_sub, Finsupp.sub_apply] using (hcs G hG hGu p q S).sub (hcs G' hG' hG'u p q S)
  have dsub : ∀ α γ : V n → Alt n, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (γ x) S) v) →
      dbarAt (fun x => α x - γ x) v = dbarAt α v - dbarAt γ v := by
    intro α γ hα hγ
    have e : (fun x => α x - γ x) =
        fun x => ∑ j ∈ (Finset.univ : Finset (Fin 2)), (![α, fun y => (-1 : ℂ) • γ y] j) x := by
      funext x; simp [Fin.sum_univ_two, sub_eq_add_neg]
    rw [e, hsum (Fin 2) Finset.univ _ ?_]
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hsmul (-1) γ hγ]
      simp [sub_eq_add_neg]
    · intro j _ S
      fin_cases j
      · exact hα S
      · simpa [map_smul] using (hγ S).const_smul (-1 : ℂ)
  have hdβ : ∀ p q, dbarAt (β p q) v = (curvEv G v p q : Alt n) - curvEv G' v p q := by
    intro p q; subst hβ
    refine (dsub _ _ (hdiff _ (hcs G hG hGu p q)) (hdiff _ (hcs G' hG' hG'u p q))).trans ?_
    rw [GlobalTheory.T.dbar_chernConnection_entry_eq_curvature n r G v hG hGu p q, GlobalTheory.T.dbar_chernConnection_entry_eq_curvature n r G' v hG' hG'u p q]
  have step : ∀ i p q, dbarAt (fun x => ((W i x q p : Ev n) : Alt n) * β p q x) v =
      (W i v q p : Alt n) * ((curvEv G v p q : Alt n) - curvEv G' v p q) := by
    intro i p q
    rw [hleib (fun x => W i x q p) (β p q) (hdiff _ (hWs i p q)) (hdiff _ (hβs p q)), hWc, zero_mul,
      zero_add, hdβ]

  have key : (fun x => transAt G G' x k) =
      fun x => ∑ i ∈ Finset.range k, ∑ p, ∑ q, ((W i x q p : Ev n) : Alt n) * β p q x := by
    funext x
    subst hW hβ
    simp only [transAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [trace_mul_mul_eq_sum_entries, Matrix.map_apply, Matrix.sub_apply, map_sub,
      AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Finset.sum_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub, sub_mul, Subalgebra.coe_sub]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Algebra.smul_def, mul_assoc, mul_sub, sub_mul]

  have alg : ∑ i ∈ Finset.range k, ∑ p, ∑ q, W i v q p * (curvEv G v p q - curvEv G' v p q) =
      powAt G v k - powAt G' v k := by
    refine Eq.trans ?_ (GlobalTheory.T.sum_trace_pow_mul_sub_mul_pow_telescope (Ev n) r (curvEv G v) (curvEv G' v) k)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.trace_mul_cycle, Matrix.trace, Finset.sum_comm, hW]
    exact Finset.sum_congr rfl fun q _ => by rw [Matrix.diag_apply, Matrix.mul_apply]; rfl
  rw [key]
  refine (hsum _ _ _ ?_).trans ?_
  · intro i _
    exact hdiff _ (ssum r Finset.univ _ fun p _ => ssum r Finset.univ _ fun q _ =>
      smul _ _ (hWs i p q) (hβs p q))
  have inner : ∀ i, dbarAt (fun x => ∑ p, ∑ q, ((W i x q p : Ev n) : Alt n) * β p q x) v =
      ∑ p, ∑ q, (W i v q p : Alt n) * ((curvEv G v p q : Alt n) - curvEv G' v p q) := by
    intro i
    refine (hsum _ _ _ ?_).trans (Finset.sum_congr rfl fun p _ => ?_)
    · intro p _
      exact hdiff _ (ssum r Finset.univ _ fun q _ => smul _ _ (hWs i p q) (hβs p q))
    refine (hsum _ _ _ ?_).trans (Finset.sum_congr rfl fun q _ => step i p q)
    intro q _
    exact hdiff _ (smul _ _ (hWs i p q) (hβs p q))
  rw [Finset.sum_congr rfl fun i _ => inner i]
  have := congrArg (fun w : Ev n => (w : Alt n)) alg
  simpa only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, Subalgebra.coe_sub] using this

end GlobalTheory.ChernCalc
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem chernFld_ldPart_eq_esymm_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ j p, chernFld (atlas X σ) (fun y z => ldPart (gramAt E H τ y z)) j p = aeval (fun i => grF E H ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j) := by
  intro F _ σ X ι _ m E H hH τ j p
  set A := (E.nonempty (under p.pt)).choose with hAdef
  have hA : A ∈ E.S (under p.pt) := (E.nonempty (under p.pt)).choose_spec
  have hev := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H hH p.pt A hA τ).2 p.1.1 p.2)
  change ∀ᶠ v in 𝓝 p.crd, MContDiffAt ∞ (fun u => H A (p.ch.symm u) τ) v ∧ (H A (p.ch.symm v) τ).PosDef at hev
  have h0 := hev.self_of_nhds
  have hs := GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth X.dim (m τ) (fun u => H A (p.ch.symm u) τ) p.crd h0.1 h0.2
  have hp0 := GlobalTheory.T.gramLowerTriangularFactor_posDef_properties (m τ) _ h0.2
  show chernAt (fun v => ldPart (H A (p.ch.symm v) τ)) p.crd j = _
  refine (GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms X.dim (m τ) (fun v => ldPart (H A (p.ch.symm v) τ))
    (fun i v => grD (H A (p.ch.symm v) τ) i) p.crd hs.1 (fun i => (hp0.2.1 i).1) ?_ j).trans rfl
  filter_upwards [hev] with x hx
  have hpx := GlobalTheory.T.gramLowerTriangularFactor_posDef_properties (m τ) _ hx.2
  exact ⟨hpx.2.2.1, fun i => (hpx.2.1 i).2⟩

end GlobalTheory.ChernCalc
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep
  GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspRep.ParLawsT

theorem lpDim_locParT (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (π : CG E a) (h : IsPlaceOver A w) : (locParT hT π h).lpDim = a := by
  obtain ⟨_, _, H⟩ := isRecT_locRecT hT h
  exact H.dim _

end GlobalTheory.CuspRep.ParLawsT

end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.DatumFourierOnCmp

open GlobalTheory.DatumFourier



theorem vecOf_eq_sum_heis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (χ : (AE D)ˣ →* Circle) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (Ω : GlobalTheory.OnCmp.DatFn D i) (ω : GlobalTheory.OnTies.WeilRep D i) (φv : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.OnCmp.IsWeilTw R i χ ω → Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q → GlobalTheory.OnCmp.ReadsOnly (R.Pg ∪ Q) Ω → GlobalTheory.OnCmp.VecOf R i Q Ω φv → ∀ (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), GlobalTheory.OnCmp.PhiOf R i Q Ω ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ Q) → φv = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun χ Q Ω ω φv _ _ hRO hVec l φ hφ hP e he => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hVec
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ Q, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    hRO _ (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))))
      (fun PP h => hred PP (Finset.mem_union.1 h)), ← (hφ x).2, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by

      rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

end GlobalTheory.DatumFourierOnCmp

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem finrank_HO1_descend_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → ∀ g : ℕ, Module.Finite L (HO1 B.hom) → Module.finrank L (HO1 B.hom) = g → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  intro K L _ _ _ A _ B _ φ hpb hA g hfin hrank
  haveI := hA.proper
  obtain ⟨⟨e, -⟩, -⟩ := flat_baseChange_HO K L A.left B.left A.hom B.hom φ hpb.1 inferInstance inferInstance
  haveI : Module.Finite L (L ⊗[K] HO1 A.hom) := Module.Finite.equiv e.symm
  have hr : Module.rank L (L ⊗[K] HO1 A.hom) = Cardinal.lift (Module.rank K (HO1 A.hom)) :=
    Module.rank_baseChange
  have hfinA : Module.Finite K (HO1 A.hom) := by
    rw [← Module.rank_lt_aleph0_iff]
    have h1 : Module.rank L (L ⊗[K] HO1 A.hom) < Cardinal.aleph0 := Module.rank_lt_aleph0 L _
    rw [hr] at h1
    simpa using h1
  refine ⟨hfinA, ?_⟩
  rw [← hrank, ← e.finrank_eq, Module.finrank_baseChange]

end GlobalTheory.AbCoh
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r), IsNrm G r P.atP δ z → P.term Kf f r K φ = P.termAt Kf f r K φ x t hx δ z := by
  first | (exact @GlobalTheory.LKMid.Pair.term_eq_termAt) | (exact GlobalTheory.LKMid.Pair.term_eq_termAt) | (intros; apply GlobalTheory.LKMid.Pair.term_eq_termAt <;> assumption)
end
