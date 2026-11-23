module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSymmetricTranslationUnitsEqKappaRatio
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle042
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLawsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle035
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle040
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle046
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
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShortChange

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem trivAt_mul {E : Type} [Field E] [NumberField E] {n : ℕ} {Λ : GenLat E n} {a b : ℕ}
    (ha : Λ.TrivAt a) (hb : Λ.TrivAt b) : Λ.TrivAt (a * b) := by
  obtain ⟨k, hk, h1, h2⟩ := ha
  obtain ⟨m, hm, h3, h4⟩ := hb
  have hg : Ideal.span {((Nat.gcd k m : ℕ) : 𝓞 E)} ≤ Ideal.span {(k : 𝓞 E)} ⊔ Ideal.span {(m : 𝓞 E)} := by
    rw [Ideal.span_singleton_le_iff_mem]
    have e : ((Nat.gcd k m : ℕ) : 𝓞 E) = (k : 𝓞 E) * (Nat.gcdA k m : ℤ) + (m : 𝓞 E) * (Nat.gcdB k m : ℤ) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) (Nat.gcd_eq_gcd_ab k m)
      push_cast at this
      exact this
    rw [e]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  refine ⟨Nat.gcd k m, (hk.coprime_dvd_left (Nat.gcd_dvd_left _ _)).mul_right
    (hm.coprime_dvd_left (Nat.gcd_dvd_right _ _)), ?_, ?_⟩
  · refine (Submodule.smul_mono hg le_rfl).trans ?_
    rw [Submodule.sup_smul]
    exact sup_le h1 h3
  · refine (Submodule.smul_mono hg le_rfl).trans ?_
    rw [Submodule.sup_smul]
    exact sup_le h2 h4

theorem badOK_host (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) :
    BadOK l (D.host.QS * D.host.q * D.host.d * l.M) := by
  have hqd := D.host.qd_big
  have hM := l.three_le
  refine ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega)) (by omega),
    D.host.toHostRaw.two_dvd_condN.mul_right _, Dvd.intro_left _ rfl, fun p hp h => ?_⟩
  exact dvd_mul_of_dvd_left (D.host.der.discr_primes.1 p hp h) _

theorem odd_rank {D : D7} (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) :
    Odd ((T.Q.Dw j).p + (T.Q.Dw j).q) := by
  obtain ⟨h1, h2, -⟩ := hF.p.toLawsCore.pins.2.2.2 j hj
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  obtain ⟨hj1, hj2⟩ := hj
  rw [h1, h2]
  exact ⟨a + b - 1, by unfold Ranks.sigW; dsimp only; omega⟩

end GlobalTheory.ShortChange
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem map_mem_span_of_constantCoeff_eq_zero {σ R S : Type} [Finite σ] [CommRing R] [CommRing S]
    (ψ : MvPowerSeries σ R →+* S) (g : MvPowerSeries σ R) (hg : MvPowerSeries.constantCoeff g = 0) :
    ψ g ∈ Ideal.span (Set.range fun j => ψ (MvPowerSeries.X j)) := by
  have h3 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
    rw [← germIdeal_eq_span]
    exact hg
  have h4 := Ideal.mem_map_of_mem ψ h3
  rwa [Ideal.map_span, ← Set.range_comp] at h4

theorem exists_pow_span_X_le_span_matV : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p p' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → p' * p = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin n × Fin d → PS (ResidueField V) n d)) ^ M ≤ Ideal.span (Set.range fun s : Fin n × Fin d => MvPowerSeries.map (residue V) (matV B p (fun j => pt V (n := n) d j) s.1 s.2)) := by
  intro V _ _ _ _ _ d O _ _ B hB n p p' N hN hp
  obtain ⟨M, hM⟩ := hB N hN
  have hpt0 : ∀ (b : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt V (n := n) d b i) = 0 := by
    intro b i; simp [pt]
  have hpt : ∀ (b : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt V (n := n) d b i) ∈ maximalIdeal V := by
    intro b i; rw [hpt0]; exact zero_mem _
  obtain ⟨-, hmul, -, hsm, -, -, -⟩ := GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p' p (fun j => pt V d j) (fun j => pt V d j) hpt hpt
  obtain ⟨hy, -, -, -, -, -, -⟩ := GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p p (fun j => pt V d j) (fun j => pt V d j) hpt hpt
  set y : Fin n → Pt V n d := matV B p (fun j => pt V d j) with hydef
  obtain ⟨-, -, -, -, hev, h0, -⟩ := GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p' p y y hy hy
  obtain ⟨⟨ψ, hψX, hψ⟩, -⟩ := evC_spec V (Fin n × Fin d) (Fin n × Fin d) Unit
    (fun s => y s.1 s.2) (fun s => hy s.1 s.2)

  have hA : ∀ (b : Fin n) (i : Fin d), compV (B.A.act (N : O)) (pt V (n := n) d b) i ∈
      Ideal.span (Set.range fun s : Fin n × Fin d => y s.1 s.2) := by
    intro b i
    have e1 : compV (B.A.act (N : O)) (pt V (n := n) d b) i = matV B p' y b i := by
      rw [← hmul, hp, hsm]
    rw [e1, ← hev, evV, hψ]
    have := map_mem_span_of_constantCoeff_eq_zero ψ.toRingHom _ (h0 b i)
    simpa [hψX] using this
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (Submodule.fg_span (Set.finite_range _))
  rw [Ideal.span_le]
  rintro _ ⟨⟨b, i⟩, rfl⟩
  let a : Fin 1 × Fin d → PS V n d := fun q => (![pt V (n := n) d b] : Fin 1 → Pt V n d) q.1 q.2
  have ha : ∀ q, a q = MvPowerSeries.X (b, q.2) := by
    rintro ⟨q1, q2⟩
    obtain rfl : q1 = 0 := Subsingleton.elim _ _
    rfl
  have ha0 : ∀ q, MvPowerSeries.constantCoeff (a q) = 0 := by
    intro q; rw [ha]; simp
  obtain ⟨-, -, hs, -⟩ := evC_spec V (Fin 1 × Fin d) (Fin n × Fin d) Unit a
    (fun q => by rw [ha0]; exact zero_mem _)
  have hS : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hS' : MvPowerSeries.HasSubst (fun q => MvPowerSeries.map (residue V) (a q)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by rw [ha]; simp)
  let θ : PS (ResidueField V) 1 d →ₐ[ResidueField V] PS (ResidueField V) n d := MvPowerSeries.substAlgHom hS'
  have hθ : ∀ f : PS V 1 d, θ (MvPowerSeries.map (residue V) f) = MvPowerSeries.map (residue V) (evC a f) := by
    intro f
    rw [hs ha0, MvPowerSeries.map_subst hS]
    simp only [θ, MvPowerSeries.coe_substAlgHom]
  have hX : θ (MvPowerSeries.X (0, i)) = MvPowerSeries.X (b, i) := by
    simp only [θ, MvPowerSeries.coe_substAlgHom]
    rw [MvPowerSeries.subst_X hS', ha]
    simp
  have h1 := Ideal.mem_map_of_mem θ (hM (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self (0, i))) M))
  rw [map_pow, hX] at h1
  refine ⟨M, ?_⟩
  refine SetLike.le_def.1 ?_ h1
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  have h2 := Ideal.mem_map_of_mem (MvPowerSeries.map (σ := Fin n × Fin d) (residue V)) (hA b j)
  rw [Ideal.map_span, ← Set.range_comp] at h2
  rw [SetLike.mem_coe, hθ]
  exact h2

end GlobalTheory.PlaceInt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.prod_symmetricTranslationUnits_eq_kappa_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (Θ : PS V 3 d) (jo : PS V 1 d), IsTheta B K h w0 Θ → IsIota B K h w0 jo → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ), Odd N → (∀ j k, ∑ i, star (mu i j) * mu i k = if j = k then (N : O) else 0) → ∀ κ : PS V n d, IsKappa B K h w0 mu N κ → ∀ α ∈ kerM B mu, ∀ u : Fin n → PS V 1 d, (∀ b, TrUnit B Θ jo N (α b) (u b)) → (∏ b, evV (n := n) ![pt V d b] (u b)) * shift B.G.F α κ = κ := by
  first | exact @GlobalTheory.PlaceInt.prod_trUnit_mul_shift_kappa | exact GlobalTheory.PlaceInt.prod_trUnit_mul_shift_kappa | (intros; apply GlobalTheory.PlaceInt.prod_trUnit_mul_shift_kappa <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.harmonicValue_eq_chart_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (k n : ℕ) (F : Fin n → SecN Xo y.x k) (f : Fin n → PS S 1 C.d), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k F P = chartVal C k f P := by
  first | exact @GlobalTheory.PlaceInt.hv_eq_chartVal | exact GlobalTheory.PlaceInt.hv_eq_chartVal | (intros; apply GlobalTheory.PlaceInt.hv_eq_chartVal <;> assumption)
end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem kappa_mul_pullM_mul_expS {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O)
    (K : Type) [CommRing K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O)
    (hh : MvPowerSeries.constantCoeff h = 0) {n : ℕ} (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d)
    (hκ : IsKappa B K h w0 mu N κ) (g : PS V n d) :
    FB.toK K (κ * pullM B mu g) * FB.expS K ((N : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i))
        (FB.toK K g * FB.expS K (((1 : ℕ) : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0))) := by
  have hpt : ∀ (b : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt V (n := n) d b i) ∈ maximalIdeal V :=
    fun b i => by rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b i]; exact Ideal.zero_mem _
  have h0 : ∀ (b : Fin n) (i : Fin d),
      MvPowerSeries.constantCoeff (matV B mu (fun j => pt V (n := n) d j) b i) = 0 :=
    (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n mu mu (fun j => pt V (n := n) d j) (fun j => pt V (n := n) d j) hpt hpt).2.2.2.2.2.1
  have hy : ∀ b : Fin n,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GP (fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) := by
    intro b i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map (algebraMap V K) (matV B mu (fun j => pt V (n := n) d j) b i)) = 0
    rw [MvPowerSeries.constantCoeff_map, h0, map_zero]
  have hact : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GP (B.actK K w0) := by
    intro i
    unfold FB.actK
    rw [MvPowerSeries.constantCoeff_map, B.A.const w0 i, map_zero]
  have hL0 : MvPowerSeries.constantCoeff (B.hL K h w0) = 0 := by
    unfold FB.hL
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _ (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.pair_points_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0)
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_comp1 _ _ hact (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0))) _ hh
  have hsm : ∀ (c : K) (f : PS K n d), MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (c • f) = 0 := by
    intro c f hf
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]
  have hS : MvPowerSeries.constantCoeff (∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := by

    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b)) _ hL0
  have hA : MvPowerSeries.constantCoeff (∑ b : Fin n, ev (n := n)
      ![fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)] (B.hL K h w0)) = 0 := by

    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (hy b)) _ hL0
  have hsub : MvPowerSeries.HasSubst
      (fun p : Fin n × Fin d => matV B mu (fun j => pt V (n := n) d j) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h0 p.1 p.2
  have hpull : FB.toK K (pullM B mu g) =
      ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) (FB.toK K g) := by
    have hC := (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin n × Fin d) (Fin n × Fin d) (Fin n × Fin d)
      (fun p : Fin n × Fin d => matV B mu (fun j => pt V (n := n) d j) p.1 p.2)
      (fun p => by rw [h0]; exact Ideal.zero_mem _)).2.2.1 (fun p => h0 p.1 p.2)
    unfold pullM evV
    rw [hC]
    unfold FB.toK ev
    exact MvPowerSeries.map_subst hsub _
  have hevy : ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i))
      (∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ∑ b : Fin n, ev (n := n) ![fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)] (B.hL K h w0) := by
    rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_sum hy]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_ev' _ _ hy (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b))]
    congr 1
    funext j
    fin_cases j
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.evP_pt _ hy b
  have hm : FB.toK K (κ * pullM B mu g) = FB.toK K κ * FB.toK K (pullM B mu g) :=
    map_mul (MvPowerSeries.map (algebraMap V K)) κ (pullM B mu g)
  have hk := hκ
  unfold IsKappa at hk
  have hAS := hsm (N : K) _ hS
  rw [Nat.cast_one, one_smul, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_mul _ hy, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_expS _ hy _ hS,
    hevy, ← hpull, hm, hk, _root_.mul_comm (FB.expS K _) (FB.toK K (pullM B mu g)), _root_.mul_assoc,
    ← ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_expS_add _ _ (by rw [map_sub, hA, hAS, sub_zero]) hAS, sub_add_cancel]

theorem nabValN_kappa_mul_pullM : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O), MvPowerSeries.constantCoeff h = 0 → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d), IsKappa B K h w0 mu N κ → ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → ∀ (P : MvPolynomial (Letter Ty r n) K) (g : PS V n d), nabValN B K h w0 N (FB.toK K (κ * pullM B mu g)) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B K h w0 1 (FB.toK K g) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.aeval (fun ℓ : Letter Ty r n => ∑ b, MvPolynomial.C (σ ℓ.1 (mu b ℓ.2.2)) * MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter Ty r n)) P) := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ h w0 hh n mu N κ hκ Ty _ r σ u hu P g
  unfold nabValN
  rw [kappa_mul_pullM_mul_expS B K h w0 hh mu N κ hκ g]
  exact GlobalTheory.T.constantCoeff_invariant_operator_along_matrix V d O B K n mu Ty r σ u hu P _

end GlobalTheory.PlaceInt
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop

theorem _root_.GlobalTheory.T.scaledShortLattice_le_of_shortGenerator_bound : ShortBoundSt → ∀ (D : D7) (T : Top D) (h : LawsP T) (_hs : LawsSh T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), Oriented T EX → ∀ (w : WeightFamilies.Wt D j) (a b : ℕ) (s : 𝓞 T.Q.c.F), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → s = (zOwnP D (T.dδ j w.n).pd w : 𝓞 T.Q.c.F) * nnW (recB h.toLawsCore) hinj EX w * (pPow D a b b : 𝓞 T.Q.c.F) → (recPJ h j hj).Thc s w ≤ (recB h.toLawsCore).Mlat j w := by
  first | exact @GlobalTheory.PlaceTop.thc_le_of_shortBound | exact GlobalTheory.PlaceTop.thc_le_of_shortBound | (intros; apply GlobalTheory.PlaceTop.thc_le_of_shortBound <;> assumption)
end
