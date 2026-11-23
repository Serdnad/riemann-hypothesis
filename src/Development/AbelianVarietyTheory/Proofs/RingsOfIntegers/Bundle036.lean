module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle021
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle093
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle021
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt


open GlobalTheory.NabLinear in
theorem nab_smul_secN {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) (F F' : SecN Xo y.x k) (r : S)
    (hF : ∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) :
    ∀ α, nab y (k : ℤ) F' α = r * nab y (k : ℤ) F α := by
  intro α
  let _ : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  obtain ⟨C, hex, hval⟩ := hnab.2 S y
  obtain ⟨f, hf⟩ := hex k F
  have hf' : IsGerm y C.d C.x C.B.A.act C.e C.wP k F' (MvPowerSeries.C r * f) := by
    unfold IsGerm at hf ⊢
    intro m
    obtain ⟨F₁, τ, h1, hc, hv⟩ := hf m
    obtain ⟨F₂, h2⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (jBase y C.d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F'
    refine ⟨F₂, τ, h2, hc, ?_⟩
    have hs := GlobalTheory.NabLinear.isValueAt_scale Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (jBase y C.d m 1) hF h1 h2 hv
    convert hs using 1
    have hj : (jBase y C.d m 1).left = spMap (algebraMap S (Jet S (Fin 1 × Fin C.d) m)) := rfl
    rw [hj, GlobalTheory.NabLinear.appTop_toΓ, ← map_mul, ← GlobalTheory.NabLinear.psJet_C]
    congr 1
    clear hval hex hs h1 h2 hv hc hF hnab hj F₁ F₂ hf
    unfold psJet
    rw [← map_mul]
    congr 1
    unfold psTrunc
    have h0 : (0 : Fin 1 × Fin C.d →₀ ℕ) ∈ degLE m := by
      unfold degLE
      simp
      exact ⟨fun _ => 0, by ext; simp⟩
    have hC : ∑ e ∈ degLE m, MvPolynomial.monomial e
        (MvPowerSeries.coeff e (MvPowerSeries.C r : MvPowerSeries (Fin 1 × Fin C.d) S)) =
        MvPolynomial.monomial 0 r := by
      rw [Finset.sum_eq_single_of_mem 0 h0 (fun e _ he => by rw [MvPowerSeries.coeff_C, if_neg he, map_zero]),
        MvPowerSeries.coeff_C, if_pos rfl]
    rw [hC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPolynomial.monomial_mul, zero_add]
  exact (hval k F' _ hf' α).trans ((GlobalTheory.NabLinear.nabVal_C_mul C.B C.h H.w0 k r f C.uvec _).trans
    (congrArg (r * ·) (hval k F f hf α).symm))

theorem sum_support_C_mul {σ K S : Type} [CommRing K] [CommRing S] [Algebra K S] (P : MvPolynomial σ K) (s : K)
    (g : (σ →₀ ℕ) → S) :
    ∑ m ∈ (MvPolynomial.C s * P).support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m =
      algebraMap K S s * ∑ m ∈ P.support, algebraMap K S (P.coeff m) * g m := by
  classical
  have hsub : (MvPolynomial.C s * P).support ⊆ P.support := by
    rw [MvPolynomial.C_mul']
    exact MvPolynomial.support_smul
  calc ∑ m ∈ (MvPolynomial.C s * P).support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m
      = ∑ m ∈ P.support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m := by
        apply Finset.sum_subset hsub
        intro m _ hm
        rw [MvPolynomial.mem_support_iff, not_not] at hm
        rw [hm, map_zero, zero_mul]
    _ = algebraMap K S s * ∑ m ∈ P.support, algebraMap K S (P.coeff m) * g m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [MvPolynomial.coeff_C_mul, map_mul, _root_.mul_assoc]

theorem hv_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), (∀ (k : ℕ) (F F' : Fin n → SecN Xo y.x k) (r : Fin n → S), (∀ b j, (F' b).f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S (r b)) * (F b).f j) → hv Xo c nab y k F' P = (∏ b, r b) * hv Xo c nab y k F P) ∧ (∀ (k : ℕ) (F : Fin n → SecN Xo y.x k) (s : c.F), hv Xo c nab y k F (MvPolynomial.C s * P) = algebraMap c.F S s * hv Xo c nab y k F P) ∧ ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) = hv Xo c nab y (N ^ 2) (fun b => sqN Xo N (F b)) P := by
  intro E _ _ _ H Dw l Xo c _ _ nab hnab S _ _ y n P
  refine ⟨?_, ?_, ?_⟩
  · intro k F F' r hF
    unfold hv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have key : ∀ b, nab y (k : ℤ) (F' b) (colOf m b) = r b * nab y (k : ℤ) (F b) (colOf m b) :=
      fun b => nab_smul_secN Xo c nab hnab y k (F b) (F' b) (r b) (hF b) _
    simp only [key, Finset.prod_mul_distrib]
    ring
  · intro k F s
    unfold hv
    exact sum_support_C_mul P s _
  · intro N F
    unfold hv sqN
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1

end GlobalTheory.PlaceInt
end
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

theorem chBound_of_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ f : Fin n → PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (∑ mo ∈ P.support, P.coeff mo * ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))) → ChBound C e ρ w n := by
  intro E _ _ _ H Dw l Xo c _ _ T io y C e ρ w n h k
  unfold nuLocC
  refine le_iInf fun P => le_iInf fun hP => le_iInf fun f => le_iInf fun hf => ?_
  exact (GlobalTheory.RamChartCmp.bound_all_iff_bound_prod C e k P _).2 (h k P hP) f hf

end GlobalTheory.PlaceInt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.AdaptExists

theorem mem_std {E : Type} [Field E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = v i := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem single_mem {E : Type} [Field E] {n : ℕ} (j : Fin n) : (Pi.single j (1 : E) : Fin n → E) ∈ stdLat E n := by
  rw [mem_std]
  intro i
  by_cases h : i = j
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

theorem nat_smul_mem {E : Type} [Field E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (k : ℕ) {v : Fin n → E}
    (hv : v ∈ L) : (k : E) • v ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact L.toAddSubmonoid.nsmul_mem hv k

theorem exists_cols {E : Type} [Field E] {n : ℕ} (c : Fin n → Fin n → E) (hc : ∀ j, c j ∈ stdLat E n) :
    ∃ q : Matrix (Fin n) (Fin n) (𝓞 E), ∀ i j, algebraMap (𝓞 E) E (q i j) = c j i := by
  choose a ha using fun j => (mem_std (c j)).1 (hc j)
  exact ⟨Matrix.of fun i j => a j i, fun i j => ha j i⟩

theorem exists_adapt (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ) (Λ : GenLat E n)
    (N M ℓ : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M) (hl : ℓ.Prime) :
    ∃ A : Adapt Λ N ℓ, IsSim H (A.p * A.q) ((A.k * N) ^ 2) := by
  obtain ⟨hodd, -, hN⟩ := hL
  have hN0 : 0 < N := hodd.pos
  have hm : 0 < 2 * ℓ := Nat.mul_pos two_pos hl.pos
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
  obtain ⟨k₂, ga, hk₂, hun, hin, hon⟩ := GlobalTheory.AdaptUnitary.exists_unitary_adapted E H n Λ N hU hN0 (hN.trans inf_le_left) (2 * ℓ) hm
  obtain ⟨k₁, g, hk₁, -, hcols, hsp⟩ := LocBasis.exists_matrix_primeTo E n Λ.Ln N hN0 inf_le_right hN (2 * ℓ) hm
  set G := g.map (algebraMap (𝓞 E) E) with hG
  have hNe : ∀ j : Fin n, (N : E) • (Pi.single j (1 : E) : Fin n → E) ∈ Λ.Ln := by
    intro j
    have h := hN (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) (single_mem (E := E) j))
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h
  choose v hv hve using fun j => hsp _ (hNe j)
  obtain ⟨q, hq⟩ := exists_cols v hv
  obtain ⟨p, hp⟩ := exists_cols (fun j => (k₂ : E) • ga.mulVec (G.mulVec (Pi.single j 1)))
    (fun j => hin _ (hcols _ (single_mem j)).1)
  have hP : p.map (algebraMap (𝓞 E) E) = (k₂ : E) • (ga * G) := by
    ext i j
    rw [Matrix.map_apply, hp, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hGQ : G * q.map (algebraMap (𝓞 E) E) = ((k₁ * N : ℕ) : E) • (1 : Matrix (Fin n) (Fin n) E) := by
    ext i j
    have h := congrFun (hve j) i
    simp only [Matrix.mul_apply, Matrix.map_apply, hq]
    simp only [Matrix.mulVec, dotProduct] at h
    rw [← h]
    simp [Matrix.one_apply, Pi.single_apply]
  have hprod : (p * q).map (algebraMap (𝓞 E) E) = ((k₁ * k₂ * N : ℕ) : E) • ga := by
    rw [Matrix.map_mul, hP, Matrix.smul_mul, Matrix.mul_assoc, hGQ, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    push_cast
    ring
  have hk : Nat.Coprime (k₁ * k₂) (2 * ℓ) := Nat.Coprime.mul_left hk₁ hk₂
  refine ⟨{
    k := k₁ * k₂, k₁ := k₁, ga := ga, p := p, q := q, g := g
    odd := (Nat.coprime_two_right).1 (Nat.Coprime.coprime_mul_right_right hk)
    cop := Nat.Coprime.coprime_mul_left_right hk
    cop₁ := Nat.Coprime.coprime_mul_left_right hk₁
    unitary := hun
    into := ?_
    onto := ?_
    prod := hprod
    cols := hcols
    spans := hsp
    gq := ?_ }, ?_⟩
  · intro w hw
    rw [Nat.cast_mul, mul_smul]
    exact nat_smul_mem _ _ (hin w hw)
  · intro w hw
    obtain ⟨u, hu, e⟩ := hon w hw
    exact ⟨(k₁ : E) • u, nat_smul_mem _ _ hu, by rw [Nat.cast_mul, mul_smul, e, Matrix.mulVec_smul]⟩
  · apply Matrix.map_injective hinj
    show (g * q).map _ = Matrix.map _ _
    rw [Matrix.map_mul, hGQ]
    ext i j
    by_cases h : i = j <;> simp [h]
  · intro j k
    apply hinj
    have he : ∀ a b, algebraMap (𝓞 E) E ((p * q) a b) = ((k₁ * k₂ * N : ℕ) : E) * ga a b :=
      fun a b => congrFun (congrFun hprod a) b
    have hb : ∀ a : 𝓞 E, algebraMap (𝓞 E) E (H.bar a) = IsCMField.complexConj E (algebraMap (𝓞 E) E a) := H.bar_eq
    show algebraMap (𝓞 E) E (∑ i, H.bar ((p * q) i j) * (p * q) i k) =
      algebraMap (𝓞 E) E (if j = k then (((k₁ * k₂ * N) ^ 2 : ℕ) : 𝓞 E) else 0)

    rw [map_sum]
    simp only [map_mul (algebraMap (𝓞 E) E), hb, he, map_mul (IsCMField.complexConj E), map_natCast]
    have : ∀ i, ((k₁ * k₂ * N : ℕ) : E) * IsCMField.complexConj E (ga i j) * (((k₁ * k₂ * N : ℕ) : E) * ga i k) =
        ((k₁ * k₂ * N : ℕ) : E) ^ 2 * (IsCMField.complexConj E (ga i j) * ga i k) := fun i => by ring
    simp only [this]
    rw [← Finset.mul_sum, hun]
    split_ifs <;> simp

end GlobalTheory.PlaceInt.AdaptExists
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem twisting_statements_of_laws :
    Laws → TwistBaseChangeStatement → TWStatement ∧ FiniteOrderValuationInvariance ∧ PullbackValuationForwardBound := by
  intro hL hT

  have hG : GlobalFnsSt := hL.globalFns
  have hTW : TWStatement := TWM.tw_of hG (twistBCSpan_of hT) GlobalTheory.T.valuation_thetaRatio_eq_bilinear
  exact ⟨hTW, galois_fixed_adelic_matrices_descend hL hTW, pullback_valuation_forward_of (pullGen_of hG) (QuadraticAlgebraValuation.qAl_of hL)⟩

end GlobalTheory
end
