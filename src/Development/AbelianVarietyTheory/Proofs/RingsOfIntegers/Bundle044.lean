module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardPrimaryTorsionTuplesKilledByMatrix
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle021
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpec
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle035
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle019
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle042
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SectionRegularOnModelOfNuNonneg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle043
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle014

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
namespace GlobalTheory.PlaceInt.FormKer

lemma cpt_const {V : Type} [CommRing V] {d : ℕ} (x : Pt V 0 d) :
    (cpt (fun i => MvPowerSeries.constantCoeff (x i)) : Pt V 0 d) = x := by
  funext i
  ext m

  obtain rfl : m = 0 := Subsingleton.elim _ _
  simp [cpt]

lemma rel_prod {M P : Type*} [Monoid M] (R : M → P → Prop) (z : P) (s : P → P → P) (h1 : R 1 z)
    (hm : ∀ a a' x x', R a x → R a' x' → R (a * a') (s x x')) :
    ∀ (n : ℕ) (f : Fin n → M) (g : Fin n → P), (∀ j, R (f j) (g j)) →
      R (List.ofFn f).prod ((List.ofFn g).foldr s z) := by
  intro n
  induction n with
  | zero => intro f g _; simpa using h1
  | succ n ih =>
    intro f g hfg
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.foldr_cons]
    exact hm _ _ _ _ (hfg 0) (ih _ _ fun j => hfg j.succ)

theorem kills_iff_mem_kerM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (a : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (α : Fin n → Fin (chD C.ch) → T.V), (∀ b, FormPt C (a b) (α b)) → (Kills Xo mu a ↔ α ∈ kerM B mu) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C B hB n mu a α hα
  obtain ⟨h1, hinj, hmul, hact, -⟩ := GlobalTheory.T.formal_group_points_of_integral_chart_spec E H Dw l Xo c hstar T io y C B hB

  have h0 : (0 : Pt T.V 0 (chD C.ch)) = cpt 0 := by
    funext k
    simp [cpt]
  have hstep : ∀ (g g' : ptO Xo (xOf y) ⟶ Xo.univ.t.G) (x x' : Pt T.V 0 (chD C.ch)),
      (∃ δ, x = cpt δ ∧ FormPt C g δ) → (∃ δ, x' = cpt δ ∧ FormPt C g' δ) →
        ∃ δ, addV B.G.F x x' = cpt δ ∧ FormPt C (g * g') δ := by
    rintro g g' x x' ⟨al, rfl, hg⟩ ⟨al', rfl, hg'⟩
    exact ⟨_, (cpt_const _).symm, hmul g g' al al' _ hg hg' (cpt_const _)⟩
  have key : ∀ i, ∃ δ : Fin (chD C.ch) → T.V,
      matV B (m := 0) mu (fun j => cpt (α j)) i = cpt δ ∧
        FormPt C (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (mu i j)).prod δ := by
    intro i
    have hrow : ∀ j, ∃ δ, compV (B.A.act (mu i j)) (cpt (α j)) = cpt δ ∧
        FormPt C (a j ≫ Xo.univ.t.act.act (mu i j)) δ := fun j =>
      ⟨_, (cpt_const _).symm, hact (a j) (α j) _ (mu i j) (hα j) (cpt_const _)⟩
    exact rel_prod (fun g x => ∃ δ, x = cpt δ ∧ FormPt C g δ) 0 (addV B.G.F) ⟨0, h0, h1⟩
      hstep n (fun j => a j ≫ Xo.univ.t.act.act (mu i j))
      (fun j => compV (B.A.act (mu i j)) (cpt (α j))) hrow
  have hcpt : ∀ δ : Fin (chD C.ch) → T.V, cpt (n := 0) δ = 0 → δ = 0 := by
    intro δ h
    funext k
    have := congrArg MvPowerSeries.constantCoeff (congrFun h k)
    simpa [cpt] using this
  simp only [Kills, kerM, Set.mem_ofPred_eq]
  constructor
  · intro hk
    refine ⟨fun b => (hα b).1, funext fun i => ?_⟩
    obtain ⟨δ, hm, hF⟩ := key i
    obtain rfl : δ = 0 := (hinj _ 1 δ 0 hF h1).mp (hk i)
    rw [hm, ← h0]
    rfl
  · rintro ⟨-, hz⟩ i
    obtain ⟨δ, hm, hF⟩ := key i
    have hδ : δ = 0 := hcpt δ (by rw [← hm]; exact congrFun hz i)
    subst hδ
    exact (hinj _ 1 0 0 hF h1).mpr rfl

end GlobalTheory.PlaceInt.FormKer
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.card_primaryTorsionTuples_killed_by_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (ℓ : ℕ), ℓ.Prime → ∀ (n : ℕ) (q g : Matrix (Fin n) (Fin n) (𝓞 E)) (k M : ℕ), Nat.Coprime k ℓ → 0 < M → g * q = ((k * M : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → AllRat Xo x M → Nat.card {u : Fin n → (ptO Xo x ⟶ Xo.univ.t.G) // Kills Xo q u ∧ ∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1)} = ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ (Dw.p + Dw.q)).factorization ℓ := by
  first | exact @GlobalTheory.card_kills_primary | exact GlobalTheory.card_kills_primary | (intros; apply GlobalTheory.card_kills_primary <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

theorem _root_.GlobalTheory.T.section_regular_on_model_of_nu_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ (k : ℕ) (F₀ : SecN Xo (xOf y) k) (hh : SecN Xo xF k), 1 ≤ k → IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((k : ℕ) : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₀ hh → (∀ σ s, SecTieF I P F xF k σ hh → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) → ∃ σ, ReciprocityTheory.ChartRestriction.G.PullbackSections.SecTie I k F₀ σ := by
  first | exact @GlobalTheory.NuRegular.main | exact GlobalTheory.NuRegular.main | (intros; apply GlobalTheory.NuRegular.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

namespace GlobalTheory.PlaceInt.ChartRam

theorem isRQ_of_not_isUnit (T : CDVR) (N : ℕ) (hN0 : N ≠ 0) (hNu : ¬ IsUnit (N : T.V)) :
    TB.IsRQ (R := T.V) T.Fr := by
  refine ⟨IsFractionRing.injective T.V T.Fr, fun y => ?_⟩
  have hNV0 : (N : T.V) ≠ 0 := by exact_mod_cast hN0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hNV0 hϖ
  have hϖN : ϖ ∣ (N : T.V) := by
    rcases m with _ | m
    · exact absurd (hm.isUnit_iff.2 (by simp)) hNu
    · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := T.V) y
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs0 hϖ
  have hsd : s ∣ (N : T.V) ^ n := hn.dvd.trans (pow_dvd_pow_of_dvd hϖN n)
  obtain ⟨c, hc⟩ := hsd
  refine ⟨c * a, N ^ n, pow_pos (Nat.pos_of_ne_zero hN0) n, ?_⟩
  have hsK : algebraMap T.V T.Fr s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]; exact hs0
  have hcast : ((N ^ n : ℕ) : T.Fr) = algebraMap T.V T.Fr ((N : T.V) ^ n) := by
    rw [map_pow, map_natCast]; push_cast; rfl
  rw [hcast, hc, map_mul, map_mul]
  field_simp

theorem vV_natCast_nonneg (T : CDVR) (N : ℕ) (hN0 : N ≠ 0) : 0 ≤ vV T.V (N : T.Fr) := by
  have hr : algebraMap T.V T.Fr (N : T.V) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]
    exact_mod_cast hN0
  have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) (N : T.V)
  have h2 : valV T.V (algebraMap T.V T.Fr (N : T.V)) ≠ 0 := valV_ne_zero hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one, map_natCast] at h3
  unfold vV
  omega



theorem chBound_ramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsGalois ℚ E → ∀ (p a m : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ¬ p ∣ m → (NumberField.discr E).natAbs = p ^ a * m → (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsPrime → (p : 𝓞 E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭) → ∀ e : ℕ, 0 < e → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ((vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) * (Formalism.L2.Pj.DF Dw w : ℝ) / 2) w n := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hG p a m hp hpu hpm hd hmv e he w n
  refine GlobalTheory.T.harmonicValue_bound_of_column_products E H Dw l Xo c hstar T io y C e _ w n ?_
  intro k P hP f hf
  let _ := io.toAlgebra
  obtain ⟨π, _, _, cc, s, hcs, φ, ψ, hψ, heig, h21a, h21b, h21c⟩ :=
    GlobalTheory.T.exists_ramified_eigen_lifts_of_chart_directions E H Dw l Xo c hstar T io y C hG p a m hp hpu hpm hd hmv e he
  obtain ⟨hF, hA, h1, h2, hs, had, hu⟩ := C.gen.1
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  let t : CVA.IntTie (algebraMap T.V T.Fr) C.ch.B :=
    ⟨C.FT, C.actT, C.ph1T, C.ph2T, C.syT, C.adT, funext fun i => (hF i).symm, fun a => funext fun i => (hA a i).symm,
      h1.symm, h2.symm, hs.symm, fun a => (had a).symm⟩
  have huv : C.ch.uvec = fun ℓ i => algebraMap T.V T.Fr (C.uvecT ℓ i) := funext fun ℓ => funext fun i => hu ℓ i
  simp only [huv] at heig h21a h21b h21c
  set cJ : ℝ := (vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) with hcJ
  have hv : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast vV_natCast_nonneg T p hp.ne_zero
  have hcJ0 : 0 ≤ cJ := by rw [hcJ]; positivity
  have hw0 : H.w0 + star H.w0 = 1 := by rw [hstar]; exact CVA.cmHostUnit_add_conj_eq_one H
  have hpmin : ∀ mo ∈ P.support, ∑ b, TB.pairMin (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1)
      (colL Dw.mult n mo b) ≤ Formalism.L2.Pj.DF Dw w / 2 := fun mo hmo =>
    sum_pairMin_le Dw.mult n cc s (fun τ i => w (τ, i)) mo (hP.1.2.2 mo hmo)
  have hmem := chartValJ (isRQ_of_not_isUnit T p hp.ne_zero hpu) (Jv T e cJ) (one_mem_Jv T e hcJ0)
    (CVA.fbOf t hinj) C.ch.h (CVA.fbOf_canon t hinj C.ch.h C.ch.gauge) H.w0 hw0 k
    Dw.mult ComplexEmbedding.conjugate (fun τ => by ext x; simp) (InPsi H)
    (CVA.inPsi_or H) cc s hcs C.uvecT φ ψ hψ heig h21a h21b h21c n (fun τ i => w (τ, i)) P hP
    (Formalism.L2.Pj.DF Dw w / 2) hpmin f hf
  have hval := mem_Jv_pow T e hcJ0 _ _ hmem
  simp only [CVA.fbOf_nabVal] at hval
  rw [huv]
  refine le_trans ?_ hval
  apply EReal.coe_le_coe_iff.2
  have hdiv : ((Formalism.L2.Pj.DF Dw w / 2 : ℕ) : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self _ 2
  nlinarith

end GlobalTheory.PlaceInt.ChartRam
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit

theorem ptOf_const_left : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (G : Over (Sp V)) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (X : limO V d 1 ⟶ G), IsLimit x X → ∀ (α : Fin d → V) (hα : Small α) (aV : Sp V ⟶ G.left), (∀ m : ℕ, ∃ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] V ⧸ maximalIdeal V ^ (m + 1), (∀ p, ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p.2)) ∧ spMap (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))) ≫ aV = spMap (ψ : Jet V (Fin 1 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (x m).left) → ∀ n : ℕ, (ptOf X (Sm.const B α hα : Sm B n)).left = spMap (algebraMap V (PS V n d)) ≫ aV := by
  intro V _ _ _ _ _ d O _ _ B G x X hX α hα aV ha n
  let χ : PS V 1 d →ₐ[V] V :=
    GlobalTheory.mvEvalAdic V (maximalIdeal V) (fun p : Fin 1 × Fin d => α p.2) (fun p => hα p.2)
  have hχ : ∀ p, χ (MvPowerSeries.X p) = α p.2 := fun p => GlobalTheory.mvEvalAdic_X _ _ _ p
  have h1 : evA ![(Sm.const B α hα : Sm B n)] = (Algebra.ofId V (PS V n d)).comp χ := by
    refine AlgHom.ext fun f => (evA_apply _ f).trans ?_
    refine evC_eq_algHom _ (fun p : Fin 1 × Fin d => ((![(Sm.const B α hα : Sm B n)] : Fin 1 → Sm B n) p.1).2 p.2)
      _ (fun p => ?_) f
    obtain ⟨i, j⟩ := p
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, hχ]
    rfl
  have h2 : spMap (χ : PS V 1 d →+* V) ≫ X.left = aV := by
    refine GlobalTheory.hom_ext_of_isHausdorff (maximalIdeal V) fun m => ?_
    obtain ⟨ψ, hψ, e⟩ := ha m
    have hj : ∀ p : Fin 1 × Fin d, jetA (V := V) (Fin 1 × Fin d) m (MvPowerSeries.X p) =
        Ideal.Quotient.mk _ (MvPolynomial.X p) := fun p => by
      first
      | exact (mk_psTrunc m _ (MvPowerSeries.constantCoeff_X p)).trans (Chart.pj_X m p)
      | exact FBIdSy.mk_psTrunc_X m p
      | exact (mk_psTrunc m _ (MvPowerSeries.constantCoeff_X p)).symm.trans (Chart.pj_X m p)
    have k : ψ.comp (jetA (Fin 1 × Fin d) m) = (Ideal.Quotient.mkₐ V (maximalIdeal V ^ (m + 1))).comp χ := by
      have hv : ∀ p, (ψ.comp (jetA (Fin 1 × Fin d) m)) (MvPowerSeries.X p) = Ideal.Quotient.mk _ (α p.2) :=
        fun p => by rw [AlgHom.comp_apply, hj, hψ]
      have hv' : ∀ p, ((Ideal.Quotient.mkₐ V (maximalIdeal V ^ (m + 1))).comp χ) (MvPowerSeries.X p) =
          Ideal.Quotient.mk _ (α p.2) := fun p => by rw [AlgHom.comp_apply, hχ]; rfl
      refine AlgHom.ext fun f => ?_
      have := GlobalTheory.algHom_sub_mem_pow _ _
        (J := (maximalIdeal V).map (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))))
        (fun p => hv p ▸ Ideal.mem_map_of_mem _ (hα p.2)) (fun p => hv' p ▸ Ideal.mem_map_of_mem _ (hα p.2))
        (n := m + 1) (fun p => by rw [hv, hv', sub_self]; exact zero_mem _) f
      rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot, sub_eq_zero] at this
      exact this
    have k2 := GlobalTheory.PlaceFormPt.spMap_homAt (jetA (Fin 1 × Fin d) m) ψ X.left
    rw [k] at k2
    have k3 : (x m).left = (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetA (Fin 1 × Fin d) m)).left ≫ X.left :=
      (congrArg (fun q => q.left) (hX m)).symm
    refine Eq.trans ?_ (k2.symm.trans ((congrArg (_ ≫ ·) k3.symm).trans e.symm))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.left) (Spec.map_comp _ _).symm)
  rw [← h2, ptOf, h1]
  exact (congrArg (· ≫ X.left) (Spec.map_comp (CommRingCat.ofHom (χ : PS V 1 d →+* V))
    (CommRingCat.ofHom (algebraMap V (PS V n d))))).trans (Category.assoc _ _ _)

end GlobalTheory.TransUnit
end
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit.LimEx

variable {V : Type} [CommRing V] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem isLocalRing_jet [IsLocalRing V] (m : ℕ) : IsLocalRing (Jet V κ m) :=
  haveI : Nontrivial (Jet V κ m) := (jetAug : Jet V κ m →ₐ[V] V).toRingHom.domain_nontrivial
  IsLocalRing.of_surjective' (jetA κ m : MvPowerSeries κ V →ₐ[V] Jet V κ m).toRingHom
    (fun a => GlobalTheory.ChartCmp.FrameRatio.psJet_surj m a)

theorem exists_ringHom_of_jets {A : Type} [CommRing A] (φ : ∀ m, A →+* Jet V κ m)
    (h : ∀ m a, (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) (φ (m + 1) a) = φ m a) :
    ∃ ψ : A →+* MvPowerSeries κ V, ∀ m a, jetA κ m (ψ a) = φ m a := by
  choose f hf using fun a => GermD.exists_ps_of_jets (fun m => φ m a) (fun m => h m a)
  have hf' : ∀ a m, jetA κ m (f a) = φ m a := hf
  have ext : ∀ {p q : MvPowerSeries κ V}, (∀ m, jetA κ m p = jetA κ m q) → p = q :=
    fun hpq => FrameBiextId.ps_ext hpq
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun m a => hf' a m⟩
  · exact ext fun m => by rw [hf', map_one, map_one]
  · exact fun a b => ext fun m => by rw [map_mul, hf', hf', hf', map_mul]
  · exact ext fun m => by rw [hf', map_zero, map_zero]
  · exact fun a b => ext fun m => by rw [map_add (f := _), hf', hf', hf', map_add (f := _)]

theorem exists_limit_hom [IsLocalRing V] {Y : Scheme.{0}} (p : Y ⟶ Spec (.of V))
    (x : ∀ m, Spec (.of (Jet V κ m)) ⟶ Y)
    (hx : ∀ m, Spec.map (CommRingCat.ofHom
      ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)) ≫ x (m + 1) = x m)
    (hp : ∀ m, x m ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (Jet V κ m)))) :
    ∃ g : Spec (.of (MvPowerSeries κ V)) ⟶ Y,
      g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (MvPowerSeries κ V))) ∧
      ∀ m, Spec.map (CommRingCat.ofHom ((jetA κ m : MvPowerSeries κ V →ₐ[V] Jet V κ m) :
        MvPowerSeries κ V →+* Jet V κ m)) ≫ g = x m := by
  have hloc := fun m => isLocalRing_jet (V := V) (κ := κ) m
  let y : Y := x 0 (closedPoint (Jet V κ 0))
  have hy : ∀ m, x m (closedPoint (Jet V κ m)) = y := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← ih, ← hx m]
      refine Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _).symm
      have : IsLocalHom (CommRingCat.ofHom
          ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)).hom :=
        IsLocalHom.of_surjective _ (fun a => by
          obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
          exact ⟨Ideal.Quotient.mk _ q, rfl⟩)
      have h1 := Spec_closedPoint (f := CommRingCat.ofHom
          ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m))
      exact congrArg (x (m + 1)) h1.symm
  choose φ hφ using fun m => (GlobalTheory.existsUnique_factor_stalk (x m) (hy m)).exists
  have hc : ∀ m a, (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) ((φ (m + 1)).hom a) = (φ m).hom a := by
    intro m a
    have h1 : Spec.map (CommRingCat.ofHom
        ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)) ≫
        Spec.map (φ (m + 1)) = Spec.map (φ m) := by
      rw [← cancel_mono (Y.fromSpecStalk y), Category.assoc, hφ, hφ, hx m]
    rw [← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom a)
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_jets (fun m => (φ m).hom) hc
  obtain ⟨s, hs⟩ := Spec.map_surjective (Y.fromSpecStalk y ≫ p)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y, ?_, fun m => ?_⟩
  · rw [Category.assoc, ← hs, ← Spec.map_comp]
    congr 1
    ext1
    refine RingHom.ext fun c => FrameBiextId.ps_ext fun m => ?_
    have h1 : Spec.map (φ m) ≫ Spec.map s = Spec.map (CommRingCat.ofHom (algebraMap V (Jet V κ m))) := by
      rw [hs, ← Category.assoc, hφ, hp]
    rw [← Spec.map_comp] at h1
    have h2 : (φ m).hom (s.hom c) = algebraMap V (Jet V κ m) c := congr($(Spec.map_injective h1).hom c)
    exact ((hψ m (s.hom c)).trans h2).trans ((jetA κ m).commutes c).symm
  · rw [← hφ m, ← Spec.map_comp_assoc]
    congr 2
    ext1
    exact RingHom.ext fun a => hψ m a

theorem exists_isLimit : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) (d : ℕ)
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G),
    (∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m) →
    ∃ X : limO V d 1 ⟶ G, IsLimit x X := by
  intro V _ _ G d x hx
  obtain ⟨g, hg, hg'⟩ := exists_limit_hom (V := V) (κ := Fin 1 × Fin d) G.hom (fun m => (x m).left)
    (fun m => congrArg CommaMorphism.left (hx m))
    (fun m => (Over.w (x m)).trans (Category.comp_id _))
  exact ⟨Over.homMk g (hg.trans (Category.comp_id _).symm), fun m => Over.OverMorphism.ext (hg' m)⟩

end GlobalTheory.TransUnit.LimEx
end
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit

theorem hom_ext_of_jets : ∀ (V : Type) [CommRing V] [IsLocalRing V] (κ : Type) [Fintype κ] [DecidableEq κ] (Y : Scheme.{0}) (f g : Sp (MvPowerSeries κ V) ⟶ Y), (∀ m, spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ f = spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ g) → f = g := by
  intro V _ _ κ _ _ Y f g h
  have hs : Function.Surjective (jetA (V := V) κ 0 : MvPowerSeries κ V →+* Jet V κ 0) :=
    fun a => GlobalTheory.ChartCmp.FrameRatio.psJet_surj 0 a
  have hn : Nontrivial (Jet V κ 0) :=
    (Formalism.L2.Pj.jetAug : Jet V κ 0 →ₐ[V] V).toRingHom.domain_nontrivial
  have hl : IsLocalRing (Jet V κ 0) := IsLocalRing.of_surjective' _ hs
  have hc : spMap (jetA (V := V) κ 0 : MvPowerSeries κ V →+* Jet V κ 0) (closedPoint (Jet V κ 0)) =
      closedPoint (MvPowerSeries κ V) := by
    have : IsLocalHom (CommRingCat.ofHom (jetA (V := V) κ 0 : MvPowerSeries κ V →+* Jet V κ 0)).hom :=
      IsLocalHom.of_surjective _ hs
    exact Spec_closedPoint
  have hx : g (closedPoint (MvPowerSeries κ V)) = f (closedPoint (MvPowerSeries κ V)) := by
    rw [← hc]
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans (Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _))
    rw [h]
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.existsUnique_factor_stalk f rfl
  obtain ⟨φ', hφ', -⟩ := GlobalTheory.existsUnique_factor_stalk g hx
  have : φ = φ' := by
    ext1
    refine RingHom.ext fun b => GlobalTheory.FrameBiextId.ps_ext fun m => ?_
    have h1 : spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ Spec.map φ =
        spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ Spec.map φ' := by
      rw [← cancel_mono (Y.fromSpecStalk _), Category.assoc, Category.assoc, hφ, hφ', h]
    rw [← Spec.map_comp, ← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom b)
  rw [← hφ', ← this, hφ]

end GlobalTheory.TransUnit
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop

theorem _root_.GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power : ∀ (D : D7) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (j : ℕ) (w : WeightFamilies.Wt D j) (a b : ℕ), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → ramLoss D la w ≤ ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) := by
  first | exact @GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow | exact GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow | (intros; apply GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.expansion_pullback_sourceLevelOne : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (s : P.U.SecK 1) (F : Fam P.D.toPre (FractionRing V) 1), P.U.Expands 1 s F → ∀ s' : P.U.SecK (1 * N), IsPullByEnd P.U (t.act.act a) 1 N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (1 * N), P.U.Expands (1 * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a 1 N F F' := by
  first | exact @GlobalTheory.PullLevelOne.expands_pull_level_one | exact GlobalTheory.PullLevelOne.expands_pull_level_one | (intros; apply GlobalTheory.PullLevelOne.expands_pull_level_one <;> assumption)
end
