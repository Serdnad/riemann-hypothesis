module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Formalism.HermitianCurvature.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle183
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsReducedBasisLePhiCy
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEqSmulOne
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle019
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GeneratesOfNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle121
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem hodgeTate_inclusion_intChart : ∀ (p : ℕ) [Fact p.Prime], HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), y.IsAlg → ∃ (N : ℕ) (u : Fin N → PS X.O 1 (chD Ch.ch)), (∀ k, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (u k)) ∧ ∀ z : X.O, X.v (algebraMap X.O X.C z) ^ (p - 1) ≤ X.v (p : X.C) → ∀ f : Fin (chD Ch.ch) → X.O, z • f ∈ Submodule.span X.O (Set.range fun k => dl (u k)) := by
  intro p _ hHT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch X hy
  obtain ⟨U⟩ := GlobalTheory.CharDepth.nonempty_unifChart E H Dw l Xo c T io y Ch hy p X
  have hp : ¬IsUnit (p : U.T'.V) := fun h => by
    have h' := h.map U.ι'
    rw [map_natCast] at h'
    exact (Fact.out : ¬IsUnit (p : X.O)) h'
  obtain ⟨N, u, hu, hz⟩ := hHT U.T'.V hp U.t.G U.P.D U.P.A U.P.U.toUnifPre (chD Ch.ch) U.F U.x
    U.chart X.C X.v X.O X.ints U.ι' U.ι'_local
  refine ⟨N, u, fun k => ?_, fun z hv f => hz z (by rwa [map_natCast]) f⟩
  rw [← U.law_eq]
  exact hu k

end GlobalTheory.CharDepth
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonempty_uniformised_formal_chart_algebraic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ∀ (p : ℕ) [Fact p.Prime] (X : ValExt T p), Nonempty (UnifChart Ch X) := by
  first | exact @GlobalTheory.CharDepth.nonempty_unifChart | exact GlobalTheory.CharDepth.nonempty_unifChart | (intros; apply GlobalTheory.CharDepth.nonempty_unifChart <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroPairing_eq_bigCell_integral_topVectors : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CptCoef p.T.base H' → KB.CutWord P p.l0 w → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H' = ∫ c, inner ℂ (tv p H' w c) (tv p H w c) := by
  first | exact @GlobalTheory.TopVecPol.beta_eq_integral_inner_tv | exact GlobalTheory.TopVecPol.beta_eq_integral_inner_tv | (intros; apply GlobalTheory.TopVecPol.beta_eq_integral_inner_tv <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.tv_approx_tendsto_L2_cutoff : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → (∀ n : ℕ, MemLp (tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w) 2 volume) ∧ MemLp (tv p (D.cutF p.T.base χ f ε) w) 2 volume ∧ Tendsto (fun n : ℕ => eLpNorm (tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w - tv p (D.cutF p.T.base χ f ε) w) 2 volume) atTop (𝓝 0) := by
  first | exact @GlobalTheory.TopVec.tv_approx_tendsto_L2 | exact GlobalTheory.TopVec.tv_approx_tendsto_L2 | (intros; apply GlobalTheory.TopVec.tv_approx_tendsto_L2 <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.ShortBasisAt

theorem rootDiscriminantDegreeRatio_eq (D : D7) : rr0 D = D.host.rdE ^ 2 / (4 * D.R.f) := by
  unfold rr0 Formalism.BasicNotions.Host.rdE
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), GlobalTheory.PinNum.finrank_host]
  push_cast
  congr 1
  · congr 1
    ring
  · ring

theorem exists_shortBasis : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (ho : OverLa la T'.V io e) (z : IntFr (T.Q.Xo j) T.Q.c T' io) (hz : z.IsAlg) (η : T.G.PY j (WeightAlgebra.resCh la)) (hl : T.G.lies j la T' io z η), letI := T.Q.H.starRing; ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z) (P : PELUnif (maximalIdeal T'.V) C.I.G) (ϖ : T'.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ (r : ℕ) (Φ M0 : ℝ), ShortBasis Q r Φ M0 ∧ r ≤ 2 * D.R.f * D.R.m ∧ M0 ≤ 2 * Real.sqrt (2 * D.R.f * D.R.m) ∧ (D.R.m ≤ j → M0 = 0 ∧ Φ = 0) ∧ Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl)) := by
  intro D T h j hj la T' io e ho z hz η hl C P ϖ hϖ Q hQ
  by_cases hm : j < D.R.m
  · obtain ⟨h0, r, b, hr, h1, h2⟩ :=
      GlobalTheory.PhiTie.exists_reduced_basis_le_phiCy D T h j hj hm la T' io e z ho hz η hl C P ϖ hϖ Q hQ
    have hφ : (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl) =
        (ramOverZ la : ℝ) * (T.G.P.loc (T.G.dat j) (WeightAlgebra.resCh la)).phiCy η := by
      rw [← H1algLink.eWL_eq la]
      exact ConjugateMinimaInstance.phiC_rec_eq (recPJ h j hj) hm la _
    rw [hφ, rootDiscriminantDegreeRatio_eq]
    have hr' : (r : ℝ) ≤ 2 * D.R.f * D.R.m := by exact_mod_cast hr
    refine ⟨r, _, _, ⟨by positivity, b, h1, h2⟩, hr, by push_cast; exact le_rfl, fun h' => absurd hm (not_lt.2 h'), ?_⟩
    gcongr
  · letI := io.toAlgebra
    letI := T.Q.H.starRing
    obtain ⟨ρ, hρ, -, hq⟩ := GlobalTheory.ToricRank.rank_le_signature D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T'.V C.I.G P
      C.I.t' C.I.m2 z.1.x C.I.m1 inferInstance
    have hq' : ρ ≤ D.R.m - j := hq.trans_eq (h.toLawsCore.pins.2.2.2 j hj).2.1
    have h0 : Module.finrank ℤ P.D.toPre.X = 0 := by
      rw [hρ, show ρ = 0 by omega, mul_zero]
    have hφ : (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl) = 0 := if_neg hm
    refine ⟨0, 0, 0, ⟨le_rfl, Module.finBasisOfFinrankEq ℤ _ h0, fun i => i.elim0, fun i => i.elim0⟩, Nat.zero_le _,
      by positivity, fun _ => ⟨rfl, rfl⟩, ?_⟩
    rw [hφ]; simp

end GlobalTheory.ShortBasisAt
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.IntegralPull

theorem exists_finite_ext_all_models_uniformised {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr)
    (y : IntFr Xo c T io) (e : ℕ) (la : HeightOneSpectrum (𝓞 c.F)) (ho : OverLa la T.V io e) (hy : y.IsAlg) :
    ∃ (T' : CDVR) (φ : T.V →+* T'.V) (φF : T.Fr →+* T'.Fr) (e₁ : ℕ) (z' : IntFr Xo c T' (φF.comp io)),
      Function.Injective φ ∧ IsLocalHom φ ∧ φ.Finite ∧
      φF.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp φ ∧
      0 < e₁ ∧ OverLa la T'.V (φF.comp io) (e * e₁) ∧ z'.IsAlg ∧
      (letI := io.toAlgebra; letI := (φF.comp io).toAlgebra
        FrMap ({ φF with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 z'.1) ∧
      ∀ I : IntData Xo c T' (φF.comp io) z'.1, ∃ P : PELUnif (maximalIdeal T'.V) I.G, P.TorsionIso := by
  have : Finite (ResidueField T.V) := hy
  obtain ⟨G, t, m1, m2, -⟩ := y.2.2
  obtain ⟨W, _, _, _, hc, _, hf, hi, hr, hS⟩ := GlobalTheory.UnifAfterExt.exists_split_baseChange T.V G.G G.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  let T' : Formalism.L2.Pj.CDVR := { V := W }
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  obtain ⟨φ, hφ⟩ : ∃ φ : T.Fr →+* T'.Fr, ∀ v, φ (algebraMap T.V T.Fr v) = algebraMap T'.V T'.Fr (algebraMap T.V W v) :=
    ⟨IsFractionRing.lift hj, IsFractionRing.lift_algebraMap hj⟩
  obtain ⟨r, hr0, hv⟩ := exists_index (V' := T'.V) (algebraMap T.V W) φ hφ
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c _ _ ψ y.1
  obtain ⟨p, χ, y₀, hy₀⟩ := y.2.1
  let y' : IntFr Xo c T' (φ.comp io) :=
    ⟨z, ⟨p, ψ.comp χ, y₀, Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ χ ψ y₀ y.1 z hy₀ hz⟩,
      integral_baseChange T T' io (φ.comp io) _ hi ψ hφ y.1 z hz y.2.2⟩
  refine ⟨T', algebraMap T.V W, φ, r, y', hi, hl, RingHom.finite_algebraMap.2 hf, RingHom.ext hφ, hr0, ?_, hr, hz,
    fun I => exists_unif_of_split T T' _ φ hφ m1 m2 hz.1 I.m1 I.m2 hS⟩
  rw [Nat.mul_comm]
  exact ho.bc φ hr0 hv

end GlobalTheory.IntegralPull
end
