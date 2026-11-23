module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Formalism.HermitianCurvature.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle162
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorEigenspace
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053
public import Formalism.PeriodIntegrals.Bundle024
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WaveBallEstimateWeightedDualAlt
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WaveInputsOfHypothesesGlobal
public import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle075
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle184
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.BigCellDerivativeExpansionOfIsDSOfCoefOf
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hodgeTate_inclusion_integralChart : ∀ (p : ℕ) [Fact p.Prime], HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), y.IsAlg → ∃ (N : ℕ) (u : Fin N → PS X.O 1 (chD Ch.ch)), (∀ k, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (u k)) ∧ ∀ z : X.O, X.v (algebraMap X.O X.C z) ^ (p - 1) ≤ X.v (p : X.C) → ∀ f : Fin (chD Ch.ch) → X.O, z • f ∈ Submodule.span X.O (Set.range fun k => dl (u k)) := by
  first | exact @GlobalTheory.CharDepth.hodgeTate_inclusion_intChart | exact GlobalTheory.CharDepth.hodgeTate_inclusion_intChart | (intros; apply GlobalTheory.CharDepth.hodgeTate_inclusion_intChart <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_word_cutF_eq_integral_inner_tv :
    P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ f ε₁)) w) (D.cutF p.T.base χ f ε₂) = ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε₂) w c) (tv p (D.cutF p.T.base χ f ε₁) w c) := by
  intro hA Cb
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.levelZeroPairing_compactApproximants_cauchy_bound
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.tv_approx_tendsto_L2_cutoff hA Cb
  refine ⟨max C₁ C₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hD hχ hf hCC hth hw hlen ε₁ ε₂ hε₁ hε₂
  have hmono : ∀ Cc : ℝ, Cc ≤ max C₁ C₂ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro Cc hC
    refine le_trans ?_ hth
    gcongr
  have hL := (h₁ P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w χ f A N hχ hf hCC (hmono _ (le_max_left _ _)) hlen
    ε₁ ε₂ hε₁ hε₂).1
  obtain ⟨a₁, b₁, c₁⟩ := h₂ Wp Wq P p f χ A N w hD hχ hf hCC (hmono _ (le_max_right _ _)) hw hlen ε₁ hε₁
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Wp Wq P p f χ A N w hD hχ hf hCC (hmono _ (le_max_right _ _)) hw hlen ε₂ hε₂
  have hR := tendsto_integral_inner_of_tendsto_eLpNorm_two _ _ _ _ _ _ _ a₁ a₂ b₁ b₂ c₁ c₂
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  have hc : ∀ ε : ℝ, 0 < ε → KB.CptCoef p.T.base (fun g : B.Mat P.k P.r =>
      ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) •
        D.cutF p.T.base χ f ε g) := fun ε hε =>
    Formalism.FourierDecayAlt.P.PBE.cutCpt P p.T.base f χ ε
      (fun (n : ℕ) (g : B.Mat P.k P.r) =>
        ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ))
      hχ hε hf (fun _ _ => rfl) n
  exact (GlobalTheory.T.levelZeroPairing_eq_bigCell_integral_topVectors hA Wp Wq P p Cb _ _ w hD (hc ε₁ hε₁) (hc ε₂ hε₂) hw).symm

end GlobalTheory
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_characters_bounded_minor_eigenspace : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), Function.Injective tau → FrobOrd V io ι tau → ∀ (s : ZMod d) (n : ℕ) (w : Fin n → Fin (Dw.mult (tau s)) → C), IsSat V w → ∃ χ : Fin n → PS C 1 (chD C3.ch), (∀ ρ, IntS V (χ ρ) ∧ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh Y.B.G.F (χ ρ)) ∧ V.v (Matrix.of fun ρ q : Fin n => ∑ x, (∑ i, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ ρ) i * ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) * w q x).det ≤ (((∑' i : ℕ, ((V.l : ℝ) ^ (-((i : ℝ) + 1))) * (Dw.mult (ComplexEmbedding.conjugate (tau (s + ((i + 1 : ℕ) : ZMod d)))) : ℝ)) : ℝ) : WithTop ℝ) := by
  first | exact @GlobalTheory.CharMinor.exists_chars_minor_le | exact GlobalTheory.CharMinor.exists_chars_minor_le | (intros; apply GlobalTheory.CharMinor.exists_chars_minor_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.exists_short_basis_uniformization_lattice : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (ho : OverLa la T'.V io e) (z : IntFr (T.Q.Xo j) T.Q.c T' io) (hz : z.IsAlg) (η : T.G.PY j (WeightAlgebra.resCh la)) (hl : T.G.lies j la T' io z η), letI := T.Q.H.starRing; ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z) (P : PELUnif (maximalIdeal T'.V) C.I.G) (ϖ : T'.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ (r : ℕ) (Φ M0 : ℝ), ShortBasis Q r Φ M0 ∧ r ≤ 2 * D.R.f * D.R.m ∧ M0 ≤ 2 * Real.sqrt (2 * D.R.f * D.R.m) ∧ (D.R.m ≤ j → M0 = 0 ∧ Φ = 0) ∧ Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl)) := by
  first | exact @GlobalTheory.ShortBasisAt.exists_shortBasis | exact GlobalTheory.ShortBasisAt.exists_shortBasis | (intros; apply GlobalTheory.ShortBasisAt.exists_shortBasis <;> assumption)
end

section

open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem discreteSeries_coefficient_expansion_bound_ball : ∀ (C : ℝ), 0 ≤ C → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (a₁ : ℕ) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → Num P.k P.r lam P.u' b bv ga h q0 → P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0 → R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) → PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f → Formalism.FourierDecayAlt.P.CutBP.BigCellDerivativeExpansion p f b (C / 2 + 6) a₁ := by
  intro C hC P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 a₁ ν₀ R0 f hN hN' hT hT' hq hR hf
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  have H : BranchingSupport.HypsG := CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap
  have hK : PI.KFinSmooth := H.1.2.2.1
  have hDG := CompanionTheory.WaveGrid.WEnd.isDG_of_num hN (by omega) hR
  have hC' : CompanionTheory.WaveGrid.BallW.CoefOf R0 f := fun l l' =>
    (GlobalTheory.isCoef_of_translate_smul_exists hK P.k P.r _ _ R0 Wp Wq l l' hR).1 f hf
  exact Gp91.WG.bigCellDerivativeExpansion_of_isDS_of_coefOf H C hC P Wp Wq p lam b bv ga h q0 a₁ R0 f ν₀ hN hN' hT hT' hq hDG hC'

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem family_cast_iff {V : Type} (P : ∀ s : ℕ, (Fin s → V) → Prop) {n s : ℕ} (h : n = s) (g : Fin s → V) :
    P n (fun i => g (Fin.cast h i)) ↔ P s g := by
  subst h; rfl

theorem colength_bound_at_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), y.IsAlg → ∀ (f : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H f vd → ∃ xs : (E →+* ℂ) → NNReal, (∀ τ, InPsi H τ → HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) (xs τ)) ∧ (open Classical in (X.v ((p : ℕ) : X.C) : ℝ) ^ ((f : ℝ) * Dw.q * (1 + vd / 2)) ≤ ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ)) := by
  intro p _ hAV E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch X hy f vd hTP
  classical
  obtain ⟨U⟩ := GlobalTheory.T.nonempty_uniformised_formal_chart_algebraic_point E H Dw l Xo c T io y Ch hy p X
  obtain ⟨τT, -, hty, hinj, hrt, -⟩ := GlobalTheory.T.exists_cmType_embeddings_into_valuation_ring E H l c T io p X
  set τO : (E →+* ℂ) → (𝓞 E →+* X.O) := fun τ => X.ι.comp (τT τ) with hτO
  have heig := fun τ => (GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers E H Dw l Xo c T io y Ch p X τO hty τ).1
  obtain ⟨n, w, vdi, hwn, hsum, he, hu, hb, hvd⟩ := hTP X.C X.v X.O X.ints τO hinj hrt
  choose t hvd using hvd
  choose s hs hst using fun (i : Fin n) (j : Fin (w i).n) => he i (t i j : 𝓞 E →+* X.O) (t i j).2
  have hp : ∀ τ, InPsi H τ → Dw.p = Dw.mult τ := fun τ h => by
    unfold Datum.mult; exact (if_pos h).symm
  have hq : ∀ τ, ¬ InPsi H τ → Dw.q = Dw.mult τ := fun τ h => by
    unfold Datum.mult; exact (if_neg h).symm
  have hact : actMap U.ι' U.act = fun a i => MvPowerSeries.map X.ι (Ch.actT a i) := funext U.act_eq
  have hnu : ¬ IsUnit ((p : U.T'.V)) := fun h => X.nonunit.out (by have h' := h.map U.ι'; rwa [map_natCast] at h')
  have key := fun i0 : Fin n => hAV U.T'.V hnu U.t.G U.P.D U.P.A U.P.U.toUnifPre _ U.F U.x U.chart (𝓞 E)
    U.t.act.toRingAct U.P.oD U.P.oA U.P.lin U.act U.acts X.C X.v X.O X.ints U.ι' U.ι'_local (w i0) (t i0) (vdi i0) (hvd i0) Dw.p Dw.q
    (fun j i k => X.ι (Ch.uvecT ⟨s i0 j, Fin.cast (hp _ (hs i0 j)) i⟩ k))
    (fun j => by
      rw [hact, hst i0 j]
      exact (family_cast_iff (fun _ g => IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO (s i0 j)) g)
        (hp _ (hs i0 j)) (fun i k => X.ι (Ch.uvecT ⟨s i0 j, i⟩ k))).2 (heig (s i0 j)))
    (fun σ hσ => by
      obtain ⟨τ, hτ, rfl⟩ := hb i0 σ hσ
      rw [hact]
      exact ⟨_, (family_cast_iff (fun _ g => IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO τ) g)
        (hq _ hτ) (fun i k => X.ι (Ch.uvecT ⟨τ, i⟩ k))).2 (heig τ)⟩)
  choose xs hxs hle using key
  let σs : (Σ i : Fin n, Fin (w i).n) → (E →+* ℂ) := fun z => s z.1 z.2
  have hmem : ∀ i j, τO (s i j) ∈ Emb (O := X.O) (w i).e := fun i j => by rw [← hst i j]; exact (t i j).2
  have hsinj : Function.Injective σs := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' : s i j = s i' j' := h
    obtain rfl : i = i' := (hu _ (hs i j)).unique (hmem i j) (by rw [h']; exact hmem i' j')
    have : j = j' := by
      apply (t i).injective
      apply Subtype.ext
      rw [hst i j, hst i j', h']
    rw [this]
  have hssurj : ∀ τ, InPsi H τ → ∃ z, σs z = τ := fun τ h => by
    obtain ⟨i, hi, -⟩ := hu τ h
    refine ⟨⟨i, (t i).symm ⟨τO τ, hi⟩⟩, hinj ?_⟩
    have := hst i ((t i).symm ⟨τO τ, hi⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  let xz : (Σ i : Fin n, Fin (w i).n) → NNReal := fun z => xs z.1 z.2
  refine ⟨Function.extend σs xz (fun _ => 1), ?_, ?_⟩
  · intro τ hτ
    obtain ⟨⟨i, j⟩, rfl⟩ := hssurj τ hτ
    rw [hsinj.extend_apply, ← U.law_eq]
    exact (family_cast_iff (fun _ g => HasAF X.v (U.F.mapF U.ι') g (xs i j))
        (hp _ (hs i j)) (fun i' k => X.ι (Ch.uvecT ⟨s i j, i'⟩ k))).1 (hxs i j)
  · have hprod : ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), ((Function.extend σs xz (fun _ => 1) τ : NNReal) : ℝ) =
        ∏ z, (xz z : ℝ) := by
      symm
      refine Finset.prod_bij (fun z _ => σs z) (fun z _ => by simpa using hs z.1 z.2) (fun j _ j' _ h => hsinj h)
        (fun τ hτ => ?_) (fun j _ => by rw [hsinj.extend_apply])
      obtain ⟨j, hj⟩ := hssurj τ (by simpa using hτ)
      exact ⟨j, Finset.mem_univ _, hj⟩
    have h2 : algebraMap X.O X.C (p : X.O) = (p : X.C) := map_natCast _ _
    have hpp : p.Prime := Fact.out
    have hr0 : (0 : ℝ) < (X.v (p : X.C) : ℝ) := by
      have : X.v (p : X.C) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hpp.ne_zero)
      exact_mod_cast pos_iff_ne_zero.2 this
    have hr1 : (X.v (p : X.C) : ℝ) ≤ 1 := by
      have hle : X.v (p : X.C) ≤ 1 := by rw [← h2]; exact X.ints.map_le_one _
      exact_mod_cast hle
    have h1 : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      rw [div_le_one (by linarith)]; linarith
    have hi : ∀ i, (X.v (p : X.C) : ℝ) ^ (((w i).n : ℝ) * Dw.q * (1 + vdi i / 2)) ≤ ∏ j, (xs i j : ℝ) := fun i => by
      have h3 := NNReal.coe_le_coe.2 (hle i)
      rw [h2, NNReal.coe_rpow, NNReal.coe_prod] at h3
      refine le_trans (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 ?_) h3
      have : (0 : ℝ) ≤ ((w i).n : ℝ) * Dw.q := by positivity
      nlinarith
    have hexp : (f : ℝ) * Dw.q * (1 + vd / 2) = ∑ i, ((w i).n : ℝ) * Dw.q * (1 + vdi i / 2) := by
      have a1 : (f : ℝ) = ∑ i, ((w i).n : ℝ) := by rw [← hwn]; push_cast; rfl
      have a2 : ∑ i, ((w i).n : ℝ) * Dw.q * (1 + vdi i / 2) =
          Dw.q * (∑ i, ((w i).n : ℝ)) + Dw.q / 2 * ∑ i, ((w i).n : ℝ) * vdi i := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [a2, hsum, ← a1]; ring
    have hfin : (X.v (p : X.C) : ℝ) ^ ((f : ℝ) * Dw.q * (1 + vd / 2)) ≤ ∏ z, (xz z : ℝ) := by
      rw [hexp, Real.rpow_sum_of_pos hr0, Fintype.prod_sigma]
      exact Finset.prod_le_prod₀ (fun i _ => (Real.rpow_pos_of_pos hr0 _).le) fun i _ => hi i
    convert hfin using 1

end GlobalTheory.CharDepth
end
