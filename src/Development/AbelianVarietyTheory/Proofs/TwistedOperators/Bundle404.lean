module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle018
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle376
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle395
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.discrete_series_multiplicity : (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ (tensor D.sp.cm.sig V.gram fa ff) := by
  first | exact @GlobalTheory.TestFnCusp.isCuspidalOp_tensor | exact GlobalTheory.TestFnCusp.isCuspidalOp_tensor | (intros; apply GlobalTheory.TestFnCusp.isCuspidalOp_tensor <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

theorem _root_.GlobalTheory.T.typeHypothesis_forms_agree : ∀ (D : D7) (V : HSp D) (T : TypeDataG V), NoFixed T → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T := by
  first | exact @GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed | exact GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed | (intros; apply GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.splitFrames_transport_localLatticeIsometry : ∀ (D : D7) (V V' : HSp D) (hr : V'.rank = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → (∀ g, j g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ s : SplitAt D.sp.cm.sig V.gram (frameLat V) v, ∃ s' : SplitAt D.sp.cm.sig V'.gram (frameLat V') v, (∀ g a b, (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr)) ∧ ∀ (k : Kv V v) (k' : Kv V' v), (k' : GLoc D.sp.cm.sig V'.gram v) = j k → ∀ a b, (s'.red k').1 a b = (s.red k).1 (a.cast hr) (b.cast hr) := by
  first | exact @GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj | exact GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj | (intros; apply GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.exists_centralizer_measures_from_unitaryTorus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∃ ea ef e, IsCentProd L (ratEmb σ J γ) ea ef e ∧ (∃ 𝓣, IsFundamentalDomain ((ratPts σ J).subgroupOf (cent (ratEmb σ J γ))) 𝓣 e ∧ e 𝓣 = torVol P dt) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin r → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), gam h = proj σ J v (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dtf v)) f c ↔ HasOrbInt μ (proj σ J v (ratEmb σ J γ)) (ef v) f c) ∧ ∀ (w : InfinitePlace F) (x : plusUnits P w.Completion) (φ : (w.Completion ⊗[F] Fld P) ≃ₗ[w.Completion ⊗[F] E] (Fin r → w.Completion ⊗[F] E)) (h : IsIsom P w.Completion J x.1.1 φ), gam h = projArch σ J w (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dta w)) f c ↔ HasOrbInt μ (projArch σ J w (ratEmb σ J γ)) (ea w) f c := by
  first | exact @GlobalTheory.TrEllMeas.exists_isCentProd_torus | exact GlobalTheory.TrEllMeas.exists_isCentProd_torus | (intros; apply GlobalTheory.TrEllMeas.exists_isCentProd_torus <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

def rowSizes (D : D7) : Sizes where
  k := D.R.k
  m := D.R.m
  s := sLen D
  t := D.R.t
  k_pos := by have := D.R.m_add_three_le_k; omega
  k_even := D.R.k_even
  m_pos := by have := D.R.two_le_m; omega
  m_even := D.R.m_even
  s_odd := odd_sLen D
  t_odd := D.R.t_odd

theorem rowSizes_nR (D : D7) (j : ℕ) : (rowSizes D).nR j = rankX D j := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  simp only [Sizes.nR, rowSizes, rankX, rankP, nRk, sLen, Ranks.r]
  zify [show 1 ≤ D.R.k + D.R.m by omega, show 1 ≤ D.R.k + D.R.m - 1 + 6 by omega] at *
  ring_nf

theorem rowSizes_nC (D : D7) (i : ℕ) : (rowSizes D).nC i = rankV D i D.R.m := by
  simp only [Sizes.nC, rowSizes, rankV, Ranks.r]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_top (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) : (G.V (.top j)).rank = (rowSizes D).nR j := by
  rw [rowSizes_nR]
  rcases j with _ | j
  · exact ((G.sp.P_is D.R.m le_rfl).rank).trans (by simp [rankX])
  · exact (G.sp.X_is (j + 1) (by omega) hj).rank

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_gridM (G : GridData L sc) {i : ℕ} (hi : i ≤ D.R.m) : (G.V (.grid i D.R.m)).rank = (rowSizes D).nC i := by
  rw [rowSizes_nC]
  rcases i with _ | i
  · show (columnBlock L D.R.m).sp.rank = _
    rw [colY_m]
    exact D.sp.X'_rank.trans (by simp [rankV, Ranks.rankX'])
  · exact (G.sp.V_is (i + 1) D.R.m (by omega) hi le_rfl).rank

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

def rowEntries (D : D7) (C : ℝ) (τ : D.what₂.Tau) : Entries (rowSizes D) where
  a l := (num D C τ).a l
  c i := (num D C τ).cen (i + 1)
  v i := (num D C τ).v (i + 2)
  u i := (num D C τ).vHalf (i + 2)
  b j := (num D C τ).b (j + 1)
  e j := (num D C τ).e (j + 1)

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def trCol (G : GridData L sc) (j : Fin D.R.m) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ]
      Pol D.what₂.Tau ((rowSizes D).nR j) ((rowSizes D).nR (j + 1)) :=
  MvPolynomial.rename fun x => (x.1, Fin.cast (rank_top G (by omega)) x.2.1, Fin.cast (rank_top G j.2.le) x.2.2)

def trRow (G : GridData L sc) (i : Fin D.R.m) :
    PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank →ₐ[ℂ]
      Pol D.what₂.Tau ((rowSizes D).nC i) ((rowSizes D).nC (i + 1)) :=
  MvPolynomial.rename fun x => (x.1, Fin.cast (rank_gridM G (by omega)) x.2.2, Fin.cast (rank_gridM G i.2.le) x.2.1)

end GlobalTheory.RowReal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin



noncomputable section

namespace GlobalTheory.StairUnit

theorem exists_mem_modul_notMem {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ P.S0) : ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) u ∈ P.modul sc := by
  have h : ∀ v' : GlobalTheory.FinPl.Pl D, ∃ x : 𝓞 D.host.F, x ∉ v.asIdeal ∧ (v' ∈ P.S0 → x ∈ v'.asIdeal) := by
    intro v'
    by_cases h' : v' ∈ P.S0
    · have hn : ¬ v'.asIdeal ≤ v.asIdeal := fun hle =>
        hv (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle) ▸ h')
      obtain ⟨x, hx, hx'⟩ := Set.not_subset.1 hn
      exact ⟨x, hx', fun _ => hx⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun h => absurd h h'⟩
  choose x hx hx' using h
  refine ⟨∏ v' ∈ P.S0, x v' ^ P.depth sc v', fun hu => ?_, ?_⟩
  · haveI := v.isPrime
    obtain ⟨v', -, h'⟩ := Ideal.IsPrime.prod_mem_iff.1 hu
    exact hx v' (v.isPrime.mem_of_pow_mem _ h')
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun v' h' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h1 : x v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := by rw [P.under_w h']; exact hx' v' h'
    exact h1

theorem mem_span_of_mem_mul {E : Type} [Field E] [NumberField E] [StarRing E] {A B A' B' C : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x ∈ A', star x ∈ A) (hB : ∀ x ∈ B', star x ∈ B) {t : E} (ht : t ∈ A' * B' * C) :
    t ∈ Submodule.span (𝓞 E) {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c} := by
  refine FractionalIdeal.mul_induction_on ht (fun x hx c hc => ?_) fun x y => Submodule.add_mem _
  refine FractionalIdeal.mul_induction_on (C := fun x => x * c ∈ Submodule.span (𝓞 E)
    {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c}) hx (fun a ha b hb => ?_) fun x y hx hy => ?_
  · exact Submodule.subset_span ⟨_, hA a ha, _, hB b hb, c, hc, by rw [star_mul', star_star, star_star]⟩
  · rw [add_mul]; exact Submodule.add_mem _ hx hy

theorem exists_unit_mem_span : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ρ : ℕ) (p : Fin (2 * ρ + 2 - 1)) (q : Fin (2 * ρ + 1 - 1)), p.1 + q.1 = 2 * ρ → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ ((u : D.host.F) : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c} := by
  intro D T L sc G ρ p q hpq v hv
  obtain ⟨u, hu, hum⟩ := exists_mem_modul_notMem G.pl sc v hv
  refine ⟨u, hu, ?_⟩
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨hAA, hAAc⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hne : ∀ {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}, I ≠ 0 → (∀ x, x ∈ J ↔ star x ∈ I) → J ≠ 0 := by
    intro I J hI hJ h0
    apply hI
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h2 := h0 _ ((hJ (star y)).2 (by rwa [star_star]))
    rwa [star_eq_zero] at h2
  have hAb := hne hA hconj
  have hAAb := hne hAA hAAc
  have hB : ∀ x ∈ (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹,
      star x ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q := by
    intro x hx
    have h1 := (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ q.rev).2 (star x)
    rw [Fin.rev_rev, star_star] at h1
    exact h1.2 hx
  have key : D.host.AAbar * (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹ *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p =
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    have hq := q.2
    have e1 : 2 * ρ + 1 - 1 - q.rev.1 = q.1 + 1 := by rw [Fin.val_rev]; omega
    have e2 : q.rev.1 + 1 = p.1 := by rw [Fin.val_rev]; omega
    have e3 : 2 * ρ + 2 - 1 - p.1 = q.1 + 1 := by omega
    have e4 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
        D.host.AAbar * (G.pl.stAbar sc)⁻¹ := by
      rw [Places.stAbar, mul_inv, inv_inv, mul_inv_cancel_left₀ hAAb]
    unfold stairId
    rw [e1, e2, e3, e4, pow_succ (G.pl.stAbar sc) p.1]
    have h1 : G.pl.stA sc ^ (q.1 + 1) ≠ 0 := pow_ne_zero _ hA
    have h2 : G.pl.stAbar sc ^ p.1 ≠ 0 := pow_ne_zero _ hAb
    field_simp
  have hmem : ((u : D.host.F) : D.host.E) ∈
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, hum, rfl⟩
  rw [← key] at hmem
  have h := mem_span_of_mem_mul (fun x hx => (hAAc x).1 hx) hB hmem
  simp only [hs] at h
  exact h

end GlobalTheory.StairUnit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.modulus_inf_conj_le_span_typePrimes_product : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), G.modul ⊓ D.host.conj • G.modul ≤ Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} := by
  first | exact @GlobalTheory.ModulConj.modul_inf_conj_le | exact GlobalTheory.ModulConj.modul_inf_conj_le | (intros; apply GlobalTheory.ModulConj.modul_inf_conj_le <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitaryEmbeddingProperties

def ex {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (h : Matrix (Fin r) (Fin r) R) : Matrix (Fin n) (Fin n) R :=
  1 + P * (h - 1) * Q

section Gen

variable {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)

theorem ex_mul_P (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : ex P Q h * P = P * h := by
  rw [ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one,
    add_sub_cancel]

theorem ex_mul_N (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : ex P Q h * (1 - P * Q) = 1 - P * Q := by
  have e : Q * (1 - P * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul, sub_self]
  rw [ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (P * (h - 1)), e, Matrix.mul_zero, add_zero]

theorem ex_mul (hQP : Q * P = 1) (a b : Matrix (Fin r) (Fin r) R) : ex P Q (a * b) = ex P Q a * ex P Q b := by
  have e3 : P * (a - 1) * Q * (P * (b - 1) * Q) = P * ((a - 1) * (b - 1)) * Q := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  have e4 : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by noncomm_ring
  rw [ex, ex, ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, e3, e4]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

theorem ex_one : ex P Q 1 = 1 := by simp [ex]

theorem ex_map {R' : Type} [CommRing R'] (φ : R →+* R') (h : Matrix (Fin r) (Fin r) R) :
    (ex P Q h).map φ = ex (P.map φ) (Q.map φ) (h.map φ) := by
  simp only [ex, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_sub _ (map_sub φ),
    Matrix.map_one _ (map_zero φ) (map_one φ)]

end Gen

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

def qM (d : HermitianOrthogonalExtensionData A B c ε) : Matrix (Fin A.rank) (Fin B.rank) D.host.E :=
  A.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram)

theorem qM_mul (d : HermitianOrthogonalExtensionData A B c ε) : qM d * frameMat B A d.ι = 1 := by
  rw [qM, Matrix.mul_assoc, GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom,
    Matrix.nonsing_inv_mul _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit]

theorem qM_mul_map {R : Type} [CommRing R] (φ : D.host.E →+* R) (d : HermitianOrthogonalExtensionData A B c ε) :
    (qM d).map φ * (frameMat B A d.ι).map φ = 1 := by
  rw [← Matrix.map_mul, qM_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem unitaryEmbedding_matrix_formula (d : HermitianOrthogonalExtensionData A B c ε) (h : GA D A) :
    (matHom B (stabilizerEmbedding d h)).1 = ex ((frameMat B A d.ι).map (incA D)) ((qM d).map (incA D)) (matHom A h).1 := by
  have hr := (embRel_iff d h _).2 rfl
  set P := frameMat B A d.ι
  set C := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * B.gram
  have hG : C * P = A.gram := GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom
  set N : Matrix (Fin B.rank) (Fin B.rank) D.host.E := 1 - P * qM d with hN
  have hC : C * N = 0 := by
    rw [hN, qM, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hG,
      Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul, sub_self]
  have h1 : (matHom B (stabilizerEmbedding d h)).1 * N.map (incA D) = N.map (incA D) := by
    ext i j
    exact congr_fun (hr.2 (fun k => N k j) (by funext k; exact congr_fun (congr_fun hC k) j)) i
  have hNm : N.map (incA D) = (1 : Matrix (Fin B.rank) (Fin B.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) -
      HMul.hMul (P.map (incA D)) ((qM d).map (incA D)) := by
    rw [hN, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine GlobalTheory.AutFunCounterexample.split_gen (incA D) P (qM d) _ _ ?_ ?_
  · rw [h1, hNm, ex_mul_N _ _ (qM_mul_map _ d)]
  · rw [hr.1, ex_mul_P _ _ (qM_mul_map _ d)]

theorem unitaryEmbedding_mul (d : HermitianOrthogonalExtensionData A B c ε) (g h : GA D A) : stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h := by
  apply GlobalTheory.AutFunCounterexample.GA_ext
  rw [map_mul, Units.val_mul, unitaryEmbedding_matrix_formula, unitaryEmbedding_matrix_formula, unitaryEmbedding_matrix_formula, map_mul, Units.val_mul,
    ex_mul _ _ (qM_mul_map _ d)]

theorem unitaryEmbedding_rational (d : HermitianOrthogonalExtensionData A B c ε) (γ : GA D A) (hγ : γ ∈ GQ A) : stabilizerEmbedding d γ ∈ GQ B := by
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have q2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram = A.gram * qM d := by
    rw [qM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul]
  set P := frameMat B A d.ι
  set Q := qM d
  have q3 : Q * P = 1 := qM_mul d
  have q1 : B.gram * P = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Q * A.gram := by
    have := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) q2
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, GlobalTheory.AutFunCounterexample.gram_herm, GlobalTheory.AutFunCounterexample.cT_cT,
      GlobalTheory.AutFunCounterexample.gram_herm] at this
  let γ' : GL (Fin B.rank) D.host.E := ⟨ex P Q γE, ex P Q (γE⁻¹ : GL (Fin A.rank) D.host.E),
    by rw [← ex_mul _ _ q3, Units.mul_inv, ex_one], by rw [← ex_mul _ _ q3, Units.inv_mul, ex_one]⟩
  have hu : γ' ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) B.gram :=
    GlobalTheory.AutFunCounterexample.ext_unitary _ B.gram A.gram P Q q1 q2 q3 _ hγE
  refine Subgroup.mem_subgroupOf.2 ⟨γ', hu, Units.ext ?_⟩
  have hA : (matHom A γ).1 = (γE : Matrix (Fin A.rank) (Fin A.rank) D.host.E).map (incA D) := by
    exact (congrArg Units.val e).symm
  show (ex P Q γE).map (incA D) = (matHom B (stabilizerEmbedding d γ)).1
  rw [unitaryEmbedding_matrix_formula, hA, ex_map]


set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_unitaryEmbedding (d : HermitianOrthogonalExtensionData A B c ε) : Continuous (stabilizerEmbedding d) := by
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hf : ∀ {f : GA D A → Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)}, Continuous f →
      Continuous fun h => ex ((frameMat B A d.ι).map (incA D)) ((qM d).map (incA D)) (f h) := fun hc =>
    continuous_const.add ((continuous_const.matrix_mul (hc.sub continuous_const)).matrix_mul continuous_const)
  have hv : Continuous fun h : GA D A => (matHom A h).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun h : GA D A => (matHom A h⁻¹).1 :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  let φ : GA D A →* GA D B := MonoidHom.mk' (stabilizerEmbedding d) (unitaryEmbedding_mul d)
  have hc : Continuous fun h => matHom B (stabilizerEmbedding d h) := by
    refine Units.continuous_iff.2 ⟨(hf hv).congr fun h => (unitaryEmbedding_matrix_formula d h).symm, (hf hi).congr fun h => ?_⟩
    have e : (stabilizerEmbedding d h)⁻¹ = stabilizerEmbedding d h⁻¹ := (map_inv φ h).symm
    rw [← map_inv (matHom B), e, unitaryEmbedding_matrix_formula]
  exact Continuous.subtype_mk (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig B.gram) hc fun h => (stabilizerEmbedding d h).2

theorem unitaryEmbedding_continuous_hom_rational : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), Continuous (stabilizerEmbedding d) ∧
    (∀ g h, stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h) ∧ ∀ γ ∈ GQ A, stabilizerEmbedding d γ ∈ GQ B :=
  fun d => ⟨continuous_unitaryEmbedding d, unitaryEmbedding_mul d, unitaryEmbedding_rational d⟩

end GlobalTheory.UnitaryEmbeddingProperties
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.unitaryLatticeCongruence_mem_conjugateIdeal_inf : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (g : GL (Fin V.rank) (Lev.EAf D)), g ∈ congLev D.sp.cm V.gram Λ 𝔪 → g ∈ congLev D.sp.cm V.gram Λ (𝔪 ⊓ D.host.conj • 𝔪) := by
  first | exact @GlobalTheory.CongSelfDual.congLev_conj | exact GlobalTheory.CongSelfDual.congLev_conj | (intros; apply GlobalTheory.CongSelfDual.congLev_conj <;> assumption)
end
