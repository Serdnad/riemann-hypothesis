module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle308
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle157
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle167
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenOfUnit
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle265
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBound
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
public import Development.WeilBound.CoreStatements.HodgeTatePoints.QacInt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle005
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle307
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionHeight
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
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.component_data_hodge_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (a : Fin Dc.nCharts), ∀ t₀ ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (L : ActPeriods E (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ g Λ) (π : Equiv.Perm (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)))) (ρ : ℝ) (σ : CMType H → (𝓞 E →+* ℂ)) (pt : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (d : MuFrameAt Hd ((Dc.chart a).γ t₀)) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (b : CMType H → Fin (Dc.N - Dc.j) → (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → Fin g → ℂ), 0 < ρ ∧ IsCMFam σ ∧ Or.IsSmallPart d s ∧ IsEigFrames (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) L.B σ b ∧ (∀ u ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), t₀ + (ρ : ℂ) • (u ∘ π) ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) ∧ InFrameDomain Dc.y d.c d.f ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ CoordsAt Or.𝔐.ξ Dc.y (pt u) ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ Or.𝔐.LabVal (pt u) Or.sm σ ∧ (Or.𝔐.Interior (pt u) ↔ u ∈ Flat.punct _ a₀ 1)) ∧ (∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le), ∃ v : CMType H × Fin (Dc.N - Dc.j) → (epsAt (pt (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ⟶ Or.𝔐.t.G), (∀ i, Or.𝔐.M.ValAt _ (s i.1 i.2) (v i)) ∧ FibreLatVec Or.𝔐.t _ (L.riem w hw) (fun i => b i.1 i.2 (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ChartFree.exists_actPeriods_chart | exact GlobalTheory.CompanionTheory.Ar.Cusp.ChartFree.exists_actPeriods_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ChartFree.exists_actPeriods_chart <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.uniform_norm_section_count : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw), ∀ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), ∃ N : ℕ, 0 < N ∧ (N : (T.M B b).Ω) * (gauge Rd u * Rd.φ (evC h Z f)) ∈ chartLatNm (T.M B b).y (degOf (T.M B b) u) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.cusp_mem_chartLatNm | exact GlobalTheory.CompanionTheory.Ar.Plug.cusp_mem_chartLatNm | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.cusp_mem_chartLatNm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)


theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) (sm : CMType H → CMType H ⊕ CMType H) (m : ℕ) (s : CMType H → Fin m → 𝔐.Li) (a : K → ℤ) (e₀ : Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → 𝔐.IsCover dg → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, LinearIndependent Ω (s τ) ∧ Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → NefOnFibres (mCoordIdeal y) a := by
  intro hG hW E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 dg sm m s a e₀ hY hp hq hcov hS hS' hsm hs hdeg
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  obtain ⟨M, 𝔐', Fl, e, i, g, bk, bx, j, hbk, hy, hd, hS2, hR, hj, hli, hV⟩ :=
    GlobalTheory.T.hodge_comp_cover_primes hW E H D Xo l c Y S Ω K J y 𝔐 dg hcov
      (fun p hp hdv => by by_contra h; exact (hS' p hp h).1 hdv) hS
  haveI : CharZero M.Ω := charZero_of_injective_ringHom i.injective
  have hNef : _ ∧ _ :=
    GlobalTheory.T.nefOnFibres_block_xdeg_sums_of_rootLines hG E H D Xo l c Y S M 𝔐' Fl e
      hY hp hq hS2 hS' hR
  obtain ⟨n1, n2⟩ := hNef
  have hb₀ : ∀ σ, LinearIndependent M.Ω (Fl.b σ) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h
  have hu := fun τ => GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.det_pull (L := 𝔐.V (sm τ)) hd hj hli (hs τ).1 (hs τ).2 (𝔐.vb (sm τ)) (hb₀ (sm τ))
    (by rw [← hV]; exact Fl.sub (sm τ))
  choose u hu0 hu using hu
  let a' : M.K → ℤ := Function.extend bk a 0
  have ha : ∀ k, a' (bk k) = a k := fun k => hbk.extend_apply _ _ k
  have ha' : ∀ k', k' ∉ Set.range bk → a' k' = 0 := fun k' h => Function.extend_apply' _ _ _ h
  have hB := GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.deg_pull hu0 hd 𝔐.tie.cover hu hbk hy ha ha' hdeg
  simp only [← hV] at hB
  have hgr : ∀ (r : CMType H × Fin (D.p + D.q)) (σ : Σ s, Fin (labelRk D s)), HodgeCpt.rootIdx D r = σ →
      ((𝔐'.V σ.1).gr (Fl.b σ.1) σ.2).IsDegOn Set.univ M.y (HodgeCpt.rootSgn D r • M.xdeg r)
        (e r ^ HodgeCpt.rootSgn D r) := by
    rintro r _ rfl
    refine GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.deg_untens ?_ (hR r)
    unfold HodgeCpt.rootSgn
    split_ifs <;> norm_num
  have hA : ∃ A e₁, (Lat.tens (fun τ => detLat (𝔐'.V (sm τ)) (Fl.b (sm τ))) fun _ => -1).IsDegOn Set.univ M.y A e₁ ∧
      NefOnFibres (mCoordIdeal M.y) A := by
    have hdet : ∀ σ, detLat (𝔐'.V σ) (Fl.b σ) = Lat.tens (fun k => (𝔐'.V σ).gr (Fl.b σ) k) fun _ => 1 := fun σ =>
      GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor _ _ _ _ _ _ _ (hb₀ σ) (Fl.sub σ)
    simp only [hdet]
    rcases hsm with rfl | rfl
    · have h1 : ∀ τ (k : Fin D.p), HodgeCpt.rootIdx D (τ, Fin.castAdd D.q k) = ⟨.inl τ, k⟩ := fun τ k => by
        unfold HodgeCpt.rootIdx
        rw [dite_eq_left (show ((Fin.castAdd D.q k : Fin _) : ℕ) < D.p from k.2)]
        rfl
      refine ⟨_, _, Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _ (fun τ => Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _
        (fun k => hgr _ _ (h1 τ k)) _) _, ?_⟩
      convert n2 using 1
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Fin.sum_univ_add]
      simp [HodgeCpt.rootSgn]
    · have h1 : ∀ τ (k : Fin D.q), HodgeCpt.rootIdx D (τ, Fin.natAdd D.p k.rev) = ⟨.inr τ, k⟩ := fun τ k => by
        unfold HodgeCpt.rootIdx
        rw [dite_eq_right (by simp)]
        congr 1
        apply Fin.ext
        have := k.2
        simp only [Fin.val_natAdd, Fin.val_rev]
        omega
      refine ⟨_, _, Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _ (fun τ => Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _
        (fun k => hgr _ _ (h1 τ k)) _) _, ?_⟩
      convert n1 using 1
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Fin.sum_univ_add]
      have h2 : ∀ k : Fin D.p, ¬ D.p ≤ (k : ℕ) := fun k => not_le.2 k.2
      have h3 := Equiv.sum_comp Fin.revPerm fun k : Fin D.q => M.xdeg (τ, Fin.natAdd D.p k)
      simp [HodgeCpt.rootSgn, h2, ← h3]
  obtain ⟨A, e₁, hA1, hA2⟩ := hA
  have hN := GlobalTheory.CompanionTheory.Relay.nef_degree_scale_invariant hI _ M.Ω M.K M.ι M.y 𝔐'.ξ _ A a' e₁ _ _ 𝔐'.tie
    (Finset.prod_ne_zero_iff.2 fun τ _ => hu0 τ) hA1 hB hA2
  obtain ⟨c₀, hc₀⟩ := 𝔐'.tie.cover ⟨genPt 𝔐'.ξ, specializes_rfl⟩
  exact GlobalTheory.T.coords_reindex_degree hI Ω M.Ω i K M.K J M.ι y M.y bk bx a a' hbk hy (fun k => ⟨_, GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.chart_ne hc₀ k⟩) ha ha' hN
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.global_pair_sum_gram_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), Top.IsGlobal Xo l c Y → ∀ (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → (∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord y) cc p → unitAt 𝔐.ξ p f → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb p) → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FramePeriods.exists_isFramePeriods | exact GlobalTheory.CompanionTheory.Ar.FramePeriods.exists_isFramePeriods | (intros; apply GlobalTheory.CompanionTheory.Ar.FramePeriods.exists_isFramePeriods <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl


theorem _root_.GlobalTheory.CompanionTheory.Relay.key_over_lie_basis_degree : KeyBadSt → ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ → GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (th : t.PP.L.Sec) (x : KeyIn L) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ t.G)), KeyOver (algebraMap (𝓞 L) L) t th x v → IsLieBasis v → KeyDeg.NonVan t.G.hom th → IsIntegral ℤ (κ L x : L) := by
  first | exact @PositivityTheory.HtPt.Qac.keydeg_integral | exact PositivityTheory.HtPt.Qac.keydeg_integral
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.key_bad_reduction_holds : KeyBadSt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KP.key_bad | exact GlobalTheory.CompanionTheory.Ar.Sl.KP.key_bad | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KP.key_bad <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cmpPair_of_inputs : PB.Inputs → CmpSt → HodgeComparisonCompatibility → ThetaUnifAV → CmpPair := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair | exact GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.cusp_intersection_height : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (w : (Σ k, J k) → L) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), Or.Good → CoordsAt Or.𝔐.ξ Dc.y (spMap (algebraMap (𝓞 L) L) ≫ z) w → Or.𝔐.IsLinPtOf z P MV A → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → ∃ x : (L →+* ℂ) → ℝ, (∀ e : L →+* ℂ, Or.PhiWeight (spMap e ≫ spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => e (w p)) (x e)) ∧ Ht.ptHt (fun k => (muTwDeg Hd B k : ℝ)) (twW (D := Dc) B fun _ => 0) L w + (∑ e : L →+* ℂ, x e) / Module.finrank ℚ L = -A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.g_height | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.g_height | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.g_height <;> assumption)
end
