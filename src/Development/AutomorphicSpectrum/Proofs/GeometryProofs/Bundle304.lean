module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle171
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle155
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle080
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle224
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle271
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamily
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GenericFrameRootOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle302
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle262
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle209
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle288
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle301
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle164
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle110
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle213
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

@[expose] public section

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_generic_frame_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h) (V : ValuationSubring RM.Ω), letI := Small.cstAlg Or; ∀ (ψ : C.R →ₐ[c.F] RM.Ω) (z : FrPt Xo c RM.Ω) (d : Ix Dw → (RM.Ω)ˣ), FrMap ψ C.y z → FrBor d Fr.y₀ z → (∀ x, ψ x ∈ V) → ∀ cc : (k : RM.K) → RM.ι k, (∀ k, RM.y ⟨k, cc k⟩ ≠ 0) → (∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, cc k⟩ ∈ V) → ∀ r : RootIx Dw, ∃ v : Vˣ, ((d (Small.rootFrameIx Dw r) ^ HodgeCpt.rootSgn Dw r : (RM.Ω)ˣ) : RM.Ω) = ((v : V) : RM.Ω) * ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) * Or.e r) := by
  first | exact @ModelDimension.generic_frame_root_origin | exact ModelDimension.generic_frame_root_origin
end

section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_flagModel_isIso_of_open_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (M' : GlobalTheory.FlagMod.FlagModel Y) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, M'.YY ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ M'.YY)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A M'.π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∀ M : GlobalTheory.FlagMod.FlagModel Y, ∃ h : M.YY ⟶ M'.YY, IsIso h ∧ h ≫ M'.π = M.π := by
  first | exact @GlobalTheory.CompanionTheory.FlagMod.flagModel_iso_cells | exact GlobalTheory.CompanionTheory.FlagMod.flagModel_iso_cells | (intros; apply GlobalTheory.CompanionTheory.FlagMod.flagModel_iso_cells <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp.RootNef

theorem nefOnFibres_of_wt {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : Top.RootModel Ψ N) (n : Ψ × Fin N → ℤ)
    (h : ∀ p : ℕ, p.Prime → M.NefAt p (fun τ i => -(n (τ, i) : ℝ)) 0) :
    NefOnFibres (mCoordIdeal M.y) (∑ r, n r • M.xdeg r) := by
  intro W h1 h2 h3 h4
  obtain ⟨d, -, he⟩ := LevelTowerAlt.geoNum_one_lin W
  have h5 := h _ (PB.prime_charOf_of_ne_zero h1.1 h3) W ⟨h1, h2, rfl, h4⟩
  unfold Top.RootModel.curveDeg at h5
  rw [Fintype.sum_option] at h5
  simp only [Top.RootModel.coef, Top.RootModel.line, zero_div, zero_mul, zero_add, neg_neg, M.x_deg, he] at h5
  rw [he]
  have : ∑ k, (∑ r, n r • M.xdeg r) k * d k = ∑ r, n r * ∑ k, M.xdeg r k * d k := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [_root_.mul_assoc]
  rw [this]
  exact_mod_cast h5

theorem nefThreshold_of_gap_one {Ψ : Type} [Fintype Ψ] {N j : ℕ} (mu : Top.Wt Ψ N) (b : ℕ) (hb : 4 * Fintype.card Ψ + 2 ≤ b)
    (h1 : ∀ τ i, |mu τ i| ≤ 1) (h2 : ∀ τ, Top.gap j mu τ = 1) : Top.NefThreshold j b mu := by
  intro τ
  have hn : ‖mu‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => h1 τ i
  have hb' : 4 * (Fintype.card Ψ : ℝ) + 2 ≤ b := by exact_mod_cast hb
  rw [h2]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Ψ)]

end GlobalTheory.CompanionTheory.Ar.Cusp.RootNef


theorem _root_.GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → Fl.RootLines M.xdeg e → NefOnFibres (mCoordIdeal M.y) (∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => D.p ≤ (i : ℕ)), M.xdeg (τ, i)) ∧ NefOnFibres (mCoordIdeal M.y) (-∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => (i : ℕ) < D.p), M.xdeg (τ, i)) := by
  intro hG E _ _ _ H D Xo l c Y S _ M 𝔐 Fl e hY hp hq hS hS' hR
  obtain ⟨Yl, hg, hYl, -, -, hdom⟩ := hY
  have key : ∀ mu : Top.Wt (CMType H) (D.p + D.q), Top.Dominant mu → (∀ τ i, |mu τ i| ≤ 1) →
      (∀ τ, Top.gap D.p mu τ = 1) → ∀ r : ℕ, r.Prime → M.NefAt r mu 0 := by
    intro mu hd h1 h2 r hr
    by_cases hrS : r ∈ S
    · exact GlobalTheory.T.root_lines_weight_bound_of_free hG.2.2.2.2.2.2.1 E H D l (Xo l) c _ _ Y S M 𝔐 Fl e r hrS (hS r hrS) hR mu hd
    · obtain ⟨a1, a2, a3⟩ := hS' r hr hrS
      exact GlobalTheory.T.hodge_cpt_global_nef_bound E H D Xo Yl (fun p W hp hW i => ⟨((hYl p W hp hW).2 i).1, ((hYl p W hp hW).2 i).2.1⟩)
        l c hg Y hdom hp hq S M 𝔐 Fl e hR r hr a3 hrS a1 mu hd (GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefThreshold_of_gap_one mu r a2 h1 h2)
  have g1 : D.p - 1 < D.p + D.q := by omega
  have g2 : D.p < D.p + D.q := by omega
  have g3 : ¬ D.p ≤ D.p - 1 := by omega
  have g4 : D.p - 1 < D.p := by omega
  constructor
  · have := GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefOnFibres_of_wt M (fun r => if D.p ≤ (r.2 : ℕ) then 1 else 0) (key _ ?_ ?_ ?_)
    · convert this using 1
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_filter, ite_smul, one_smul, zero_smul]
    · intro τ a b hab
      have : (a : ℕ) ≤ b := hab
      dsimp only
      split_ifs <;> first | omega | norm_num
    · intro τ i
      dsimp only
      split_ifs <;> norm_num
    · intro τ
      simp [Top.gap, Top.ent, g1, g2, g3]
  · have := GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefOnFibres_of_wt M (fun r => if (r.2 : ℕ) < D.p then -1 else 0) (key _ ?_ ?_ ?_)
    · convert this using 1
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_filter, ite_smul, neg_smul, one_smul, zero_smul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · intro τ a b hab
      have : (a : ℕ) ≤ b := hab
      dsimp only
      split_ifs <;> first | omega | norm_num
    · intro τ i
      dsimp only
      split_ifs <;> norm_num
    · intro τ
      simp [Top.gap, Top.ent, g1, g2, g4]
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrArch

theorem scale_facts {t₀ : ℝ} (h0 : 0 < t₀) (h1 : t₀ < 1) {s : ℝ} (hs : 0 < s)
    (hs' : s ≤ Real.sqrt (1 / Real.log (1 / t₀))) :
    0 < Top.scale s ∧ Top.scale s ≤ t₀ ∧ Real.log (Real.log (1 / Top.scale s)) = 2 * Real.log (1 / s) := by
  have hL : 0 < Real.log (1 / t₀) := Real.log_pos (by rw [lt_div_iff₀ h0]; linarith)
  have hs2 : 0 < s ^ 2 := by positivity
  have e1 : Real.log (1 / Top.scale s) = (s ^ 2)⁻¹ := by
    rw [Top.scale, one_div, Real.log_inv, Real.log_exp, neg_neg]
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · have hsq : s ^ 2 ≤ 1 / Real.log (1 / t₀) := by
      have := Real.sq_sqrt (show 0 ≤ 1 / Real.log (1 / t₀) by positivity)
      nlinarith [Real.sqrt_nonneg (1 / Real.log (1 / t₀))]
    have hinv : Real.log (1 / t₀) ≤ (s ^ 2)⁻¹ := by
      rw [le_inv_comm₀ hL hs2]
      simpa using hsq
    have : Real.log t₀ = -Real.log (1 / t₀) := by rw [one_div, Real.log_inv, neg_neg]
    rw [Top.scale, ← Real.exp_log h0, this]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [e1, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
    push_cast
    ring

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem comp_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (S₀ : Finset ℕ)
    (R : Top.RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (o₀ : RootOrigin Y S₀ R Fx) (hJ₀ : o₀.Re.J = ⊤)
    (hflat : ∀ (τ : CMType H) (p : Fin (D.p + D.q)), (p : ℕ) + 1 = D.p + D.q → ∀ t,
      ReciprocityTheory.AnForm.M.IsPsh Sys.A ((Sys.potT (some (τ, p)) t).rsmul (-1)) ∧
        ReciprocityTheory.AnForm.M.IsPsh Sys.A (Sys.potT (some (τ, p)) t)) :
    ∃ C s₀ : ℝ, 0 ≤ C ∧ 0 < s₀ ∧ s₀ ≤ 1 ∧ ∀ (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q))
      (o : RootOrigin Y S M Fx) (i : R.Ω →+* M.Ω), o.Re.J = ⊤ → i.comp o₀.g = o.g →
      ∀ (mu : Top.Wt (CMType H) (D.p + D.q)) (s : ℝ), Top.Dominant mu → ‖mu‖ ≤ 2 → 0 < s → s ≤ s₀ →
        Ht.ArchBetween M R i (fun j => j.elim 1 fun r => i (o₀.e r) / o.e r) (Top.scale s) mu s
          (-(C * Real.log (1 / s)) - C) C := by
  classical

  have hb : ∀ r : RootIx D, ∃ Cr : ℝ, ∀ z : (Σ k, R.ι k) → ℂ, (∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) →
      |Real.log ((o₀.Re.ref (some r)).h z) + ∑ k ∈ Finset.Iic r.2, Real.log ((R.x 1 (r.1, k)).h z)| ≤ Cr := by
    rintro ⟨τ, p⟩
    refine GlobalTheory.T.log_hermitian_sum_bounded R.K R.ι (Fin (D.p + D.q)) (o₀.Re.ref (some (τ, p))) (fun k => R.x 1 (τ, k)) (Finset.Iic p)
      (o₀.Re.ref_smooth _) (fun k => R.x_smooth _ _) ?_
    rw [o₀.fund_deg]
    simp only [R.x_deg]
  choose Cb hCb using hb
  obtain ⟨B₁, hB₁⟩ := Finite.exists_le Cb
  have hc : ∀ r : RootIx D, ∃ Cr : ℝ, (r.2 : ℕ) + 1 = D.p + D.q → ∀ t, 0 < t → t ≤ Sys.t₀ → ∀ x,
      |Sys.phT (some r) t x| ≤ Cr := by
    rintro ⟨τ, p⟩
    by_cases hp : (p : ℕ) + 1 = D.p + D.q
    · obtain ⟨C, hC⟩ := GlobalTheory.T.potential_bounded_psh_both _ _ Sys (some (τ, p)) (hflat τ p hp)
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose Cc hCc using hc
  obtain ⟨C₁, hC₁⟩ := Finite.exists_le Cc
  have ht₀ := (Sys.reg none).1
  have ht₁ := (Sys.reg none).2.1
  set Creg := |Sys.C| with hCreg
  set B₀ := max B₁ 0 with hB₀
  set C₀ := max C₁ 0 with hC₀
  set F : ℝ := (Fintype.card (CMType H) : ℝ) with hF
  have hF0 : 0 ≤ F := Nat.cast_nonneg _
  have hCreg0 : 0 ≤ Creg := abs_nonneg _
  have hB0 : 0 ≤ B₀ := le_max_right _ _
  have hC00 : 0 ≤ C₀ := le_max_right _ _
  refine ⟨F * (8 * Creg + 6 * B₀ + 2 * C₀), min 1 (Real.sqrt (1 / Real.log (1 / Sys.t₀))), by positivity,
    lt_min one_pos (Real.sqrt_pos.2 (one_div_pos.2 (Real.log_pos (by rw [lt_div_iff₀ ht₀]; linarith)))),
    min_le_left _ _, ?_⟩
  intro S M o i hJ hi mu s hmu hmu2 hs hs'
  obtain ⟨hs1, hst⟩ := le_min_iff.1 hs'
  obtain ⟨hsc0, hsct, hsll⟩ := scale_facts ht₀ ht₁ hs hst
  have hlog : 0 ≤ Real.log (1 / s) := Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith)
  obtain ⟨f, hf, hfp⟩ := GlobalTheory.T.root_origin_compare_second E H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi hJ hJ₀
  have hG := (GlobalTheory.T.root_origin_compare_third E H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi)
  have hunit : ∀ j, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R j)
      ((fun j => j.elim 1 fun r => i (o₀.e r) / o.e r : Option (RootIx D) → M.Ω) j) := by
    rintro (_ | r)
    · exact hG.1
    · refine GlobalTheory.T.root_model_flag_compare E H D l Xo c Y S S₀ M R o.𝔐 o₀.𝔐 o.Fl o₀.Fl i o.e o₀.e ?_ ?_ o.lines o₀.lines r
      · rw [o.g_over, o₀.g_over, ← hi, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      · intro s' k
        have hd : dualMap o.g = (dualMap i).comp (dualMap o₀.g) := by
          rw [← hi]
          ext a <;> simp [dualMap]
        rw [o.g_flag, o₀.g_flag, hd, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  refine GlobalTheory.T.join_coords_unit_values _ _ M R i _ _ mu s _ _ f hf hunit ?_
  intro w hw hwf val hval
  obtain ⟨x, x', z₁, z₂, ho₁, ho₂, hπ, hop, hc₁, hc₂, hi₁, hi₂⟩ := hfp w hw hwf
  obtain ⟨hw₁, hw₂⟩ := (GlobalTheory.T.join_model_points_project _ _ M R i).2.2.1 ℂ w hw
  have hw₁' : (fun p => w (Cmp.joinInl M.ι R.ι p)) ∈ mcPts M.P := by
    rw [← Small.LineModel.ptsOver_complex]; exact hw₁
  have hw₂' : (fun p => w (Cmp.joinInr M.ι R.ι p)) ∈ mcPts R.P := by
    rw [← Small.LineModel.ptsOver_complex]; exact hw₂
  set w₁ := fun p => w (Cmp.joinInl M.ι R.ι p) with hw₁d
  set w₂ := fun p => w (Cmp.joinInr M.ι R.ι p) with hw₂d
  have hsing : ∀ r, ‖val (some r)‖ * (o₀.sing r).h w₂ = (o.sing r).h w₁ := fun r =>
    GlobalTheory.T.root_origin_compare_first E H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi z₁ z₂ w hw hc₁ hc₂ hi₁ hi₂ r _ (hval (some r))
  have hpos : ∀ r, 0 < ‖val (some r)‖ := fun r => by
    have h1 := (o.sing r).pos w₁ hw₁'.1
    have h2 := (o₀.sing r).pos w₂ hw₂'.1
    rw [← hsing r] at h1
    exact (mul_pos_iff_of_pos_right h2).1 h1
  have hid := GlobalTheory.T.root_origin_point_compare E H D l Xo c Y S S₀ M R Sys Fx o o₀ x x' w₁ w₂ (fun r => ‖val (some r)‖) (Top.scale s) hsc0 hsct hw₁'
    hw₂' ho₁ ho₂ hπ hop fun r => ⟨hpos r, hsing r⟩

  have hA : Real.log (M.A.h w₁) - Real.log (R.A.h w₂) - Real.log ‖val none‖ = 0 := by
    have h1 := hG.2 w hw _ (hval none)
    have hp1 := M.A.pos w₁ hw₁'.1
    have hp2 := R.A.pos w₂ hw₂'.1
    have hv : 0 < ‖val none‖ := by
      rw [h1] at hp1
      exact (mul_pos_iff_of_pos_right hp2).1 hp1
    rw [h1, Real.log_mul hv.ne' hp2.ne']
    ring
  set Dd : RootIx D → ℝ := fun r => Real.log ((M.x (Top.scale s) r).h w₁) - Real.log ((R.x 1 r).h w₂) -
    Real.log ‖val (some r)‖ with hDd
  have hsum : ∑ j, M.coef mu s j * (Real.log ((M.line (Top.scale s) j).h w₁) - Real.log ((R.line 1 j).h w₂) -
      Real.log ‖val j‖) = ∑ τ, ∑ p, -mu τ p * Dd (τ, p) := by
    rw [Fintype.sum_option, Fintype.sum_prod_type]
    have : M.coef mu s none * (Real.log ((M.line (Top.scale s) none).h w₁) - Real.log ((R.line 1 none).h w₂) -
        Real.log ‖val none‖) = 0 := by
      show _ * (Real.log (M.A.h w₁) - Real.log (R.A.h w₂) - Real.log ‖val none‖) = 0
      rw [hA, mul_zero]
    rw [this, zero_add]
    rfl
  have hτ : ∀ τ : CMType H, -(4 * (2 * Creg * Real.log (1 / s) + B₀) + 2 * (C₀ + B₀)) ≤ ∑ p, -mu τ p * Dd (τ, p) ∧
      ∑ p, -mu τ p * Dd (τ, p) ≤ 4 * (Creg + B₀) + 2 * (C₀ + B₀) := by
    intro τ
    have hbr : ∀ p : Fin (D.p + D.q), |Real.log ((o₀.Re.ref (some (τ, p))).h w₂) +
        ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h w₂)| ≤ B₀ := fun p =>
      ((hCb (τ, p) w₂ hw₂'.1).trans (hB₁ _)).trans (le_max_left _ _)
    have hY : ∀ p : Fin (D.p + D.q), -∑ k ∈ Finset.Iic p, Dd (τ, k) =
        Sys.phT (some (τ, p)) (Top.scale s) (o.Re.π x) + (Real.log ((o₀.Re.ref (some (τ, p))).h w₂) +
          ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h w₂)) := fun p => hid τ p
    refine GlobalTheory.T.abel_summation_bound _ (mu τ) (fun p => Dd (τ, p)) (Creg + B₀) (2 * Creg * Real.log (1 / s) + B₀) (C₀ + B₀)
      (by positivity) (by positivity) (by positivity) (hmu τ) (fun p => ?_) (fun p _ => ?_) (fun p hp => ?_)
    · have := ((norm_le_pi_norm (mu τ) p).trans (norm_le_pi_norm mu τ)).trans hmu2
      simpa [Real.norm_eq_abs] using this
    · obtain ⟨-, hup, -, hlow, -⟩ := (Sys.reg (some (τ, p))).2.2 _ hsc0 hsct
      have h1 := hup (o.Re.π x)
      have h2 := hlow (o.Re.π x)
      rw [hsll] at h2
      have h3 := abs_le.1 (hbr p)
      have h4 := le_abs_self Sys.C
      rw [hY p]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.2 h4) hlog]
      · linarith
    · have h1 := (hCc (τ, p) hp _ hsc0 hsct (o.Re.π x)).trans ((hC₁ _).trans (le_max_left C₁ 0))
      rw [← abs_neg, hY p]
      exact (abs_add_le _ _).trans (add_le_add h1 (hbr p))
  rw [hsum]
  constructor
  · have := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => (hτ τ).1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    rw [← hF] at this
    nlinarith [this, mul_nonneg hF0 (mul_nonneg hB0 hlog), mul_nonneg hF0 (mul_nonneg hC00 hlog), mul_nonneg hF0 hCreg0]
  · have := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => (hτ τ).2
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    rw [← hF] at this
    nlinarith [this, mul_nonneg hF0 hCreg0]

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem arch_between : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (g : Top.GoodOrigin Y T), ∃ C s₀ : ℝ, 0 < s₀ ∧ ∀ (B : ℕ) (a : T.Comp) (i : (g.R a).Ω →+* (T.M B a).Ω), i.comp (g.refOr a).g = (g.Or B a).g → ∀ (mu : Top.Wt (CMType H) (D.p + D.q)) (s : ℝ), Top.Dominant mu → ‖mu‖ ≤ 2 → 0 < s → s ≤ s₀ → Ht.ArchBetween (T.M B a) (g.R a) i (fun j => j.elim 1 fun r => i ((g.refOr a).e r) / (g.Or B a).e r) (Top.scale s) mu s (-(C * Real.log (1 / s)) - C) C := by
  intro E _ _ _ H D l Xo c Y _ T g
  have hcomp := fun a : T.Comp => comp_bound E H D l Xo c Y ∅ (g.R a) (g.Sys a) (g.Fx a) (g.refOr a) (g.ref_top a)
    (fun τ p hp t => g.flat a τ p hp t)
  choose C s₀ hC0 hs₀ hs₁ hmain using hcomp
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_min_image Finset.univ s₀ ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  refine ⟨∑ a, C a, s₀ a₀, hs₀ a₀, ?_⟩
  intro B a i hi mu s hmu hmu2 hs hs' z hz val hval
  have hCa : C a ≤ ∑ a, C a := Finset.single_le_sum (fun a _ => hC0 a) (Finset.mem_univ a)
  have hsa : s ≤ s₀ a := hs'.trans (ha₀ a (Finset.mem_univ a))
  have hlog : 0 ≤ Real.log (1 / s) :=
    Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith [hs₁ a])
  have := hmain a _ _ (g.Or B a) i (g.smooth B a).1 hi mu s hmu hmu2 hs hsa z hz val hval
  obtain ⟨h1, h2⟩ := this
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_right hCa hlog], by linarith⟩

end GlobalTheory.CompanionTheory.Ar.OrArch
end
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi


theorem _root_.GlobalTheory.T.integral_frame_subalgebra_relay : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntAll Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → T.FinRes → ∀ y : IntFr Xo c T io, letI := io.toAlgebra; ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (ψ : S →ₐ[c.F] T.Fr) (z₀ : FrPt Xo c T.Fr) (t₀ : Ix Dw → T.Frˣ), FrMap ψ w z₀ → FrBor t₀ z₀ y.1 → ∃ (F : Finset S) (n : ℕ), ∀ ψ' : S →ₐ[c.F] T.Fr, (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) → ∀ z' : FrPt Xo c T.Fr, FrMap ψ' w z' → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ letI := io'.toAlgebra; ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z'' : FrPt Xo c T'.Fr) (t' : Ix Dw → T'.Frˣ), FrMap φ z' z'' ∧ FrBor t' z'' y'.1 ∧ (∀ x : T.Fr, x ≠ 0 → vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), vV T'.V ((t' (some ⟨τ, i⟩) : T'.Frˣ) : T'.Fr) * (e₀ : ℤ) = (e' : ℤ) * vV T.V ((t₀ (some ⟨τ, i⟩) : T.Frˣ) : T.Fr) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.integral_frame_subalgebra_relay | exact GlobalTheory.CompanionTheory.Relay.integral_frame_subalgebra_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.integral_frame_subalgebra_relay <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.local_system_split_fibres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Yl : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Yl p W hp hW i).SplitFibres ∧ (Yl p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Y (Yl p W hp hW ⟨l, c, hg p hp⟩) b) → ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ), p.Prime → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (τ : CMType H) (a : ⋀[Ω]^D.p 𝔐.Li) (b : ⋀[Ω]^D.q 𝔐.Li), a ≠ 0 → b ≠ 0 → (∃ x f, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b x f) → NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b) (p : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.numTriv_offS | exact GlobalTheory.CompanionTheory.Ar.Flat.numTriv_offS | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.numTriv_offS <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.boundary_chart_log_period_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ z ∈ Flat.punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem | exact GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.log_periods_riemann_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : LogPeriods n a C.g Λ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_isRiem | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_isRiem | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_isRiem <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.comp_laws_root_model_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → letI := Small.cstAlg Or; ∃ (φ : Om Z →ₐ[c.F] RM.Ω) (P : FrPt Xo c RM.Ω) (t : Ix Dw → (RM.Ω)ˣ), FrMap φ (genFr h Z) P ∧ FrBor t P Fr.y₀ ∧ (letI := φ.toRingHom.toAlgebra; Module.finrank (Om Z) RM.Ω = Or.Fl.deg) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.comp_laws_root_model_relay | exact GlobalTheory.CompanionTheory.Relay.comp_laws_root_model_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.comp_laws_root_model_relay <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.intersection_datum_degree_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (bb : ∀ τ, Fin Dc.N → W τ) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (lam : Ω), (∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)) → Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)) → (∀ τ, LinearIndependent Ω (s τ)) ∧ (Lat.tens (fun τ => detLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y (muTwDeg Hd B) (lam⁻¹ * ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.intersection_datum_degree_sum | exact GlobalTheory.CompanionTheory.Relay.intersection_datum_degree_sum | (intros; apply GlobalTheory.CompanionTheory.Relay.intersection_datum_degree_sum <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.twisted_hodge_tie_compare : HodgeComparisonCompatibility → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ) (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'), Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) → IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ : M.K → K) (v : (Σ k, M.ι k) → Σ k, ι k) (κ' : M'.K → K) (v' : (Σ k, M'.ι k) → Σ k, ι k) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, ι k) → Ω) (b : MRing ι) (d : K → ℕ), IsBlockMap κ v ∧ IsBlockMap κ' v' ∧ mCoordIdeal (y ∘ v) = M.P ∧ mCoordIdeal (y ∘ v') = M'.P ∧ IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * T.Fl.deg = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * T'.Fl.deg ∧ ∀ (r : CMType H × Fin (D.p + D.q)) (L L' : HermLine ι), IsPullHerm κ v (T.sing r) L → IsPullHerm κ' v' (T'.sing (π r.1, r.2)) L' → IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} L L' := by
  first | exact @GlobalTheory.CompanionTheory.Relay.twisted_hodge_tie_compare | exact GlobalTheory.CompanionTheory.Relay.twisted_hodge_tie_compare | (intros; apply GlobalTheory.CompanionTheory.Relay.twisted_hodge_tie_compare <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem vs_tower : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given →
    Top.GoodTowerExistsX → Top.VolumeTheoremX → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [DecidableEq (CMType H)] (II : IntersectionSystem), IsFullIntersectionSystem II → FnAlgClosed (Xo := Xo) (c := c) → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → 1 ≤ Dw.q → 3 * Dw.q + 1 ≤ Dw.p + Dw.q → (2 * discr E * l.M').natAbs.primeFactors.card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 → ∃ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp), o.Extra ∧ CompOf o.toTowerOrigin κ ∧ T.bad = (2 * discr E * l.M').natAbs.primeFactors ∧ T.Proportional ∧ T.T1 II ∧ T.VolEq ∧ T.MeanSlope II C (hostRd E) (hostLval H) := by
  intro hG hTow hVol
  obtain ⟨C, hC, hV⟩ := hVol
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ H Dw l Xo c _ II hII hcl hgood hA hq hpq hcard
  have hN : 1 ≤ Dw.p + Dw.q := by omega
  have hp : 1 ≤ Dw.p := by omega
  obtain ⟨Xf, rfl⟩ : ∃ Xf : ∀ l' : Level H, Moduli Dw l', Xf l = Xo := by
    classical
    refine ⟨Function.update (fun l' => (GlobalTheory.Moduli.moduli_scheme_exists E H Dw l' hN).some) l Xo, ?_⟩
    simp
  obtain ⟨Y, hY⟩ := GlobalTheory.CompanionTheory.Ar.Rec.exists_isGlobal E H Dw Xf l c hN hgood hA
  obtain ⟨T, o, hX⟩ := hTow E H Dw Xf l c Y hY (GlobalTheory.T.split_components_of_alg_closed E H Dw l (Xf l) c Y hcl) hp hq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.tower_components_equiv_of_given E H Dw l (Xf l) c Y T o.toTowerOrigin hG
  have hbad : T.bad = (2 * discr E * l.M').natAbs.primeFactors := by
    have hne : 2 * discr E * l.M' ≠ 0 := by
      intro h0
      obtain ⟨r, hr, hrp⟩ := Nat.exists_infinite_primes (T.bad.sup id + 1)
      have hmem : r ∈ T.bad := (o.bad_iff r).2 ⟨hrp, by rw [h0]; exact dvd_zero _⟩
      have := Finset.le_sup (f := id) hmem
      simp only [id] at this
      omega
    ext r
    rw [o.bad_iff, Nat.mem_primeFactors, Int.natCast_dvd]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, by simpa using hne⟩
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
  have hc : T.bad.card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 := by
    rw [hbad]; exact hcard
  obtain ⟨h1, h2, h3, -, -, h6⟩ := hV E H Dw Xf l c Y T o II hY hX hII hq hpq hc
  exact ⟨Y, T, o, κ, hX, hκ, hbad, h1, h3, h2, h6⟩

end GlobalTheory.CompanionTheory.Ar.Plug
end
