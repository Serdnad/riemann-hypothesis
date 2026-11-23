module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle175
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle018
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle176
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle030
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle034
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle174
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle108
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle155
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle547
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle196
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem exists_const_of_forall_unit_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {O : Set V} (hO : IsOpen O) (hc : IsPreconnected O) (hne : O.Nonempty) {ι : Type} (P Q : ι → V → ℂ)
    (hP : ∀ j, DifferentiableOn ℂ (P j) O) (hQ : ∀ j, DifferentiableOn ℂ (Q j) O)
    (h : ∀ x ∈ O, ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ j, P j x = u * Q j x) :
    ∃ c : ℂˣ, ∀ j, ∀ x ∈ O, P j x = c * Q j x := by
  by_cases h0 : ∃ j, ∃ x₁ ∈ O, Q j x₁ ≠ 0
  · obtain ⟨j₀, x₁, hx₁, hq⟩ := h0
    obtain ⟨u₁, hu₁, hPu⟩ := h x₁ hx₁
    have hu0 : u₁ ≠ 0 := by
      intro e
      rw [e, norm_zero] at hu₁
      exact zero_ne_one hu₁

    have step : ∀ j, ∀ x ∈ O, P j x + (1 - Q j x₁) / Q j₀ x₁ * P j₀ x =
        u₁ * (Q j x + (1 - Q j x₁) / Q j₀ x₁ * Q j₀ x) := by
      intro j
      set μ : ℂ := (1 - Q j x₁) / Q j₀ x₁ with hμ
      obtain ⟨-, c', hc'⟩ := GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq V Unit O hO hc hne
        (fun x => P j x + μ * P j₀ x) (fun _ x => Q j x + μ * Q j₀ x)
        ((hP j).add ((hP j₀).const_smul μ))
        (fun _ => (hQ j).add ((hQ j₀).const_smul μ))
        (fun x hx => by
          obtain ⟨u, hu, hPx⟩ := h x hx
          refine ⟨(), ?_⟩
          simp only [hPx, ← mul_add, mul_left_comm μ u, norm_mul, hu, one_mul])
      have hQ1 : Q j x₁ + μ * Q j₀ x₁ = 1 := by
        rw [hμ, div_mul_cancel₀ _ hq]
        ring
      have hc1 : c' = u₁ := by
        have e := hc' x₁ hx₁
        rw [hQ1, mul_one, hPu j, hPu j₀, mul_left_comm μ u₁, ← mul_add, hQ1, mul_one] at e
        exact e.symm
      intro x hx
      rw [hc' x hx, hc1]
    have h₀ : ∀ x ∈ O, P j₀ x = u₁ * Q j₀ x := by
      intro x hx
      have e := step j₀ x hx
      have hne' : 1 + (1 - Q j₀ x₁) / Q j₀ x₁ ≠ 0 := by
        rw [add_div' _ _ _ hq]
        simp [hq]
      have : (1 + (1 - Q j₀ x₁) / Q j₀ x₁) * (P j₀ x - u₁ * Q j₀ x) = 0 := by
        linear_combination e
      rcases mul_eq_zero.1 this with h1 | h1
      · exact (hne' h1).elim
      · exact sub_eq_zero.1 h1
    refine ⟨Units.mk0 u₁ hu0, fun j x hx => ?_⟩
    have e := step j x hx
    rw [Units.val_mk0]
    linear_combination e - (1 - Q j x₁) / Q j₀ x₁ * h₀ x hx
  · push_neg at h0
    refine ⟨1, fun j x hx => ?_⟩
    obtain ⟨u, -, hPx⟩ := h x hx
    rw [hPx j, h0 j x hx, mul_zero, mul_zero]

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem transp_reads_const_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a → ∃ c : ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ), rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) γ F.1) k x = (c : ℂ) * rdU (uAt r v i) F.1 k' (castFrame h2 (lact a x)) := by
  intro D L hT Gi Gl Kc Y cX eX Csz p hp r h hr i v ψ γ k k' a ht
  obtain ⟨hm, hb, -⟩ := ht
  have hl := h.laws v
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ := (r.used v).full.toCore.good_σ₀
  have hU : IsUnf (uAt r v i) := hl.p.unf _ hj _ hσ
  have hpins := hl.p.pins
  have hpq : 1 ≤ ((r.used v).full.Q.Dw ((i : ℕ) + 1)).p + ((r.used v).full.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hpins.2.2.2 _ hj).1, (hpins.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D (r.used v).full.Q ((i : ℕ) + 1) hpq hpins.2.1.2
  have hsecF : ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
      F.1 ∈ sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n := fun F =>
    ((mem_cusp _ _ _ _ _ _).1 (Submodule.mem_inf.1 F.2).1).1
  have hsecG : ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
      actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1 ∈
        sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n := fun F =>
    actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ (hsecF F)
  have P1 : ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom)
      (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _)
      (hbt : FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩)
        (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩)))
      (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)),
      rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
        toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t : CAt (r.used v).full.σ₀) *
          rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) := by
    intro x hx hy t hbt F
    have e1 : rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
        toC (evR _ _ (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1)
          ((uAt r v i).un k ⟨x, hx⟩)) := dif_pos hx
    have e2 : rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) =
        toC (evR _ _ F.1 ((uAt r v i).un k' ⟨_, hy⟩)) := dif_pos hy
    have e3 := evalAt_actL hL (hl.p.evalWD _ hj) frMap_trans_id γ (hsecF F).1 ((uAt r v i).un k ⟨x, hx⟩)
    have e4 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ _ _).2.2.2.2.2.2 (CAt _)
      (inferInstanceAs (IsReduced ℂ)) _ _ F.1 (hsecF F) t _ _ hbt
    rw [e1, e2]
    exact congrArg toC (e3.trans e4)
  have hUf : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) := hU
  have hσf : Formalism.L2.PjFree.GoodEmb (r.used v).full.Q.c (r.used v).full.σ₀ := hσ
  have hr1 : 1 ≤ D.R.r := hU.1 ▸ hpq
  have hxi : ∀ k k' (τ : D.host.E →+* ℂ), ‖τ ((uAt r v i).X k).ξ0‖ = ‖τ ((uAt r v i).X k').ξ0‖ :=
    fun k k' τ => (hl.p.xiAbs _ hj _ hσ k τ).trans (hl.p.xiAbs _ hj _ hσ k' τ).symm
  obtain ⟨hun1, -⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσf hUf
  have hsk : ∀ (f : Rul ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c),
      f ∈ sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n → ∀ k,
      ((uAt r v i).X k).IsSec (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) (rdU (uAt r v i) f k) :=
    fun f hf k => hU.2.2.2.2.1 _ _ (dom_wtA _) f hf k
  have key : ∀ x ∈ ((uAt r v i).X k).dom, ∃ u : ℂ, ‖u‖ = 1 ∧
      ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
        rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
          u * rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) := by
    intro x hx
    obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀'⟩, -⟩ := hun1 k ⟨x, hx⟩
    have e₀ : x₀.1 = rmul x b₀ := e₀'
    obtain ⟨hy₀, t₀, hbt₀⟩ := hb x₀.1 x₀.2
    obtain ⟨ρ, ν, -, -, hmv⟩ := mvPt_spec hL.total γ ((uAt r v i).un k x₀)
    have hx₀' : GlobalTheory.FrameNorm.IsUnitFr ((uAt r v i).X k') (castFrame hm.psi (lact a x₀.1)) := fun τ j => by
      exact (congrArg norm (hm.dmin_eq x₀.1 τ j)).trans (hx₀ _ _)
    obtain ⟨-, -, -, -, -, -, ht1⟩ := GlobalTheory.LevelCusp.exists_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσf hUf hr1
      hxi (x := x₀) (x' := ⟨castFrame hm.psi (lact a x₀.1), hy₀⟩) hmv hbt₀ hx₀ hx₀'
    refine ⟨toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t₀ : CAt (r.used v).full.σ₀), ?_, fun F => ?_⟩
    · have : toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t₀ : CAt (r.used v).full.σ₀) =
          ∏ j, toC (t₀ j : CAt (r.used v).full.σ₀) ^ ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n j := rfl
      rw [this, norm_prod]
      exact Finset.prod_eq_one fun j _ => by
        rw [norm_pow, show ‖toC (t₀ j : CAt (r.used v).full.σ₀)‖ = 1 from ht1 j, one_pow]
    · have A := P1 x₀.1 x₀.2 hy₀ t₀ hbt₀ F
      have B := (hsk _ (hsecG F) k).2.1 x hx b₀ hb₀
      have C := (hsk _ (hsecF F) k').2.1 _ (hb x hx).1 _ (GlobalTheory.Dict.Pull.cast_bor hm.psi hb₀)
      have e5 : castFrame hm.psi (lact a x₀.1) = rmul (castFrame hm.psi (lact a x)) (GlobalTheory.Dict.castFr hm.psi b₀) := by
        rw [e₀]
        exact (congrArg (castFrame hm.psi) (GlobalTheory.Dict.Extend.lact_rmul a x b₀)).trans (GlobalTheory.Dict.Pull.cast_rmul hm.psi _ _)
      have e6 : bchar (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k') (GlobalTheory.Dict.castFr hm.psi b₀) =
          bchar (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) b₀ :=
        GlobalTheory.Dict.Pull.cast_bchar hm.psi (GlobalTheory.LevelCusp.laU_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hm _ _) b₀
      rw [e5, C, e6, e₀, B] at A
      have hβ := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne ((uAt r v i).X k) (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) hb₀
      apply mul_left_cancel₀ hβ
      rw [A]
      ring
  obtain ⟨c, hc⟩ := exists_const_of_forall_unit_mul (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).isPreconnected
    (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).nonempty
    (fun (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) x =>
      rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x)
    (fun (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) x =>
      rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)))
    (fun F => (hsk _ (hsecG F) k).1)
    (fun F => (hsk _ (hsecF F) k').1.comp
      ((GlobalTheory.Dict.Pull.cast_diff hm.psi).comp (GlobalTheory.Dict.Extend.differentiable_lact a)).differentiableOn
      (fun x hx => (hb x hx).1))
    key
  refine ⟨c, fun F x hx h2 => ?_⟩
  exact hc F x hx

end GlobalTheory.ShareOn
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isTransp_comp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ γ' : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a a' : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ' k k₁ a' → IsTransp p r i v ψ γ k₁ k₂ a → IsTransp p r i v ψ (γ' * γ) k k₂ (a * a') := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v ψ γ γ' k k₁ k₂ a a' h₁ h₂
  obtain ⟨m₁, f₁, l₁⟩ := h₁
  obtain ⟨m₂, f₂, l₂⟩ := h₂
  have hP := (h.laws v).p
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left 1 _, i.isLt⟩
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1)
    (GlobalTheory.Proof.ModelAtPrimeToLevel.one_le_rank hP hj) hP.pins.2.1.2
  have hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k₂) (a * a') :=
    { psi := m₁.psi.trans m₂.psi
      p0 := m₁.p0.trans m₂.p0
      xi := m₁.xi.trans m₂.xi
      iso := fun u w => by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, m₂.iso, m₁.iso]
      lat := fun w => by
        rw [m₁.lat, m₂.lat, Units.val_mul, Matrix.mulVec_mulVec] }
  refine ⟨hm, fun x hx => ?_, fun w => ?_⟩
  · obtain ⟨hy₁, t₁, b₁⟩ := f₁ x hx
    obtain ⟨hy₂, t₂, b₂⟩ := f₂ _ hy₁
    have ef : castFrame hm.psi (lact (a * a') x) =
        castFrame m₂.psi (lact a (castFrame m₁.psi (lact a' x))) := by
      funext τ
      simp only [castFrame, lact, mat, Units.val_mul, Matrix.map_mul, Matrix.of_apply]
      rw [mul_assoc]
      rfl
    set Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)
    set c := (r.used v).full.Q.c
    set y₀ := (uAt r v i).un k ⟨x, hx⟩
    set y₁ := (uAt r v i).un k₁ ⟨castFrame m₁.psi (lact a' x), hy₁⟩
    have e1 := hL.mul γ' γ _ y₀ _ _ (mvPt_spec hL.total γ' y₀) (mvPt_spec hL.total γ (mvLev Xo c γ' y₀))
    have e2 := hL.func (γ' * γ) _ y₀ _ _ (mvPt_spec hL.total (γ' * γ) y₀) e1
    have e3 : mvLev Xo c γ (mvLev Xo c γ' y₀) = mvLev Xo c (γ' * γ) y₀ :=
      ((GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id _ _) _).1 _ _ e2
        (GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id _ _) _).2.1)
    have e4 := hL.bor γ _ t₁ y₁ _ (mvLev Xo c γ' y₀) _ b₁ (mvPt_spec hL.total γ y₁)
      (mvPt_spec hL.total γ (mvLev Xo c γ' y₀))
    have e5 := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ _ _ _ _ _ _).2.1 t₂ t₁ _ _ _ b₂ e4
    have key : ∀ (z : Frame ((uAt r v i).X k₂).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k₂).dom),
        z = castFrame m₂.psi (lact a (castFrame m₁.psi (lact a' x))) →
        FrBor (t₂ * t₁) ((uAt r v i).un k₂ ⟨z, hz⟩) (mvLev Xo c (γ' * γ) y₀) := by
      rintro z hz rfl
      rw [← e3]
      exact e5
    exact ⟨ef ▸ hy₂, t₂ * t₁, key _ _ ef⟩
  · obtain ⟨hw₁, q₁⟩ := l₁ w
    obtain ⟨hw₂, q₂⟩ := l₂ ⟨_, hw₁⟩
    have e : ((a * a' : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (w : Fin D.R.r → D.host.E) =
        (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec
          ((a' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (w : Fin D.R.r → D.host.E)) := by
      rw [Units.val_mul, Matrix.mulVec_mulVec]
    have hs : ∀ z, (γ' * γ).symm z = γ.symm (γ'.symm z) := fun z =>
      (γ' * γ).injective (by
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply])
    rw [e]
    refine ⟨hw₂, q₂.trans ?_⟩
    refine congrArg (ψ k₂) ?_
    refine (congrArg γ.symm ((congrArg (ψ k₁).symm q₁).trans ((ψ k₁).symm_apply_apply _))).trans ?_
    exact (hs _).symm

end GlobalTheory.ShareOn

end
end

section

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BigOn.Exp

section ScalarGeneric

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

theorem exists_smul_eq_sum_tmul_finBasis (x : L ⊗[O] M) : ∃ d : O, d ≠ 0 ∧
    ∃ c : _ → L, d • x = ∑ a, c a ⊗ₜ Module.finBasis (FractionRing O) M a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, hd, c, e⟩ := hx
    obtain ⟨d', hd', c', e'⟩ := hy
    refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
    rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
    simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      fun c => (Module.finBasis (FractionRing O) M).repr f c
    choose y hy using hd
    refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
    rw [← TensorProduct.tmul_smul]
    conv_lhs => rw [← (Module.finBasis (FractionRing O) M).sum_repr f]
    rw [Finset.smul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_scalar_mem_range
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c))
    (x₁ x₂ : L ⊗[O] M) (κ : ℂ) (h : readExt rd eL hL x₁ = κ • readExt rd eL hL x₂) (h₂ : readExt rd eL hL x₂ ≠ 0) :
    ∃ b : L, eL b = κ := by
  set v := Module.finBasis (FractionRing O) M
  have hδ : ∀ d : O, d ≠ 0 → eL (algebraMap O L d) ≠ 0 := fun d hd => by
    rw [hL]
    exact (map_ne_zero eK).2 ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd)
  have hsum : ∀ x : L ⊗[O] M, ∀ (d : O) (c : _ → L), d • x = ∑ a, c a ⊗ₜ v a →
      ∑ a, eL (c a) • rd (v a) = eL (algebraMap O L d) • readExt rd eL hL x := fun x d c e => by
    have := congrArg (readExt rd eL hL) e

    rw [← algebraMap_smul L d x, readExt_smul, map_sum] at this
    rw [this]
    rfl
  obtain ⟨d₁, hd₁, c₁, e₁⟩ := exists_smul_eq_sum_tmul_finBasis x₁
  obtain ⟨d₂, hd₂, c₂, e₂⟩ := exists_smul_eq_sum_tmul_finBasis x₂
  have r₁ := hsum _ _ _ e₁
  have r₂ := hsum _ _ _ e₂
  set δ₁ := eL (algebraMap O L d₁)
  set δ₂ := eL (algebraMap O L d₂)
  have h0 : ∑ a, (eL (c₁ a) - δ₁ * κ * δ₂⁻¹ * eL (c₂ a)) • rd (v a) = 0 := by
    have e3 : ∑ a, (eL (c₁ a) - δ₁ * κ * δ₂⁻¹ * eL (c₂ a)) • rd (v a) =
        ∑ a, eL (c₁ a) • rd (v a) - (δ₁ * κ * δ₂⁻¹) • ∑ a, eL (c₂ a) • rd (v a) := by
      simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, mul_smul]
    rw [e3, r₁, r₂, h, smul_smul, smul_smul, inv_mul_cancel_right₀ (hδ _ hd₂), sub_self]
  have hc := Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ h0
  obtain ⟨a, ha⟩ : ∃ a, c₂ a ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply h₂
    have : δ₂ • readExt rd eL hL x₂ = 0 := by rw [← r₂]; simp [hne]
    exact (smul_eq_zero.1 this).resolve_left (hδ _ hd₂)
  have hca : eL (c₂ a) ≠ 0 := (map_ne_zero eL).2 ha
  refine ⟨c₁ a * algebraMap O L d₂ / (algebraMap O L d₁ * c₂ a), ?_⟩
  have e := sub_eq_zero.1 (hc a)
  rw [map_div₀, map_mul, map_mul, e]
  have h1 : δ₁ ≠ 0 := hδ _ hd₁
  have h2 : δ₂ ≠ 0 := hδ _ hd₂
  change δ₁ * κ * δ₂⁻¹ * eL (c₂ a) * δ₂ / (δ₁ * eL (c₂ a)) = κ
  rw [div_eq_iff (mul_ne_zero h1 hca)]
  calc δ₁ * κ * δ₂⁻¹ * eL (c₂ a) * δ₂ = δ₁ * κ * eL (c₂ a) * (δ₂⁻¹ * δ₂) := by ring
    _ = κ * (δ₁ * eL (c₂ a)) := by rw [inv_mul_cancel₀ h2]; ring

end ScalarGeneric

theorem exists_algebraMap_eq_of_isIntegral {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (e : FractionRing R →+* ℂ) (b₀ : FractionRing R) (N : ℕ) (hN : IsUnit (N : R)) (m : ℕ)
    (h : IsIntegral ℤ ((N : ℂ) ^ m * e b₀)) : ∃ b : R, algebraMap R (FractionRing R) b = b₀ := by
  let f : FractionRing R →ₐ[ℤ] ℂ := { e with commutes' := fun r => by simp }
  have e1 : (N : ℂ) ^ m * e b₀ = f ((N : FractionRing R) ^ m * b₀) := by
    simp [f, map_mul, map_pow, map_natCast]
  rw [e1] at h
  have h' : IsIntegral ℤ ((N : FractionRing R) ^ m * b₀) := (isIntegral_algHom_iff f e.injective).1 h
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h'.tower_top (A := R))
  refine ⟨(↑hN.unit⁻¹ : R) ^ m * c, ?_⟩
  have hu : algebraMap R (FractionRing R) (↑hN.unit⁻¹ : R) * (N : FractionRing R) = 1 := by
    rw [← map_natCast (algebraMap R (FractionRing R)) N, ← map_mul, hN.val_inv_mul, map_one]
  rw [map_mul, map_pow, hc, ← mul_assoc, ← mul_pow, hu, one_pow, one_mul]

end GlobalTheory.BigOn.Exp
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.IndefR.Mult Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameProdLoc

theorem mem_locGrp_of_isLocEnv {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0)
    (i : ok × ℕ) (x : Bridge.Gf V) (h : isLocEnv V pl ok i x) :
    x ∈ GlobalTheory.HeckeRowsCompare.locGrp V ((pl i.1).under (𝓞 D.host.F)) := by
  rw [GlobalTheory.HeckeRowsCompare.mem_locGrp]
  exact GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 h)

theorem isLocEnv_of_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0)
    (i : ok × ℕ) (x : Bridge.Gf V) (e : Formalism.L2.Theta.AE D) (he : Formalism.L2.NTheta.IsIdemAt e (pl i.1))
    (h : x ∈ GlobalTheory.HeckeRowsCompare.locGrp V ((pl i.1).under (𝓞 D.host.F))) : isLocEnv V pl ok i x := by
  obtain ⟨α, hα, hfin⟩ := GlobalTheory.HeckeRowsCompare.fin_lift V x
  have hI : IsPrimeIdem (pl i.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hI
  refine ⟨e, α, he, hα, ?_, ?_⟩
  · show SuppF V (e + cA D e) α
    rw [hf, GlobalTheory.HeckeRowsCompare.suppF_iff V hε hα, hfin]
    exact h
  · rw [← hfin]
    rfl

theorem isLocEnv_prod : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0)
    (i i' : ok × ℕ) (a b c d : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) = (pl i'.1).under (𝓞 D.host.F) →
    isLocEnv V pl ok i a → isLocEnv V pl ok i' b → isLocEnv V pl ok i' c → isLocEnv V pl ok i d →
    isLocEnv V pl ok i ((c * d)⁻¹ * (a * b)) := by
  intro D V Pl0 pl ok i i' a b c d hv ha hb hc hd
  obtain ⟨e, -, he, -⟩ := id ha
  apply isLocEnv_of_mem V pl ok i _ e he
  have ha' := mem_locGrp_of_isLocEnv V pl ok i a ha
  have hd' := mem_locGrp_of_isLocEnv V pl ok i d hd
  have hb' := mem_locGrp_of_isLocEnv V pl ok i' b hb
  have hc' := mem_locGrp_of_isLocEnv V pl ok i' c hc
  rw [← hv] at hb' hc'
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hc' hd')) (Subgroup.mul_mem _ ha' hb')

end GlobalTheory.FrameProdLoc
end
