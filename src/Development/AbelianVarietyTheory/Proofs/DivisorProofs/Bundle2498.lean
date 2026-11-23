module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.NumbersP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle849
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle877
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle912
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle925
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle003
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.BigOn.Exp.SerBase




theorem natPrime_notMem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q.Prime)
    (hne : q ≠ Formalism.EigenvalueLevelCeiling.plc v) : (q : 𝓞 K) ∉ v.asIdeal := by
  intro hmem
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
  have hdvd : Formalism.EigenvalueLevelCeiling.plc v ∣ q := (ringChar.spec (𝓞 K ⧸ v.asIdeal) q).1 hmem
  exact hne ((Nat.prime_dvd_prime_iff_eq (Formalism.L2.DIV.plc_prime' v) hq).1 hdvd).symm

theorem ownAt_prime_ne (D : D7) (w : D.what₂.places.Pl) :
    (ownAt D (D.plEq w)).Prime ∧ ownAt D (D.plEq w) ≠ Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := by
  unfold ownAt
  split_ifs with h
  · exact ⟨D.host.pde'_prime, fun e => D.host.pde_ne (h.symm.trans e.symm)⟩
  · exact ⟨D.host.pde_prime, fun e => h e.symm⟩

theorem ownUnit : OwnUnit := by
  intro D c w
  obtain ⟨hq, hne⟩ := ownAt_prime_ne D w
  set q := ownAt D (D.plEq w) with hqdef
  have hnot := natPrime_notMem (D.plEq w) hq hne
  have hv : (D.plEq w).valuation D.what₂.LL (q : D.what₂.LL) = 1 := by
    have := ((D.plEq w).valuation_eq_one_iff_notMem (K := D.what₂.LL)).2 hnot
    simpa using this
  have hq0 : (q : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hnn : (0 : WithTop ℤ) ≤ D.what₂.places.val w (q : D.what₂.LL)⁻¹ :=
    (D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one])
  obtain ⟨y, hy⟩ := (c.embW_w w _).1 hnn
  rw [map_inv₀, map_natCast] at hy
  have hqF : ((q : ℕ) : FractionRing (c.Oe w)) ≠ 0 := by
    have := (map_ne_zero (c.embW w)).2 hq0
    rwa [map_natCast] at this
  have h1 : algebraMap (c.Oe w) (FractionRing (c.Oe w)) (y * (q : c.Oe w)) = 1 := by
    rw [map_mul, hy, map_natCast]
    exact inv_mul_cancel₀ hqF
  have h2 : y * (q : c.Oe w) = 1 := by
    apply IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w))
    rw [h1, map_one]
  exact (Units.mkOfMulEqOne (q : c.Oe w) y (by rw [mul_comm]; exact h2)).isUnit

end GlobalTheory.BigOn.Exp.SerBase
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem movesAt_of_movesAt_open : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' k'' : (uAt r v i).Comp) (a c : GL (Fin D.R.r) D.host.E) (hma : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (hmc : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k'') c) (W : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen W → W.Nonempty → W ⊆ ((uAt r v i).X k).dom → (∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W → MovesAt p r i v γ k k' a hma z hz ∧ MovesAt p r i v γ k k'' c hmc z hz) → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k'' c hmc x hx → MovesAt p r i v γ k k' a hma x hx := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v γ k k' k'' a c hma hmc W hWo hWn hWd hW x hx hcx
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hU : IsUnf (uAt r v i) := (h.laws v).p.toLawsCore.unf _ hj _ (r.used v).full.toCore.good_σ₀
  obtain ⟨-, htr, hsy, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid D.host.E _ _ _
    ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (CAt (r.used v).full.σ₀)

  have step : ∀ z (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W →
      ∃ γ' ∈ ((uAt r v i).X k').Γ, ∃ b ∈ Bor ((uAt r v i).X k').Ψ D.R.r,
        (⟨k'', castFrame hmc.psi (lact c z)⟩ : Σ k, Frame ((uAt r v i).X k).Ψ D.R.r) =
          ⟨k', rmul (lact γ' (castFrame hma.psi (lact a z))) b⟩ := by
    intro z hz hzW
    obtain ⟨⟨hy₁, t₁, f₁⟩, ⟨hy₂, t₂, f₂⟩⟩ := hW z hz hzW
    have hb := htr _ _ _ _ _ f₁ (hsy _ _ _ f₂)
    exact (hU.2.2.2.1 k' k'' ⟨_, hy₁⟩ ⟨_, hy₂⟩).1 ⟨_, hb⟩
  obtain ⟨z₀, hz₀⟩ := hWn
  have hk : k'' = k' := by
    obtain ⟨g₀, -, b₀, -, e₀⟩ := step z₀ (hWd hz₀) hz₀
    exact (Sigma.mk.inj_iff.1 e₀).1
  subst hk
  have hcast : ∀ z (b : Frame ((uAt r v i).X k'').Ψ D.R.r) (γ' : GL (Fin D.R.r) D.host.E),
      castFrame hmc.psi (lact c z) = rmul (lact γ' (castFrame hma.psi (lact a z))) b →
      lact c z = rmul (lact γ' (lact a z)) (castFrame hma.psi.symm b) := by
    intro z b γ' e
    funext τ
    have := congrFun e ⟨τ.1, hma.psi ▸ τ.2⟩
    exact this
  have hborc : ∀ b ∈ Bor ((uAt r v i).X k'').Ψ D.R.r, castFrame hma.psi.symm b ∈ Bor ((uAt r v i).X k).Ψ D.R.r := by
    intro b hb τ
    exact hb ⟨τ.1, hma.psi ▸ τ.2⟩
  obtain ⟨γ', hγ', V, hVo, hVn, hVd, hV⟩ := GlobalTheory.T.exists_candidate_borel_move_open_frames_baire ((uAt r v i).X k) ((uAt r v i).X k'').Γ a c W hWo ⟨z₀, hz₀⟩ hWd
    (fun z hz => by
      obtain ⟨γ', hγ', b, hb, e⟩ := step z (hWd hz) hz
      exact ⟨γ', hγ', _, hborc b hb, hcast z b γ' (eq_of_heq (Sigma.mk.inj_iff.1 e).2)⟩)
  obtain ⟨s, hs⟩ := GlobalTheory.T.scalar_of_borel_moves_open_frames ((uAt r v i).X k) _ V hVo hVn hVd hV
  set m : GL (Fin D.R.r) D.host.E := (γ' * a)⁻¹ * c with hm_def
  have hcm : (c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
      (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (a : Matrix _ _ _) * (m : Matrix _ _ _) := by
    have : c = γ' * a * m := by rw [hm_def]; group
    rw [this]; simp [Units.val_mul]
  obtain ⟨hy₂, t₂, f₂⟩ := hcx
  have hy₁ : castFrame hma.psi (lact a x) ∈ ((uAt r v i).X k'').dom := hma.mem_dom hx
  let bm : Frame ((uAt r v i).X k'').Ψ D.R.r := fun τ => (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1
  have hbm : bm ∈ Bor ((uAt r v i).X k'').Ψ D.R.r := by
    intro τ
    refine ⟨?_, fun p q hpq => ?_⟩
    · show ((m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1).det ≠ 0
      rw [show (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = τ.1.mapMatrix (m : Matrix _ _ _) from rfl,
        ← RingHom.map_det]
      have hu : IsUnit (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det :=
        (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
      exact (map_ne_zero τ.1).2 hu.ne_zero
    · show (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 p q = 0
      rw [hs, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (ne_of_lt hpq).symm, map_zero]
  have heq : castFrame hmc.psi (lact c x) = rmul (lact γ' (castFrame hma.psi (lact a x))) bm := by
    funext τ
    show (c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, _⟩ =
      ((γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * ((a : Matrix _ _ _).map τ.1 * mat x ⟨τ.1, _⟩)) *
        (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1
    rw [hcm, hs, Matrix.map_mul, Matrix.map_mul]
    have hsc : (Matrix.scalar (Fin D.R.r) s).map τ.1 = Matrix.scalar (Fin D.R.r) (τ.1 s) := by
      ext p q; by_cases hpq : p = q <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hpq]
    rw [hsc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 2
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
  have hb := (hU.2.2.2.1 k'' k'' ⟨_, hy₁⟩ ⟨_, hy₂⟩).2 ⟨γ', hγ', bm, hbm, congrArg (Sigma.mk k'') heq⟩
  obtain ⟨t', ht'⟩ := hb
  exact ⟨hy₁, _, htr _ _ _ _ _ ht' f₂⟩

end GlobalTheory.ShareOn

end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.LiftThreeStep

theorem omegaQ_union {D : D7} {a b : ℕ} {Sa St : Finset (Pl D.host.E)} (hd : Disjoint Sa St) (r : ℕ)
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ (Sa ∪ St) r ξ k y = omegaQ Sa r ξ k y * omegaQ St r ξ k y := by
  let g : Pl D.host.E → ℂ := fun PP =>
    if h : LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ k else 0
  have key : ∀ Q : Finset (Pl D.host.E), omegaQ Q r ξ k y = ∏ PP ∈ Q, g PP := by
    intro Q
    unfold omegaQ
    by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
    · rw [dite_eq_left h, ← Finset.prod_attach Q g]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [g]
      rw [dite_eq_left (h PP.1 PP.2)]
    · rw [dite_eq_right h]
      obtain ⟨PP, hPP⟩ := not_forall.1 h
      obtain ⟨hQ, hn⟩ := Classical.not_imp.1 hPP
      refine (Finset.prod_eq_zero hQ ?_).symm
      simp only [g]
      rw [dite_eq_right hn]
  rw [key, key, key, Finset.prod_union hd]

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem adjDat_union {Sa St : Finset (Pl D.host.E)} {ea et : AE D} (hg : IsIdemSum ea Sa) (hq : IsIdemSum et St)
    (hd : Disjoint Sa St) (he : IsIdemSum (ea + et) (Sa ∪ St)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    adjDat R i (Sa ∪ St) ξ (cA D (ea + et)) =
      GlobalTheory.TwoStepModel.tensorHalf (cA D et) (cA D ea) (adjDat R i Sa ξ (cA D ea)) (adjDat R i St ξ (cA D et)) := by
  have hA := GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he
  have hB := GlobalTheory.TwoStepRed.redM_twoStep D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hcg : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D ea) (cA D ea • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x
  have hcQ : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D et) (cA D et • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x
  funext x
  rw [GlobalTheory.TwoStepModel.tensorHalf_apply]
  unfold adjDat
  have hc : cA D (ea + et) = cA D et + cA D ea := by rw [map_add (f := _), add_comm]
  by_cases hx : IsHalf (cA D (ea + et)) x
  · have hx' : IsHalf (cA D et + cA D ea) x := hc ▸ hx
    rw [if_pos hx', mul_one]
    by_cases hi : IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)
    · obtain ⟨i1, i2⟩ := (hA x hx).1 hi
      obtain ⟨r1, r2⟩ := hB x hx hi
      rw [if_pos (And.intro hx hi), if_pos (And.intro (hcQ x) i2), if_pos (And.intro (hcg x) i1), omegaQ_union hd, mul_comm]
      congr 1
      · exact GlobalTheory.PlaceVec.omegaQ_congr St _ ξ _ fun PP hPP => (r2 PP hPP).symm
      · exact GlobalTheory.PlaceVec.omegaQ_congr Sa _ ξ _ fun PP hPP => (r1 PP hPP).symm
    · have c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)) := fun h => hi h.2
      rw [if_neg c1]
      have := mt (hA x hx).2 hi
      rcases not_and_or.1 this with h | h
      · have c3 : ¬ (IsHalf (cA D ea) (cA D ea • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D ea • x))) :=
          fun h' => h h'.2
        rw [if_neg c3, mul_zero]
      · have c2 : ¬ (IsHalf (cA D et) (cA D et • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D et • x))) :=
          fun h' => h h'.2
        rw [if_neg c2, zero_mul]
  · have c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)) := fun h => hx h.1
    have hx' : ¬ IsHalf (cA D et + cA D ea) x := hc ▸ hx
    rw [if_neg c1, if_neg hx', mul_zero]

end

theorem thetaVector_three_step_decomposition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Disjoint Sa St → Sa ∪ St = R.Q t → ∀ (eg ea et : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ gA : WO (Vc D i) (Wc D i) → ℂ, ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) gA ∧ ThAt R i (cA D et) gA (adjDat R i St (R.xiR t) (cA D et)) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i t _ Sa St hd hU eg ea et fg hg ha ht hfg
  obtain ⟨⟨hψ, -⟩, e, he, -⟩ := hC.thP.vP i t
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  obtain ⟨eQ, hq⟩ := (GlobalTheory.IdemFlip.idemSum_sub_and_flip D e _ (R.Q t) he Finset.subset_union_right).1
  have h2 : ThAt R i (cA D eQ) fg (adjDat R i (R.Q t) (R.xiR t) (cA D eQ)) (R.vP i t) :=
    GlobalTheory.ConjTwist.isThetaAt_vP_twoStep D G Pl0 T0 A Ks R F hC hG i t eg eQ fg hg hq hfg
  rw [← hU] at hq h2
  have hsum : eQ = ea + et := by
    rw [← GlobalTheory.ExportSeries.idem_eq hq, ← GlobalTheory.ExportSeries.idem_eq ha, ← GlobalTheory.ExportSeries.idem_eq ht]
    exact Finset.sum_union hd
  subst hsum
  have hea := GlobalTheory.PlaceVec.idemSum_mul_self ha
  have het := GlobalTheory.PlaceVec.idemSum_mul_self ht
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hat : ea * et = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - hea - het
  have hca : cA D ea * cA D ea = cA D ea := by rw [← map_mul, hea]
  have hct : cA D et * cA D et = cA D et := by rw [← map_mul, het]
  have hta : cA D et * cA D ea = 0 := by rw [← map_mul, mul_comm, hat, map_zero]
  have hat' : cA D ea * cA D et = 0 := by rw [mul_comm, hta]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfa : infPart D (cA D ea) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha)
  have hinft : infPart D (cA D et) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ht)
  have hSB : ∀ (Q : Finset (Pl D.host.E)) (a : AE D), infPart D a = 0 →
      IsSBHalf a (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (adjDat R i Q (R.xiR t) a) :=
    fun Q a hinf => GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinf (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
      Q (fun y => omegaQ Q (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := h2
  have hc : cA D (ea + et) = cA D et + cA D ea := by rw [map_add (f := _), add_comm]
  have hc' : cA D (ea + et) = cA D ea + cA D et := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hct hca hta hΛ (hSB Sa _ hinfa) (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hca hct hat' hΛ (hc' ▸ hTe1)
  refine ⟨_, ⟨⟨_, hm2⟩, fun T' hT' => ?_⟩, ⟨_, hm1⟩, fun T' hT' => ?_⟩
  · exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hca hinfa hm2 hT' (hSB Sa _ hinfa)
  · rw [hTe2 Te hTe1, adjDat_union R i ha ht hd hq (R.xiR t)]
    exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hct hinft hm1 hT' (hSB St _ hinft)

end GlobalTheory.LiftThreeStep

end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.ThetaBaseMove

open Formalism.IndefR.Fin.LevelGroupLemmas

section General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem heisO_smul' (u : WO S T) (c : ℂ) (g : WO S T → ℂ) : heisO ψ S T u (c • g) = c • heisO ψ S T u g := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_smul (c : ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (c • g) := by
  refine ⟨fun γ w => ?_, ?_, hg.cont.const_smul c, fun k L hL h0 w => (hg.smooth k L hL h0 w).const_smul c⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [hg.quasi]; ring
  · obtain ⟨U, hU, h⟩ := hg.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul', h u hu h0]⟩

theorem isPlaceModel_move (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ)) (g : GA D S) (h : GA D T) (c : ℂ)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g h x = x) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • om (g, h) f₀) (c • (om (g, h)).comp Tm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ hΦ x hx
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, hTm.trans Φ hΦ x hx, LinearMap.comp_apply,
      hW.om_heis g h x (Tm Φ) (hth Φ hΦ), hfx x (Or.inl hx), heisO_smul']
  · intro Φ hΦ y hy
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, hTm.modul Φ hΦ y hy, LinearMap.comp_apply,
      hW.om_heis g h y (Tm Φ) (hth Φ hΦ), hfx y (Or.inr hy), heisO_smul']
  · rw [LinearMap.smul_apply, LinearMap.comp_apply, hTm.vac]

theorem isThetaAt_move (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hth : ∀ f₀, IsThetaFunO ψ S T f₀ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm →
      ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ))
    {b Φ f : WO S T → ℂ} (hb : IsThetaFunO ψ S T b) (g : GA D S) (h : GA D T) {c : ℂ} (hc : c ≠ 0)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g h x = x)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 b Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • om (g, h) b) Φ (c • om (g, h) f) := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  refine ⟨⟨_, isPlaceModel_move hW hTm (hth b hb Tm hTm) g h c hfx⟩, fun T' hT' => ?_⟩
  have hfx' : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g⁻¹ h⁻¹ x = x := fun x hx => by
    conv_lhs => rw [← hfx x hx]
    rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
  have k1 : ∀ v, om (g⁻¹, h⁻¹) (om (g, h) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have k2 : ∀ v, om (g, h) (om (g⁻¹, h⁻¹) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have hm := isPlaceModel_move hW hT' (hth _ (theta_smul c (hW.om_pres _ _ hb)) T' hT') g⁻¹ h⁻¹ c⁻¹ hfx'
  rw [map_smul, k1, smul_smul, inv_mul_cancel₀ hc, one_smul] at hm
  have e1 : f = _ := hall _ hm
  rw [e1, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, k2, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem actO_fix_of_orth {a e : AE D} {z : GA D S} (hz : SuppAt a S z) (h0 : e * (a + cA D a) = 0) {x : WO S T}
    (hx : IsHalf e x) : actO S T z⁻¹ 1 x = x := by
  rw [actO_eq, inv_inv, mt_one', Matrix.one_mul]
  have : HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S z - 1) = 0 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← hx k j, ← hz j l]
    linear_combination (x k j * (mt S z - 1) j l) * h0
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this

end General

theorem thAt_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Sa ⊆ R.Q t → St ⊆ R.Q t → Disjoint Sa St → ∀ (eg ea et : AE D) (fg b Φ f : WO (Vc D i) (Wc D i) → ℂ) (z : GA D (Vc D i)) (c : ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) b → SuppAt ea (Vc D i) z → c ≠ 0 → ThAt R i (cA D et) b Φ f → ThAt R i (cA D et) (c • R.ωP i t (z⁻¹, 1) b) Φ (c • R.ωP i t (z⁻¹, 1) f) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t _hV Sa St hSa hSt hd eg ea et fg b Φ f z c hg ha ht hfg hb hz hc hf
  obtain ⟨⟨hψ, hvac⟩, e, he, -⟩ := hC.thP.vP i t
  have hW := (GlobalTheory.OnCmp.kerDat_tuple (i := i) hC.lev hC.thP t).weil
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hsp : SplitSet (R.Q t) := SplitSet.mono ⟨e, he⟩ (by convert Finset.subset_union_right)
  have hth : ∀ {a : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum a P → ∀ f₀, IsThetaFunO R.ψ (Vc D i) (Wc D i) f₀ → ∀ Tm,
      IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D a)
        (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 f₀ Tm →
      ∀ Ψ, IsSBHalf (cA D a) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ →
        IsThetaFunO R.ψ (Vc D i) (Wc D i) (Tm Ψ) := by
    intro a P h f₀ hf₀ Tm hTm Ψ hΨ
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSV
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSW
    exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ inferInstance inferInstance (by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self h])
      (by rw [← map_mul, h.2, map_zero]) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart h)) hf₀ Tm hTm Ψ hΨ
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg))
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBa := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha))
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    Sa (fun y => omegaQ Sa (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  have hfgθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) fg := by
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hfg
    rw [hall Tm hTm]
    exact hth hg _ hvac.theta Tm hTm _ hSBg
  have hbθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) b := by
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hb
    rw [hall Tm hTm]
    exact hth ha _ hfgθ Tm hTm _ hSBa
  have o1 : et * ea = 0 := by
    rw [← idem_eq ht, ← idem_eq ha, idem, idem, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq =>
      hsp.mul_eq_zero (hSt hp) (hSa hq) fun e => Finset.disjoint_left.1 hd hq (e ▸ hp)
  have o2 : et * cA D ea = 0 := by

    rw [← idem_eq ht, ← idem_eq ha, idem, idem, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => hsp.mul_conj (hSt hp) (hSa hq)
  have o3 : et * (ea + cA D ea) = 0 := by rw [mul_add, o1, o2, add_zero]
  have o4 : cA D et * (ea + cA D ea) = 0 := by
    have := congrArg (cA D) o3
    rwa [map_mul, map_add, GlobalTheory.LatVac.cA_cA, map_zero, add_comm] at this
  refine isThetaAt_move hW (hth ht) hbθ z⁻¹ 1 hc (fun x hx => ?_) hf
  rcases hx with hx | hx
  · exact actO_fix_of_orth hz o4 hx
  · rw [GlobalTheory.LatVac.cA_cA] at hx
    exact actO_fix_of_orth hz o3 hx

end GlobalTheory.ThetaBaseMove
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLift_intertwines_lifts_smoothVectors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : (R.MW i (sg0 D A)).Vec) (x : GA D (Wc D i)), R.thF i t y' v x = R.thF i t y v (x * κ') := by
  first | exact @GlobalTheory.ThetaShiftSmooth.thF_shift_all | exact GlobalTheory.ThetaShiftSmooth.thF_shift_all | (intros; apply GlobalTheory.ThetaShiftSmooth.thF_shift_all <;> assumption)
end
