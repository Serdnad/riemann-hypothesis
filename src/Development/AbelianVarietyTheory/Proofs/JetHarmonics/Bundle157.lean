module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179
public import Formalism.HermitianCurvature.Bundle006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle030
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle186
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVstep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndTop
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerbB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle023
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle009
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle025
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.MoveValues

open GlobalTheory.MoveCalc

noncomputable abbrev cpt : Sp ℂ := IsLocalRing.closedPoint ℂ

noncomputable def ev : (Sp ℂ).presheaf.stalk cpt →+* ℂ := (stalkClosedPointIso (CommRingCat.of ℂ)).hom.hom

theorem mem_iff {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) : f cpt ∈ U ↔ ⊤ ≤ f ⁻¹ᵁ U :=
  ⟨fun h p _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) p cpt]
    exact h, fun h => h trivial⟩

theorem ev_gs {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)) :
    ev (gs f cpt U a) = valAt' f U a := by
  have h' := (mem_iff f U).1 h
  rw [gs_eq f cpt U h, valAt', dite_eq_left h', valAt, ← germ_stalkClosedPointIso_hom (CommRingCat.of ℂ)]
  exact congrArg ev (TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h') cpt trivial _).symm

theorem ev_gm {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)ˣ) :
    ev (gm f cpt U a).val = valAt' f U a.val :=
  (congrArg ev (gs_unit f cpt U h a).symm).trans (ev_gs f U h _)

section General

variable {X Y Y' : Scheme.{0}} {L : LB X} {F : X ⟶ X}

theorem mem_div {p : Sp ℂ ⟶ X} {i j : L.ι} :
    ⊤ ≤ p ⁻¹ᵁ (LB.div (L.pull F) L).U ((fun _ => i), j) ↔ F (p cpt) ∈ L.U i ∧ p cpt ∈ L.U j :=
  (mem_iff p _).symm.trans (and_congr_left' (mem_pull (F := F) (J := fun _ => i)))

theorem ev_gw (w : LB.Iso L (L.pull F)) (p : Sp ℂ ⟶ X) {i j : L.ι} (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) :
    ev (gw w p cpt i j).val =
      valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val :=
  ev_gm p _ (show p cpt ∈ (L.pull F).U (fun _ => i) ⊓ L.U j from ⟨mem_pull.2 hi, hj⟩) _

theorem val_ne (w : LB.Iso L (L.pull F)) (p : Sp ℂ ⟶ X) {i j : L.ι} (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) :
    valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val ≠ 0 := by
  rw [← ev_gw w p hi hj]
  exact ((gw w p cpt i j).isUnit.map ev).ne_zero

theorem val_pgen {w : LB.Iso L (L.pull F)} (h : PGen w) (p : Sp ℂ ⟶ X) {i j i' j' : L.ι}
    (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) (hi' : F (p cpt) ∈ L.U i') (hj' : p cpt ∈ L.U j') :
    valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' p (L.U j ⊓ L.U j') (L.g j j').val =
      valAt' (p ≫ F) (L.U i ⊓ L.U i') (L.g i i').val *
        valAt' p ((LB.div (L.pull F) L).U ((fun _ => i'), j')) (w.s ((fun _ => i'), j')).val := by
  have e : gw w p cpt i j * gm p cpt _ (L.g j j') = gm (p ≫ F) cpt _ (L.g i i') * gw w p cpt i' j' := by
    rw [h _ p cpt i i' j j' hi hi' hj hj', mul_right_comm, inv_mul_cancel_right]
  rw [← ev_gw w p hi hj, ← ev_gw w p hi' hj', ← ev_gm p (L.U j ⊓ L.U j') ⟨hj, hj'⟩,
    ← ev_gm (p ≫ F) (L.U i ⊓ L.U i') ⟨hi, hi'⟩, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, e]

theorem val_pmaps {w : LB.Iso L (L.pull F)} {e : Y ⟶ X} {t : LB.Gen (L.pull e)} {ρ : Y ⟶ Y} (he : e ≫ F = ρ ≫ e)
    (h : PMaps w (K := PUnit) (fun _ => e) (fun _ => e) (fun _ => 1) t t ρ) (x : Sp ℂ ⟶ Y) {i j : L.ι}
    (hi : F ((x ≫ e) cpt) ∈ L.U i) (hj : (x ≫ e) cpt ∈ L.U j) :
    valAt' (x ≫ ρ) ((L.pull e).U (fun _ => i)) (t.s (fun _ => i)).val =
      valAt' (x ≫ e) ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' x ((L.pull e).U (fun _ => j)) (t.s (fun _ => j)).val := by
  have A := h _ x cpt (fun _ => i) (fun _ => j) (fun _ => hi) (fun _ => hj)
  rw [Fintype.prod_unique, zpow_one] at A
  have m : (x ≫ ρ) cpt ∈ (L.pull e).U (fun _ => i) := mem_pull.2 (by
    have h' : (e ≫ F) (x cpt) ∈ L.U i := hi
    rw [he] at h'
    exact h')
  rw [← ev_gw w (x ≫ e) hi hj, ← ev_gm (x ≫ ρ) _ m, ← ev_gm x ((L.pull e).U (fun _ => j)) (mem_pull.2 hj),
    ← map_mul, ← Units.val_mul]
  exact congrArg (fun u : ((Sp ℂ).presheaf.stalk cpt)ˣ => ev u.val) A

theorem val_carry {w : LB.Iso L (L.pull F)} {q : Y ⟶ X} {q' : Y' ⟶ X} {pm : Y ⟶ Y'} (hpm : pm ≫ q' = q ≫ F)
    {a : Fam L q} {a' : Fam L q'} (h : Carry w pm a a') (pt : Sp ℂ ⟶ Y) {i j : L.ι}
    (hi : F ((pt ≫ q) cpt) ∈ L.U i) (hj : (pt ≫ q) cpt ∈ L.U j) :
    valAt' (pt ≫ pm) _ (a' fun _ => i) =
      valAt' (pt ≫ q) ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' pt _ (a fun _ => j) := by
  have m : (pt ≫ pm) cpt ∈ LB.wchart L (fun _ : Fin 1 => q') (fun _ => i) := mem_chart.2 (by
    have h' : (q ≫ F) (pt cpt) ∈ L.U i := hi
    rw [← hpm] at h'
    exact h')
  rw [← ev_gw w (pt ≫ q) hi hj, ← ev_gs (pt ≫ pm) _ m,
    ← ev_gs pt (LB.wchart L (fun _ : Fin 1 => q) (fun _ => j)) (mem_chart.2 hj), ← map_mul]
  exact congrArg ev (h _ pt cpt i j hi hj)

end General

theorem frMove_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y y' : FrPt Xo c (CAt σ)), FrMove ρ ν y y' → ∃ (O : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → Xo.univ.t.G.left.Opens) (ω : ∀ i j, Γ(Xo.univ.t.G.left, O i j)), (∀ i j (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j ↔ (⊤ ≤ (p ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ p ⁻¹ᵁ Xo.univ.t.PP.L.U j)) ∧ (∀ i j (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → valAt' p (O i j) (ω i j) ≠ 0) ∧ (∀ i j i' j' (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → ⊤ ≤ p ⁻¹ᵁ O i' j' → valAt' p (O i j) (ω i j) * valAt' p (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val = valAt' (p ≫ ν.φ) (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * valAt' p (O i' j') (ω i' j')) ∧ (∀ i j (x : Sp ℂ ⟶ Xo.X) (p : Sp ℂ ⟶ Xo.univ.t.G.left), p = x ≫ eSec Xo.univ.t.G → ⊤ ≤ p ⁻¹ᵁ O i j → valAt' (x ≫ ρ) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val = valAt' p (O i j) (ω i j) * valAt' x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧ ∀ i j (pt : Sp ℂ ⟶ Gx y.x) (pt' : Sp ℂ ⟶ Gx y'.x) (p : Sp ℂ ⟶ Xo.univ.t.G.left), pt ≫ Formalism.L2.PjFree.gxFst y.x = p → pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 (Sp ℂ) → pt' ≫ Formalism.L2.PjFree.gxFst y'.x = p ≫ ν.φ → pt' ≫ Formalism.L2.PjFree.gxSnd y'.x = 𝟙 (Sp ℂ) → ⊤ ≤ p ⁻¹ᵁ O i j → valAt' pt' ((PPx y'.x).U (fun _ => i)) (y'.s.f (fun _ => i)) = valAt' p (O i j) (ω i j) * valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) := by
  intro E _ _ _ H Dw l Xo c σ ρ ν y y' h
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := frMove_iff_carry.1 h
  obtain ⟨g, r, -⟩ := (cubIso_iff ν w).1 hw
  refine ⟨fun i j => (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j),
    fun i j => (w.s ((fun _ => i), j)).val, fun i j p => ?_, fun i j p hp => ?_, fun i j i' j' p hp hp' => ?_,
    fun i j x p e hp => ?_, fun i j pt pt' p e₁ e₂ e₃ e₄ hp => ?_⟩
  · exact mem_div.trans (and_congr (mem_iff (p ≫ ν.cm.F) _) (mem_iff p _))
  · exact val_ne w p (mem_div.1 hp).1 (mem_div.1 hp).2
  · exact val_pgen g p (mem_div.1 hp).1 (mem_div.1 hp).2 (mem_div.1 hp').1 (mem_div.1 hp').2
  · subst e
    have A := val_pmaps ν.cm.e_comm r x (mem_div.1 hp).1 (mem_div.1 hp).2
    rw [ν.base] at A
    exact A
  · subst e₁
    obtain rfl : pt' = pt ≫ pm := by
      apply Limits.pullback.hom_ext
      · exact e₄.trans (e₂.symm.trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hf)).symm)
      · exact e₃.trans ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hs)).symm)
    exact val_carry hs hc pt (mem_div.1 hp).1 (mem_div.1 hp).2

end GlobalTheory.MoveValues
end

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.WaveIsometry

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBFV

theorem isometry_of_bounded (hRad : JC.RadialModuleForm) (hP : P5.ThmPActualCpt) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (hw : KB.CutWord P p.l0 w) (s : ℂ)
    (x x' : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ) (hε : 0 < ε)
    (hx : ∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) (hx' : ∀ e, JC.NiceCoef (p.T.bs j) ε (x' e))
    (hb : ∀ e, ∃ R, PBF.BSR R (x e)) (hb' : ∀ e, ∃ R, PBF.BSR R (x' e))
    (hbw : ∀ e, ∃ R, PBF.BSR R (KB.waveG (p.T.bs j) s w x' e)) :
    p.form j hj w (KB.waveG (p.T.bs j) s w x) (KB.waveG (p.T.bs j) s w x') = p.form j hj w x x' := by
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X
      (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j))) L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  obtain ⟨K, hThm, -, -, hJc⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hJ := fun (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hF : JC.NiceCoef (p.T.bs j) ε F)
    (hR : ∃ R, PBF.BSR R F) => PBF.pic_of_cptClause (p.T.bs jF) (K 0) hJc hε hF hR.choose_spec
  obtain ⟨Cst, hC, hform⟩ := hRad Wp Wq P p.T jF X μ L st p.l0 hD
  have hwOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2
  choose Φ hΦK hΦ using fun a => hJ (x a) (hx a) (hb a)
  choose Φ' hΦ'K hΦ' using fun a => hJ (x' a) (hx' a) (hb' a)
  have hnx := waveG_nice (p.T.bs j) ε s w x hx
  have hnx' := waveG_nice (p.T.bs j) ε s w x' hx'
  show D.formLev p.T (M.sgn P p.l0) jF w (KB.waveG (p.T.bs j) s w x) (KB.waveG (p.T.bs j) s w x') =
    D.formLev p.T (M.sgn P p.l0) jF w x x'
  have hmem : ∀ (Ψ' : Ix (Fin w.length) → RadSp (JC.parLev P jF).k (JC.parLev P jF).r
      (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'),
      (∀ e, ∀ y ∈ DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        (Ψ' e : Fn (JC.parLev P jF).k (JC.parLev P jF).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _) (B.JF (p.T.bs jF) (KB.waveG (p.T.bs j) s w x' e))
            y.1 y.2) → InK (K 0) Ψ' := by
    intro Ψ' hΨ' e
    obtain ⟨Ψ0, hΨ0K, hΨ0⟩ := hJ (KB.waveG (p.T.bs j) s w x' e) (hnx' e) (hbw e)
    have : Ψ' e = Ψ0 := radSp_ext (fun y hy => (hΨ' e y hy).trans (hΨ0 y hy).symm)
    rw [this]
    exact hΨ0K
  by_cases hr : 0 < P.r - j
  · obtain ⟨Wv, hW⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ s
    obtain ⟨Wv', hW'⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (c : Fin (P.r - j) → ℂ) (_ : Mx P.k (P.r - j)) => fsv s (c ⟨0, hr⟩)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_cell_eq_coord (p.T.bs jF).z_mem (p.T.bs jF).z'_mem hr y.1 hy.2.1]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hx Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx' Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hx hx' hΦ hΦ']
    congr 1
    have key := rr_wave_A (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))
  · have hr0 : P.r - j = 0 := by omega
    obtain ⟨Wv, hW⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' s
    obtain ⟨Wv', hW'⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (_ : Fin (P.r - j) → ℂ) (g : Mx P.k (P.r - j)) => fsv s (P5.zeta P.k (P.r - j) (p.T.bs jF).z
          (p.T.bs jF).z' g)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_top_eq_zeta hr0]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hx Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx' Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hx hx' hΦ hΦ']
    congr 1
    have key := rr_wave_B (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr0 s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))

end GlobalTheory.WaveIsometry
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrderGerm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}



theorem jetD_twist {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)] (y : FrPt Xo c S)
    (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m) (m : ℕ) (cc : Fin C.d → Fin C.d → S)
    (he : ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G cc)) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m)))
    (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin C.d) S)
    (hf : JetD y C.d C.x C.B.A.act C.e C.wP k F m f) :
    JetD y C.d C.x C.B.A.act e' C.wP k F m (f * expP ((k : S) • diagL C.B H.w0 cc)) := by
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf
  obtain ⟨u, hu, hCe⟩ := he
  have h1 := corr_pull_scale _ _ (e' m) (C.e m) (unitΓ u) (homAt y.x (GermD.sL m (C.B.A.act H.w0))).left hCe
  rw [FBIdLB.unitΓ_homAt] at h1
  have hEL : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL y C.d C.x C.B.A.act e' C.wP m)
      (scaleGen _ _ (unitΓ (Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u))
        (eL y C.d C.x C.B.A.act C.e C.wP m)) := by
    have h2 := ReciprocityTheory.ChartRestriction.G.DVR.corr_mulGen
      (ExpTieGerm.corr_refl (L := Xo.univ.t.PP.L) (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (C.x m).left)) h1
    rw [mulGen_scale_right] at h2
    exact h2
  set U : (Jet S (Fin 1 × Fin C.d) m)ˣ := Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u with hU
  set w : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ := unitΓ U with hw
  have hG : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eL y C.d C.x C.B.A.act e' C.wP m) k)
      (scaleGen _ _ (w ^ k) (genPow _ _ (eL y C.d C.x C.B.A.act C.e C.wP m) k)) := by
    have := ExpTieGerm.corr_genPow hEL k
    rwa [genPow_scale] at this
  have h3 := ExpTieGerm.corr_scale hC₁ (w ^ k)
  have hC' := ReciprocityTheory.ChartRestriction.G.DVR.corr_trans hL h3 (ReciprocityTheory.ChartRestriction.G.DVR.corr_symm hG)
  have hV' := isValueAt_scale hV₁ (w ^ k)
  have hprod := unit_jet C.B H.w0 cc m k u hu
  have hinv : psJet m (expP ((k : S) • diagL C.B H.w0 cc)) = ↑((U ^ k)⁻¹) := by
    set X := psJet m (expP ((k : S) • diagL C.B H.w0 cc)) with hX
    calc X = X * ((↑(U ^ k) : Jet S (Fin 1 × Fin C.d) m) * ↑((U ^ k)⁻¹)) := by
          rw [Units.mul_inv, _root_.mul_one]
      _ = (X * ↑(U ^ k)) * ↑((U ^ k)⁻¹) := (_root_.mul_assoc _ _ _).symm
      _ = ↑((U ^ k)⁻¹) := by rw [hprod, _root_.one_mul]
  have hw' : ((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) = unitΓ ((U ^ k)⁻¹) := by
    simp [hw, unitΓ, map_pow, map_inv]
  refine ⟨F₁, _, hP₁, hC', ?_⟩
  have hv : toΓ _ (psJet m (f * expP ((k : S) • diagL C.B H.w0 cc))) =
      toΓ _ (psJet m f) * (((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) :
        Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)) := by
    rw [hw']
    show _ = toΓ _ _ * toΓ _ _
    rw [← map_mul, FBIdJet.psJet_mul, hinv]
  rw [hv]
  exact hV'

theorem jetD_unique {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (D : ℕ) (f g : MvPowerSeries (Fin 1 × Fin d) S)
    (hf : JetD y d x act e wP k F D f) (hg : JetD y d x act e wP k F D g) : psJet D f = psJet D g := by
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := hg
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have hτ := GermFun.gen_eq_of_corr _ hL _ _ _ _ _ _ _ hC₁ hC₂
  subst hτ
  exact GermFun.toΓ_injective _ (GermFun.value_unique _ _ hL _ _ _ _ _ _ hV₁ hV₂)

theorem ord_holds : OrdStatement := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S _ _ _ y C k n D F f hf a P hP hD
  have hs := hnab.1
  obtain ⟨C₀, hex, hpin⟩ := hnab.2 S y
  choose f₀ hf₀ using fun b => hex k (F b)
  obtain ⟨e', hfr, hrig, cc, hT, -, hsym, hbal, hu⟩ :=
    frFixB_of (frTruncFix_of frRatio_holds) linEigSt_holds E H Dw l Xo c hs S y C
  have hgerm : ∀ b, ∃ g, IsGerm y C.d C.x C.B.A.act e' C.wP k (F b) g := fun b => by
    obtain ⟨g, hg⟩ := germSt_holds E H Xo.X Xo.univ.t S y.x C.d C.B.G.F C.B.A.act (Lt1 Dw)
      (fun ℓ => y.u ℓ.1 ℓ.2) C.uvec C.x C.B.ph1 C.B.ph2 C.B.sy C.B.ad e' C.wP
      ((isChart_iff y C.d _ _ _ _).1 C.chart) ((isFrame_iff y C.d _ _ _ _ _ _ _ _).1 hfr) ((isPrim_iff _).1 C.prim)
      (fun m => hT m) k (F b)
    exact ⟨g, (isGerm_iff y C.d _ _ _ _ _ _ _).2 hg⟩
  choose g hg using hgerm
  have h₁ : chartVal C k g P = chartVal C k f P :=
    harmInv_of (expActOf_of linEigSt_holds) E H Dw l Xo c hs S y C (cc D) (hsym D) (hbal D) k n D f g
      (fun b => jetD_unique y C.d C.x C.B.A.act e' C.wP k (F b) D _ _ (hg b D)
        (jetD_twist y C e' D (cc D) (hu D) k (F b) (f b) (hf b))) a P hP hD
  have h₂ := chartIndep2_of_glob GlobalTheory.SemiRigid.globalFns E H Dw l Xo c hs S y
    { C with e := e', frame := hfr, rig0 := hrig } C₀ k n F g f₀ hg hf₀ a P hP
  refine h₁.symm.trans (h₂.trans ?_)
  refine Finset.sum_congr rfl fun m _ => congrArg _ (Finset.prod_congr rfl fun b _ => ?_)
  exact (hpin k (F b) (f₀ b) (hf₀ b) (colOf m b)).symm

end GlobalTheory.OrderGerm
end
end

section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_rational_isometry_of_trace_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r), (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ ≃ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (gam v : Fin r → E)) ∧ (∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  first | exact @GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry | exact GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry | (intros; apply GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry <;> assumption)
end
