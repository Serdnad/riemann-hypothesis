module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle172
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle180
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle184
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle160
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle140
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle141
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle175
import Aesop.Main
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle183
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Module.HahnBanach
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

theorem nice_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} {ε ε' : ℝ}
    (h : JC.NiceCoef Bs ε F) (hle : ε' ≤ ε) : JC.NiceCoef Bs ε' F :=
  ⟨h.1, h.2.1, fun g hg hne => le_trans hle (h.2.2 g hg hne)⟩

theorem common_eps_R {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    {ι ι' : Type} [Fintype ι] [Fintype ι'] (x : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (x' : ι' → B.Mat k r → (Wq →L[ℂ] Wp))
    (hx : ∀ e, KB.CptCoef Bs (x e)) (hx' : ∀ e, KB.CptCoef Bs (x' e)) :
    ∃ ε, 0 < ε ∧ ∃ R, (∀ e, JC.NiceCoef Bs ε (x e)) ∧ (∀ e, BSR R (x e)) ∧ (∀ e, JC.NiceCoef Bs ε (x' e)) ∧
      (∀ e, BSR R (x' e)) := by
  choose e1 he1 hn1 using fun e => (cpt_nice_bsr (hx e)).1
  choose e2 he2 hn2 using fun e => (cpt_nice_bsr (hx' e)).1
  choose R1 hR1 using fun e => (cpt_nice_bsr (hx e)).2
  choose R2 hR2 using fun e => (cpt_nice_bsr (hx' e)).2
  obtain ⟨ε1, hε1, h1⟩ := Formalism.FourierDecayAlt.P.JCx2.exists_common_eps (fun e ε => JC.NiceCoef Bs ε (x e))
    (fun e ε ε' _ h hF => nice_mono hF h) (fun e => ⟨e1 e, he1 e, hn1 e⟩)
  obtain ⟨ε2, hε2, h2⟩ := Formalism.FourierDecayAlt.P.JCx2.exists_common_eps (fun e ε => JC.NiceCoef Bs ε (x' e))
    (fun e ε ε' _ h hF => nice_mono hF h) (fun e => ⟨e2 e, he2 e, hn2 e⟩)
  let R := (∑ e, |R1 e|) + ∑ e, |R2 e|
  have hb1 : ∀ e, R1 e ≤ R := fun e => (le_abs_self _).trans ((Finset.single_le_sum (f := fun e => |R1 e|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ e)).trans (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
  have hb2 : ∀ e, R2 e ≤ R := fun e => (le_abs_self _).trans ((Finset.single_le_sum (f := fun e => |R2 e|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ e)).trans (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
  refine ⟨min ε1 ε2, lt_min hε1 hε2, R, fun e => nice_mono (h1 e) (min_le_left _ _),
    fun e g hg hne => (hR1 e g hg hne).trans (hb1 e), fun e => nice_mono (h2 e) (min_le_right _ _),
    fun e g hg hne => (hR2 e g hg hne).trans (hb2 e)⟩

theorem pb_sizeStdCpt_main : Formalism.FourierDecayAlt.KB.SizeStdCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w ys hc1 hc2 hys
  have hOK : P.OK := p.hP.1
  obtain ⟨hl1, hlk, -⟩ := p.hl
  have hqpos := qw_pos P hOK p.l0 hl1 hlk w ys hc1 hc2
  refine ⟨fun y hy => (hqpos y hy).1, ?_⟩
  intro x x' hx hx'
  obtain ⟨ε, hε, R, hxN, hxR, hx'N, hx'R⟩ := common_eps_R (p.T.bs j) x x' hx hx'
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJc⟩ := hP Wp Wq (Fin (KB.plusW ys w).length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Cst, hC, hform⟩ := Formalism.FourierDecayAlt.P.radial_module_form Wp Wq P p.T jF X μ L st p.l0 hD
  have hJ' : PicsInBS p.T jF (K 0) := fun F ε R hε hF hR => pic_of_cptClause (p.T.bs jF) (K 0) hJc hε hF hR

  choose Φ hΦK hΦ using fun a => hJ' (x a) ε R hε (hxN a) (hxR a)
  choose Φ' hΦ'K hΦ' using fun a => hJ' (x' a) ε R hε (hx'N a) (hx'R a)

  let Pts : Set ℝ := {Y | (∃ l ∈ KB.plusW ys w, l.2 = Y) ∨ (∃ l ∈ KB.minusW ys w, l.2 = Y)}
  have hW1 := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 (KB.plusW ys w)
    hc1.1 hc1.2
  have hW2 := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 (KB.minusW ys w)
    hc2.1 hc2.2
  have hPts : ∀ Y ∈ Pts, ∃ s0 : Fin (KB.plusW ys w).length,
      WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' st p.l0
        [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ (Fin (KB.plusW ys w).length))] := by
    intro Y hY
    have hn : 0 < (KB.plusW ys w).length ∧ I.OnCut P.u P.u' p.l0 Y := by
      rcases hY with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
      · exact ⟨List.length_pos_of_mem hl, cutWord_mem P hc1 hl⟩
      · exact ⟨by rw [← len_pm]; exact List.length_pos_of_mem hl, cutWord_mem P hc2 hl⟩
    refine ⟨⟨0, hn.1⟩, wordOK_gen (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 _ (by simp)
      (fun l hl => ⟨Y, by simp at hl; rw [hl], hn.2⟩) (by simp)⟩
  have hΦU : ∀ e, Φ e ∈ Ucls (K 0) (Gen L st Pts) := fun e => pic_mem_UclsC hD hJ' Pts hε (hxN e) (hxR e) (Φ e) (hΦ e)
  have hΦ'U : ∀ e, Φ' e ∈ Ucls (K 0) (Gen L st Pts) := fun e =>
    pic_mem_UclsC hD hJ' Pts hε (hx'N e) (hx'R e) (Φ' e) (hΦ' e)

  have hS := isStart_QQi _ _ _ _ _ X μ L st p.l0 hD 0
  have hle := Ucls_le (K 0) (Gen L st Pts)
  have hU := (sesquilinear_level_zero_pairing hThm).mono hle

  have hP1 : ∀ l ∈ Lw ys w ++ Ww ys w, ∃ Y ∈ Pts, l.pt = (Y : ℂ) := by
    intro l hl
    rw [Lw_append_Ww] at hl
    unfold D.positionted at hl
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hl
    exact ⟨((KB.plusW ys w).get a).2, Or.inl ⟨_, List.get_mem _ _, rfl⟩, rfl⟩
  have hLmem : ∀ l ∈ Lw ys w, ∃ y ∈ ys, l.pt = (y : ℂ) := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    rw [Lw_getElem]
    exact ⟨_, List.getElem_mem _, rfl⟩
  have hP2 : ∀ l ∈ Lw ys w, ∃ Y ∈ Pts, l.pt + 1 = (Y : ℂ) := by
    intro l hl
    obtain ⟨y, hy, e⟩ := hLmem l hl
    refine ⟨y + 1, Or.inr ⟨(false, y + 1), ?_, rfl⟩, by rw [e]; push_cast; ring⟩
    rw [minusW_eq]
    exact List.mem_append_left _ (List.mem_map.2 ⟨y, hy, rfl⟩)
  have hOK1 : WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' st p.l0
      (Lw ys w ++ Ww ys w) := by rw [Lw_append_Ww]; exact hW1
  have hOK2 : WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' st p.l0
      ((Lw ys w).map dl ++ Ww ys w) := by
    rw [Lw_dual]
    exact cast_map_pred (len_pm ys w) (fun k u => WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z'
      (p.T.bs jF).π (p.T.bs jF).π' st p.l0 u) _ hW2
  have hDK : FormPairingAction.DKHyp (M.qC (JC.parLev P jF)) (Ww ys w) (Lw ys w) := by
    refine ⟨Lw_plus ys w, good_of_adm st _ hOK1.1, good_of_adm st _ hOK2.1, Lw_pairwise w ys hys, ?_⟩
    intro l hl
    obtain ⟨y, hy, e⟩ := hLmem l hl
    rw [e, qw_Ww]
    intro h0
    have := (hqpos y hy).1
    rw [show qw (M.qC P) (D.positionted w) (y : ℂ) = qw (M.qC (JC.parLev P jF)) (D.positionted w) (y : ℂ) from rfl, h0] at this
    simp at this
  have dk := dk_radial hD hThm Pts hPts (Ww ys w) (Lw ys w) hDK hOK1 hOK2 hP1 hP2 Φ
    (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) hΦU (fun e => hΦ'U _)

  have hRRw : RRw (QQi L st 0) (D.positionted w) ∈ entSub (adjB (Ucls (K 0) (Gen L st Pts)) (bet μ) hU) := by
    refine rrw_mem_at _ _ fun l hl a b => ?_
    unfold D.positionted at hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    refine gen_mem_adjB hThm hS Pts hPts ⟨(w.get i).2, Or.inl ⟨w.get i, ?_, rfl⟩, a, b, rfl⟩
    rw [plusW_eq]; exact List.mem_append_right _ (List.get_mem _ _)
  have hodd := bet_neg (k := (JC.parLev P jF).k) (r := (JC.parLev P jF).r) (z := (p.T.bs jF).z)
    (z' := (p.T.bs jF).z') (π := (p.T.bs jF).π) (π' := (p.T.bs jF).π') μ
  have hmn : w.length ≤ (KB.plusW ys w).length := by rw [len_plusW]; omega
  have ePlus := hform (KB.plusW ys w) x x Φ Φ ε hε hxN hxN hΦ hΦ
  have eMinus := hform (KB.minusW ys w) x' x' Φ' Φ' ε hε hx'N hx'N hΦ' hΦ'
  have ePJ := pairJ_rel (w := w) (fun F Ψ => JC.NiceCoef (p.T.bs jF) ε F ∧ IsPic p.T jF Ψ F) (Cst : ℂ)
    (p.form j hj w) (fun u u' => form μ 0 (P5.act (RRi L st 0 (D.positionted w)) u) u' 0)
    (fun u u' v v' hu hu' => hform w u u' v v' ε hε (fun e => (hu e).1) (fun e => (hu' e).1) (fun e => (hu e).2)
      (fun e => (hu' e).2)) ys x x' Φ Φ' (fun e => ⟨hxN e, hΦ e⟩) (fun e => ⟨hx'N e, hΦ' e⟩)
  have eXi := pairJ_rel (w := w) (fun a b => a = b ∧ a ∈ Ucls (K 0) (Gen L st Pts)) (1 : ℂ)
    (fun u u' => form μ 0 (P5.act (RRi L st 0 (D.positionted w)) u) u' 0)
    (fun x x' => ∑ e, bet μ (actP (RRw (QQi L st 0) (D.positionted w)) x e) (x' e))
    (fun u u' v v' hu hu' => by
      have e1 : u = v := funext fun e => (hu e).1
      have e2 : u' = v' := funext fun e => (hu' e).1
      subst e1 e2
      rw [one_mul]
      have hin : InU (Ucls (K 0) (Gen L st Pts)) (actP (RRw (QQi L st 0) (D.positionted w)) u) :=
        blockMulVec_apply_mem (fun a b x hx => (hRRw a b).1 x hx) (fun e => (hu e).2)
      exact form_zero_eq_position_pairing_of_le hThm hmn _ _ (fun a => hle (hin a)) (fun a => hle (hu' a).2))
    ys Φ Φ' Φ Φ' (fun e => ⟨rfl, hΦU e⟩) (fun e => ⟨rfl, hΦ'U e⟩)
  have ePosition := position_pair (V := RadSp (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z'
    (p.T.bs jF).π (p.T.bs jF).π') (bet μ) hodd (QQi L st 0) w ys Φ Φ'
  have eA : form μ 0 (P5.act (RRi L st 0 (Lw ys w ++ Ww ys w)) Φ) Φ 0 =
      form μ 0 (P5.act (RRi L st 0 (D.positionted (KB.plusW ys w))) Φ) Φ 0 := by rw [Lw_append_Ww]
  have eB : form μ 0 (P5.act (RRi L st 0 ((Lw ys w).map dl ++ Ww ys w)) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))))
      (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0 =
      form μ 0 (P5.act (RRi L st 0 (D.positionted (KB.minusW ys w))) Φ') Φ' 0 := by
    rw [Lw_dual]
    show form μ 0 (actP (RRw (QQi L st 0) ((D.positionted (KB.minusW ys w)).map (castL (len_pm ys w))))
      (fun z => Φ' (z ∘ Fin.cast (len_pm ys w)))) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0 = _
    have hc := blockMulVec_cast (QQi L st 0) (len_pm ys w) (D.positionted (KB.minusW ys w)) Φ'
    exact (congrArg (fun V => form μ 0 V (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0) hc).trans
      (form_castIx μ (len_pm ys w) _ _ 0)

  obtain ⟨hAi, -, hBi, -, hdk⟩ := dk
  have ePlus' : p.form j hj (KB.plusW ys w) x x =
      (Cst : ℂ) * form μ 0 (P5.act (RRi L st 0 (Lw ys w ++ Ww ys w)) Φ) Φ 0 := ePlus.trans (congrArg _ eA.symm)
  have eMinus' : p.form j hj (KB.minusW ys w) x' x' = (Cst : ℂ) *
      form μ 0 (P5.act (RRi L st 0 ((Lw ys w).map dl ++ Ww ys w)) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))))
        (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0 := eMinus.trans (congrArg _ eB.symm)
  have hPJ : KB.pairJ (p.form j hj w) ys x x' = (Cst : ℂ) *
      pairS (bet μ) (actP (JL (Lw ys w) * RRw (QQi L st 0) (Ww ys w)) Φ) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) :=
    ePJ.trans (congrArg (fun t => (Cst : ℂ) * t) (eXi.trans ((one_mul _).trans ePosition.symm)))
  have hQ : ((Lw ys w).map fun l => qw (M.qC (JC.parLev P jF)) (Ww ys w) l.pt).prod =
      (ys.map fun y : ℝ => qw (M.qC P) (D.positionted w) (y : ℂ)).prod := congrArg List.prod (Lw_qw _ ys w)
  have hre : (ys.map fun y : ℝ => (qw (M.qC P) (D.positionted w) (y : ℂ)).re) =
      (ys.map fun y : ℝ => qw (M.qC P) (D.positionted w) (y : ℂ)).map Complex.re := by
    rw [List.map_map]; rfl
  rw [hPJ, ePlus', eMinus', hre]
  refine final_ineq Cst _ _ _ _ _ hQ (fun z hz => ?_) hAi hBi hdk
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  exact hqpos y hy

end

end Formalism.FourierDecayAlt.P.PBF

namespace Formalism.FourierDecayAlt.P

theorem size_standard_compact : Formalism.FourierDecayAlt.KB.SizeStdCpt := PBF.pb_sizeStdCpt_main

end Formalism.FourierDecayAlt.P
end

section

open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inCC_antiA {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {A A' : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : A' ≤ A) (hF : B.InCC A m F) : B.InCC A' m F := by
  obtain ⟨c, hc1, hc2⟩ := hF
  refine ⟨c, hc1, fun u w hu hw hl g hg => ?_⟩
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 h) (norm_nonneg _)).trans
    (hc2 u w hu hw hl g hg)

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem cCg_antiA {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {A A' Bg : ℝ} {F : GFn S v} (h : A' ≤ A)
    (hF : CCg S v A Bg F) : CCg S v A' Bg F :=
  fun m => inCC_antiA (by linarith) (hF m)

theorem locCC_antiA {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A A' Bg : ℝ} {J : GFn S v} (h : A' ≤ A) (hJ : LocCC S T v A Bg J) : LocCC S T v A' Bg J := by
  refine ⟨hJ.1, fun δ hδ => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := hJ.2 δ hδ
  exact ⟨F, h1, cCg_antiA h h2, h3⟩

theorem locCC_JF {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A Bg : ℝ} {F : GFn S v} (hF : B.CkOn ⊤ (B.GV S.G.k S.G.r) F) (hA : ∀ m : ℕ, B.InCC A m F)
    (hFF : B.JF (T v).base F ∈ smoothFormsPositiveCone S T v) (hBg : 0 ≤ Bg) : LocCC S T v A Bg (B.JF (T v).base F) :=
  ⟨hFF, fun _ _ => ⟨F, hF, fun m => inCC_antiA (sub_le_self _ (mul_nonneg hBg (Nat.cast_nonneg m))) (hA m),
    fun _ _ _ => rfl⟩⟩

theorem locCC_smul {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A Bg : ℝ} (c : ℂ) {J : GFn S v} (hJ : LocCC S T v A Bg J) : LocCC S T v A Bg (c • J) := by
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_smul hJ.1 c, fun δ hδ => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := hJ.2 δ hδ
  refine ⟨c • F, Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' c h1, fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c0, hc0⟩ := h2 m
    exact ⟨‖c‖ * c0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul c hc0⟩
  · rw [Formalism.FourierDecayAlt.P.CutMP.En.JF_smul', Pi.smul_apply, h3 x hx hG]

end loc

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBI

def ExhPic : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    KB.IsTopLift2 P p.l0 p.T.base L₀ st₀ p.Θ →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (e : Wd.Ix (Fin w.length)) (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₁ ∧ KB.CptCoef p.T.base F₂ ∧
      (∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V (p.Θ.Θ w e F₁) (h ++ [(1, ζ)])) ∧
      (∀ Φ₁ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ₁ F₁ →
        Top.IsRadOf P p.T.base
          (P5.act ((Fr.ofWord L₀ st₀ (D.positionted w)).F * P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e) F₂) ∧
      ∀ (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e') (KB.slv p.T F P.r le_rfl w h hh.2 e')) →
        ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
          0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
          B.JF (p.T.bs P.r) (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h)) γ =
            (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem exhaustion_of_radial_form : PBI.ExhPic → PBI.Exh := by
  intro hPic Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb hD hdd hF hcut e h hh
  obtain ⟨X₀, μ₀, L₀, st₀, hD₀, hTL⟩ := p.hΘ
  obtain ⟨F₁, F₂, hF₁, hF₂, hloc, hpic, hii⟩ :=
    hPic Wp Wq P p F w X μ L st Cb X₀ μ₀ L₀ st₀ hD hD₀ hTL hdd hF hcut e h hh
  obtain ⟨F', hF', hagree, hVeq⟩ := theta_compact_support Wp Wq P p F₁ w e Cb hdd hF₁ hcut
  refine ⟨F₂, hF₂, fun ζ => ?_, hii⟩
  obtain ⟨Φ₁, hΦ₁⟩ := PBN.radExists p hF₁
  have hΘpic := hTL w hcut F₁ hF₁ Φ₁ hΦ₁ e
  have hF'pic := PBN.isRadOf_congr p.T.base hΘpic hagree
  rw [hloc ζ, hVeq]
  exact PBN.vecV_eq_of_rad density_constant p hF' hF₂ hF'pic (hpic Φ₁ hΦ₁) _

theorem head_top_of_radial_exhaustion (hU5 : PBI.HighestUnipotentIntegral) (hPic : PBI.ExhPic) (hW : PBI.HeadWeightAt) : KB.HeadTop :=
  head_top_of_parts hU5 (exhaustion_of_radial_form hPic) hW

end Formalism.FourierDecayAlt.P
end
end

section

open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem aCInt_of_proper (hP : ACProper) : ACInt := by
  intro k r Wp Wq _ _ _ _ D φ₀ hφ hφc g hg
  obtain ⟨P, hPc, hPm⟩ := hP k r Wp Wq D (tsupport φ₀) {g} hφc isCompact_singleton
    (Set.singleton_subset_iff.2 hg)
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨fun K hK => D.haarW'.finite_compact K hK⟩
  have hfin : D.μSS P < ⊤ := by
    show ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) P < ⊤
    exact hPc.measure_lt_top
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hφ' : Continuous (fun x : Mt k r => φ₀ (Matrix.of x)) :=
    hφ.comp (continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i))
  have hmeasφ : Measurable (fun x : Mt k r => φ₀ (Matrix.of x)) := hφ'.measurable
  have hmeas : Measurable (fun p : B.SS k r => φ₀ (B.sgs p g)) := by
    have h1 : Measurable (fun p : B.SS k r => Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgF (p, (g : Mt k r))) :=
      Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgF_meas.comp (measurable_id.prodMk measurable_const)
    exact hmeasφ.comp h1
  have hind : Integrable (P.indicator fun _ : B.SS k r => M) D.μSS :=
    (integrable_indicator_iff hPc.isClosed.measurableSet).2 (integrableOn_const hfin.ne)
  refine hind.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  by_cases hpP : p ∈ P
  · rw [Set.indicator_of_mem hpP]; exact hM _
  · have h0 : φ₀ (B.sgs p g) = 0 := by
      by_contra hne
      exact hpP (hPm p hp g rfl (subset_tsupport _ hne))
    rw [h0, norm_zero, Set.indicator_of_notMem hpP]

theorem averaging_integrability_holds : ACInt := aCInt_of_proper averaging_properness_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nd_deriv_smul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℂ) (v : E) :
    deriv (fun t => φ t • v) 0 = deriv φ 0 • v := by
  by_cases hφ : DifferentiableAt ℝ φ 0
  · exact deriv_smul_const hφ v
  by_cases hv : v = 0
  · simp [hv]
  rw [deriv_zero_of_not_differentiableAt hφ, zero_smul]
  apply deriv_zero_of_not_differentiableAt
  intro hd
  apply hφ
  obtain ⟨ℓ, -, hℓv⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)
  have h1 : DifferentiableAt ℝ (fun t => ℓ (φ t • v)) 0 :=
    (ℓ.restrictScalars ℝ).differentiableAt.comp 0 hd
  have hn : ℓ v ≠ 0 := by
    rw [hℓv]; exact RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  have h2 : φ = fun t => ℓ (φ t • v) * (ℓ v)⁻¹ := by
    funext t
    rw [map_smul, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hn, mul_one]
  rw [h2]
  exact h1.mul_const _

theorem nd_exp_mem {k r : ℕ} {X : B.Mat k r} (hX : X ∈ JfS.lieOf (Nset k r)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Q.Nlev k r 0 :=
  ⟨hX t, (hX t).1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩

theorem nd_om_mem {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r z z' :=
  ⟨⟨hg.1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩

theorem nilpotent_derivative : NDiff := by
  intro k r Wp Wq _ _ _ _ D m J hJ
  obtain ⟨_, hL, hR, _⟩ := hJ
  constructor
  · intro X hX
    refine ⟨deriv (fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩
    show deriv (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
    have e : (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) =
        fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X)) • J g :=
      funext fun t => hR g (nd_om_mem hg) _ (nd_exp_mem hX t)
    rw [e, nd_deriv_smul_const]
  · intro X hX
    refine ⟨deriv (fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩
    show deriv (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) 0 = _
    have e : (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) =
        fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X)) • J g :=
      funext fun t => hL g (nd_om_mem hg) _ (nd_exp_mem hX t)
    rw [e, nd_deriv_smul_const]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
