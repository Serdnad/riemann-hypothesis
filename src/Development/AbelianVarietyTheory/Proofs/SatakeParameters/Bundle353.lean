module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle343
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle300
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle344
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle342
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle004
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.step_basis_spans_latticeFirstFactor_at_p : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) j hj β, GlobalTheory.TwV.LbAtB (((Z.inTw Fl ht Gt).at' j hj).st.loc β) (((Z.inTw Fl ht Gt).at' j hj).st.K β).lev.Lb := by
  exact fun {D} X0 u w hg Tw μ Z Fl ht Gt =>
    @GlobalTheory.TwV.LbB.lbAtB_inTw D X0 u w hg Tw μ Z Fl ht Gt
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.MvS

theorem cast_lev {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (c : C.cls i) (c' : C'.cls i) (hc' : c' = castCls h i c) (β : S.Ch) (hβ : S.chOf c = β) (κ : (S.K β).lev.U) :
    ∃ κ' : (St.K (St.chOf c')).lev.U, κ'.1 = κ.1 ∧ (St.K (St.chOf c')).lev.chi κ' = (S.K β).lev.chi κ := by
  subst hSt hc' h hβ
  exact ⟨κ, rfl, rfl⟩



theorem pt_step {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (β : S.Ch) (hC : S.Core e β) (a : S.cmpt β)
    (γ : ((S.charts.gat β).lev a).Γ) (L : G.P.Tup) (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (hg' : ∀ v, ((S.charts.gat β).lev a).smul γ L v = colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x x' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hx : (S.loc β).IsPt a g x.1) (hx' : (S.loc β).IsPt a g' x'.1) :
    ∃ κ : (S.K β).lev.U, x'.1 = GlobalTheory.TwU.ratA D.host.F ((S.loc β).gamI a γ) * x.1 * κ.1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((S.K β).lev.chi κ : ℂˣ) : ℂ) ∧
        algebraMap G.O G.Kf ((((S.charts.gat β).lev a).χ γ : G.Oˣ) : G.O) = e r := by
  obtain ⟨κa, hκa⟩ := awayEx_of hC.good (S.K β).lev hC.gam a γ
  obtain ⟨ra, hra1, hra2⟩ := hC.chi a γ κa hκa
  obtain ⟨κ, hκ1, hκ2⟩ := GlobalTheory.TwV.Xc.isPt_move_eq _ _ _ _ _ _ (S.loc β) _ _ _ _ (S.K β).lev hC.good hC.int hC.hypP hC.actB hC.bad_p a γ
    (hC.gamU a γ) κa hκa g g' (fun v => (hg' v).symm.trans (PStabEq.smul_colSpan (G := S.charts.gat β) a γ L g hg v)) x x' hx hx'
  refine ⟨κ, hκ1, ra⁻¹, ?_, ?_⟩
  · rw [map_inv₀, hra1, ← Units.val_inv_eq_inv_val]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (eq_inv_of_mul_eq_one_left hκ2).symm
  · rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hra2

end GlobalTheory.TwV.Xc.MvS

namespace GlobalTheory.TwV.Xc



theorem moveBy_succ : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ i (hi : i + 1 ≤ D.R.m) (c : (sysS H X std).Lv.comp (i + 1)) (La : ((sysS H X std).Pj (i + 1)).Tup) (γ : ((sysS H X std).Lv.lev (i + 1) c).Γ), ((sysS H X std).Pj (i + 1)).IsLatTup La → ∃ g κ, MoveBy std J (i + 1) hi c La γ g κ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS i hi c La γ hL
  obtain ⟨⟨β, a⟩, rfl⟩ := (I.at' i hi).st.eC.surjective c
  have hC := H.core i hi β
  have hpt : ∀ L', ((I.at' i hi).st.loc β).IsPt a
      (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (i + 1) L')
      (J.pt std (i + 1) hi ((I.at' i hi).st.eC ⟨β, a⟩, L')).1 := by
    intro L'
    have h := (Joint.pt_succ_isPt t std J i hi ((I.at' i hi).st.eC ⟨β, a⟩, L')).2
    have key : ∀ (b : Σ β : (I.at' i hi).st.Ch, (I.at' i hi).st.cmpt β), b = ⟨β, a⟩ → ∀ g x, ((I.at' i hi).st.loc b.1).IsPt b.2 g x →
        ((I.at' i hi).st.loc β).IsPt a g x := by
      rintro _ rfl g x h
      exact h
    exact key _ (Equiv.symm_apply_apply _ _) _ _ h
  have hb := Joint.basesAt_span t std J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) hL
  have hb' : ∀ v, (sysS H X std).latAt v (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La) =
      colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La)) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
    intro v
    unfold basesAt
    exact Classical.epsilon_spec (p := fun g' : GL (Fin (((sysS H X std).Pj (i + 1)).m + 1)) ((sysS H X std).G.P.Qq v) =>
      (sysS H X std).latAt v (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La) = colSpan ((sysS H X std).G.P.W v) (g' : Matrix _ _ _))
      ⟨_, PStabEq.smul_colSpan (G := (I.at' i hi).st.charts.gat β) a γ La _ (fun v => hb v) v⟩
  obtain ⟨κ, hκ, r, hr1, hr2⟩ := MvS.pt_step (I.at' i hi).st _ β hC a γ La _ _ (fun v => hb v) (fun v => hb' v) _ _ (hpt La) (hpt _)
  have hc : (I.at' i hi).st.chOf (clsOf (S := (I.at' i hi).st) (H.core i hi) ((I.at' i hi).st.eC ⟨β, a⟩) La) = β :=
    (clsOf_chart (S := (I.at' i hi).st) (H.core i hi) ((I.at' i hi).st.eC ⟨β, a⟩) La hL).trans
      (congrArg Sigma.fst (Equiv.symm_apply_apply (I.at' i hi).st.eC ⟨β, a⟩))
  obtain ⟨κ', hκ'1, hκ'2⟩ := MvS.cast_lev (X.onCh i hi) (I.at' i hi).st (J.St (i + 1) hi) (J.st i hi) _
    (clsAt X H (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩) La) (clsAt_succ X H i hi _ La) β hc κ
  refine ⟨((I.at' i hi).st.loc β).gamI a γ, κ', hC.gamU a γ, ?_, ?_, r, ?_, hr2⟩
  · exact hκ.trans (congrArg _ hκ'1.symm)
  · intro hr v
    have hB : (J.cp std).B (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) =
        Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' i hi).st.loc β).rk.symm) ((I.at' i hi).st.loc β).B := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).B = _
      rw [dite_eq_left hi]
      show Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).rk.symm)
        ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).B = _
      rw [Equiv.symm_apply_apply]
    have hJ : (J.cp std).J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) =
        (gramN D (i + 1) hi).reindex (finCongr ((I.at' i hi).st.loc β).rk.symm) (finCongr ((I.at' i hi).st.loc β).rk.symm) := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).J = _
      rw [dite_eq_left hi]
    have hiw : (J.cp std).iw (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) = ((I.at' i hi).st.loc β).iw := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).iw = _
      rw [dite_eq_left hi]
      show ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).iw = _
      rw [Equiv.symm_apply_apply]
    have hρ : J.rho std v = ((I.at' i hi).st.loc β).iw v := (J.iw i hi β v).symm
    have hF : (J.fd std).frM (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) v =
        (((LinearMap.toMatrix' ((stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La))).toLinearMap)) *
          ((J.cp std).B (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La)).1).map ((J.cp std).iw (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) v)).submatrix
          (finCongr rfl) (finCongr rfl) := rfl
    rw [hF, hB, hJ, hiw, hρ]
    exact Mv0.frm_gen (Q := (sysS H X std).G.P.Qq v) _ ((I.at' i hi).st.loc β).rk hr (gramN D (i + 1) hi) ((I.at' i hi).st.loc β).B (((I.at' i hi).st.loc β).gamI a γ)
      (((I.at' i hi).st.loc β).iw v) _ (hC.actB a v γ)
  · exact hr1.trans (congrArg (fun z : ℂˣ => (z : ℂ)) hκ'2.symm)

end GlobalTheory.TwV.Xc

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.ChiPow

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem exists_upts_det {n : ℕ} (hn : 0 < n) (Gm : Matrix (Fin n) (Fin n) E) (C : GL (Fin n) E)
    (hC : cT (σ : E →+* E) C.1 * C.1 = Gm) (x : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ)
    (hx : (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * sigR σ _ x = 1) :
    ∃ Y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), Y ∈ UPts σ Gm (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det Y = x := by
  set R := FiniteAdeleRing (𝓞 F) F
  let f : Fin n → (E ⊗[F] R)ˣ := Pi.mulSingle ⟨0, hn⟩ x
  have hf : f = Pi.mulSingle ⟨0, hn⟩ x := rfl
  let d : GL (Fin n) (E ⊗[F] R) := Units.map (Matrix.diagonalRingHom (Fin n) (E ⊗[F] R)).toMonoidHom
    (MulEquiv.piUnits.symm f)
  have hd : (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = Matrix.diagonal (fun k => ((f k : (E ⊗[F] R)ˣ) : E ⊗[F] R)) := rfl
  let Cb := bc (inclE (F := F) R) C
  refine ⟨Cb⁻¹ * d * Cb, ?_, ?_⟩
  · have hsig : (inclE (F := F) R).comp (σ : E →+* E) = (sigR σ R).comp (inclE R) := by
      ext e
      simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
    have hG : Gm.map (inclE (F := F) R) = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
      rw [← hC, Matrix.map_mul, ← Formalism.UG.P.cT_map (σ : E →+* E) (sigR σ R) (inclE R) hsig]
      rfl
    have hdd : cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 := by
      rw [hd]
      unfold cT
      rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      by_cases hk : k = ⟨0, hn⟩
      · subst hk
        rw [hf, Pi.mulSingle_eq_same, mul_comm]
        exact hx
      · rw [hf, Pi.mulSingle_eq_of_ne hk, Units.val_one, map_one, one_mul]
    have h1 : cT (sigR σ R) ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
        cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 := by
      rw [← cT_mul, Units.mul_inv, cT_one]
    have h2 : (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 :=
      Units.mul_inv Cb
    show cT (sigR σ R) (((Cb⁻¹ * d * Cb : GL (Fin n) (E ⊗[F] R))) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * Gm.map (inclE (F := F) R) *
      (((Cb⁻¹ * d * Cb : GL (Fin n) (E ⊗[F] R))) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = Gm.map (inclE (F := F) R)
    rw [hG, Units.val_mul, Units.val_mul, cT_mul, cT_mul]
    calc _ = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          (cT (sigR σ R) ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          ((Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
            simp only [Matrix.mul_assoc]
      _ = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          (cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (d : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
            rw [h1, h2]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hdd, Matrix.mul_one]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul, hd, Matrix.det_diagonal]
    rw [← Units.coe_prod, hf, Finset.prod_pi_mulSingle', if_pos (Finset.mem_univ _)]
    calc _ = (Matrix.det ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          Matrix.det (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R))) * (x : E ⊗[F] R) := by ring
      _ = _ := by rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

end Gen

end GlobalTheory.TwV.Xc.ChiPow

namespace GlobalTheory.TwV.Xc.ChiPow



theorem tw_ch_rat {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}
    (S : StepIn M i hi G) (β : S.Ch) (hr : S.ChRat β)
    (X : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = ((S.tw β).ch X : ℂ) := by
  obtain ⟨cl, hcl⟩ := (S.K β).y_bij.2 (Quotient.mk'' X)
  have hrel := Quotient.eq''.1 hcl
  rw [DoubleCoset.rel_iff] at hrel
  obtain ⟨h, hh, k, hk, hX⟩ := hrel
  obtain ⟨γ, hγ, hγh⟩ := hh
  have h1 := (S.tw β).ch_rat γ hγ h hγh.symm
  have h2 := (S.tw β).ch_U k hk
  obtain ⟨rc, hrc⟩ := hr cl
  refine ⟨(∏ τ, (tEL D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det) ^ (cTw D i))⁻¹ * rc, ?_⟩
  rw [hX, map_mul (S.tw β).ch, map_mul (S.tw β).ch, h2, mul_one, Units.val_mul, map_mul D.what₂.embLL, hrc, map_inv₀, map_prod]
  congr 1
  have e1 : ∏ τ, D.what₂.embLL (tEL D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det ^ cTw D i) =
      ∏ τ, (embT D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det) ^ cTw D i :=
    Finset.prod_congr rfl fun τ _ => by rw [map_zpow₀, tEL_emb]
  rw [e1]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end GlobalTheory.TwV.Xc.ChiPow

namespace GlobalTheory.TwV.Xc



theorem chiI_pow_rat : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), (sysS H X std).Lv.comp j → ∀ x ∈ U1 (sigD D), ∃ r : D.what₂.LL, D.what₂.embLL r = chiI J x ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj c x hx
  cases j with
  | zero => exact ⟨1, by simp⟩
  | succ i =>
    have hi : i + 1 ≤ D.R.m := hj
    have hxc : (x : AfE D.host.F D.host.E) * sigR (sigD D) _ x = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hx)
    obtain ⟨Y, hY, hYd⟩ := ChiPow.exists_upts_det (sigD D) Nat.one_pos (1 : Matrix (Fin 1) (Fin 1) D.host.E) 1
      (by rw [Units.val_one, cT_one, Matrix.one_mul]) x hxc
    have hex : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x := ⟨⟨Y, hY⟩, hYd⟩
    have hchi : chiI J x = ((D.chiD (J.dtU hex.choose) : ℂˣ) : ℂ) := by
      unfold chiI
      rw [dite_eq_left hex]
    obtain ⟨Z, hZ, hZd⟩ := ChiPow.exists_upts_det (sigD D) (D.R.N_pos (i + 1)) (gramN D (i + 1) hi) (J.A.crd (i + 1) hi)
      (J.pins.crd_orth (i + 1) hi) x hxc
    let β := ((I.at' i hi).st.eC.symm c).1
    have htw := J.tw i hi β ⟨Z, hZ⟩ hex.choose (hex.choose_spec.trans hZd.symm)
    obtain ⟨r, hr⟩ := ChiPow.tw_ch_rat (I.at' i hi).st β (H.core i hi β).chRat ⟨Z, hZ⟩
    have ht : (sysS H X std).t = D.R.t := (GlobalTheory.TwV.DelB.sysS_ranks S).2.1
    refine ⟨r, ?_⟩
    rw [hr, htw, hchi, ht, Units.val_zpow_eq_zpow_val]
    rfl

end GlobalTheory.TwV.Xc

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.comparisonSite_charts_twists_eq_tupleChain : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (Hh : Formalism.L2.Herm.SymmetricHermitianColumns D) (St : GlobalTheory.TwU.ChainCharts D u μ) (hv : ValAll Tw St), Z.Fo = foOf Hh St hv → (∀ j hj, St (j + 1) hj = GlobalTheory.TwU.StepCharts.ofStepIn ((Z.inTw Fl ht Gt).at' j hj).st) ∧ ∀ j hj β (x : UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 → (((Z.inTw Fl ht Gt).at' j hj).st.tw β).ch x = D.chiD (Hh.dt y) ^ cTw D (j + 1) := by
  first | exact @GlobalTheory.Port.siteD_inTw_charts_tw | exact GlobalTheory.Port.siteD_inTw_charts_tw | (intros; apply GlobalTheory.Port.siteD_inTw_charts_tw <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTuple_chart_eq_of_same_component : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), ((sysS H X std).Pj j).IsLatTup La → ((sysS H X std).Pj j).IsLatTup Lb → J.chart std j hj (c, La) = J.chart std j hj (c, Lb)) := by
  first | exact @GlobalTheory.TwV.Xc.chart_eq_of_comp | exact GlobalTheory.TwV.Xc.chart_eq_of_comp | (intros; apply GlobalTheory.TwV.Xc.chart_eq_of_comp <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' z = S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe hr hr' z)) := by
  first | exact @GlobalTheory.TwV.Xc.xiM_eq_adelic | exact GlobalTheory.TwV.Xc.xiM_eq_adelic | (intros; apply GlobalTheory.TwV.Xc.xiM_eq_adelic <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coeff_renamed_thetaClass_series : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) {K : Type} [Field K] (ι : ℂ →+* K) (j : ℕ) (hN : RankTie X D j) (La : X.Lt j) (La' : X.Lt (j + 1)) (s : K) (α : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) →₀ ℕ), MvPowerSeries.coeff (α.mapDomain (eIdx X D pos j hN)) (resV (kapOf X pos j) (s • MvPowerSeries.map ι (tay (thCl t u μ cls j La La')))) = s * ι (TaylorLogMetric.taylor D ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (cls (j + 1) La'.1 La'.2)) α) := by
  first | exact @GlobalTheory.TwV.DelB.coeff_resV_thCl | exact GlobalTheory.TwV.DelB.coeff_resV_thCl | (intros; apply GlobalTheory.TwV.DelB.coeff_resV_thCl <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_adelic_latticeTuple_decomposition : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → Nonempty (Dec J std)) := by
  first | exact @GlobalTheory.TwV.DelB.dec_exists | exact GlobalTheory.TwV.DelB.dec_exists | (intros; apply GlobalTheory.TwV.DelB.dec_exists <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelFunction_latticeTuple_pair_eq_adelic : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)), ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') = reV hr hr' (kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D j (Nat.le_of_succ_le hj)) J.a (J.pt std j (Nat.le_of_succ_le hj) La).1 ((J.St j (Nat.le_of_succ_le hj)).K (J.chart std j (Nat.le_of_succ_le hj) La)).lev.Lb) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La').1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La')).lev.Lb) (S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La')))) := by
  first | exact @GlobalTheory.TwV.DelB.kerTh_pair_eq | exact GlobalTheory.TwV.DelB.kerTh_pair_eq | (intros; apply GlobalTheory.TwV.DelB.kerTh_pair_eq <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.padicSeries_algebraic_multiple_via_place_extension : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ {a b : ℕ} (K G : TaylorLogMetric.VC D a b → ℂ) (s s' : ℂ), s ∈ TaylorLogMetric.Qbar → TaylorLogMetric.CoefIn D K TaylorLogMetric.Qbar → (∀ z, K z = s' * G z) → serP lam (fun z => s * K z) = ι (s * s') • MvPowerSeries.map ι (tay G) := by
  first | exact @GlobalTheory.TwV.SerMap.padicSeries_const_mul | exact GlobalTheory.TwV.SerMap.padicSeries_const_mul | (intros; apply GlobalTheory.TwV.SerMap.padicSeries_const_mul <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pullback_then_frame_substitution_eq_changed_frames : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → (∀ v, IsUnit (fd.frM j La v).det ∧ IsUnit (fd.frM (j + 1) La' v).det) → ∀ x y, ∑ z, ι (pullMat (e j La) (e (j + 1) La') x z) * (c * subBG E pos fd j La La' z y) = c * subBG E pos (reframe fd ρ e) j La La' x y := by
  first | exact @GlobalTheory.TwV.DelB.sum_pullMat_subBG_reframe | exact GlobalTheory.TwV.DelB.sum_pullMat_subBG_reframe | (intros; apply GlobalTheory.TwV.DelB.sum_pullMat_subBG_reframe <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.taylorSeries_matrixPullback_eq_linear_substitution : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ Θ → tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ) = linSub (pullMat e e') (tay Θ) := by
  first | exact @GlobalTheory.TwV.DelB.tay_pull_linSub | exact GlobalTheory.TwV.DelB.tay_pull_linSub | (intros; apply GlobalTheory.TwV.DelB.tay_pull_linSub <;> assumption)
end
