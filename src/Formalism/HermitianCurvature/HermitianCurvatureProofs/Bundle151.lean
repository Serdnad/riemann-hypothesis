module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockRelationTwistedHeight
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTCLocalFrameC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle092
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle140
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLIsoAlg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle116
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.FinRangeListSplitting

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

section split

variable {k ρ : ℕ} {z z' : Fin (2 * (1 + ρ) + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem finRange_split (ρ : ℕ) :
    (List.finRange (1 + ρ)).reverse = (List.finRange ρ).reverse.map shS ++ [⟨0, by omega⟩] := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  by_cases hi : i < ρ
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [List.getElem_reverse, List.getElem_map, List.getElem_finRange, List.length_finRange]
    ext
    simp [shS]
    omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_reverse, List.getElem_finRange, List.length_finRange, List.length_map,
      List.length_reverse, List.getElem_singleton]
    ext
    simp
    omega

theorem bTall_split (L : R.LevelData (Pr (RadSp k (1 + ρ) z z' π π')) (1 + ρ)) (w : List (Wd.Letter ℂ S)) :
    P5.bTall L w = ((List.finRange ρ).reverse.map fun l => P5.bTl L (shS l) w).prod * P5.bTl L ⟨0, by omega⟩ w := by
  unfold P5.bTall
  rw [finRange_split, List.map_append, List.map_map, List.prod_append]
  simp [Function.comp_def]

end split

section rel

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem arel_listProd {ι : Type} (f : ι → Wd.SlopeTestRemainingChoices S (Pr V)) (f' : ι → Wd.SlopeTestRemainingChoices S (Pr V'))
    (h : ∀ i, ARel T (f i) (f' i)) : ∀ l : List ι, ARel T (l.map f).prod (l.map f').prod
  | [] => by simp only [List.map_nil, List.prod_nil]; exact arel_one
  | a :: l => by
    simp only [List.map_cons, List.prod_cons]
    exact arel_mul (h a) (arel_listProd f f' h l)

end rel

section tr

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem bTall_tr {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) {S : Type} [Fintype S] [DecidableEq S]
    (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (e : Wd.Ix S) :
    trL ht z z' π π' (P5.act (P5.bTall L w) x e) =
      P5.act (P5.bTall Ls w) (fun a => trL ht z z' π π' (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a)) e := by
  have hop := fun (l : Fin ρ) (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  have hsite : ∀ l : Fin ρ, ARel (trL ht z z' π π') (P5.bTl L (shS l) w) (P5.bTl Ls l w) := by
    intro l
    refine Formalism.FourierDecayAlt.P.PBP.arel_bT ?_ ?_ ?_ w
    · show Rel _ (L.p (shS l)) (Ls.p l)
      rw [hL.1, hLs.1]
      exact rel_mk (fun v => hop l 0 v) (fun v => by simp only [LinearMap.neg_apply, hop l 3, map_neg])
    · show Rel _ (L.c (shS l)) (Ls.c l)
      rw [hL.2.2.1, hLs.2.2.1]
      exact rel_mk (fun v => hop l 1 v) (fun v => hop l 4 v)
    · show Rel _ (L.ci (shS l)) (Ls.ci l)
      rw [hL.2.2.2.1, hLs.2.2.2.1]
      exact rel_mk (fun v => hop l 2 v) (fun v => hop l 5 v)
  have hall : ARel (trL ht z z' π π') ((List.finRange ρ).reverse.map fun l => P5.bTl L (shS l) w).prod
      (P5.bTall Ls w) := arel_listProd _ _ hsite _
  rw [bTall_split, Formalism.FourierDecayAlt.P5.act_mul]
  exact act_tr hall _ e

end tr

section cast

variable {k n ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem bTall_cast (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ)
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) {t : ℂ} (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn.symm l)) (D.castM hn (ιLev k 1 ρ g))) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → RadSp k n z z' π π')
        (e : Wd.Ix S),
        T (P5.act (P5.bTall L w) x e) =
          P5.act (P5.bTall Ls w) (fun a => T (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a)) e := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k 1 ρ y) := funext fun y => by rw [hπ, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k 1 ρ y) := funext fun y => by rw [hπ', Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  refine ⟨trL ht zs zs' π π', fun Φ c g => ?_, fun S _ _ w x e => bTall_tr ht hL hLs w x e⟩
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  rfl

end cast

section misc

theorem exists_cons {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin n → ℂ) :
    ∃ (t : ℂ) (c' : Fin ρ → ℂ), c = fun l => consC t c' (Fin.cast hn.symm l) := by
  refine ⟨c ⟨0, by omega⟩, fun i => c ⟨i.val + 1, by omega⟩, funext fun l => ?_⟩
  unfold consC
  by_cases h : l.val = 0
  · rw [dite_eq_left (by simpa using h)]
    exact congrArg c (Fin.ext h)
  · rw [dite_eq_right (by simpa using h)]
    exact congrArg c (Fin.ext (by simp; omega))

theorem omX_cons {n ρ : ℕ} (hn : 1 + ρ = n) {t : ℂ} {c : Fin ρ → ℂ}
    (h : (fun l => consC t c (Fin.cast hn.symm l)) ∈ OmX n) : t ≠ 0 ∧ c ∈ OmX ρ := by
  refine ⟨?_, fun i => ?_⟩
  · have := h ⟨0, by omega⟩
    simpa [consC] using this
  · have := h ⟨i.val + 1, by omega⟩
    simpa [consC] using this

theorem hcell_cons {n ρ : ℕ} (hn : 1 + ρ = n) (t : ℂ) (c : Fin ρ → ℂ) :
    PBI.hcell (fun l : Fin n => consC t c (Fin.cast hn.symm l)) = (1, t) :: PBI.hcell c := by
  subst hn
  refine List.ext_getElem (by simp [PBI.hcell]; omega) fun i h1 h2 => ?_
  simp only [PBI.hcell, List.getElem_ofFn]
  rcases i with _ | i
  · simp [consC]
  · simp [consC]

theorem hcell_nil {n : ℕ} (hn : n = 0) (c : Fin n → ℂ) : PBI.hcell c = [] := by
  subst hn; rfl

theorem prod_cons {n ρ : ℕ} (hn : 1 + ρ = n) (k : ℕ) (t : ℂ) (c : Fin ρ → ℂ) :
    (∏ i : Fin n, ‖consC t c (Fin.cast hn.symm i)‖ ^ (2 * (n - (i : ℕ)) + k)) =
      ‖t‖ ^ (2 * n + k) * ∏ i : Fin ρ, ‖c i‖ ^ (2 * (ρ - (i : ℕ)) + k) := by
  subst hn
  rw [← (finCongr (Nat.add_comm ρ 1)).prod_comp, Fin.prod_univ_succ]
  congr 1
  simp only [consC, finCongr_apply, Fin.val_cast, Fin.val_succ]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  omega

theorem iota_split {k n ρ m : ℕ} (hn : 1 + ρ = n) (hm : m = 0) (e1 : n + m = n) (e2 : ρ + m = ρ)
    (g : B.Mat k m) :
    D.castM e1 (ιLev k n m g) = D.castM hn (ιLev k 1 ρ (D.castM e2 (ιLev k ρ m g))) := by
  subst hn hm
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  exact (ιLev_comp g).symm

theorem castM_iota_self {k a : ℕ} (ha : a = 0) (e : a + a = a) (g : B.Mat k a) : D.castM e (ιLev k a a g) = g := by
  subst ha
  exact Formalism.FourierDecayAlt.P.Dx2.Tower.castMat_levelEmbed_zero e g

theorem resG_empty {k a : ℕ} (ha : a = 0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (J : Mx k a → E)
    (c : Fin a → ℂ) (g : Mx k a) : resG k a (Fin.last a) J c g = J g := by
  subst ha
  simp [resG, wCell]

theorem ptSize_append (h h' : C.LPt) : D.ptSize (h ++ h') = D.ptSize h + D.ptSize h' := by
  simp [D.ptSize]

end misc

end Formalism.FourierDecayAlt.P.FinRangeListSplitting
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section fin

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem gcl_fn_mulZ {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    ((X.fn 0 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ∧
      ((X.fn 2 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
  have key : ∀ (j : Fin 6) (f : ℂ → ℂ),
      (∀ g, Q.fnVal P.k P.r Bs.z Bs.z' j g = f (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g)) →
      ((X.fn j Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' f (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro j f hf
    funext c g
    unfold NF.mulZ
    by_cases hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'
    · rw [Set.indicator_of_mem hx]
      have h1 := X.fn_apply j Φ (c, g) hx
      dsimp only at h1
      rw [h1, hf]
    · simp only [Set.indicator, hx, if_false]
      obtain ⟨h0, -, -⟩ := (X.fn j Φ).2
      exact h0 (c, g) hx
  exact ⟨key 0 id (fun _ => rfl), key 2 (starRingEnd ℂ) (fun _ => rfl)⟩

end fin

private theorem fnZ_apply_eq_snd (P : M.Par) (f : ℂ → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ann P)) (q : MA.Qp P.r P.TT) :
    ((fnZ P f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = f q.1.2 := by
  have hmem : (fun q : MA.Qp P.r P.TT => f q.1.2) ∈ MA.smSub P.r P.TT := by
    show ContDiffOn ℝ _ (MA.ext _) (MA.Qset P.r P.TT)
    have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MA.E P.r => x.2) (MA.Qset P.r P.TT) :=
      contDiff_snd.contDiffOn
    refine (hf.comp hs (fun x hx => hx.2)).congr (fun x hx => ?_)
    simp [MA.ext, hx]
  simp only [fnZ, MA.toSm, dif_pos hmem]

theorem local_frame_holds : GTCLFrame := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk hN hNs
  have hTT : 0 ≤ P.TT := torus_parameter Wp Wq P Bs X d hH
  have hact := hH.2.2.2.1
  have hR := hH.2.2.2.2.2.1
  have hζ1 : d.L.ζ.1 = X.fn 0 := by
    rw [hact.2.2.2.2.2.2.1]
    rfl
  have hζb1 : d.L.ζb.1 = X.fn 2 := by
    rw [hact.2.2.2.2.2.2.2.2.1]
    rfl
  have hmulζ : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ((d.L.ζ.1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Φ
    rw [hζ1]
    exact (gcl_fn_mulZ X Φ).1
  have hmulζb : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ((d.L.ζb.1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Φ
    rw [hζb1]
    exact (gcl_fn_mulZ X Φ).2
  have hΨζ : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) →
        Ψ = d.L.ζ.1 Φ :=
    fun Φ Ψ h => Subtype.ext (h.trans (hmulζ Φ).symm)
  have hΨζb : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) →
        Ψ = d.L.ζb.1 Φ :=
    fun Φ Ψ h => Subtype.ext (h.trans (hmulζb Φ).symm)
  have c1 : d.L.nab.1 * d.L.ζ.1 = d.L.ζ.1 * d.L.nab.1 + 1 := congrArg Prod.fst d.L.nab_ζ
  have c2 : d.L.nab.1 * d.L.ζb.1 = d.L.ζb.1 * d.L.nab.1 := congrArg Prod.fst d.L.nab_ζb
  have c3 : d.L.nabs.1 * d.L.ζ.1 = d.L.ζ.1 * d.L.nabs.1 := congrArg Prod.fst d.L.nabs_ζ
  have c4 : d.L.nabs.1 * d.L.ζb.1 = d.L.ζb.1 * d.L.nabs.1 - 1 := congrArg Prod.fst d.L.nabs_ζb
  have hκ1 : ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      d.L.nab.1 ((d.κ f).1 Φ) = (d.κ f).1 (d.L.nab.1 Φ) := by
    intro f Φ
    have h := (hR.2.1 f d.L.nab (Or.inr (Or.inl rfl))).eq
    have h1 : (d.κ f).1 * d.L.nab.1 = d.L.nab.1 * (d.κ f).1 := congrArg Prod.fst h
    exact (LinearMap.congr_fun h1 Φ).symm
  have hκ2 : ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      d.L.nabs.1 ((d.κ f).1 Φ) = (d.κ f).1 (d.L.nabs.1 Φ) := by
    intro f Φ
    have h := (hR.2.1 f d.L.nabs (Or.inr (Or.inr rfl))).eq
    have h1 : (d.κ f).1 * d.L.nabs.1 = d.L.nabs.1 * (d.κ f).1 := congrArg Prod.fst h
    exact (LinearMap.congr_fun h1 Φ).symm
  obtain ⟨A, hAs, hA⟩ := gcl_core P Bs X d hH e he hk d.L.nab.1 hN 1 0
    (fun Φ Ψ h => by
      rw [hΨζ Φ Ψ h, show d.L.nab.1 (d.L.ζ.1 Φ) = d.L.ζ.1 (d.L.nab.1 Φ) + Φ from LinearMap.congr_fun c1 Φ,
        Submodule.coe_add, hmulζ, one_smul])
    (fun Φ Ψ h => by
      rw [hΨζb Φ Ψ h, show d.L.nab.1 (d.L.ζb.1 Φ) = d.L.ζb.1 (d.L.nab.1 Φ) from LinearMap.congr_fun c2 Φ,
        hmulζb, zero_smul, add_zero])
    hκ1
  obtain ⟨B, hBs, hB⟩ := gcl_core P Bs X d hH e he hk d.L.nabs.1 hNs 0 (-1)
    (fun Φ Ψ h => by
      rw [hΨζ Φ Ψ h, show d.L.nabs.1 (d.L.ζ.1 Φ) = d.L.ζ.1 (d.L.nabs.1 Φ) from LinearMap.congr_fun c3 Φ,
        hmulζ, zero_smul, add_zero])
    (fun Φ Ψ h => by
      rw [hΨζb Φ Ψ h, show d.L.nabs.1 (d.L.ζb.1 Φ) = d.L.ζb.1 (d.L.nabs.1 Φ) - Φ from LinearMap.congr_fun c4 Φ,
        Submodule.coe_sub, hmulζb, neg_one_smul, sub_eq_add_neg])
    hκ2
  refine ⟨A, B, fun ρ => ⟨hAs ρ, hBs ρ⟩, fun Φ ρ => ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    funext q
    rw [hA Φ ρ q]
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply]
    rw [dzQ_apply P hTT, fnZ_apply_eq_snd P (A ρ) (hAs ρ)]
    ring
  · apply Subtype.ext
    funext q
    rw [hB Φ ρ q]
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg, Pi.add_apply, Pi.mul_apply,
      Pi.neg_apply]
    rw [dzbQ_apply P hTT, fnZ_apply_eq_snd P (B ρ) (hBs ρ)]
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section aux

variable {P : M.Par}

theorem nf_evQ_toSm_le (u : MA.Qp P.r P.TT → ℂ) (q : MA.Qp P.r P.TT) : ‖MA.evQ P (MA.toSm P u) q‖ ≤ ‖u q‖ := by
  unfold MA.evQ MA.toSm
  split_ifs with h
  · exact le_rfl
  · simp

theorem nf_wq_eq (k r : ℕ) (T T' : ℝ) (x : (Fin r → ℂ) × ℂ) (hx : T * T' ≤ Complex.normSq x.2) :
    MA.wq k x (T * T') = (∏ l : Fin r, Complex.normSq (x.1 l)) * bcWeight k r T T' x := by
  unfold MA.wq bcWeight
  rw [if_pos hx, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  have hl : MA.Mdim k r l - 1 = (Formalism.QuantumDeterminants.Mdim k r l - 2) + 1 := by
    have := l.2
    unfold MA.Mdim Formalism.QuantumDeterminants.Mdim
    omega
  rw [hl, pow_mul, ← Complex.normSq_eq_norm_sq, pow_succ, mul_comm]

end aux

theorem trace_norm_bound_constant_one : NFTrNormKB := by
  intro Wp Wq _ _ _ _ _ _ P p e he
  refine ⟨1, fun H c q hq hloc hG => ?_⟩
  have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
  have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  have hon : Orthonormal ℂ (fun ρ => B.hsVec (e ρ q.1.2)) := by
    rw [orthonormal_iff_ite]
    convert (he.2 q.1.2 hζ).2.1
  have hw0 : 0 ≤ MA.wq P.k q.1 P.TT := by
    unfold MA.wq
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (Complex.normSq_nonneg _) _)
      (pow_nonneg (sub_nonneg.2 hζ.le) _)
  have hterm : ∀ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2 ≤
      MA.wq P.k q.1 P.TT *
        ‖inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1)))‖ ^ 2 := by
    intro ρ
    have h1 := nf_evQ_toSm_le (P := P) (fun q : MA.Qp P.r P.TT =>
      ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1)))) q
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (le_of_eq ?_)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hw0]
  have hsum : ∑ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2 ≤
      MA.wq P.k q.1 P.TT * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1))‖ ^ 2 := by
    refine (Finset.sum_le_sum fun ρ _ => hterm ρ).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hon.sum_inner_products_le _) hw0
  have hwq : MA.wq P.k q.1 P.TT =
      (∏ l : Fin P.r, Complex.normSq (q.1.1 l)) * bcWeight P.k P.r P.T P.T' q.1 :=
    nf_wq_eq P.k P.r P.T P.T' q.1 hζ.le
  have hEw0 : 0 ≤ TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) := by
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p H hloc]
    positivity
  have hpt := pt_le p H c
  rw [hT, hT', ENNReal.ofReal_le_ofReal_iff hEw0] at hpt
  have hkey : bcWeight P.k P.r P.T P.T' q.1 * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1))‖ ^ 2 ≤
      TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) := by
    unfold B.gq
    rw [hq]
    exact hpt
  have hprod : ∏ l : Fin P.r, Complex.normSq (q.1.1 l) = ∏ l : Fin P.r, Complex.normSq (c l.castSucc) := by
    rw [hq]
  calc ∑ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2
      ≤ (∏ l : Fin P.r, Complex.normSq (q.1.1 l)) *
          (bcWeight P.k P.r P.T P.T' q.1 * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1))‖ ^ 2) := by
        rw [← mul_assoc, ← hwq]
        exact hsum
    _ ≤ (∏ l : Fin P.r, Complex.normSq (q.1.1 l)) * TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) :=
        mul_le_mul_of_nonneg_left hkey (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)
    _ = 1 * (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) *
          TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) := by
        rw [hprod, one_mul]

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem lie_group_existence_holds : KLExists := lie_existence_of_iso_group KLIso.lie_algebra_isomorphism_holds lie_group_realization

theorem gauge_kappa_line_holds : GTKLine := gTKLine_of_cut lie_eigenvalue_holds lie_weight_at_most_holds lie_group_existence_holds

theorem gauge_kappa_holds : GTKap := GTK.gauge_kappa_of_point_line gauge_kappa_pointwise_holds gauge_kappa_line_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
