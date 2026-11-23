module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
public import Formalism.LocalRingCardinality.Bundle009
public import Formalism.LocalToGlobal.HermitianForms.TiedBrRep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle338
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle148
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle004
public import Formalism.LocalToGlobal.HermitianForms.TiedBrCl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.PerRedTw

section Copied

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.Forms Matrix NumberField
open scoped BigOperators

theorem exists_orthonormal_frame_twisted (D : D7) : ∃ o : FrP D, o.IsON := by
  classical
  let _ := D.host.cmStar
  have hY : ∀ τ, ∃ Y : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ,
      IsUnit Y.det ∧ Yᴴ * (gramP D).map (embT D τ) * Y = 1 := by
    intro τ
    have hs := D.sp.X'_sig (embT D τ)
    rw [D.X'_posDef (embT D τ)] at hs
    dsimp only at hs
    obtain ⟨e, P, hP⟩ := hs
    have hJ : Formalism.UG.Jpq D.sp.X'.rank 0 = 1 := by
      ext i j
      rcases i with i | i
      · rcases j with j | j
        · simp [Formalism.UG.Jpq, Matrix.one_apply]
        · exact j.elim0
      · exact i.elim0
    have hcT : Formalism.UG.cT (starRingEnd ℂ) P.1 = P.1ᴴ := by
      ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    rw [hcT, hJ] at hP
    let f : Fin D.sp.X'.rank ≃ Fin (D.R.N D.R.m - 1) := finCongr (rankP D)
    let g : Fin (D.R.N D.R.m - 1) ≃ Fin D.sp.X'.rank ⊕ Fin 0 := f.symm.trans e
    have hG : ((gramP D).map (embT D τ)).submatrix g.symm g.symm = (D.sp.X'.gram.map (embT D τ)).reindex e e := by
      ext i j
      simp [g, f, gramP, Matrix.reindex_apply, Matrix.submatrix_apply]
    refine ⟨P.1.submatrix g g, ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self]; exact Matrix.isUnits_det_units P
    · have h1 : (gramP D).map (embT D τ) = (((gramP D).map (embT D τ)).submatrix g.symm g.symm).submatrix g g := by
        ext i j; simp
      rw [Matrix.conjTranspose_submatrix, h1, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hG, hP]
      exact Matrix.submatrix_one_equiv g
  choose Y hYu hY using hY
  exact ⟨⟨Y, hYu⟩, fun τ => Or.inl (hY τ)⟩

theorem nfAll_zero_tw {D : D7} (n : ℕ) (lam : D.what₂.Tau → DomWeight n) : nfAll lam 0 0 = 0 := by
  simp [nfAll, Formalism.REAL.fockF]

end Copied

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms Formalism.MainNotions.RT.PeriodPointConditions GlobalTheory.PerQ

attribute [local instance] MemberForms.clsPFin

variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
  {Tw : TwForms D} {Y : DivX D}

theorem eW_rep_o_tw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (o : FrP D)
    (z : (D.PTw u μ).Wrow) (hz : z ∈ (Tw.fm u μ).ptC) (c : (Tw.fm u μ).clsP) :
    ∃ Q ∈ CSpan (Tw.fm u μ).sg,
      (t.pt.val u μ hμ).eW z c = fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) Q := by
  have hF := ((t.pt.val u μ hμ).ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) ((t.pt.cls u μ hμ).y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ CSpan (Tw.fm u μ).sg := by
    have := CSpan_shW (Tw.fm u μ).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgTG at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : (t.pt.val u μ hμ).eW z c = fnOf _ (shiftOf (sgTG (Tw.fm u μ))) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hM : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (o.2 τ).ringInverse
  refine ⟨_, ?_, he.trans (fnOf_change _ _ _ _ hM Q0)⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hQ0')

open Classical in
theorem eW_resCTw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (Tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) :
    (t.pt.val u μ hμ).eW (resCTw t u μ hμ c z) = fun c' => if c' = c then (t.pt.val u μ hμ).eW z c' else 0 := by
  classical
  unfold resCTw
  rw [LinearEquiv.apply_symm_apply]

theorem petersson_eq_sum_restrict_twist (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (a b : (D.PTw u μ).Wrow) (ha : a ∈ (Tw.fm u μ).ptC) (hb : b ∈ (Tw.fm u μ).ptC) :
    (Tw.fm u μ).ipP a b = ∑ c, (Tw.fm u μ).ipP (resCTw t u μ hμ c a) (resCTw t u μ hμ c b) := by
  classical
  obtain ⟨o, ho⟩ := exists_orthonormal_frame_twisted D
  choose P hP hPe using eW_rep_o_tw t u μ hμ o a ha
  choose Q hQ hQe using eW_rep_o_tw t u μ hμ o b hb
  rw [(t.pt.val u μ hμ).ipP o ho a b P Q hP hQ hPe hQe]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hP' : ∀ c', (if c' = c then P c' else 0) ∈ CSpan (Tw.fm u μ).sg := fun c' => by
    split_ifs
    · exact hP c'
    · exact Submodule.zero_mem _
  have hQ' : ∀ c', (if c' = c then Q c' else 0) ∈ CSpan (Tw.fm u μ).sg := fun c' => by
    split_ifs
    · exact hQ c'
    · exact Submodule.zero_mem _
  have hPe' : ∀ c', (t.pt.val u μ hμ).eW (resCTw t u μ hμ c a) c' =
      fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) (if c' = c then P c' else 0) := fun c' => by
    rw [eW_resCTw]
    dsimp only
    split_ifs
    · exact hPe c'
    · exact (map_zero _).symm
  have hQe' : ∀ c', (t.pt.val u μ hμ).eW (resCTw t u μ hμ c b) c' =
      fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) (if c' = c then Q c' else 0) := fun c' => by
    rw [eW_resCTw]
    dsimp only
    split_ifs
    · exact hQe c'
    · exact (map_zero _).symm
  rw [(t.pt.val u μ hμ).ipP o ho _ _ _ _ hP' hQ' hPe' hQe', Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    simp [hc', nfAll_zero_tw]
  · intro h; exact absurd (Finset.mem_univ c) h

open Classical in
def pcTw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (Tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) (G : (D.PTw u μ).Mt) : ℂ :=
  if z ∈ (Tw.fm u μ).ptC then pcLTw t u μ hμ c z G
  else if h : Nonempty (Tw.fm u μ).clsP then
    (if c = Classical.choice h then ((Nat.card ((Tw.fm u μ).stabilizer₂ c) : ℕ) : ℂ) * (D.PTw u μ).period z G else 0)
  else 0

theorem perDecTw_of_at (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (h : PerDecTwT Y t u μ hμ) : Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ := by
  classical
  have hcard : ∀ c, ((Nat.card ((Tw.fm u μ).stabilizer₂ c) : ℕ) : ℂ) ≠ 0 := fun c =>
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨pcTw t u μ hμ, fun z G => ?_, fun x hx F hF c => ?_⟩
  · by_cases hz : z ∈ (Tw.fm u μ).ptC
    · have hG : t.ptE.jM u μ G ∈ (Tw.fm u μ).ptC := ((t.ptE.per u μ hμ).2.1) G
      rw [((t.ptE.per u μ hμ).2.2) z G, petersson_eq_sum_restrict_twist t u μ hμ _ _ hG hz]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [pcTw, if_pos hz, pcLTw]
      rw [← mul_assoc, inv_mul_cancel₀ (hcard c), one_mul]
    · by_cases hne : Nonempty (Tw.fm u μ).clsP
      · rw [Finset.sum_eq_single (Classical.choice hne)]
        · simp only [pcTw, if_neg hz, dif_pos hne, ↓reduceIte]
          rw [← mul_assoc, inv_mul_cancel₀ (hcard _), one_mul]
        · intro c _ hc
          simp only [pcTw, if_neg hz, dif_pos hne, if_neg hc, mul_zero]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · have hE : IsEmpty (Tw.fm u μ).clsP := not_nonempty_iff.mp hne
        have hz0 : z = 0 := (t.pt.val u μ hμ).eW.injective (funext fun c => hE.elim c)
        subst hz0
        simp
  · obtain ⟨y, hy, hv⟩ := h x hx F hF c
    have hz : (Tw.fm u μ).ptEmb x ∈ (Tw.fm u μ).ptC := (((t.pt.val u μ hμ).rat _).1 ⟨x, rfl⟩).1
    refine ⟨y, ?_, hv⟩
    simp only [pcTw, if_pos hz]
    exact hy

theorem reduction_perDecTw : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (tp : Formalism.L2.Host.TupTied D cf nch) (C : ColsTiedSym D) (Tw : TwForms D) (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (Y : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0), GlobalTheory.PerQ.PerDecTwT Y t u μ hμ → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ :=
  fun _ _ _ _ _ _ t _ u μ hμ h => perDecTw_of_at t u μ hμ h

end GlobalTheory.PerRedTw
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem valAt_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (φ : (I.stp u I.mu0 0).Cl → Fr B.fields.emb B.embLL (B.R.N 0) → ℂ)
    (b : (I.stp u I.mu0 0).β) (b' : (I.stp u a 0).β) (p : (I.stp u I.mu0 0).D b) (p' : (I.stp u a 0).D b')
    (h : p.1.1.deco = p'.1.1.deco) :
    valAt (I.stp u a 0) B.fields.emb B.embLL (fun c => φ ((I.eCls0 l u a).symm c)) b' p' =
      valAt (I.stp u I.mu0 0) B.fields.emb B.embLL φ b p := by
  have hc : I.eCls0 l u a ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p')) = (I.stp u a 0).cl b' p' :=
    (I.eCls0 l u a).apply_symm_apply _
  have hdeco : ((I.stp u a 0).rep ((I.stp u a 0).cl b' p')).1.1.deco =
      ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p'))).1.1.deco := by
    conv_lhs => rw [← hc]
    exact stepZero_corresponding_representatives_same_deco hI u a _ _
  show (I.stp u a 0).tr B.fields.emb B.embLL b' ((I.stp u a 0).mv b' p')
      (φ ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p'))) = _
  generalize (I.eCls0 l u a).symm ((I.stp u a 0).cl b' p') = c at hdeco ⊢
  obtain ⟨b₁, q⟩ := c
  obtain rfl : b = b₁ := stepZero_chartIndex_subsingleton hI _ _ _
  have hm := (I.stp u a 0).mv_smul b' p'
  have hy : ∀ N, (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) 0).ys N = {∅} := fun N => by rw [ys0]; rfl
  obtain ⟨g, g1, g2, g3⟩ := GlobalTheory.LvT.StartTie.exists_lift (y' := ysAt B.R I.sel (I.tup a) (I.cst a) 0) hy
    ((levelTypePrimes_stepZero_eq_colLev hI I.mu0 b).trans (levelTypePrimes_stepZero_eq_colLev hI a b').symm) (chartIndexLevelTwistPrimes_stepZero_eq_top hI I.mu0 b) (chartIndexLevelTwistPrimes_stepZero_eq_top hI a b')
    ((I.stp u a 0).mv b' p') ((I.stp u I.mu0 0).rep ⟨b, q⟩) p ((I.stp u a 0).rep ((I.stp u a 0).cl b' p'))
    hdeco.symm (h.trans (congrArg (fun r : (I.stp u a 0).D b' => r.1.1.deco) hm).symm)
  have h1 := valAt_eq B.fields.emb B.embLL (l.lev u I.mu0).free0 φ ⟨b, q⟩ g
  refine Eq.trans ?_ (h1.symm.trans (congrArg _ g1))
  have h2 : (I.stp u a 0).tr B.fields.emb B.embLL b' ((I.stp u a 0).mv b' p') =
      (I.stp u I.mu0 0).tr B.fields.emb B.embLL b g :=
    congrArg₂ (trFr B.fields.emb B.embLL) (congrArg (Formalism.L2.Col.ufGL B.fields.E (B.R.N 0)) g2.symm) g3.symm
  exact congrFun (congrArg DFunLike.coe h2) _

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem rep_eCls0_symm (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c' : (I.stp u a 0).Cl) :
    ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm c')).1.1.deco = ((I.stp u a 0).rep c').1.1.deco := by
  conv_rhs => rw [← (I.eCls0 l u a).apply_symm_apply c']
  exact (stepZero_corresponding_representatives_same_deco hI u a _ _).symm

theorem nm_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Nm (tw (I.tw l l0 Z) u I.mu0) 0 v φ) = Nm (tw (I.tw l l0 Z) u a) 0 v ((I.cols l).e0Tw u a φ) := by
  unfold Nm
  erw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  funext c'
  refine (valAt_eCls0 hI l u a φ _ _ _ _ ?_).symm
  exact (dia_deco _ v a').trans ((congrArg (Formalism.L2.Col.DecoSet.dia1 v a') (rep_eCls0_symm hI l u a c')).trans
    (dia_deco _ v a').symm)

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem up_deco0 (l : I.Laws) (u : B.Word) (a : I.ι) (b : (I.stp u a 0).β) (p : (I.stp u a 0).D b)
    (P : (I.atIn u a).ST) (x : Formalism.L2.Col.Sp B.fields.E (B.R.N 0)) (hx : x ∈ p.1.1.deco.1.N) (hf : p.1.1.deco.1.f P x = 1) :
    (((I.atIn u a).A 0).up b p P x).1.1.deco = p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x := by
  change (p.mv (p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x)).1.1.deco = _
  by_cases hc : (p.1.1.deco.1.up P ((I.atIn u a).T : 𝓞 B.fields.E) x).Ok
  · apply mv_deco
    have h1 := congrArg Formalism.L2.Col.Deco.N (((l.lev u a).tied 0).up_deco b p P x hx hf)
    refine Eq.trans h1 ?_
    unfold Formalism.L2.Col.DecoSet.up
    rw [dif_pos hc]
    rfl
  · have h1 : p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x = p.1.1.deco := dif_neg hc
    rw [h1]
    exact congrArg (fun q : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => q.1.1.deco) (dif_pos ⟨p.1.1.2, p.2⟩ : p.mv p.1.1.deco = _)

def onesAt {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v : Y.A.vT) (c : Y.C.cls 0) : Finset (Y.fm.lv 0 v c) :=
  Finset.univ.filter (fun x : Y.fm.lv 0 v c => Y.fm.fv 0 v c x = 1)

theorem mem_onesAt {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v : Y.A.vT) (c : Y.C.cls 0) (x : Y.fm.lv 0 v c) :
    x ∈ onesAt Y v c ↔ Y.fm.fv 0 v c x = 1 := by
  simp [onesAt]

theorem uop_apply {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v) (φ : Fn Y 0) :
    Uop Y 0 v φ = fun c => ∑ x ∈ onesAt Y v c, Y.fm.upT 0 v c x (φ (Y.fm.up 0 v c x)) := by
  funext c
  simp [Uop, LinearMap.sum_apply, onesAt]

theorem uop_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ) = Uop (tw (I.tw l l0 Z) u a) 0 v ((I.cols l).e0Tw u a φ) := by
  funext c'
  have hd := rep_eCls0_symm hI l u a c'
  have hN := congrArg (fun d : Formalism.L2.Col.DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := _) (SG := _) => d.1.N) hd
  have hF := congrArg (fun d : Formalism.L2.Col.DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := _) (SG := _) => d.1.f v) hd
  refine (show (I.cols l).e0Tw u a (Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ) c' =
    Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ ((I.eCls0 l u a).symm c') from rfl).trans ?_
  refine (congrFun (uop_apply (tw (I.tw l l0 Z) u I.mu0) v φ) _).trans
    (Eq.trans ?_ (congrFun (uop_apply (tw (I.tw l l0 Z) u a) v ((I.cols l).e0Tw u a φ)) c').symm)
  revert hd hN hF
  generalize (I.eCls0 l u a).symm c' = c
  intro hd hN hF
  refine Eq.trans ?e1 (up_match B.fields.emb B.embLL (l.lev u I.mu0).free0 ((l.lev u I.mu0).lev 0) ((l.lev u I.mu0).tied 0)
    ((l.lev u a).lev 0) ((l.lev u a).tied 0) v (onesAt (tw (I.tw l l0 Z) u I.mu0) v) ?hs c' _ ?hs' φ ((I.cols l).e0Tw u a φ) c.1 ((I.stp u I.mu0 0).rep c)
    hN hF ?hup)
  case e1 =>
    exact (valAt_rep B.fields.emb B.embLL (l.lev u I.mu0).free0 (fun c => ∑ x ∈ onesAt (tw (I.tw l l0 Z) u I.mu0) v c,
      valAt (I.stp u I.mu0 0) B.fields.emb B.embLL φ c.1 (((I.atIn u I.mu0).A 0).upPt v c x)) c).symm
  case hs => exact fun c x => mem_onesAt (tw (I.tw l l0 Z) u I.mu0) v c x
  case hs' => exact fun x => mem_onesAt (tw (I.tw l l0 Z) u a) v c' x
  case hup =>
    intro x hx h1
    refine valAt_eCls0 hI l u a φ _ _ _ _ ?_
    refine (up_deco0 l u I.mu0 _ _ v x hx h1).trans ((congrArg (fun d : Formalism.L2.Col.DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := _) (SG := _) =>
      d.up v ((I.atIn u a).T : 𝓞 B.fields.E) x) hd).trans
        (up_deco0 l u a _ _ v x (hN ▸ hx) (by rw [← congrFun hF x]; exact h1)).symm)

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem uop_mem (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) {φ : Fn (tw (I.tw l l0 Z) u a) 0} (hφ : φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0) :
    Uop (tw (I.tw l l0 Z) u a) 0 v φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0 := by
  erw [uop_apply]
  exact DiaStab.mem_Fi _ B.fields.emb B.embLL _ (l.lev u a).free0 _ fun _ => Submodule.sum_mem _ fun _ _ =>
    DiaStab.tr_mem _ B.fields.emb B.embLL _ _ _ (hφ _).1

theorem ulist_mem (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (ls : List (tw (I.tw l l0 Z) u a).A.vT) {φ : Fn (tw (I.tw l l0 Z) u a) 0} (hφ : φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0) :
    Ulist (tw (I.tw l l0 Z) u a) ls φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0 := by
  induction ls with
  | nil => exact hφ
  | cons v ls ih => exact uop_mem l l0 Z u a v ih

theorem ulist_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (ls : List (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Ulist (tw (I.tw l l0 Z) u I.mu0) ls φ) = Ulist (tw (I.tw l l0 Z) u a) ls ((I.cols l).e0Tw u a φ) := by
  induction ls with
  | nil => rfl
  | cons v ls ih => exact (uop_eCls0 hI l l0 Z u a v _).trans (congrArg (Uop (tw (I.tw l l0 Z) u a) 0 v) ih)

theorem step0Tie_trueCols : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), Step0Tie (I.tw l l0 Z) u a := by
  intro B X I hI l l0 Z u a w _
  refine ⟨rfl, fun x hx => ?_⟩
  refine nlam_map (X := tw (I.tw l l0 Z) u I.mu0) (Y := tw (I.tw l l0 Z) u a)
    (e := (I.cols l).e0Tw u a) (eL := (I.tw l l0 Z).e0 u a) w rfl ((I.tw l l0 Z).embed_mul_block_embedding u a)
    (fun x hx => ((I.tw l l0 Z).twist_preserves_base_lattice u a x).1 hx) (fun v => ⟨v, fun φ _ => nm_eCls0 hI l l0 Z u a v φ⟩) rfl
    (fun φ hφ => ulist_mem l l0 Z u I.mu0 _ hφ) (fun φ _ => ulist_eCls0 hI l l0 Z u a _ φ) hx

end GlobalTheory.LvT.TrueStep0
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Pointwise

theorem _root_.GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Dense ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) ∧ Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} ∧ (∀ k : infU E n, ∀ g ∈ finU (E := E) (n := n), k.1 * g = g * k.1) ∧ ∃ (a : UA E n →* finU (E := E) (n := n)) (b : UA E n →* infU E n), Continuous a ∧ Continuous b ∧ (∀ x, x = (a x).1 * (b x).1) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), a (g.1 * k.1) = g ∧ b (g.1 * k.1) = k := by
  first | exact @GlobalTheory.UnitarySplit.dense_and_split | exact GlobalTheory.UnitarySplit.dense_and_split | (intros; apply GlobalTheory.UnitarySplit.dense_and_split <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem _root_.GlobalTheory.T.heckeChar_productFormula_normOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (rep : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E)) (V : Finset (HeightOneSpectrum (𝓞 F))) (x z : Eˣ), (∀ y : F, star (algebraMap F E y) = algebraMap F E y) → Module.finrank F E = 2 → (∃ a : E, star a ≠ a) → (∀ P : HeightOneSpectrum (𝓞 E), ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) → χ.TrivOn F → (∀ P, χ.TameAt P) → (∀ P, conjPrime₂ P = P → χ.UnrAt P) → (∀ v, (rep v).under (𝓞 F) = v) → (x : E) = z * star (x : E) → (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ V → χ.UnrAt P ∧ P.valuation E (x : E) = 1) → χ.inf x * ∏ v ∈ V, χ.locK (rep v) z = 1 := by
  first | exact @GlobalTheory.NormOneProd.inf_mul_prod | exact GlobalTheory.NormOneProd.inf_mul_prod | (intros; apply GlobalTheory.NormOneProd.inf_mul_prod <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.PtCo

theorem intSpan_smul' (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam) : D.what₂.embLL r • p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan at *
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    exact ⟨r * r', f, mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem ptCo_one (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) (B w c))
    (w : D.what₂.places.Pl) (y : (D.fm u).ptLat.V) (hy : y ∈ (D.fm u).ptLat.L) (c : (D.fm u).clsP) :
    Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg := by
  obtain ⟨P, hP, hq⟩ := (Tf.valP.lat y).1 hy w c (B w c) (hB w c)
  rw [Matrix.coe_units_inv] at hq
  have e : Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c = P := by
    change fnInv (gramC (gramP D) (_root_.Formalism.L2.Forms.embT D)) (shiftOf (sgT u))
      (atInf (_root_.Formalism.L2.embT D) (↑(B w c))⁻¹) (Tf.valP.eW ((D.fm u).ptEmb y) c) = P
    rw [hq]
    erw [fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (Matrix.isUnits_det_units (B w c)))]
  rw [e]
  exact hP

theorem ptCo_mem_intSpan : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E), (∀ w c, IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) (B w c)) → ∀ w, ∀ y ∈ (D.fm u).SP w, ∀ c, Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg := by
  intro D u Ch chOf Tf B hB w y hy c
  induction hy using Submodule.span_induction with
  | mem y hy => exact ptCo_one D u Ch chOf Tf B hB w y hy c
  | zero => rw [map_zero, map_zero, Pi.zero_apply]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _), Pi.add_apply]; exact add_mem hy hz
  | smul r y _ hy =>
    have e : r • y = (r : D.what₂.LL) • y := rfl
    rw [e, LinearMap.map_smulₛₗ, map_smul, Pi.smul_apply]
    exact intSpan_smul' D w _ (r : D.what₂.LL) r.2 _ hy

end GlobalTheory.PtCo

end
end
