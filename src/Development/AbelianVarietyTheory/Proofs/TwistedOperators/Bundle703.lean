module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodChangeOfMeasures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle050
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_definitePeriod_change_of_measures : Big fun ch => VolAt ch := by
  first | exact @GlobalTheory.RowVal.volAt_big | exact GlobalTheory.RowVal.volAt_big | (intros; apply GlobalTheory.RowVal.volAt_big <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

namespace NormalJac

theorem jacobiDualColumn_scalar_identity {K : Type} [Field K] (X : K) (hX : X ≠ 0) (i k : ℕ) :
    (X ^ (i + 1 + k))⁻¹ * (-((-X) ^ (i + 1 + k) * X ^ (i + 1 + k)) / X) * (-1 / X) ^ k = (-X) ^ i := by
  have h1 : ((-1 : K) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [neg_pow X, neg_pow X, div_pow]
  field_simp
  linear_combination (X * X ^ i * X ^ k * (-1) ^ i) * h1

theorem mul_col_eq {ι' ι κ μ K : Type} [Fintype ι] [Field K] (P : Matrix ι' ι K) (Y : Matrix ι κ K) (Z : Matrix ι μ K)
    (c : κ) (c' : μ) (h : ∀ l, Y l c = Z l c') (r : ι') : (P * Y) r c = (P * Z) r c' := by
  simp only [Matrix.mul_apply, h]

theorem hz_besAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t : T} {M : Vol G} (hM : M.Is t)
    (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j σ hj)) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) :
    p.hz (besAt G hM j σ hj vN) = -((-p.xi) ^ σ * p.xi ^ σ) := by
  simp only [Place.hz, besAt, dotProduct, mulVec]
  show p.pr (∑ i : Fin 1, star (fun _ : Fin 1 => D.host.xi0 ^ σ) i * ∑ i_1 : Fin 1, (GlobalTheory.SeeSaw.Model.nLine D).gram i i_1 * D.host.xi0 ^ σ) = _
  simp only [Fin.sum_univ_one, nLine_gram, Pi.star_apply, star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Place.xi, Place.pr, map_mul, map_neg, map_pow, map_one]
  ring

theorem pr_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    (x y : D.host.E) : p.pr (x * y) = p.pr x * p.pr y := map_mul (p.π.comp (incA D)) x y

theorem place_proj_neg_xi_pow {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (n : ℕ) : p.pr ((-D.host.xi0) ^ n) = (-p.xi) ^ n :=
  (map_pow (p.π.comp (incA D)) _ n).trans (congrArg (· ^ n) (map_neg (p.π.comp (incA D)) _))

theorem neg_mul_neg_one_eq_of_eq {K : Type} [Field K] (y a S : K) (h : S = a) : -(y * a) * -1 = S * y := by rw [h]; ring

end NormalJac


open NormalJac in

theorem big_jacP : Big fun ch => JacP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc => ?_⟩⟩
  clear hε hx hsc hch s
  intro t w hw p hp M hM j σ hj vN a ha c hc
  have h1 := ch.S.row t trivial w hw (j + 1) (by omega)
  have hm : (locGrid ch.G t w).m = D.R.m := rfl
  obtain rfl : c = 2 * σ := by
    have h2 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
    rw [hm] at h2; omega
  have hpr : ∀ x, p.pr x = algebraMap D.host.E (Kw w) x := fun x =>
    (hp.2.1 _).trans (Comparison₂.cpt_tmul w x)
  have hxi : p.xi ≠ 0 := by
    rw [Place.xi, hpr]; exact (map_ne_zero _).2 (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have hE : (epsV ch.G t w (D.R.m, j + 1)).val =
      diagonal fun q => if topRank (locGrid ch.G t w) (j + 1) + σ ≤ q.val then -1 else 1 := by
    by_cases hσ : σ = 0
    · subst hσ
      rw [epsV_eq_one _ _ (by omega), Units.val_one]
      ext q q'
      rw [Matrix.one_apply, diagonal_apply, if_neg (show ¬ (topRank (locGrid ch.G t w) (j + 1) + 0 ≤ q.val) by have := q.2; omega)]
    · have hodd : Odd (j + 1) := by
        obtain ⟨b, hb⟩ := D.R.m_even
        exact ⟨j / 2, by omega⟩
      rw [epsV_apply, if_pos (mem_idx.2 ⟨by omega, by omega⟩), sgnAt, GlobalTheory.SplitFlip.diagGL_val]
      congr 1
      funext q
      have e : (D.R.m - 1 - (j + 1)) / 2 = σ := by omega
      simp only [e, hodd, true_and]
      split_ifs <;> simp
  have h₁ : j + 1 < D.R.m := by omega
  have h₂ : D.R.m - 1 - (j + 1) = 2 * σ := by omega
  obtain ⟨T0, T1, T2⟩ : (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr = (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr ∧
      (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).e.map p.pr =
        ((rowJac ch.G (j + 1) h₁ σ h₂).e * diagonal fun a : Fin σ => (D.host.xi0 ^ a.1)⁻¹).map p.pr ∧
      (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).e'.map p.pr =
        ((rowJac ch.G (j + 1) h₁ σ h₂).e' * diagonal fun a : Fin σ => star (D.host.xi0 ^ a.1)).map p.pr := by
    rcases ha with ⟨rfl, rfl⟩ | ⟨δ, hδ, hδa⟩
    · refine ⟨?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      rw [show mt (ch.G.V (Node.grid D.R.m (j + 1))) 1 = 1 by simp [Formalism.L2.Theta.mt], Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    · obtain ⟨e0, e1, e2⟩ := hδ.2.2 σ h₁ h₂
      have key : ∀ {n : ℕ} (X Y : Matrix (Fin (ch.G.V (Node.grid D.R.m (j + 1))).rank) (Fin n) D.host.E),
          HMul.hMul (mt _ δ) (X.map (incA D)) = Y.map (incA D) → (mt _ a).map p.π * X.map p.pr = Y.map p.pr := by
        intro n X Y h
        have := congrArg (fun Z => Z.map p.π) h
        simp only [Matrix.map_mul, Matrix.map_map] at this
        rw [hδa]
        exact this
      exact ⟨key _ _ e0, key _ _ e1, key _ _ e2⟩
  have hfl : ∀ {a c b : ℕ} (h : a + c = b) (x : Fin a), ((frame h (Sum.inl x)) : ℕ) = x := by intros; simp [frame]
  have hfr : ∀ {a c b : ℕ} (h : a + c = b) (q : Fin c), ((frame h (Sum.inr q)) : ℕ) = a + q := by intros; simp [frame]
  clear ha
  have T0' : ∀ {n : Type} [Fintype n] (Z : Matrix (Fin (ch.G.V (Node.top (j + 1))).rank) n (Kw w)), (mt _ a).map p.π * ((rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr * Z) =
      (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr * Z := by
    intro n _ Z; rw [← Matrix.mul_assoc, T0]
  dsimp only [Place.IsJacFrame, jacAt]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro r x
    simp only [mvFr, frRow, frOf, frTop, submatrix_apply, id, hE, mul_diagonal]
    rw [if_neg (by rw [hfl]; omega), mul_one]
    refine (mul_col_eq _ _ ((rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr *
      (loc w (ch.S.βp (j + 1))).val.submatrix id (Fin.cast (topRank_eq ch.G t w h₁.le))) _ x (fun l => ?_) r).trans
      (congrFun (congrFun (T0' _) r) x)
    have e1 := congrFun (congrFun h1 l) (Sum.inl (Fin.cast (topRank_eq ch.G t w h₁.le) x))
    simp only [submatrix_apply, id, fromCols_apply_inl, Matrix.mul_apply, Matrix.map_apply] at e1
    simp only [submatrix_apply, id, Matrix.mul_apply, Matrix.map_apply, hpr]
    refine (congrArg _ (Fin.ext ?_)).trans e1
    simp [frame]
  · intro i jj hij r
    simp only [mvFr, frRow, frOf, submatrix_apply, id, hE, mul_diagonal]
    rw [if_neg (by rw [hfr]; omega), mul_one]
    refine (mul_col_eq _ _ ((rowJac ch.G (j + 1) h₁ σ h₂).e.map p.pr) _ i (fun l => ?_) r).trans ?_
    rotate_left
    · rw [T1]
      have hinv : ∀ x : D.host.E, p.π (incA D x⁻¹) = (p.π (incA D x))⁻¹ := fun x => map_inv₀ (p.π.comp (incA D)) x
      simp only [Matrix.map_apply, mul_diagonal, Place.pr, Place.xi, map_mul, hinv, map_pow]
      have hx : p.π (incA D D.host.xi0) ≠ 0 := hxi
      have e : p.π (incA D D.host.xi0) ^ σ = p.π (incA D D.host.xi0) ^ (σ - i.val) * p.π (incA D D.host.xi0) ^ i.val := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      field_simp
    · have e1 := congrFun (congrFun h1 l) (Sum.inr (Fin.cast h₂.symm jj))
      simp only [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e1
      rw [if_neg (Nat.succ_ne_zero j), pow_zero, mul_one, frameSign, if_neg (by simp only [Fin.val_cast]; omega), mul_one] at e1
      simp only [submatrix_apply, id, Matrix.map_apply, hpr]
      refine (congrArg _ (Fin.ext ?_)).trans (e1.trans ?_)
      · simp [frame, topRank_eq ch.G t w h₁.le]
      · have he : (rowJac ch.G (j + 1) h₁ σ h₂).e l i = (ch.G.rowDec (j + 1) h₁).a l (Fin.castLE (by omega) i) := rfl
        rw [he]
        exact congrArg _ (congrArg _ (Fin.ext (by simp; omega)))
  · intro i jj hij r
    simp only [mvFr, frRow, frOf, submatrix_apply, id, hE, mul_diagonal]
    rw [if_pos (by rw [hfr]; omega)]
    refine (congrArg (· * (-1)) (mul_col_eq _ _ (-((rowJac ch.G (j + 1) h₁ σ h₂).e'.map p.pr)) _ i (fun l => ?_) r)).trans ?_
    rotate_left
    · rw [Matrix.mul_neg, Matrix.neg_apply, T2, hz_besAt]
      simp only [Matrix.neg_apply, Matrix.map_apply, mul_diagonal, pr_mul', star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, place_proj_neg_xi_pow]
      have key := jacobiDualColumn_scalar_identity p.xi hxi i (σ - 1 - i)
      rw [show (i : ℕ) + 1 + (σ - 1 - i) = σ by omega] at key
      exact neg_mul_neg_one_eq_of_eq _ _ _ key
    · have e1 := congrFun (congrFun h1 l) (Sum.inr (Fin.cast h₂.symm jj))
      simp only [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e1
      rw [if_neg (Nat.succ_ne_zero j), pow_zero, mul_one, frameSign, if_pos (by simp only [Fin.val_cast]; omega), mul_neg_one] at e1
      simp only [submatrix_apply, id, Matrix.neg_apply, Matrix.map_apply, hpr]
      refine (congrArg _ (Fin.ext ?_)).trans (e1.trans ?_)
      · simp [frame, topRank_eq ch.G t w h₁.le]
      · simp only [rowJac, jacDec, submatrix_apply, id]
        exact congrArg _ (congrArg _ (congrArg _ (Fin.ext (by simp; omega))))

end GlobalTheory.FlatPlace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem pr_eq_algebraMap_of_isPlc {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) :
    (p.pr : D.host.E → Kw w) = algebraMap D.host.E (Kw w) := funext fun a => by
  show p.π (incA D a) = _
  rw [hp.2.1]
  exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z w) (GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) a)

theorem topVertexFrame_renumbered_cast (ch : Choice R) (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (n : ℕ) (hn : D.R.m = n) (hle : n ≤ D.R.m) :
    ∃ e : Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit ≃ Fin (topRank (locGrid ch.G t w) n),
      (∀ i, (e (Sum.inl i)).val = i.val) ∧ (e (Sum.inr ())).val = topRank (locGrid ch.G t w) n - 1 ∧
      ∃ FX : Frame (Kw w) (ch.G.V (.top n)).rank (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit),
        FX.β = fromCols ((topOrthAt ch.G hn).iA.map p.pr * (frRow ch.S.B t w D.R.m le_rfl).β)
          (Matrix.of fun r _ => ((topOrthAt ch.G hn).iB.map p.pr *ᵥ fun _ => (1 : Kw w)) r) ∧
        ∀ r z, FX.β r z = (frTop ch.S.toGridChoice t w n hle).β r (e z) := by
  subst hn
  have hL := ch.S.last t (Set.mem_univ t) w hw
  unfold IsSumFrame at hL
  rw [pr_eq_algebraMap_of_isPlc hp]
  set d := ch.G.sp.topDec with hd
  have h1 : (locGrid ch.G t w).rank (D.R.m, D.R.m) = (ch.G.V (.grid D.R.m D.R.m)).rank :=
    rank_vertex ch.G t w (X := (D.R.m, D.R.m)) ⟨le_rfl, le_rfl⟩
  have h2 : topRank (locGrid ch.G t w) D.R.m = (ch.G.V (.top D.R.m)).rank := topRank_eq ch.G t w hle
  have h3 : (ch.G.V (.grid D.R.m D.R.m)).rank + 1 = (ch.G.V (.top D.R.m)).rank := d.rank
  let e : Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit ≃ Fin (topRank (locGrid ch.G t w) D.R.m) :=
    ((Equiv.sumCongr (finCongr h1) (⟨fun _ => 0, fun _ => (), fun _ => rfl, fun x => Subsingleton.elim _ _⟩ : Unit ≃ Fin 1)).trans (frame h3)).trans (finCongr h2.symm)
  refine ⟨e, fun i => rfl, ?_, ?_⟩
  · simp [e, frame]
    omega
  let F := frTop ch.S.toGridChoice t w D.R.m hle
  refine ⟨⟨F.β.submatrix id e, F.γ.submatrix e id, ?_, ?_⟩, ?_, fun r z => rfl⟩
  · rw [submatrix_mul_equiv, submatrix_id_id, F.βγ]
  · rw [← submatrix_mul _ _ _ id _ Function.bijective_id, F.γβ, submatrix_one_equiv]
  · refine Matrix.ext fun r z => ?_
    rcases z with i | u
    · have := congrFun (congrFun hL r) (Sum.inl (Fin.cast h1 i))
      refine Eq.trans ?_ (this.trans ?_)
      · rfl
      · simp only [fromCols_apply_inl]
        rfl
    · have := congrFun (congrFun hL r) (Sum.inr 0)
      refine Eq.trans ?_ (this.trans ?_)
      · rfl
      · simp only [fromCols_apply_inr, of_apply, Matrix.mul_diagonal, Matrix.map_apply, mul_one]
        rw [Pi.one_apply, mul_one]
        symm
        show ∑ k : Fin 1, (_ : Kw w) = _
        rw [Fin.sum_univ_one]
        exact mul_one _

theorem frame_top_last : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (j : ℕ) (hj : j + 2 = D.R.m),
    ∃ e : Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit ≃ Fin (topRank (locGrid ch.G t w) (j + 1 + 1)),
      (∀ i, (e (Sum.inl i)).val = i.val) ∧ (e (Sum.inr ())).val = topRank (locGrid ch.G t w) (j + 1 + 1) - 1 ∧
      ∃ FX : Frame (Kw w) (ch.G.V (.top (j + 1 + 1))).rank (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit),
        FX.β = fromCols ((topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)).iA.map p.pr * (frRow ch.S.B t w D.R.m le_rfl).β)
          (Matrix.of fun r _ => ((topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)).iB.map p.pr *ᵥ fun _ => (1 : Kw w)) r) ∧
        ∀ r z, FX.β r z = (frTop ch.S.toGridChoice t w (j + 1 + 1) (by omega)).β r (e z) :=
  fun ch t w hw p hp j _ => topVertexFrame_renumbered_cast ch t w hw p hp (j + 1 + 1) (by omega) (by omega)

end GlobalTheory.FlatPlace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.PlcAtW

variable {D : D7}


open Classical in
theorem cpt_atPl_self (w : Pl D.host.E) (x : Kw w) : cpt w (toEAf D (atPl w x)) = x := by
  rw [(atPl_spec w x).2 w, Pi.single_eq_same]

theorem atPl_zero (w : Pl D.host.E) : atPl w (0 : Kw w) = 0 := by
  have h := atPl_add w 0 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

def atPlHom (w : Pl D.host.E) : Kw w →+ AE D where
  toFun := atPl w
  map_zero' := atPl_zero w
  map_add' := atPl_add w

theorem atPl_cpt (w : Pl D.host.E) (a : AE D) : atPl w (cpt w (toEAf D a)) = atPl w 1 * a := by
  classical
  refine ae_ext ?_ fun Q => ?_
  · rw [(atPl_spec w _).1, map_mul, (atPl_spec w 1).1, zero_mul]
  · rw [(atPl_spec w _).2 Q, map_mul, map_mul, (atPl_spec w 1).2 Q]
    by_cases hQ : Q = w
    · subst hQ
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne hQ, Pi.single_eq_of_ne hQ, zero_mul]

theorem valuation_le_of_inv_mul {k : Type} [Field k] [ValuativeRel k] (u : kˣ) (b : k)
    (h : ValuativeRel.valuation k (((u⁻¹ : kˣ) : k) * b) ≤ 1) :
    ValuativeRel.valuation k b ≤ ValuativeRel.valuation k (u : k) := by
  have hne : ValuativeRel.valuation k (u : k) ≠ 0 := by simp
  rw [Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h
  calc ValuativeRel.valuation k b
      = ValuativeRel.valuation k (u : k) * ((ValuativeRel.valuation k (u : k))⁻¹ * ValuativeRel.valuation k b) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ ≤ ValuativeRel.valuation k (u : k) * 1 := by gcongr
    _ = _ := mul_one _

theorem cpt_atPl_mul (w : Pl D.host.E) (x : Kw w) (z : AE D) :
    cpt w (toEAf D (atPl w x * z)) = x * cpt w (toEAf D z) := by
  rw [map_mul, map_mul, cpt_atPl_self]

theorem valuation_cpt_le_one (w : Pl D.host.E) (x : AE D) (h : finPart D x ∈ intAE D) :
    ValuativeRel.valuation (Kw w) (cpt w (toEAf D x)) ≤ 1 := by
  have h2 := ((GlobalTheory.StdFrames.comp_toAd D).int x).1 h w
  have h3 : cpt w (toEAf D x) ∈ (ValuativeRel.valuation (Kw w)).integer :=
    (GlobalTheory.FinPl.SplitPoint.mem_integer_iff D.host.E w _).2 h2
  exact h3

end GlobalTheory.PlcAtW

open scoped TensorProduct

namespace GlobalTheory.PlcAtW

variable {D : D7}


open scoped Topology in
theorem continuous_cpt_toEAf (w : Pl D.host.E) : Continuous fun a : AE D => cpt w (toEAf D a) := by
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, -⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  have h1 : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
    rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
    convert this using 1
    ext z
    simp
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero (Kw w)) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  let f : AE D →+ Kw w := ((cpt w).comp (toEAf D)).toAddMonoidHom
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  refine (IsValuativeTopology.hasBasis_nhds_zero (Kw w)).tendsto_right_iff.2 fun γ _ => ?_
  have hϖ : ValuativeRel.valuation (Kw w) (unifAt w : Kw w) < 1 := by
    rw [isUnif_unifAt w]
    exact ValuativeRel.uniformizer_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ γ
  set u : (Kw w)ˣ := unifAt w ^ n
  have hu : ValuativeRel.valuation (Kw w) (u : Kw w) < γ := by
    simpa [u, Units.val_pow_eq_pow_val, map_pow] using hn
  have hU : {z : AE D | finPart D (atPl w ((u⁻¹ : (Kw w)ˣ) : Kw w) * z) ∈ intAE D} ∈ 𝓝 (0 : AE D) := by
    refine IsOpen.mem_nhds (h1.preimage (hfc.comp (continuous_const.mul continuous_id))) ?_
    simp only [Set.mem_setOf_eq, mul_zero, map_zero]
    exact zero_mem _
  filter_upwards [hU] with z hz
  have h3 := valuation_cpt_le_one w _ hz
  rw [cpt_atPl_mul] at h3
  exact (valuation_le_of_inv_mul u _ h3).trans_lt hu

end GlobalTheory.PlcAtW

namespace GlobalTheory.PlcAtW

variable {D : D7}

theorem continuous_atPl (w : Pl D.host.E) : Continuous (atPl (D := D) w) := by
  classical
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, -, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hs : Function.Bijective (Formalism.IndefR.Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).bijective
  have ht : Function.Bijective (toAd D) :=
    ⟨GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D), GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)⟩
  let R : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    RingEquiv.ofBijective ((toAd D).comp (Formalism.IndefR.Lev.swapAE D)) (ht.comp hs)
  have hfin : ∀ y, finPart D (e.symm (0, y)) = y := fun y => by
    rw [← (he _).2, RingEquiv.apply_symm_apply]
  have hR : Continuous R.symm := by
    refine GlobalTheory.AdeleBaseChange.continuous_symm_finite D.host.F D.host.E R fun y => ?_
    have key := (GlobalTheory.StdFrames.comp_toAd D).int (e.symm (0, y))
    rw [hfin] at key
    have e1 : ((toAd D).comp (toEAf D)) (e.symm (0, y)) = R y := by
      show toAd D (Formalism.IndefR.Lev.swapAE D (finPart D (e.symm (0, y)))) = toAd D (Formalism.IndefR.Lev.swapAE D y)
      rw [hfin]
    rw [e1] at key
    exact key
  have hform : ∀ x, atPl w x = e.symm (0, R.symm (singleV D.host.E w x)) := fun x => by
    refine ae_ext ?_ fun Q => ?_
    · rw [(atPl_spec w x).1, ← (he _).1, RingEquiv.apply_symm_apply]
    · rw [(atPl_spec w x).2 Q]
      show _ = toAd D (Formalism.IndefR.Lev.swapAE D (finPart D (e.symm (0, R.symm (singleV D.host.E w x))))) Q
      rw [hfin]
      show _ = R (R.symm (singleV D.host.E w x)) Q
      rw [RingEquiv.apply_symm_apply]
      by_cases hQ : Q = w
      · subst hQ
        rw [Pi.single_eq_same]
        exact (RestrictedProduct.single_eq_same _ _ _).symm
      · rw [Pi.single_eq_of_ne hQ]
        exact (RestrictedProduct.single_eq_of_ne _ _ hQ).symm
  rw [funext hform]
  exact hes.comp (continuous_const.prodMk (hR.comp (GlobalTheory.FinPl.SplitPoint.continuous_single_at D.host.E w)))

end GlobalTheory.PlcAtW

namespace GlobalTheory.PlcAtW

theorem exists_plc : ∀ (D : D7) (w : Pl D.host.E) (e : AE D), IsIdemSum e {w} → ∃ p : Place D (Kw w), IsPlc w p ∧ p.e = e := by
  intro D w e he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_singleton]
  have h := hes w (Finset.mem_singleton_self w)
  have he1 := GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt h
  refine ⟨{ e := es w
            split := h.1
            π := (cpt w).comp (toEAf D)
            ι := atPlHom w
            π_ι := cpt_atPl_self w
            ι_π := fun a => by
              show atPl w (cpt w (toEAf D a)) = es w * a
              rw [atPl_cpt, ← he1]
            cont_π := continuous_cpt_toEAf w
            cont_ι := continuous_atPl w }, ⟨h, fun _ => rfl, fun _ => rfl⟩, rfl⟩

end GlobalTheory.PlcAtW

end
end
