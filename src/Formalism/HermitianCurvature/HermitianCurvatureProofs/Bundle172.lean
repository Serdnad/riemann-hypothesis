module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle129
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SesquilinearLevelZeroPairing
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitTailEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

theorem pairJ_rel {X Y : Type} {w : List C.Letter} (R : X → Y → Prop) (c : ℂ)
    (Ξ1 : (Ix (Fin w.length) → X) → (Ix (Fin w.length) → X) → ℂ)
    (Ξ2 : (Ix (Fin w.length) → Y) → (Ix (Fin w.length) → Y) → ℂ)
    (h : ∀ x x' y y', (∀ e, R (x e) (y e)) → (∀ e, R (x' e) (y' e)) → Ξ1 x x' = c * Ξ2 y y') :
    ∀ (ys : List ℝ) (x : Ix (Fin (KB.plusW ys w).length) → X) (x' : Ix (Fin (KB.minusW ys w).length) → X)
      (y : Ix (Fin (KB.plusW ys w).length) → Y) (y' : Ix (Fin (KB.minusW ys w).length) → Y),
      (∀ e, R (x e) (y e)) → (∀ e, R (x' e) (y' e)) → KB.pairJ Ξ1 ys x x' = c * KB.pairJ Ξ2 ys y y'
  | [], x, x', y, y', hx, hx' => h x x' y y' hx hx'
  | _ :: ys, x, x', y, y', hx, hx' => by
    show KB.pairJ Ξ1 ys _ _ - KB.pairJ Ξ1 ys _ _ = c * (KB.pairJ Ξ2 ys _ _ - KB.pairJ Ξ2 ys _ _)
    have a1 := pairJ_rel R c Ξ1 Ξ2 h ys (fun e => x (Fin.cons 1 e)) (fun e => x' (Fin.cons 0 e))
      (fun e => y (Fin.cons 1 e)) (fun e => y' (Fin.cons 0 e)) (fun e => hx _) (fun e => hx' _)
    have a2 := pairJ_rel R c Ξ1 Ξ2 h ys (fun e => x (Fin.cons 0 e)) (fun e => x' (Fin.cons 1 e))
      (fun e => y (Fin.cons 0 e)) (fun e => y' (Fin.cons 1 e)) (fun e => hx _) (fun e => hx' _)
    exact (congrArg₂ (· - ·) a1 a2).trans (mul_sub _ _ _).symm

theorem prod_real (zs : List ℂ) (h : ∀ z ∈ zs, z.im = 0) : zs.prod.im = 0 ∧ zs.prod.re = (zs.map Complex.re).prod := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hz := h z (by simp)
    obtain ⟨h1, h2⟩ := ih fun z' hz' => h z' (by simp [hz'])
    simp only [List.prod_cons, List.map_cons, Complex.mul_im, Complex.mul_re, hz, h1, mul_zero, zero_mul,
      add_zero, sub_zero, h2]
    exact ⟨trivial, trivial⟩

theorem form_castIx {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    {n m : ℕ} (h : n = m) (U V : Ix (Fin n) → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (fun z => U (z ∘ Fin.cast h)) (fun z => V (z ∘ Fin.cast h)) c = form μ 0 U V c := by
  subst h
  rfl

theorem form_embed {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] (ι : Ix S' → Ix S)
    (hι : Function.Injective ι) (x y : Ix S' → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (Function.extend ι x 0) (Function.extend ι y 0) c = form μ 0 x y c := by
  unfold form
  congr 1
  funext c'
  congr 1
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun a _ b _ h => hι h)]
  · simp only [hι.extend_apply]
  · intro z _ hz
    have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, pairAt_zero_left]

theorem pairS_embed {V : Type} [AddCommGroup V] [Module ℂ V] {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S']
    [DecidableEq S'] (β : V → V → ℂ) (hβ : ∀ v, β 0 v = 0) (ι : Ix S' → Ix S) (hι : Function.Injective ι)
    (x y : Ix S' → V) : pairS β (Function.extend ι x 0) (Function.extend ι y 0) = pairS β x y := by
  unfold pairS
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun a _ b _ h => hι h)]
  · simp only [hι.extend_apply]
  · intro z _ hz
    have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, hβ]

def ixEmb {m n : ℕ} (h : m ≤ n) (e : Ix (Fin m)) : Ix (Fin n) := fun t => if ht : t.val < m then e ⟨t, ht⟩ else 0

theorem ixEmb_inj {m n : ℕ} (h : m ≤ n) : Function.Injective (ixEmb h) := by
  intro e e' he
  funext t
  have := congrFun he ⟨t.val, by omega⟩
  simpa [ixEmb, t.isLt] using this

theorem bet_neg {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    (v v' : RadSp k r z z' π π') : bet μ (-v) v' = -bet μ v v' := by
  unfold bet
  have := pairLev_smul_left (μ := μ) (i := 0) v v' (fun _ => 1) (-1)
  have e : ((-1 : ℂ) • v) = -v := neg_one_smul ℂ v
  rw [e, neg_one_mul] at this
  exact this

theorem bet_zero {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    (v : RadSp k r z z' π π') : bet μ 0 v = 0 := by
  unfold bet; exact pairLev_zero_left v _

section EmbData

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {n : ℕ}
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : MeasureTheory.Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem form_zero_eq_position_pairing_of_le (hThm : ThmPOn (S := Fin n) P z z' π π' μ L st K l0) {m : ℕ} (hmn : m ≤ n)
    (Y₁ Y₂ : Ix (Fin m) → RadSp P.k P.r z z' π π') (h₁ : ∀ a, Y₁ a ∈ K 0) (h₂ : ∀ a, Y₂ a ∈ K 0) :
    form μ 0 Y₁ Y₂ 0 = pairS (bet μ) Y₁ Y₂ := by
  have extK : ∀ v : Ix (Fin m) → RadSp P.k P.r z z' π π', (∀ a, v a ∈ K 0) →
      ∀ z, Function.extend (ixEmb hmn) v 0 z ∈ K 0 := by
    intro v hv z
    by_cases hz : ∃ a, ixEmb hmn a = z
    · obtain ⟨a, rfl⟩ := hz
      rw [(ixEmb_inj hmn).extend_apply]; exact hv a
    · rw [Function.extend_apply' _ _ _ hz]; exact (K 0).zero_mem
  have e1 := form_embed μ (ixEmb hmn) (ixEmb_inj hmn) Y₁ Y₂ 0
  have e2 := form_zero_eq_position_pairing hThm (Function.extend (ixEmb hmn) Y₁ 0) (Function.extend (ixEmb hmn) Y₂ 0)
    (extK _ h₁) (extK _ h₂)
  have e3 := pairS_embed (V := RadSp P.k P.r z z' π π') (bet μ) (fun v => bet_zero μ v) (ixEmb hmn) (ixEmb_inj hmn) Y₁ Y₂
  exact e1.symm.trans (e2.trans e3)

end EmbData

theorem final_ineq (Cst : ℝ) (A B P0 Q : ℂ) (qs : List ℂ) (hQ : Q = qs.prod)
    (hqs : ∀ z ∈ qs, 0 < z.re ∧ z.im = 0) (hAi : A.im = 0) (hBi : B.im = 0) (hdk : ‖P0‖ ^ 2 ≤ (A * B / Q).re) :
    ‖(Cst : ℂ) * P0‖ ^ 2 * (qs.map Complex.re).prod ≤ ((Cst : ℂ) * A).re * ((Cst : ℂ) * B).re := by
  obtain ⟨hQi, hQr⟩ := prod_real qs fun z hz => (hqs z hz).2
  have hpos : 0 < (qs.map Complex.re).prod := List.prod_pos fun x hx => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    exact (hqs z hz).1
  have eA : A = (A.re : ℂ) := Complex.ext (by simp) (by simp [hAi])
  have eB : B = (B.re : ℂ) := Complex.ext (by simp) (by simp [hBi])
  have eQ : Q = ((qs.map Complex.re).prod : ℂ) := by
    rw [hQ]; exact Complex.ext (by simp [hQr]) (by simp [hQi])
  have h1 : (A * B / Q).re = A.re * B.re / (qs.map Complex.re).prod := by
    rw [eA, eB, eQ, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    simp
  rw [h1, le_div_iff₀ hpos] at hdk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.re_ofReal_mul, Complex.re_ofReal_mul, mul_pow, sq_abs]
  nlinarith [sq_nonneg Cst]

theorem cast_map_pred {n m : ℕ} (h : n = m) (Q : ∀ k, List (Letter ℂ (Fin k)) → Prop) (u : List (Letter ℂ (Fin n)))
    (hu : Q n u) : Q m (u.map (castL h)) := by
  subst h; rwa [castL_rfl]

theorem Lw_qw (q : ℂ → ℂ) (ys : List ℝ) (w : List C.Letter) :
    ((Lw ys w).map fun l => qw q (Ww ys w) l.pt) = ys.map fun y : ℝ => qw q (D.positionted w) (y : ℂ) := by
  apply List.ext_getElem
  · simp [Lw_length]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, Lw_getElem, qw_Ww]

end

end Formalism.FourierDecayAlt.P.PBF

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem point_size_append_single (h : C.LPt) (c : ℂ) : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := by
  rw [Dx2.SL.ptSize_append]

theorem integrable_slice_append_single {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h : C.LPt) (c : ℂ)
    (hle : D.ptSize (h ++ [(1, c)]) ≤ r) (hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])))
    (γ' : B.Mat k (r - D.ptSize (h ++ [(1, c)])))
    (hI : Integrable (JCTx6.gInt k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
        (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
        (D.castF (by have := point_size_append_single h c; omega) F) γ')
      (JCTx6.muG k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h))) :
    Integrable (fun ξ : U.Xi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) =>
        U.psiStar k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) (D.castV (by omega) z)
            (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))
            (D.ptDiag (h ++ [(1, c)])) ξ (fun a => a.elim0) γ'))
      (U.muXi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))) := by
  have hP : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := point_size_append_single h c
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ (Dx2.SL.isLocPt_head hloc)).1
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) (Fin.cast hP a)).val = (D.ptPerm (h ++ [(1, c)]) a).val := by
    intro a
    rw [hspec a, Dx2.SL.partner_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      Dx2.SL.dP (n := 0) (D.ptDiag h) c (Fin.cast hP a) = D.ptDiag (h ++ [(1, c)]) a := by
    intro a
    simp only [D.ptDiag]
    rw [Dx2.SL.scal_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.dP, Fin.addCases_right]

  have hσ' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      (D.ptPerm (h ++ [(1, c)]) (Fin.cast hP.symm b)).val = ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) b).val := by
    intro b
    have := hσ (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have hd' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      D.ptDiag (h ++ [(1, c)]) (Fin.cast hP.symm b) = Dx2.SL.dP (n := 0) (D.ptDiag h) c b := by
    intro b
    have := hd (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have h1 := JCTx6.Int.orbit_slice_integrable k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z') E
    (D.castF (by have := point_size_append_single h c; omega) F) γ' hI
  have h2 := (Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(1, c)])) hP.symm _ _ hσ' _ _ hd'
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
    (D.castF (by have := point_size_append_single h c; omega) F) γ').1 h1
  simpa only [Dx2.SL.castV_castV, Dx2.SL.castF_castF] using h2

end Formalism.FourierDecayAlt.P.PBH
end
end

section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory Filter

noncomputable section

section om

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem maxpow_le_onepow {x y a : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (ha : 0 ≤ a) :
    (1 + x) ^ (-a) ≤ (max 1 y) ^ (-a) := by
  refine Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_ (by linarith)
  exact max_le (by linarith) (by linarith)

theorem continuous_lowRow (n : ℕ) : Continuous (fun a : Fin n → ℂ => lowRow a) := by
  unfold lowRow
  exact P.G7.continuous_blk continuous_const continuous_const continuous_id continuous_const

theorem continuous_blkU (n : ℕ) :
    Continuous (fun p : (UT n → ℂ) × (Fin n → ℂ) => blk (upper p.1) p.2 0 1) :=
  P.G7.continuous_blk (P.Dx2.SL.cont_upper.comp continuous_fst) continuous_snd continuous_const continuous_const

theorem continuous_orbM (n : ℕ) (t c : ℂ) : Continuous (orbM n t c) := by
  unfold orbM
  refine Continuous.matrix_mul (Continuous.matrix_mul ((continuous_lowRow n).comp continuous_fst) continuous_const) ?_
  exact (continuous_blkU n).comp (continuous_snd)

theorem integrable_blockIntegrand (β : ℂ) (m : ℕ) (Φ : Mat (m + 2) → V) (t c : ℂ) (ht : t ≠ 0) (K a : ℝ)
    (ha : ((m : ℝ) + 1) * ((m : ℝ) + 4) < a) (hc : ∀ p, ContinuousAt Φ (orbM (m + 1) t c p))
    (hb : ∀ p, ‖Φ (orbM (m + 1) t c p)‖ ≤ K * (1 + ‖orbM (m + 1) t c p‖) ^ (-a)) :
    Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖orbM (m + 1) t c 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (orbM (m + 1) t c 0))]
  have hpt : ∀ p : BlockCoord (m + 1),
      ‖blockIntegrand β (m + 1) Φ t c p‖ ≤ K * (max 1 ‖coordMap (m + 1) t p‖) ^ (-a) := by
    intro p
    rw [P.OrbitTailEstimates.norm_blockIntegrand]
    refine (hb p).trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact maxpow_le_onepow (norm_nonneg _) (P.OrbitTailEstimates.norm_coordMap_le (m + 1) t c p) ha0
  obtain ⟨k, hk⟩ := P.G7.muBlock_eq β (m + 1)
  have i3 : BorelSpace (BlockCoord (m + 1)) := inferInstance
  have j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hfr : (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) < a := by
    rw [P.OrbitTailEstimates.finrank_block_cast]; exact ha
  have hI : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a)) (muBlock β (m + 1)) := by
    rw [hk]; exact (P.OrbitTailEstimates.integrable_maxpow volume a hfr).smul_measure_nnreal
  have hJ := P.G7.jacobian (m + 1) β t ht
  have hI' : Integrable (fun p : BlockCoord (m + 1) => (max 1 ‖coordMap (m + 1) t p‖) ^ (-a))
      (muBlock β (m + 1)) := by
    have h2 : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a))
        (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) := hJ ▸ hI.smul_measure_nnreal
    exact (P.G7.embedding_coordMap _ t ht).integrable_map_iff.1 h2
  have hcont : Continuous (blockIntegrand β (m + 1) Φ t c) := by
    unfold blockIntegrand
    refine Continuous.smul ?_ ?_
    · have h1 : Continuous fun p : BlockCoord (m + 1) => G.subSum (lowRow p.1) := by
        unfold G.subSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_lowRow (m + 1)).comp continuous_fst))
      have h2 : Continuous fun p : BlockCoord (m + 1) => G.superSum (blk (upper p.2.1) p.2.2 0 1) := by
        unfold G.superSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_blkU (m + 1)).comp continuous_snd))
      exact ((P.G7.continuous_psi β).comp h1).mul ((P.G7.continuous_psi β).comp h2)
    · exact continuous_iff_continuousAt.2 fun p => (hc p).comp (continuous_orbM (m + 1) t c).continuousAt
  exact (hI'.const_mul K).mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt)

theorem integrable_longIntegrand (n : ℕ) (Φ : Mat (n + 1) → V) (z : ℂ) (hz : z ≠ 0) (K a : ℝ)
    (ha : (Module.finrank ℝ (UT (n + 1) → ℂ) : ℝ) < a)
    (hc : ∀ v, ContinuousAt Φ (P.JCTx6.Pos.Zv n z v))
    (hb : ∀ v, ‖Φ (P.JCTx6.Pos.Zv n z v)‖ ≤ K * (1 + ‖P.JCTx6.Pos.Zv n z v‖) ^ (-a)) :
    Integrable (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v))
      (muPi U.betaU (UT (n + 1))) := by
  have ha0 : 0 ≤ a := le_trans (Nat.cast_nonneg _) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖P.JCTx6.Pos.Zv n z 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (P.JCTx6.Pos.Zv n z 0))]
  have hZc : Continuous (fun v : UT (n + 1) → ℂ => P.JCTx6.Pos.Zv n z v) := by
    show Continuous (fun v : UT (n + 1) → ℂ =>
      ((ptLong (n + 1) z * upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Mat (n + 1)))
    exact continuous_const.matrix_mul P.Dx2.SL.cont_upper
  have hΦc : Continuous (fun v : UT (n + 1) → ℂ => Φ (P.JCTx6.Pos.Zv n z v)) :=
    continuous_iff_continuousAt.2 fun v => (hc v).comp hZc.continuousAt
  have hψc : Continuous (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v))) := by
    have h1 : Continuous fun v : UT (n + 1) → ℂ => superSum (upper v) := by
      unfold superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp P.Dx2.SL.cont_upper)
    exact (P.G7.continuous_psi _).comp h1
  have hbound : ∀ v : UT (n + 1) → ℂ, ‖psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v)‖ ≤
      K * (min 1 ‖z‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro v
    rw [norm_smul, P.WirtingerIntegrationByParts.norm_psi, one_mul]
    refine (hb v).trans ?_
    have := mul_le_mul_of_nonneg_left (P.JCTx6.Pos.Zv_decay n hz v ha0) hK
    rw [← mul_assoc] at this
    exact this
  rw [P.Dx2.SL.muPi_betaU]
  apply Integrable.smul_measure_nnreal
  exact ((integrable_one_add_norm ha).const_mul (K * (min 1 ‖z‖) ^ (-a))).mono'
    (hψc.smul hΦc).aestronglyMeasurable (Eventually.of_forall hbound)

theorem clm_omBlock [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (t c : ℂ) (hI : Integrable (blockIntegrand β n Φ t c) (muBlock β n)) :
    L (OmBlock β n Φ t c) = OmBlock β n (fun Z => L (Φ Z)) t c := by
  unfold OmBlock
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [blockIntegrand, L.map_smul]

theorem clm_omLong [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (z : ℂ) (hI : Integrable (fun v : UT (n + 1) → ℂ => psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v))
      (muPi β (UT (n + 1)))) :
    L (OmLong β n Φ z) = OmLong β n (fun Z => L (Φ Z)) z := by
  unfold OmLong
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [L.map_smul]

end om

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end
