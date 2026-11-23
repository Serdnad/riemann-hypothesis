module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle009
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle011
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.EdgeLatOfG
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterWtAnti
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RhoAtGOfPair
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestCloudBOfTop
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.OrdMaxRest
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin)

section Words

variable {R : Type} [CommRing R] {n' k : ℕ}

def WSpan (l : List (Fin n' × (Fin k × Fin k))) (h : MvPolynomial (Fin n' × Fin k) R) :
    Submodule R (MvPolynomial (Fin n' × Fin k) R) :=
  Submodule.span R {y | ∃ l' : List (Fin n' × (Fin k × Fin k)), l'.map Prod.fst = l.map Prod.fst ∧ y = opWord l' h}

theorem wspan_op (l : List (Fin n' × (Fin k × Fin k))) (h : MvPolynomial (Fin n' × Fin k) R) (s : Fin n')
    (x : Fin k × Fin k) (c c' : Fin k) {z : MvPolynomial (Fin n' × Fin k) R} (hz : z ∈ WSpan l h) :
    X (s, c) * pderiv (s, c') z ∈ WSpan ((s, x) :: l) h := by
  unfold WSpan at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l', hl', rfl⟩ := hy
    exact Submodule.subset_span ⟨(s, (c, c')) :: l', by simp [hl'], rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add (f := _), mul_add]
    exact Submodule.add_mem _ ha hb
  | smul a y _ hy =>
    rw [Derivation.map_smul, mul_smul_comm]
    exact Submodule.smul_mem _ a hy

theorem Lin_word (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1)
    (f : MvPolynomial (Fin n' × Fin k) R) :
    ∀ l : List (Fin n' × (Fin k × Fin k)), Lin N (opWord l f) ∈ WSpan l (Lin N f) := by
  intro l
  induction l with
  | nil => exact Submodule.subset_span ⟨[], rfl, rfl⟩
  | cons y l ih =>
    obtain ⟨s, a, b⟩ := y
    show Lin N (X (s, a) * pderiv (s, b) (opWord l f)) ∈ _
    rw [map_mul, Lin_X, Lin_pderiv N N' h, Finset.sum_mul]
    refine Submodule.sum_mem _ fun b' _ => ?_
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [mul_smul_comm, MvPolynomial.C_mul', smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (wspan_op l _ s (a, b) b' c ih))

theorem wspan_le_OpCl (TT : Finset (Fin n')) (c : ℕ) (M : Submodule R (MvPolynomial (Fin n' × Fin k) R))
    (l : List (Fin n' × (Fin k × Fin k))) (h1 : ∀ z ∈ l, z.1 ∈ TT) (h2 : ∀ s, (l.filter fun z => z.1 = s).length ≤ c)
    {h : MvPolynomial (Fin n' × Fin k) R} (hh : h ∈ M) : WSpan l h ≤ OpCl TT c M := by
  rw [WSpan, Submodule.span_le]
  rintro y ⟨l', hl', rfl⟩
  refine Submodule.subset_span ⟨h, hh, l', ?_, ?_, rfl⟩
  · intro z hz
    have hz' : z.1 ∈ l.map Prod.fst := hl' ▸ List.mem_map_of_mem hz
    obtain ⟨z', hz'', e⟩ := List.mem_map.1 hz'
    exact e ▸ h1 z' hz''
  · intro s
    have e : ∀ L : List (Fin n' × (Fin k × Fin k)), (L.filter fun z => decide (z.1 = s)).length =
        ((L.map Prod.fst).filter fun t => decide (t = s)).length := by
      intro L
      rw [List.filter_map, List.length_map]
      rfl
    rw [e, hl', ← e]
    exact h2 s

theorem Lin_OpCl (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (TT : Finset (Fin n')) (c : ℕ)
    (M M' : Submodule R (MvPolynomial (Fin n' × Fin k) R)) (hM : ∀ f ∈ M, Lin N f ∈ M') :
    ∀ f ∈ OpCl TT c M, Lin N f ∈ OpCl TT c M' := by
  intro f hf
  unfold OpCl at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f0, hf0, l, h1, h2, rfl⟩ := hy
    exact wspan_le_OpCl TT c M' l h1 h2 (hM f0 hf0) (Lin_word N N' h f0 l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end Words

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 Formalism.MainNotions.SourceCleaning
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti flat_lam tensor_lattice_twist_eq edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF flat_Ar)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ} {d : Fin n' → ℕ}

theorem HL_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det)
    (u : ↥(Vsp Kf (flW (m := m) d))) :
    u ∈ HL (O := O) ι σ (flW d) (colSpan W ℓ) ↔
      (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O d (fun s => la_tw ι σ s.val ℓ) := by
  show (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
    Hten O (flW d) (fun s => extO O ι σ s.val (colSpan W ℓ)) ↔ _
  rw [Hten_flW, tensor_lattice_twist_eq hS m (vecE n') d (fun x => x) ℓ hℓ]
  rfl

theorem HLe_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (u : ↥(Vsp Kf (flW (m := m) d))) :
    u ∈ HLe p ι σ w (flW d) e ↔
      (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        LatM O d (fun s => la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
  show (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
    Hten O (flW d) (fun s => LeAt p ι σ w s.val e) ↔ _
  have := hS.frac_O
  have e1 : (fun x : Fin n' => H0 O m (letterWt m (d x) (vecE n' x)) (LeAt p ι σ w x.val e)) =
      fun s => nablaLTw O Kf m (letterWt m (d s) (vecE n' s))
        (la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
    funext x
    rw [(edgeLat_of hS m r e b hb).2.1, H0_eq_twisted_nabla (la_indep (IsFractionRing.injective O Kf)) _ _ (letterWt_anti _ _ _) _
      (by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS)))]
  rw [Hten_flW, e1]
  rfl

theorem la_tw_invT (s : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose) = ((la_tw ι σ s b)⁻¹).transpose := by
  rw [la_tw_transpose, la_tw_inv _ _ hb]

theorem la_tw_dE (s r : ℕ) : la_tw ι σ s (dE (m + 1) r ((p : ℕ) : Qq)) = dE (m + 1) r ((p : ℕ) : Kf) := by
  ext a c
  simp only [la_tw, dE, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem dualM (hS : HidaSetting p n' W Qq O Kf ι σ j w) (s r : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) * lb_D (m + 1) r (algebraMap O Kf w) =
      ((la_tw ι σ s b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose := by
  have hω := w_ne hS
  have hp : ((p : ℕ) : Kf) = (algebraMap O Kf w) ^ 2 := by rw [← map_pow, hS.w_sq, map_natCast]
  rw [la_tw_mul, la_tw_invT s b hb, la_tw_dE, Matrix.mul_inv_rev, Matrix.transpose_mul, mul_assoc]
  congr 1
  simp only [dE, lb_D, Matrix.diagonal_mul_diagonal, Matrix.inv_diagonal, Matrix.diagonal_transpose]
  congr 1
  funext a
  have hu : IsUnit (fun a : Fin (m + 1) => if a.val < r then (algebraMap O Kf w)⁻¹ else (1 : Kf)) := by
    rw [Pi.isUnit_iff]
    intro a
    split_ifs
    · exact isUnit_iff_ne_zero.mpr (inv_ne_zero hω)
    · exact isUnit_one
  have hinv := congrFun (Ring.inverse_mul_cancel _ hu) a
  rw [Pi.mul_apply, Pi.one_apply] at hinv
  rw [eq_inv_of_mul_eq_one_left hinv]
  split_ifs with h
  · rw [inv_inv, hp]; field_simp
  · simp

variable (thK : ↥(Pol Kf (ι := Fin n') (m + 1) d) ≃ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)))

theorem FD_edge (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (i : ℤ)
    (y : ↥(Vsp Kf (flW (m := m) d)))
    (hy : y ∈ scale (algebraMap O Kf w ^ i) (Re p ι σ w r (flW d) e.dual)) :
    TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y ∈
      scale (algebraMap O Kf w ^ i) (Re' p ι σ w r (flW d) e) := by
  obtain ⟨y1, hy1, rfl⟩ := mem_scale.1 hy
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy1
  refine mem_scale.2 ⟨_, mem_scale.2 ⟨TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y0, ?_, rfl⟩, ?_⟩
  · intro u hu
    refine sandwich thK hm hthK p κ hMD (fun s => la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w))
      (fun s => by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS))) u y0
      ((HLe_iff hS r e b hb u).1 hu) ?_
    have h1 := (HLe_iff hS r e.dual _ (dual_edgeBasis p r (pQ_ne hS) e b hb) y0).1 hy0
    have e1 : (fun s : Fin n' => la_tw ι σ s.val ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) *
        lb_D (m + 1) r (algebraMap O Kf w)) =
        fun s => ((la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose :=
      funext fun s => dualM hS s.val r b hb.1
    rw [e1] at h1
    exact h1
  · rw [map_smul, map_smul]

theorem FD_HL (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d)
    (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det) (c : Kf)
    (y : ↥(Vsp Kf (flW (m := m) d)))
    (hy : y ∈ scale c (HL (O := O) ι σ (flW d) (colSpan W ((ℓ⁻¹).transpose)))) :
    TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y ∈
      scale c (dualLat O Kf (HL (O := O) ι σ (flW d) (colSpan W ℓ))) := by
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy
  refine mem_scale.2 ⟨TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y0, ?_, by rw [map_smul]⟩
  intro u hu
  refine sandwich thK hm hthK p κ hMD (fun s => la_tw ι σ s.val ℓ) (fun s => la_tw_det _ _ _ _ hℓ) u y0
    ((HL_iff hS ℓ hℓ u).1 hu) ?_
  have hℓt : IsUnit ((ℓ⁻¹).transpose).det := Formalism.L2.G.Model.det_invT ℓ hℓ
  have h1 := (HL_iff hS _ hℓt y0).1 hy0
  have e1 : (fun s : Fin n' => la_tw ι σ s.val ((ℓ⁻¹).transpose)) = fun s => ((la_tw ι σ s.val ℓ)⁻¹).transpose :=
    funext fun s => la_tw_invT s.val ℓ hℓ
  rw [e1] at h1
  exact h1

end

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

theorem topW_lam {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    topW TT lam0 = flW (dT TT lam0) + topW TT (restW TT lam0) := by
  funext s
  by_cases hs : s ∈ TT
  · have := congrFun (lambda_zero_eq_product TT lam0) s
    simp only [topW, if_pos hs, Pi.add_apply] at this ⊢
    exact this
  · funext i
    simp [topW, hs, flW, dT]

theorem ordMax_top {n' m : ℕ} (hm : 2 ≤ m) {TT : Finset (Fin n')} {aT bT : Fin n' → ℤ} {cpp c0 : ℕ} {a : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} (hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0) (r : ℕ) :
    ordMax r (topW TT (restW TT lam0)) ≤ ((r * TT.card * c0 : ℕ) : ℤ) := by
  obtain ⟨hb, hdom, hw⟩ := hW
  have hdr := topW_dom TT (restW_dom (by omega) TT lam0 hdom)
  have hl0 : Fin.last m ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hv1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have key : ∀ s, topW TT (restW TT lam0) s 0 - topW TT (restW TT lam0) s (Fin.last m) ≤
      (if s ∈ TT then (c0 : ℤ) else 0) := by
    intro s
    by_cases hs : s ∈ TT
    · have e1 : restW TT lam0 s (Fin.last m) = lam0 s (Fin.last m) := by
        unfold restW flW
        simp [Pi.single_apply, hl0]
      have e0 : restW TT lam0 s 0 = lam0 s 0 - (dT TT lam0 s : ℤ) := by
        unfold restW flW
        simp
      simp only [topW, if_pos hs]
      rw [e0, e1]
      obtain ⟨_, elast, hc⟩ := (hb s).1 hs
      obtain ⟨_, _, hb0, hbc⟩ := hw s hs
      have h01 : lam0 s 1 ≤ lam0 s 0 := hdom s (Fin.zero_le _)
      have hc1 := abs_le.1 (hc 1 (by omega) (by omega))
      unfold dT flatDeg
      rw [if_pos hs, Int.toNat_of_nonneg (by omega), elast]
      omega
    · simp [topW, hs]
  unfold ordMax
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
  calc ∑ s : Fin n', ∑ a : Fin (m + 1) with a.val < r,
        (lamAt (topW TT (restW TT lam0)) s a - lamAt (topW TT (restW TT lam0)) s (Fin.last m))
      ≤ ∑ s : Fin n', (r : ℤ) * (if s ∈ TT then (c0 : ℤ) else 0) :=
        Finset.sum_le_sum fun s _ => le_trans (ord_pos r _ hdr s) (mul_le_mul_of_nonneg_left (key s) hr0)
    _ = ((r * TT.card * c0 : ℕ) : ℤ) := by
        rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const]
        push_cast
        simp only [nsmul_eq_mul]
        ring

def PairTopStep (C CK : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        PairAt p n' ι σ w r TT (dT TT lam0) (topW TT (restW TT lam0)) (topW TT lam0) c0
          (CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e Θ

def RestPairTop (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → PairTopStep C CK

theorem rhoTopStep_of_pair (D : Formalism.BasicNotions.D7) (C CK : ℝ) (hR : PairTopStep C CK) : RhoTopStep C CK := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    e he htgt hm g hhm hg hbasis Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  exact rhoAtG_of_pair D hSet.1 r TT (dT TT lam0) (topW TT (restW TT lam0)) (topW TT lam0) (topW_lam TT lam0)
    (topW_dom TT (restW_dom (by omega) TT lam0 hdom)) c0 (r * TT.card * c0)
    (ordMax_top (by omega) H.2.2.2.2.1 r) _ e he Θ
    (hR p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
      e he htgt hm g hhm hg hbasis Θ hΘ)

theorem restRhoTop_of_pair (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestPairTop D CLa Ck Crk Cdeg) :
    RestRhoTop D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨CK, C₁, h1, h2, h3⟩ := h hA
  exact ⟨CK, C₁, h1, h2, fun C hC => rhoTopStep_of_pair D C CK (h3 C hC)⟩

theorem restCloudB_of_pair (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestPairTop D CLa Ck Crk Cdeg) :
    RestCloudB D CLa Ck Crk Cdeg :=
  restCloudB_of_top D CLa Ck Crk Cdeg (restRhoTop_of_pair D CLa Ck Crk Cdeg h)

end Formalism.MainNotions.TestSideCounting
end
end
