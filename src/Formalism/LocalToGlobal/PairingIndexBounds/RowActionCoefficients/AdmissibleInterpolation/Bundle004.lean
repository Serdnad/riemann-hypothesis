module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bundle003
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.CoefficientProductHolds
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bundle001
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.InterpolationHolds
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bundle002
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.TransposedFrameImageBlockwiseHolds
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.YVMapRowAct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem hinjX : Function.Injective (algebraMap X.G.O X.G.Kf) := IsFractionRing.injective X.G.O X.G.Kf

theorem phi_mem (hS : XShape) (hBrS : XBrS) (hInj : XInj) (j : ℕ) (L : (X.Pj j).Tup)
    (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (hg : ∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v)))
    (M : AddSubgroup Kc) (hM : ∀ (o : X.G.O), ∀ a ∈ M, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) * a ∈ M)
    (Φ : (X.Pj j).Xsp →ₗ[X.G.Kf] Kc) (A : MvPolynomial (X.FrI j) Kc) (hA : ∀ m, AddMonoidAlgebra.coeff A m ∈ M)
    (hnum : ∀ x : X.FrI j → X.G.Kf, Φ (sX X j (fun v => g v) • ∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((g b.1)⁻¹ : GL _ _))
      (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b)))) = eval (fun t => algebraMap X.G.Kf Kc (x t)) A) :
    ∀ G ∈ (X.Pj j).HtupW L, Φ G ∈ M := by
  have : CharZero X.G.Kf := (algebraMap X.G.Kf Kc).charZero
  let T : Submodule X.G.O (X.Pj j).Xsp :=
    { carrier := {G | Φ G ∈ M}
      add_mem' := fun {a b} ha hb => by
        show Φ (a + b) ∈ M
        rw [map_add (f := _)]; exact M.add_mem ha hb
      zero_mem' := by show Φ 0 ∈ M; rw [map_zero]; exact M.zero_mem
      smul_mem' := fun o G hG => by
        show Φ (o • G) ∈ M
        rw [← algebraMap_smul X.G.Kf o G, map_smul, Algebra.smul_def]
        exact hM o _ hG }
  refine hBrS p X (hinjX X) j L (fun v => g v) (fun v => (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit) hg T ?_
  intro F hF
  let Φ' : (X.Pj j).Xsp →ₗ[X.G.Kf] Kc := Φ ∘ₗ (LinearMap.lsmul X.G.Kf (X.Pj j).Xsp (sX X j fun v => g v))
  exact src_abs (O := X.G.O) (emX X j) (xmX X j) (hInj p X j).2 (nuM X j) (fun b => mF X j b (g b.1))
    (fun b => mF X j b ((g b.1)⁻¹ : GL _ _)) (fun b => mF_inv_mul X j b (g b.1)) M hM (HgX X X.G.Kf j) (hQX X hS j) Φ' A hA hnum
    interpolation_holds coefficient_product_holds F hF

theorem xSpan (hS : XShape) (hBrS : XBrS) (hInj : XInj) (hSp : XSpanN) (j : ℕ) (L : (X.Pj j).Tup)
    (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (hg : ∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v)))
    (f : MvPowerSeries (X.ZA j) Kc) (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).HtupW L) : delF X Kc j G f ∈ WT X Kc j := by
  by_contra hne
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_le_ker_of_notMem hne
  have h0 := phi_mem X Kc hS hBrS hInj j L g hg ⊥ (fun o a ha => by
    rw [AddSubgroup.mem_bot] at ha ⊢; rw [ha, mul_zero]) (PhiX X Kc j l 1 f) 0 (fun m => by simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, AddSubgroup.zero_mem])
    (fun x => by
      obtain ⟨a, x'', hx⟩ := prod_rowAct X j g x
      rw [hx, map_zero, PhiX_apply, one_mul, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
      have h1 : delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x'' b))) f ∈ WT X Kc j := hSp p X Kc j x'' f
      have h2 : l (delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x'' b))) f) = 0 := hl2 h1
      rw [← algebraMap_smul Kc (sX X j fun v => g v), ← algebraMap_smul Kc a, map_smul, map_smul, h2, smul_zero, smul_zero]) G hG
  rw [AddSubgroup.mem_bot, PhiX_apply, one_mul] at h0
  exact hl1 h0

end Formalism.L2.PairingIndexBounds.Ent
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace XAAux

section Rule

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem NJ_pos : 0 < NJ X j := by
  unfold NJ NN
  omega

theorem hvE_congr {A : Type*} [CommRing A] {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h h' : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) (hh' : ∀ k, h' k ≤ n) (e : h = h') : hvE x y c h hh = hvE x y c h' hh' := by
  subst e
  rfl

theorem rename_yV (b : BX X) :
    (yV X.G.Kf (NJ X j)).map ((rename (emX X j b) :
      MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf →ₐ[X.G.Kf] (X.Pj j).Xsp) :
      MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf →+* (X.Pj j).Xsp) = yL X j b.1 b.2 := by
  refine Matrix.ext fun a t => ?_
  simp only [Matrix.map_apply, yV, RingHom.coe_coe, rename_X]
  rfl

theorem rename_hvO (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) :
    rename (emX X j b) (hvO (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) c h) = hvOdd X j b.1 b.2 x c h := by
  rw [← RingHom.coe_coe (rename (emX X j b)), map_hvO, rename_yV]
  unfold hvO hvOdd
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 2
  funext a i
  rw [RingHom.coe_coe, rename_C]

theorem subD_rename_hvE (b : BX X) (ho : ¬ IsOddPos b.2) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ NJ X j) :
    subD X Kc j (rename (emX X j b) (hvE (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) c h hh)) =
      hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x a i)) (dyMat X Kc j b.1 b.2) c h hh := by
  rw [← RingHom.coe_coe (rename (emX X j b)), map_hvE, rename_yV, ← RingHom.coe_coe (subD X Kc j), map_hvE]
  congr 1
  · funext a i
    rw [RingHom.coe_coe, RingHom.coe_coe, rename_C]
    exact (subD X Kc j).commutes (x a i)
  · have := subD_yL X Kc j b.1 b.2
    unfold ySub at this
    rw [if_neg ho] at this
    exact this

theorem hvE_dy (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ NJ X j)
    (hh' : ∀ k, h k ≤ NJ X (j + 1)) :
    hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x a i)) (dyMat X Kc j b.1 b.2) c h hh =
      hvE (xd X Kc j b.1 b.2 x) (yMat X Kc j b.1 b.2) c h hh' := by
  unfold hvE
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  refine Matrix.ext fun i t => ?_
  rw [Matrix.of_apply, Matrix.of_apply]
  exact pair_dy X Kc j b.1 b.2 x i.val (Fin.castLE (hh k) t)

end Rule

end XAAux

theorem xA_of (hS : XShape) : XA := by
  intro p _ X Kc _ _ j x
  have key := polDel_hv X Kc j (fun v s => x ⟨v, s⟩) (fun v s => cX X j ⟨v, s⟩)
    (fun v s k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val)
    (fun v s => rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩)))
    (fun v s _ k => colH_le _ _) (fun v s _ => cMu_toNat X v j s)
    (fun v s _ => by
      rw [← sum_colHt X v j s]
      congr 1
      exact Finset.sum_congr rfl fun k _ => (hS p X j ⟨v, s⟩).2.2.2.2.1 k.val)
  rw [Fintype.prod_sigma, Fintype.prod_sigma]
  have h1 : (∏ v, ∏ s, rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩))) =
      ∏ v, ∏ s, if IsOddPos s then hvOdd X j v s (x ⟨v, s⟩) (cX X j ⟨v, s⟩) (fun k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val)
        else rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩)) := by
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    split_ifs with ho
    · unfold srcN
      rw [if_pos ho]
      exact XAAux.rename_hvO X j ⟨v, s⟩ _ _ _
    · rfl
  rw [h1, key]
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
  obtain ⟨-, -, hanti, hle, hc1, hc2, he1, he2, -, -⟩ := hS p X j ⟨v, s⟩
  unfold tgtD
  split_ifs with ho
  · unfold hvOdd' hvO
    refine Finset.prod_congr rfl fun k _ => ?_
    beta_reduce
    rw [hc1, hc2]
  · have hf := highest_vector_full_holds (DA X Kc j) (NJ X j) (muX X j (NJ X j) ⟨v, s⟩) (hanti _) (cX X j ⟨v, s⟩) (eX X j ⟨v, s⟩)
      (hle _) he1 he2 (XAAux.NJ_pos X j) (fun a i => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i)) (dyMat X Kc j v s)
    have hnu : nuS X j ⟨v, s⟩ = fun t => muX X j (NJ X j) ⟨v, s⟩ t - eX X j ⟨v, s⟩ := if_neg ho
    have hdet : (Matrix.of fun a i : Fin (NJ X j) => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i.val)).det =
        algebraMap X.G.Kf (DA X Kc j) (Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det := by
      rw [RingHom.map_det]
      rfl
    have h2 : hvE (xd X Kc j v s (x ⟨v, s⟩)) (yMat X Kc j v s) (cX X j ⟨v, s⟩)
        (fun k => colH (muX X j (NJ X (j + 1)) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val) =
        hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i)) (dyMat X Kc j v s) (cX X j ⟨v, s⟩)
          (fun k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val) := by
      rw [XAAux.hvE_dy X Kc j ⟨v, s⟩ _ _ _ _ (fun k => (colH_le _ k.val).trans (NN_le X j))]
      exact XAAux.hvE_congr _ _ _ _ _ _ _ (funext fun k => by rw [hc1, hc2])
    show _ = hvE (xd X Kc j v s (x ⟨v, s⟩)) (yMat X Kc j v s) (cX X j ⟨v, s⟩)
        (fun k => colH (muX X j (NJ X (j + 1)) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val)
    rw [h2, hf, hdet]
    unfold srcN
    rw [if_neg ho, map_mul, map_mul, rename_C, XAAux.subD_rename_hvE X Kc j ⟨v, s⟩ ho,
      show subD X Kc j (C ((Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det ^ eX X j ⟨v, s⟩)) =
        algebraMap X.G.Kf (DA X Kc j) ((Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det ^ eX X j ⟨v, s⟩) from
        (subD X Kc j).commutes _, map_pow, mul_pow,
      XAAux.hvE_congr _ _ _ (fun k => colH (nuS X j ⟨v, s⟩) k.val)
        (fun k => colH (fun t => muX X j (NJ X j) ⟨v, s⟩ t - eX X j ⟨v, s⟩) k.val) _ (fun k => colH_le _ k.val) (by rw [hnu])]
    show _ * _ * (dyMat X Kc j v s).det ^ eX X j ⟨v, s⟩ = _
    ring

namespace XAAux

section Span

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem pairD_mem [Infinite Kc] (W : Submodule Kc (XspC (X.Pj (j + 1)) Kc)) (P : DA X Kc j)
    (h : ∀ d0 : X.ZA j → Kc, evD X Kc j d0 P ∈ W) (f : MvPowerSeries (X.ZA j) Kc) : pairD X Kc j P f ∈ W := by
  by_contra hn
  obtain ⟨l, hl, hW⟩ := Submodule.exists_le_ker_of_notMem hn
  refine hl ?_
  rw [pairing_series_linear_form_holds p X Kc j P f l 0 fun d0 => by rw [map_zero, LinearMap.mem_ker.1 (hW (h d0))]]
  simp

theorem map_bidet {K K' : Type} [CommRing K] [CommRing K'] (φ : K →+* K') {r n c : ℕ} (sz : Fin c → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : map φ (bideterminant K sz hsz I) = bideterminant K' sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem tgtN_mem [CharZero Kc] (hS : XShape) (b : BX X) (z : Fin (NJ X (j + 1)) → ℕ → Kc) :
    tgtN X Kc j b z ∈ dualWeyl Kc (NJ X (j + 1)) (NJ X (j + 1)) (nuT X j b) := by
  obtain ⟨-, -, hanti, hle, -⟩ := hS p X j b
  unfold tgtN nuT
  split_ifs with ho
  · exact highest_vector_mem_odd Kc _ _ (hanti _) _ (hle _) z
  · exact highest_vector_mem_even Kc _ _ (hanti _) _ (hle _) z

end Span

end XAAux

theorem xSpanN_of (hS : XShape) : XSpanN := by
  intro p _ X Kc _ _ _ j x f
  classical
  rw [delF_apply, xA_of hS p X Kc j x]
  refine XAAux.pairD_mem X Kc j _ _ (fun d0 => ?_) f
  rw [map_prod]
  simp only [frame_change_compatibility_holds p X Kc j]
  refine prod_span (R := Kc) (fun b : BX X => {y : XspC (X.Pj (j + 1)) Kc |
      ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ NJ X (j + 1)) (I : ∀ k, Fin (sz k) → Fin (NJ X (j + 1))),
        shapeDeg sz = nuT X j b ∧ y = rename (emX X (j + 1) b) (bideterminant Kc sz hsz I)}) _ (fun g hg => ?_) _ (fun b => ?_)
  · choose K sz hsz I hsh hgb using hg
    refine Submodule.subset_span ⟨fun b => bideterminant X.G.Kf (sz b) (hsz b) (I b), fun b => ?_, ?_⟩
    · rw [← hsh b]
      exact bidetMem X.G.Kf _ _ _ _ _ _
    · rw [map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hgb b, map_rename, XAAux.map_bidet]
  · have h1 := XAAux.tgtN_mem X Kc j hS b
      (mulC (dM X Kc j b d0).transpose fun a i => algebraMap X.G.Kf Kc (x b a i))
    rw [standardMonomialSpanDomain Kc] at h1
    have h2 := Submodule.mem_map_of_mem (f := (rename (emX X (j + 1) b) :
      MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) Kc →ₐ[Kc] XspC (X.Pj (j + 1)) Kc).toLinearMap) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨q, ⟨K, sz, hsz, I, hsh, rfl⟩, rfl⟩
    exact ⟨K, sz, hsz, I, hsh, rfl⟩

end Formalism.L2.PairingIndexBounds.Ent
end
end
