module

public import Formalism.LocalToGlobal.Columns.Bundle007
public import Formalism.LocalToGlobal.Columns.Bundle017
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
public import Formalism.LocalToGlobal.Columns.Bundle018
public import Formalism.LocalToGlobal.HermitianForms.Bundle007
public import Formalism.LocalToGlobal.Columns.XtSumSingle
public import Formalism.LocalToGlobal.Columns.RecLevelSym
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

@[expose] public section

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem hq_toGLb_mulVec {n : ℕ} (b : Basis (Fin n) E V) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Herm.toGLb b γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ b.equivFun x = b.equivFun (γ x) :=
  LinearMap.toMatrix_mulVec_repr b b (γ : V →ₗ[E] V) x

def hqCrd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) : V ≃ₗ[E] (Fin N → E) :=
  b.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem hq_reGL_mulVec {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b γ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x = hqCrd b h (γ x) := by
  subst h
  rw [Formalism.L2.Forms.reGL_rfl]
  exact hq_toGLb_mulVec b γ x

def hqLin {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) : V ≃ₗ[E] V :=
  (Formalism.L2.Herm.toGLb b).symm ((Formalism.L2.Forms.reGL h E).symm g)

theorem hqLin_re {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) :
    Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b (hqLin b h g)) = g := by
  unfold hqLin
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem hqLin_crd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) (x : V) :
    hqCrd b h (hqLin b h g x) = (g : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x := by
  have := hq_reGL_mulVec b h (hqLin b h g) x
  rw [hqLin_re] at this
  exact this.symm

end Mat

section Form

variable {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]

theorem hq_hform_dot (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]

theorem hq_hform_UJ (σ : A →+* A) (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) (x y : n → A) :
    hform σ J ((g : Matrix n n A) *ᵥ x) ((g : Matrix n n A) *ᵥ y) = hform σ J x y := by
  have hτ : σ ∘ ((g : Matrix n n A) *ᵥ x) = (g : Matrix n n A).map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ (g : Matrix n n A) x i
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  rw [hq_hform_dot, hq_hform_dot, hτ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  show _ ⬝ᵥ ((cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *ᵥ y) = _
  rw [hg']

end Form

variable {D : ColRec}

theorem hq_crdN (i : ℕ) (hi : i ≤ D.R.m) : CF.crdN D i hi = hqCrd (D.sp.X i).frame (CF.rankN D i hi) := rfl

def hqG (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) : CH.GX D i :=
  ⟨hqLin (D.sp.X i).frame (CF.rankN D i hi) g.1, fun x y => by
    rw [hx_hform i hi, hx_hform i hi, hq_crdN, hqLin_crd, hqLin_crd]
    exact hq_hform_UJ _ _ g.1 g.2 _ _⟩

variable {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} {K : CF.ClsPTied u}

variable (T : CF.TilTied u A K (P D.R.m le_rfl))




end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section LR

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem xt_N_top {m2 : ℕ} (hm : R.m = m2 + 2) : R.N (m2 + 1 + 1) - 1 = R.r + R.m * R.t := by
  unfold Ranks.N Ranks.r
  rw [hm]
  have e : (m2 + 1 + 1) * (R.t + 1) = (m2 + 2) * R.t + (m2 + 2) := by ring
  omega

theorem lastRow_colLevSym (Ch : Chars X Pr R.m) {m2 : ℕ} (hm : R.m = m2 + 2) : LastRow (colLevSym Ch (m2 + 1 + 1)) := by
  intro w h' hh' l
  rw [colLevSym_top_H Ch (by omega) w] at hh'
  have hN := xt_N_top (R := R) hm
  have hbt := HPar_le _ _ _ hh'.1
  by_cases hl : l.1 = R.N (m2 + 1 + 1) - 1
  · rw [if_pos hl, hh'.2 _ l (by rw [hl, hN])]
    have : (⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ : Fin (R.N (m2 + 1 + 1))) = l := Fin.ext hl.symm
    rw [this, Matrix.one_apply_eq]
  · rw [if_neg hl]
    refine mem_btG.1 hbt _ l ?_
    have hl2 : l.1 < R.r + R.m * R.t := by have := l.2; omega
    show coarse R.r (List.replicate R.m R.t) l.1 < coarse R.r (List.replicate R.m R.t) (R.N (m2 + 1 + 1) - 1)
    rw [hN]
    have e1 : coarse R.r (List.replicate R.m R.t) (R.r + R.m * R.t) = R.m + 1 := by
      unfold coarse blkIdx
      rw [if_neg (by omega), Nat.add_sub_cancel_left, blkIdx_replicate_of_le _ _ _ le_rfl]
    rw [e1]
    unfold coarse blkIdx
    split_ifs with h0
    · omega
    · have := blkIdx_replicate_lt R.t R.m (l.1 - R.r) (by omega)
      omega

end LR

end Formalism.L2.Col
end
end
