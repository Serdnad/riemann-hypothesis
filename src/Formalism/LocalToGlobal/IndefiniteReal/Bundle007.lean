module

public import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle005
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CSDForm

variable (S : CSD K)

def csumForm : S.Forms →ₗ⋆[K] S.Forms →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun f g => S.csum (f : S.Cl → S.V) (g : S.Cl → S.V))
    (fun f f' g => by
      simp only [CSD.csum, Submodule.coe_add, Pi.add_apply, map_add (f := _), LinearMap.add_apply, mul_add,
        Finset.sum_add_distrib])
    (fun a f g => by
      simp only [CSD.csum, Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => by ring)
    (fun f g g' => by
      simp only [CSD.csum, Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib])
    (fun a f g => by
      simp only [CSD.csum, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      refine Finset.sum_congr rfl fun c _ => by ring)

theorem csumForm_apply (f g : S.Forms) : csumForm S f g = S.csum (f : S.Cl → S.V) (g : S.Cl → S.V) := rfl

end CSDForm

namespace BlockGood

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)

def goodR (ℓ : Lvl K G) : Submodule K B.S.Forms :=
  LinearMap.range ((B.S.basis.equivFun.symm : (Fin B.S.dim → K) →ₗ[K] B.S.Forms) ∘ₗ (B.vE ℓ).mulVecLin)

theorem toF_mem_goodR (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ goodR B ℓ := by
  unfold goodR
  exact LinearMap.mem_range.2 ⟨(B.zE ℓ Z).mulVecLin y, rfl⟩

theorem toF_mem (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z := by
  have hs := (subspace_image_spec K _ (B.Z0 ℓ Z)).2
  have hy : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
    rw [← hs]
    exact ⟨y, rfl⟩
  obtain ⟨f, hf, he⟩ := hy
  have : B.toF ℓ Z y = f := by
    have he' : B.S.basis.equivFun f = (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y) := he
    change B.S.basis.equivFun.symm ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y)) = f
    rw [← he', LinearEquiv.symm_apply_apply]
  rw [this]
  exact hf

theorem csum_toF (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (x y : Fin (B.dZ ℓ Z) → K) :
    B.S.csum (B.toF ℓ Z x : B.S.Cl → B.S.V) (B.toF ℓ Z y : B.S.Cl → B.S.V) =
      (Nat.card ℓ.P : K) * (star x ⬝ᵥ (B.HZ ℓ Z).mulVec y) := by
  change B.S.csum (B.S.I ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec x))) (B.S.I ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y))) = _
  rw [B.S.csum_sum]
  have h1 : ∀ u w : Fin B.S.dim → K, (∑ i, ∑ j, star (u i) * B.S.H i j * w j) = star u ⬝ᵥ B.S.H.mulVec w := by
    intro u w
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hP : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h2 : (B.vE ℓ * B.zE ℓ Z)ᴴ * (B.S.H * B.vE ℓ) * B.zE ℓ Z = (Nat.card ℓ.P : K) • B.HZ ℓ Z := by
    simp only [BlockDat.HZ, BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, Matrix.conjTranspose_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hP, one_smul, Matrix.mul_assoc]
  rw [h2]
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem csum_toF_at {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (ℓ : Lvl K G)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (x y : Fin (B.dZ ℓ Z) → K) :
    v0.embedding (CSDForm.csumForm B.S (B.toF ℓ Z x) (B.toF ℓ Z y)) =
      ((Nat.card ℓ.P : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v0 x y := by
  rw [CSDForm.csumForm_apply, csum_toF, map_mul, map_natCast, Formalism.L2.DIV.majAt_eq]
  have hm : metOf (B.XQ ℓ Z v0) = (B.HZ ℓ Z).map v0.embedding := (BlockDat.XQ_herm hv0 h hX (Z := Z)).2
  rw [hm]
  push_cast
  congr 1

  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv0]
  rfl

end BlockGood

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem opC_adjoint (hK : X.KFormR) (cv : CrdV A) (hJ : X.JIsoR cv) (t : Bs.Tup) (i i' : A.OpR t)
    (h : ∀ f g, cv.hR t (A.opR t i f) g = cv.hR t f (A.opR t i' g)) :
    X.opC t i' = LinearMap.adjoint (X.opC t i) := by
  have h1 : X.opC t i = LinearMap.adjoint (X.opC t i') := by
    rw [LinearMap.eq_adjoint_iff_basis (Basis.mk (hK t).1 (hK t).2.ge) (Basis.mk (hK t).1 (hK t).2.ge)]
    intro k l
    simp only [Basis.mk_apply]
    rw [← jR_opR X hK, ← jR_opR X hK, hJ, hJ, h]
  rw [h1, LinearMap.adjoint_adjoint]

theorem opLC_adjoint (hK : X.KFormL) (cv : CrdV A) (hJ : X.JIsoL cv) (j : Bs.J) (t : Bs.Tup) (i i' : A.OpL j t)
    (h : ∀ f g, cv.hL j t (A.opL j t i f) g = cv.hL j t f (A.opL j t i' g)) :
    X.opLC j t i' = LinearMap.adjoint (X.opLC j t i) := by
  have h1 : X.opLC j t i = LinearMap.adjoint (X.opLC j t i') := by
    rw [LinearMap.eq_adjoint_iff_basis (Basis.mk (hK j t).1 (hK j t).2.ge) (Basis.mk (hK j t).1 (hK j t).2.ge)]
    intro k l
    simp only [Basis.mk_apply]
    rw [← jL_opL X hK, ← jL_opL X hK, hJ, hJ, h]
  rw [h1, LinearMap.adjoint_adjoint]

end CxData

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def cvOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) : CrdV A.fam.amb where
  v0R _ b t := match b with
    | false => BlockGood.goodR (A.fam.R t) (A.fam.lvl P0 ψ0)
    | true => BlockGood.goodR (A.fam.R t) (A.fam.lvl P1 ψ1)
  v0L _ b j t := match b with
    | false => BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P0 ψ0)
    | true => BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P1 ψ1)
  hR t := CSDForm.csumForm (A.fam.R t).S
  hL j t := CSDForm.csumForm (A.fam.L j t).S

variable {A : FamIn K G Pl0 T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

theorem csum_act_inv {B : BlockDat K G Pl0} (h : B.S.ActGood B.r) (g : G) (f f' : B.S.Forms) :
    B.S.csum (B.r g f : B.S.Cl → B.S.V) (f' : B.S.Cl → B.S.V) =
      B.S.csum (f : B.S.Cl → B.S.V) (B.r g⁻¹ f' : B.S.Cl → B.S.V) := by
  have h1 := h.unitary g f (B.r g⁻¹ f')
  have h2 : B.r g (B.r g⁻¹ f') = f' := by
    show (B.r g * B.r g⁻¹) f' = f'
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [h2] at h1
  exact h1

end Concrete

end Formalism.IndefR.Cx
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem fnorm_gram_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ} (w : Fin n → E)
    (hli : LinearIndependent ℂ w) (c : ℝ) (hc : 0 < c) (y : Fin n → ℂ) :
    fnorm (frameOf ((c : ℂ) • Matrix.gram ℂ w)) y = Real.sqrt c * ‖lin w y‖ := by
  have hpd : ((c : ℂ) • Matrix.gram ℂ w).PosDef :=
    (Matrix.posDef_gram_of_linearIndependent hli).smul (Complex.zero_lt_real.mpr hc)
  have hm := (frameOfSpec n _ hpd).2
  set Y := frameOf ((c : ℂ) • Matrix.gram ℂ w) with hY
  have h0 : star y ⬝ᵥ (metOf Y).mulVec y = star (Y⁻¹.mulVec y) ⬝ᵥ Y⁻¹.mulVec y := by
    rw [metOf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  have hg : star y ⬝ᵥ (metOf Y).mulVec y = (c : ℂ) * ⟪lin w y, lin w y⟫_ℂ := by
    rw [hm, Matrix.smul_mulVec, dotProduct_smul, Matrix.star_dotProduct_gram_mulVec, smul_eq_mul]
    rfl
  have h2 : ((∑ i, ‖Y⁻¹.mulVec y i‖ ^ 2 : ℝ) : ℂ) = star (Y⁻¹.mulVec y) ⬝ᵥ Y⁻¹.mulVec y := by
    push_cast
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have h3 : ⟪lin w y, lin w y⟫_ℂ = ((‖lin w y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have h1 : (∑ i, ‖Y⁻¹.mulVec y i‖ ^ 2 : ℝ) = c * ‖lin w y‖ ^ 2 := by
    have h4 : ((∑ i, ‖Y⁻¹.mulVec y i‖ ^ 2 : ℝ) : ℂ) = ((c * ‖lin w y‖ ^ 2 : ℝ) : ℂ) := by
      rw [h2, ← h0, hg, h3]
      push_cast
      ring
    exact_mod_cast h4
  unfold fnorm Formalism.HermitianLatticesTheory.cnorm
  rw [h1, Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _)]

theorem cpt_single (σ : K →+* ℂ) {n : ℕ} (i : Fin n) : cpt σ (Pi.single i (1 : K)) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h
    simp [cpt]
  · simp [cpt, h]

theorem bil_expand {a D : ℕ} (Φ : (Fin a → ℂ) →ₗ[ℂ] (Fin D → ℂ) →ₗ[ℂ] ℂ) (x : Fin a → ℂ) (y : Fin D → ℂ) :
    Φ x y = ∑ i, ∑ k, x i * y k * Φ (Pi.single i (1 : ℂ)) (Pi.single k (1 : ℂ)) := by
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℂ) : Fin a → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hy : y = ∑ k, y k • (Pi.single k (1 : ℂ) : Fin D → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx, hy]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _

theorem mulVec_rinv {d n : ℕ} (P : Matrix (Fin d) (Fin n) K) (h : Function.Surjective P.mulVec) (y : Fin d → K) :
    P.mulVec ((CxData.rinv P).mulVec y) = y := by
  rw [Matrix.mulVec_mulVec, CxData.rinv_spec P h, Matrix.one_mulVec]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

structure MIDat (fc : DefSub A → DefFace Bs) where

  V : X.EE →ₗ[ℂ] X.EE

  a : (fc X.zs).Dc.Mem → ℂ

  U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ

  ζC : (fc X.zs).Dc.Mem → Bs.Tup → ℂ

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A)

def AuNZ (d : X.MIDat fc) : Prop := ∀ u, d.a u ≠ 0

def MIid (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (d : X.MIDat fc) : Prop :=
  ∀ u t (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K),
    d.ζC u t * Bs.v0.embedding ((fc X.zs).Dc.Pt u t φ F) =
      d.a u * ⟪sEE (d.V (X.Θ t (X.jR t (eV t F)))), (fc X.zs).Sp.Pu u ((d.U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ

def EVTie (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) : Prop :=
  (∀ t F, eV t F ∈ cv.v0R X.zs true t) ∧
    ∀ t F (x : Fin ((lv (fc X.zs) true).dQ t) → K),
      cv.hR t (cr.toR X.zs true t x) (eV t F) =
        cv.hR t (cr.toR X.zs true t x) (cr.toR X.zs true t (((fc X.zs).Df1.Pq t).mulVec F))

def SEEIso (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) : Prop :=
  (∀ e ∈ X.EEl true, X.nP true * ‖sEE e‖ ^ 2 = ‖e‖ ^ 2) ∧ (∀ e ∈ X.EEl true, sEE e ∈ (fc X.zs).Sp.Rw) ∧
    Module.finrank ℂ (fc X.zs).Sp.Rw = Module.finrank ℂ (X.EEl true)

def zetaOf (d : X.MIDat fc) (u : (fc X.zs).Dc.Mem) (t : Bs.Tup) : K :=
  open Classical in if h : ∃ k : K, Bs.v0.embedding k = d.ζC u t then h.choose else 1

theorem iC_cpt' (b : Bool) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • (Pi.single k (1 : K) : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [iC, map_sum, map_smul, map_smulₛₗ, lin, Fintype.linearCombination_apply, cpt]

theorem theta_eV (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (t : Bs.Tup) (F : Fin ((fc X.zs).Df1.nV t) → K) :
    X.Θ t (X.jR t (eV t F)) = X.Θ t (X.jR t (cr.toR X.zs true t (((fc X.zs).Df1.Pq t).mulVec F))) := by
  set q : A.FR t := cr.toR X.zs true t (((fc X.zs).Df1.Pq t).mulVec F) with hq
  have hdV : eV t F - q ∈ cv.v0R X.zs true t := sub_mem (hE.1 t F) (hC t _)
  have hdo : ∀ x, cv.hR t (cr.toR X.zs true t x) (eV t F - q) = 0 := by
    intro x; rw [map_sub, hE.2 t F x, sub_self]
  have hjV : X.jR t (eV t F - q) ∈ X.V0C cv true t := Submodule.subset_span ⟨_, hdV, rfl⟩
  have hΘE : X.Θ t (X.jR t (eV t F - q)) ∈ X.EEl true := hDn t ⟨_, hjV, rfl⟩
  have horth : ∀ e ∈ X.EEl true, ⟪e, X.Θ t (X.jR t (eV t F - q))⟫_ℂ = 0 := by
    intro e he
    rw [← LinearMap.adjoint_inner_left]
    have h1 : LinearMap.adjoint (X.Θ t) e ∈
        Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) true).dQ t) → K => X.jR t (cr.toR X.zs true t x)) := by
      rw [hRL t]
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_range_self _ e, hUp t (Submodule.mem_map_of_mem he)⟩
    have h2 : Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) true).dQ t) → K => X.jR t (cr.toR X.zs true t x)) ≤
        (Submodule.span ℂ {X.jR t (eV t F - q)})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hJ, hdo x, map_zero]
    have h3 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 h1)
    rwa [inner_eq_zero_symm] at h3
  have h0 : X.Θ t (X.jR t (eV t F - q)) = 0 := inner_self_eq_zero.1 (horth _ hΘE)
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

section Ident

variable {eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH} {d : X.MIDat fc}

theorem zetaOf_spec (u : (fc X.zs).Dc.Mem) (t : Bs.Tup) (h : ∃ k : K, Bs.v0.embedding k = d.ζC u t) :
    Bs.v0.embedding (X.zetaOf d u t) = d.ζC u t := by
  simp only [zetaOf, dif_pos h]
  exact h.choose_spec

theorem zetaOf_not (u : (fc X.zs).Dc.Mem) (t : Bs.Tup) (h : ¬ ∃ k : K, Bs.v0.embedding k = d.ζC u t) :
    X.zetaOf d u t = 1 := by
  simp only [zetaOf, dif_neg h]

end Ident

end CxData

end Formalism.IndefR.Cx
end
end
