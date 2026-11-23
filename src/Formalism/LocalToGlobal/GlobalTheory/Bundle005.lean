module

public import Formalism.LocalToGlobal.GlobalTheory.Bundle004
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkGLOBAL7Tied4
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
public import Formalism.LocalToGlobal.GlobalTheory.ColValS
public import Formalism.LocalToGlobal.HermitianForms.Bundle004
public import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PColInf
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

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem class_lattice_eq_global {D : D7} (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    (K0 D).lat (D.clsLat u 0 c) = globLat ((Lv u).y c).1 (Lv u).Lb :=
  eq_glob_of_hat ((K0 D).isLat_lat (D.clsLat_lat u 0 c)) _ (fun v => by exact (Lv u).y_lat c v)

theorem Lb_le_dl_lv {D : D7} (Lv : LevelData D) (u : D.what₂.Word) :
    (Lv u).Lb ≤ dl D.sp.cm.sig (K0 D).J (Lv u).Lb := by
  intro x hx
  exact Submodule.subset_span ((Lv u).Lb_int x hx)

theorem class_lattice_integral {D : D7} (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    D.clsLat u 0 c ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (D.clsLat u 0 c) := by
  have h1 : (K0 D).lat (D.clsLat u 0 c) ≤ (K0 D).lat (Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (D.clsLat u 0 c)) := by
    rw [(K0 D).lat_dual, class_lattice_eq_global Lv u c]
    exact le_trans (glob_mono _ (Lb_le_dl_lv Lv u)) (glob_dl_le _ _ _ _ (by exact ((Lv u).y c).2))
  intro x hx
  have h2 := h1 ⟨x, hx, rfl⟩
  rw [(K0 D).mem_lat] at h2
  simpa using h2

theorem latT_of_sym {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    flipTwoThree.LatT (D.sp.X 0) (flipTwoThree.Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [dualSub_eq]
    exact class_lattice_integral F.herm.base.lev0 u c hx
  · obtain ⟨e⟩ := (F.herm.atT u).disc 0 (Nat.zero_le _) c
    rw [dualSub_eq, AddSubgroup.relIndex, ← card_ringOfIntegers_quot_natCast_eq_pow D (flipTwoThree.Tu D u)]
    have := Nat.card_congr e.toEquiv
    have hT : flipTwoThree.Tu D u = (D.mem u).A.T := rfl
    rw [hT, ← this]
    rfl

theorem classes_level_zero_nonempty {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word) :
    Nonempty ((D.mem u).C.cls 0) := by
  obtain ⟨c, -⟩ := (F.herm.base.lev0 u).y_bij.2 (Quotient.mk'' 1)
  exact ⟨c⟩

def ColRest {D : D7} {u : D.what₂.Word} (B : Formalism.MainNotions.GlobalTheoryTheory.Inhab.ColBase D u) : Prop :=
  ∃ co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL),
    Function.Injective co ∧
    (∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0)) ∧
    (∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
      (∀ c τ, flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ flipTwoThree.IntSpanAt D w ((D.fm u).lam 0)) ∧
    ∀ (v : NumberField.InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (flipTwoThree.nfAll ((D.fm u).lam 0)
          (flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))
          (flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))).re

theorem colValOfTiedS_of_rest
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → flipTwoThree.adm3 D →
      ∀ u : D.what₂.Word, ∃ B : Formalism.MainNotions.GlobalTheoryTheory.Inhab.ColBase D u, ColRest B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  column_value_of_tie_local_bases fun D F h3 u => by
    obtain ⟨B, co, h1, h2, h3', h4⟩ := h D F h3 u
    exact ⟨B, classes_level_zero_nonempty F u, latT_of_sym F u, co, h1, h2, h3', h4⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section

noncomputable section

open Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions

section Map

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {n : ℕ}

theorem map_aeval_sub (s : K →+* L) (f : (ι × Fin n × Fin n) → MvPolynomial (ι × Fin n × Fin n) K)
    (p : MvPolynomial (ι × Fin n × Fin n) K) :
    MvPolynomial.map s (MvPolynomial.aeval f p) = MvPolynomial.aeval (fun v => MvPolynomial.map s (f v)) (MvPolynomial.map s p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X]

theorem map_actAll (s : K →+* L) (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) K)
    (p : MvPolynomial (ι × Fin n × Fin n) K) :
    MvPolynomial.map s (Formalism.MainNotions.flipTwoThree.actAll lam g p) =
      Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (g τ).map s) (MvPolynomial.map s p) := by
  unfold Formalism.MainNotions.flipTwoThree.actAll
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_aeval_sub]
  congr 1
  · simp only [map_prod, map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]
  · congr 1
    congr 1
    funext v

    simp [map_sum, Matrix.map_apply]

end Map

section Fock

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem actAll_eq_subP (lam : ι → DomWeight n) (Z : ι → Matrix (Fin n) (Fin n) ℂ)
    (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.MainNotions.flipTwoThree.actAll lam Z p = (∏ τ, (Z τ).det ^ (lam τ).detShift) • Formalism.L2.Forms.subP (fun τ => (Z τ)ᵀ) p := rfl

theorem nfAll_eq (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.MainNotions.flipTwoThree.nfAll lam p q = Formalism.L2.Forms.nfAll lam p q := rfl

theorem nfAll_smul_self_re (lam : ι → DomWeight n) (a : ℂ) (q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    (Formalism.MainNotions.flipTwoThree.nfAll lam (a • q) (a • q)).re = ‖a‖ ^ 2 * (Formalism.MainNotions.flipTwoThree.nfAll lam q q).re := by
  rw [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.nfAll_smul_left, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.nfAll_smul_right, ← mul_assoc, Complex.mul_conj,
    Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

end Fock

section Polar

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

def defect (φ : E →+* ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : ℂ :=
  star (Y *ᵥ fun i => φ (x i)) ⬝ᵥ (Y *ᵥ fun i => φ (y i)) - φ (star x ⬝ᵥ (G *ᵥ y))

variable (φ : E →+* ℂ) (hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) (Y : Matrix (Fin n) (Fin n) ℂ) (G : Matrix (Fin n) (Fin n) E)

theorem defect_add_left (x x' y : Fin n → E) : defect φ Y G (x + x') y = defect φ Y G x y + defect φ Y G x' y := by
  unfold defect
  have e : (fun i => φ ((x + x') i)) = (fun i => φ (x i)) + fun i => φ (x' i) := by funext i; simp
  rw [e, Matrix.mulVec_add, star_add, add_dotProduct, star_add, add_dotProduct, map_add (f := _)]
  ring

theorem defect_add_right (x y y' : Fin n → E) : defect φ Y G x (y + y') = defect φ Y G x y + defect φ Y G x y' := by
  unfold defect
  have e : (fun i => φ ((y + y') i)) = (fun i => φ (y i)) + fun i => φ (y' i) := by funext i; simp
  rw [e, Matrix.mulVec_add, dotProduct_add, Matrix.mulVec_add, dotProduct_add, map_add (f := _)]
  ring

include hφ in
theorem defect_smul_left (t : E) (x y : Fin n → E) :
    defect φ Y G (t • x) y = starRingEnd ℂ (φ t) * defect φ Y G x y := by
  unfold defect
  have e : (fun i => φ ((t • x) i)) = φ t • fun i => φ (x i) := by funext i; simp
  rw [e, Matrix.mulVec_smul, star_smul, smul_dotProduct, star_smul, smul_dotProduct]
  simp only [smul_eq_mul, map_mul, hφ, Complex.star_def]
  ring

theorem defect_smul_right (t : E) (x y : Fin n → E) :
    defect φ Y G x (t • y) = φ t * defect φ Y G x y := by
  unfold defect
  have e : (fun i => φ ((t • y) i)) = φ t • fun i => φ (y i) := by funext i; simp
  rw [e, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_smul, dotProduct_smul]
  simp only [smul_eq_mul, map_mul]
  ring


include hφ in
theorem defect_eq_zero (t : E) (ht : (φ t).im ≠ 0) (h0 : ∀ x, defect φ Y G x x = 0) (x y : Fin n → E) :
    defect φ Y G x y = 0 := by
  have h1 : ∀ x y, defect φ Y G x y + defect φ Y G y x = 0 := fun x y => by
    have := h0 (x + y)
    rw [defect_add_left, defect_add_right, defect_add_right, h0 x, h0 y] at this
    linear_combination this
  have h2 := h1 x (t • y)
  rw [defect_smul_right, defect_smul_left φ hφ] at h2
  have h3 := h1 x y
  have h4 : (φ t - starRingEnd ℂ (φ t)) * defect φ Y G x y = 0 := by linear_combination h2 - starRingEnd ℂ (φ t) * h3
  have h5 : φ t - starRingEnd ℂ (φ t) ≠ 0 := by
    intro h
    apply ht
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im] at this
    linarith
  exact (mul_eq_zero.1 h4).resolve_left h5


include hφ in
theorem gram_of_norm (hG : Gᴴ = G) (t : E) (ht : (φ t).im ≠ 0)
    (h : ∀ x : Fin n → E, (star (Y *ᵥ fun i => φ (x i)) ⬝ᵥ (Y *ᵥ fun i => φ (x i))).re = (φ (star x ⬝ᵥ (G *ᵥ x))).re) :
    Yᴴ * Y = G.map φ := by
  have h0 : ∀ x, defect φ Y G x x = 0 := fun x => by
    unfold defect
    apply Complex.ext
    · rw [Complex.sub_re, h x, sub_self, Complex.zero_re]
    · rw [Complex.sub_im, Complex.zero_im]
      have i1 : (star (Y *ᵥ fun i => φ (x i)) ⬝ᵥ (Y *ᵥ fun i => φ (x i))).im = 0 := by
        simp only [dotProduct, Pi.star_apply, Complex.im_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [RCLike.star_def, Complex.conj_mul']
        norm_cast
      have i2 : (φ (star x ⬝ᵥ (G *ᵥ x))).im = 0 := by
        have e : star (star x ⬝ᵥ (G *ᵥ x)) = star x ⬝ᵥ (G *ᵥ x) := by
          simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          have hij : star (G j i) = G i j := by
            have := congrFun (congrFun hG i) j
            rwa [Matrix.conjTranspose_apply] at this
          rw [hij]
          ring
        have := hφ (star x ⬝ᵥ (G *ᵥ x))
        rw [e] at this
        have := congrArg Complex.im this
        rw [Complex.conj_im] at this
        linarith
      rw [i1, i2, sub_zero]
  apply Matrix.ext
  intro i j
  have := defect_eq_zero φ hφ Y G t ht h0 (Pi.single i 1) (Pi.single j 1)
  unfold defect at this
  have e : ∀ k : Fin n, (fun a => φ ((Pi.single k (1 : E) : Fin n → E) a)) = Pi.single k 1 := fun k => by
    funext a
    by_cases hk : a = k
    · subst hk; simp
    · simp [hk]
  rw [e, e, sub_eq_zero] at this
  have k1 : star (Y *ᵥ (Pi.single i 1 : Fin n → ℂ)) ⬝ᵥ (Y *ᵥ (Pi.single j 1 : Fin n → ℂ)) = (Yᴴ * Y) i j := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hs : star (Pi.single i (1 : E) : Fin n → E) = Pi.single i 1 := by
    funext a
    by_cases hk : a = i
    · subst hk; simp
    · simp [hk]
  have k2 : star (Pi.single i (1 : E) : Fin n → E) ⬝ᵥ (G *ᵥ (Pi.single j 1 : Fin n → E)) = G i j := by
    rw [hs]
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [k1, k2] at this
  rw [this, Matrix.map_apply]

end Polar

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end
