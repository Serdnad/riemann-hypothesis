module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.SatakeDualWeyl.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LvT.PtNorm

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
open Formalism.REAL (fockF)
open Formalism.L2.DIV (fockL fockS)
open scoped ComplexOrder Matrix

theorem psd_had {κ : Type} {A B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.of fun i j => A i j * B i j).PosSemidef := hA.hadamard hB

theorem psd_prod {ι κ : Type} [Fintype κ] (A B : ι → Matrix κ κ ℂ) (hB : ∀ τ, (B τ).PosSemidef)
    (hAB : ∀ τ, (A τ - B τ).PosSemidef) (s : Finset ι) :
    (Matrix.of fun i j => ∏ τ ∈ s, B τ i j).PosSemidef ∧
      ((Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - (Matrix.of fun i j => ∏ τ ∈ s, B τ i j)).PosSemidef := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · have h := Matrix.posSemidef_vecMulVec_self_star (fun _ : κ => (1 : ℂ))
      convert h using 1
      ext i j
      simp [Matrix.vecMulVec]
    · simpa using Matrix.PosSemidef.zero
  | insert τ s hτ ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · convert psd_had (hB τ) h1 using 1
      ext i j
      simp [Finset.prod_insert hτ]
    · have h3 := (psd_had (hAB τ) (h2.add h1)).add (psd_had (hB τ) h2)
      convert h3 using 1
      ext i j
      simp [Finset.prod_insert hτ]
      ring

theorem fockF_eq {σ : Type} (f g : MvPolynomial σ ℂ) : fockF f g = fockL g f := by
  have h := Formalism.L2.Col.map_fockS (RingHom.id ℂ) g f (fun _ => rfl)
  simp only [RingHom.id_apply, MvPolynomial.map_id] at h
  rw [Formalism.L2.DIV.fockL_apply, h]

theorem fockL_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ fockL f f := by
  by_cases hf : f = 0
  · simp [hf]
  · rw [← fockF_eq]; exact (Formalism.L2.DIV.ps_fockF_pos f hf).le

def gram {σ κ : Type} (v : κ → MvPolynomial σ ℂ) : Matrix κ κ ℂ := Matrix.of fun i j => fockL (v i) (v j)

theorem gram_dot {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ ℂ) (x : κ → ℂ) :
    star x ⬝ᵥ (gram v) *ᵥ x = fockL (∑ i, x i • v i) (∑ i, x i • v i) := by

  simp only [gram, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
  LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_herm {σ κ : Type} (v : κ → MvPolynomial σ ℂ) : (gram v).IsHermitian := by
  ext i j
  simp only [gram, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact (Formalism.L2.DIV.fockL_symm _ _).symm

theorem gram_psd {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ ℂ) : (gram v).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gram_herm v) fun x => by rw [gram_dot]; exact fockL_nonneg _

theorem gram_sub_psd {σ σ' κ : Type} [Fintype κ] (V : Submodule ℂ (MvPolynomial σ ℂ))
    (F : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ' ℂ) (C : ℝ)
    (h : ∀ f ∈ V, (fockL (F f) (F f)).re ≤ C * (fockL f f).re) (v : κ → MvPolynomial σ ℂ) (hv : ∀ i, v i ∈ V) :
    ((C : ℂ) • gram v - gram fun i => F (v i)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.sub ?_ (gram_herm _)
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (gram_herm v).eq]
    simp
  · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, gram_dot, gram_dot]
    have e : ∑ i, x i • F (v i) = F (∑ i, x i • v i) := by simp
    rw [e]
    have hm : ∑ i, x i • v i ∈ V := V.sum_mem fun i _ => V.smul_mem _ (hv i)
    have h1 := h _ hm
    have h2 := (Complex.le_def.mp (fockL_nonneg (∑ i, x i • v i))).2
    have h3 := (Complex.le_def.mp (fockL_nonneg (F (∑ i, x i • v i)))).2
    refine Complex.le_def.mpr ⟨?_, ?_⟩
    · simp only [smul_eq_mul, Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul]; linarith
    · simp only [smul_eq_mul, Complex.zero_im, Complex.sub_im, Complex.im_ofReal_mul, ← h2, ← h3]; simp

def eN {n : ℕ} (l : DomWeight n) : ℝ := (fockF (extremal ℂ n l) (extremal ℂ n l)).re

theorem eN_pos {n : ℕ} (l : DomWeight n) : 0 < eN l :=
  (Complex.lt_def.mp (Formalism.L2.DIV.ps_fockF_pos (extremal ℂ n l) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))).1

theorem eN_eq {n : ℕ} (l : DomWeight n) : fockF (extremal ℂ n l) (extremal ℂ n l) = (eN l : ℂ) := by
  have h := (Complex.lt_def.mp (Formalism.L2.DIV.ps_fockF_pos (extremal ℂ n l) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))).2
  exact Complex.ext (by simp [eN]) (by simpa using h.symm)

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}
  (br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))

end GlobalTheory.LvT.PtNorm
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.OverCompare

def genSums (F : Type) {E : Type} [Field F] [Field E] [Algebra F E] {k m : ℕ}
    (l : Fin m → Fin k → E) (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) :
    AddSubgroup (Fin k → E ⊗[F] R) where
  carrier := {u | ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j}
  zero_mem' := ⟨0, fun _ => zero_mem _, by funext i; simp⟩
  add_mem' := by
    rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    refine ⟨t + t', fun j => add_mem (ht j) (ht' j), ?_⟩
    funext i
    simp [TensorProduct.tmul_add, Finset.sum_add_distrib]
  neg_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨-t, fun j => neg_mem (ht j), ?_⟩
    funext i
    simp [TensorProduct.tmul_neg, Finset.sum_neg_distrib]

theorem tmul_mem_genSums {F E : Type} [Field F] [Field E] [Algebra F E] {k m : ℕ}
    (l : Fin m → Fin k → E) (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)
    {x : Fin k → E} (hx : x ∈ Submodule.span ℤ (Set.range l)) {s : R} (hs : s ∈ S₂) :
    (fun i => x i ⊗ₜ[F] s) ∈ genSums F l R S₂ := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  refine ⟨fun j => c j • s, fun j => zsmul_mem hs _, ?_⟩
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.smul_tmul]

theorem exists_int_generators {E : Type} [Field E] [NumberField E] {k : ℕ}
    (Λ : Submodule (𝓞 E) (Fin k → E)) [Module.Finite (𝓞 E) Λ] :
    ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧
      ∀ x ∈ Λ, x ∈ Submodule.span ℤ (Set.range l) := by
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  refine ⟨m, fun j => (s j : Fin k → E), fun j => (s j).2, fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : Λ) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h
  refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

theorem exists_generators_mem_latS_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) (u : Fin k → E ⊗[F] R), u ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S₂) Λ ↔ ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j := by
  intro F E _ _ _ _ _ k Λ hΛ
  obtain ⟨m, l, hl, hgen⟩ := exists_int_generators Λ
  refine ⟨m, l, hl, fun R _ _ S₂ u => ⟨fun hu => ?_, ?_⟩⟩
  · show u ∈ genSums F l R S₂
    have hst : ∀ s ∈ tensInt (F := F) R (intOE E) S₂, ∀ v ∈ genSums F l R S₂,
        s • v ∈ genSums F l R S₂ := by
      intro s hs
      induction hs using Subring.closure_induction with
      | mem x hx =>
        rintro _ ⟨t, ht, rfl⟩
        rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩
        · have e : ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : R)) • (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
              ∑ j, fun i => (a • l j) i ⊗ₜ[F] t j := by
            funext i
            simp [Finset.mul_sum, Algebra.smul_def]
          rw [show ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : R)) • (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
              ∑ j, fun i => (a • l j) i ⊗ₜ[F] t j from e]
          exact sum_mem fun j _ =>
            tmul_mem_genSums l R S₂ (hgen _ (Λ.smul_mem a (hl j))) (ht j)
        · refine ⟨fun j => (y : R) * t j, fun j => mul_mem y.2 (ht j), ?_⟩
          funext i
          simp [Finset.mul_sum]
      | zero => intro v _; rw [zero_smul]; exact zero_mem _
      | one => intro v hv; rwa [one_smul]
      | add x y _ _ hx hy => intro v hv; rw [add_smul]; exact add_mem (hx v hv) (hy v hv)
      | neg x _ hx => intro v hv; rw [neg_smul]; exact neg_mem (hx v hv)
      | mul x y _ _ hx hy => intro v hv; rw [mul_smul]; exact hx _ (hy v hv)
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact tmul_mem_genSums l R S₂ (hgen y hy) (one_mem _)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact hst a a.2 x hx
  · rintro ⟨t, ht, rfl⟩
    have e : (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
        ∑ j, (⟨(1 : E) ⊗ₜ[F] t j, Subring.subset_closure (Or.inr ⟨⟨t j, ht j⟩, rfl⟩)⟩ :
          tensInt (F := F) R (intOE E) S₂) • (fun i => inclE (F := F) R (l j i)) := by
      funext i
      simp [inclE, Subring.smul_def]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨l j, hl j, rfl⟩)

end GlobalTheory.OverCompare
end
end
