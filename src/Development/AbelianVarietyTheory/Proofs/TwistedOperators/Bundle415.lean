module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightWittLeviLePowOfBoundedUnipo
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.exists_rational_translate_flagUnipotent_height_le : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C := by
  first | exact @GlobalTheory.FlagHeight.exists_rat_translate_height_le | exact GlobalTheory.FlagHeight.exists_rat_translate_height_le | (intros; apply GlobalTheory.FlagHeight.exists_rat_translate_height_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.unitaryQuotientHeight_wittLevi_le_pow_of_boundedUnipotent : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (C₀ : ℝ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, height S n ≤ C₀ → ∀ h : GA D S₀, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a := by
  first | exact @GlobalTheory.HtWittLow.quotHeight_le_of_height_le | exact GlobalTheory.HtWittLow.quotHeight_le_of_height_le | (intros; apply GlobalTheory.HtWittLow.quotHeight_le_of_height_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnPieces

variable {D : D7}

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_zero_right (S T : HSp D) (x : WO S T) : hO S T x 0 = 0 := by
  unfold hO
  simp

theorem hO_zero_left (S T : HSp D) (y : WO S T) : hO S T 0 y = 0 := by
  unfold hO
  simp

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO
  rw [hO_add_right, mul_add, map_add (f := _)]

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  unfold symplO
  rw [hO_zero_right, mul_zero, map_zero]

theorem symplO_neg_right (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (M : Mx D n k) : MxAt P (a ⬝ M) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem mxAt_zero {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} : MxAt P (0 : Mx D m n) := fun _ _ => zero_mem _

theorem mxAt_add {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {a b : Mx D m n} (ha : MxAt P a) (hb : MxAt P b) : MxAt P (a + b) :=
  fun i j => add_mem (ha i j) (hb i j)

theorem mxAt_neg {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {a : Mx D m n} (ha : MxAt P a) : MxAt P (-a) :=
  fun i j => neg_mem (ha i j)

variable {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem hO_extY_right (u : WO V W) (a' : Mx D W.rank ρ) : hO V W u (d.extY W a') = hO V W (d.extX W (u ⬝ d.jX)) (d.extY W a') := by
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY,
    HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_zero, Matrix.mul_one, hO_zero_right, pairS, adj_zero,
    Matrix.zero_mul, Matrix.trace_zero, add_zero]

theorem hO_extX_left (a : Mx D W.rank ρ) (u' : WO V W) : hO V W (d.extX W a) u' = hO V W (d.extX W a) (d.extY W (u' ⬝ d.jY)) := by
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY,
    HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_zero, Matrix.mul_one, pairS, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.trace_zero, add_zero, zero_add, hO_zero_left, hO_zero_right]

end GlobalTheory.AscFin.AnnPieces

namespace GlobalTheory.AscFin.AnnPieces

variable {D : D7} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (d : HypDec V V₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (Γ : AddSubgroup (WO V W))

theorem symplO_extY_right (u : WO V W) (a' : Mx D W.rank ρ) :
    symplO V W u (d.extY W a') = symplO V W (d.extX W (u ⬝ d.jX)) (d.extY W a') := by
  unfold symplO
  rw [hO_extY_right]

theorem symplO_extX_left (a : Mx D W.rank ρ) (u' : WO V W) :
    symplO V W (d.extX W a) u' = symplO V W (d.extX W a) (d.extY W (u' ⬝ d.jY)) := by
  unfold symplO
  rw [← hO_extX_left]

theorem extY_mul_jY (a' : Mx D W.rank ρ) : d.extY W a' ⬝ d.jY = a' := by
  rw [HypDec.extY_apply, Matrix.mul_assoc, HypDec.pY_jY, Matrix.mul_one]

theorem extX_mul_jX (a : Mx D W.rank ρ) : d.extX W a ⬝ d.jX = a := by
  rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]

def annY : AddSubgroup (Mx D W.rank ρ) where
  carrier := {a' | MxAt (fun _ => True) a' ∧ ∀ a, d.extX W a ∈ Γ → ψ (symplO V W (d.extX W a) (d.extY W a')) = 1}
  zero_mem' := ⟨mxAt_zero, fun a _ => by rw [map_zero, symplO_zero_right, AddChar.map_zero_eq_one]⟩
  add_mem' := fun {x y} hx hy => ⟨mxAt_add hx.1 hy.1, fun a ha => by
    rw [map_add (f := _), symplO_add_right, AddChar.map_add_eq_mul, hx.2 a ha, hy.2 a ha, one_mul]⟩
  neg_mem' := fun {x} hx => ⟨mxAt_neg hx.1, fun a ha => by
    rw [map_neg, symplO_neg_right, AddChar.map_neg_eq_inv, hx.2 a ha, inv_one]⟩

def annSet : Set (WO V W) := {u' | MxAt (fun _ => True) u' ∧ ∀ u ∈ Γ, ψ (symplO V W u u') = 1}

variable {d ψ Γ}

theorem extY_mem_annSet (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ) {a' : Mx D W.rank ρ} (ha' : a' ∈ annY d ψ Γ) :
    d.extY W a' ∈ annSet ψ Γ :=
  ⟨mxAt_mul ha'.1 _, fun u hu => by rw [symplO_extY_right]; exact ha'.2 _ (hX u hu)⟩

theorem mul_jY_mem_annY {u' : WO V W} (hu' : u' ∈ annSet ψ Γ) : u' ⬝ d.jY ∈ annY d ψ Γ :=
  ⟨mxAt_mul hu'.1 _, fun a ha => by rw [← symplO_extX_left]; exact hu'.2 _ ha⟩

theorem annY_eq_image (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ) :
    (annY d ψ Γ : Set (Mx D W.rank ρ)) = (fun u : WO V W => u ⬝ d.jY) '' annSet ψ Γ :=
  Set.ext fun a' => ⟨fun h => ⟨_, extY_mem_annSet hX h, extY_mul_jY d a'⟩, by
    rintro ⟨u, hu, rfl⟩
    exact mul_jY_mem_annY hu⟩

theorem A₂_eq (dW : HypDec W W₀ σ) (Γ₂ : AddSubgroup (WO V W)) :
    (piecesOf d dW ψ Γ Γ₂).A₂ = annY d ψ Γ := by
  show AddSubgroup.closure (annY d ψ Γ : Set (Mx D W.rank ρ)) = _
  exact AddSubgroup.closure_eq _

theorem pieces_dualA (dW : HypDec W W₀ σ) (Γ₂ : AddSubgroup (WO V W))
    (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ)
    (hc : IsCompact (annSet ψ Γ))
    (ho : ∃ U : Set (WO V W), IsOpen U ∧ (0 : WO V W) ∈ U ∧
      ∀ u' ∈ U, MxAt (fun _ => True) u' → ∀ u ∈ Γ, ψ (symplO V W u u') = 1)
    (hb : ∀ u, MxAt (fun _ => True) u → (∀ u' ∈ annSet ψ Γ, ψ (symplO V W u u') = 1) → u ∈ Γ) :
    FinLat (piecesOf d dW ψ Γ Γ₂).A₂ ∧
      (∀ a, MxAt (fun _ => True) a → (a ∈ (piecesOf d dW ψ Γ Γ₂).A₁ ↔
        ∀ a' ∈ (piecesOf d dW ψ Γ Γ₂).A₂, ψ (symplO V W (d.extX W a) (d.extY W a')) = 1)) ∧
      (∀ a', MxAt (fun _ => True) a' → (a' ∈ (piecesOf d dW ψ Γ Γ₂).A₂ ↔
        ∀ a ∈ (piecesOf d dW ψ Γ Γ₂).A₁, ψ (symplO V W (d.extX W a) (d.extY W a')) = 1)) := by
  rw [A₂_eq]
  refine ⟨⟨fun a' ha' => ha'.1, ?_, ?_⟩, fun a ha => ⟨fun h a' ha' => ha'.2 a h, fun h => ?_⟩,
    fun a' ha' => ⟨fun h a ha => h.2 a ha, fun h => ⟨ha', h⟩⟩⟩
  · rw [annY_eq_image hX]
    exact hc.image (continuous_id.matrix_mul continuous_const)
  · obtain ⟨U, hU, h0, hUm⟩ := ho
    refine ⟨(fun a' => d.extY W a') ⁻¹' U, hU.preimage (continuous_id.matrix_mul continuous_const), ?_, ?_⟩
    · show d.extY W 0 ∈ U
      rw [map_zero]
      exact h0
    · intro a' ha' hfin
      refine ⟨hfin, fun b hb' => ?_⟩
      have := hUm _ ha' (mxAt_mul hfin _) _ hb'
      rwa [symplO_extY_right, extX_mul_jX] at this
  · show d.extX W a ∈ Γ
    refine hb _ (mxAt_mul ha _) fun u' hu' => ?_
    rw [symplO_extX_left]
    exact h _ (mul_jY_mem_annY hu')

end GlobalTheory.AscFin.AnnPieces

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory

theorem projX_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e * d.qX) *ᵥ v ∈ a.lat Λ 𝔟 := by
  intro D A B B₀ c ρ a d hA Λ 𝔟 v hv
  obtain ⟨hc, he, s, he'⟩ := hA
  obtain ⟨y, hy, u, hu, rfl⟩ := hv
  have hGh : B.gramᴴ = B.gram := GlobalTheory.MixModel.gram_conjTranspose B
  have hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0 := a.perp
  have hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  set N : Matrix (Fin c) (Fin c) D.host.E := antiDiagonalSignGramMatrix c (-1) with hN
  have hK : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have := congrArg Matrix.conjTranspose hperp
    simpa [Matrix.conjTranspose_mul, hGh, Matrix.mul_assoc] using this
  have hρc : ρ ≤ c := by omega
  let P : Matrix (Fin c) (Fin ρ) D.host.E := fun q p => if q = (Fin.castLE hρc p).rev then s p else 0
  let Q : Matrix (Fin c) (Fin ρ) D.host.E := fun q p => if q = Fin.castLE hρc p then (-D.host.xi0) ^ (p.1 + 1) else 0
  have heP : d.e' = a.a * P := by
    rw [he']; ext i p; rw [Matrix.mul_apply]; simp [colsOf, P, mul_comm]
  have heQ : d.e = a.a * Q := by
    rw [he]; ext i p; rw [Matrix.mul_apply]; simp [colsOf, Q, mul_comm]
  have hPN : ∀ p q, (Pᴴ * N) p q = if q = Fin.castLE hρc p then star (s p) else 0 := by
    intro p q
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    simp only [P, apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := p.2; have := q.2
    simp only [hN, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, Fin.val_castLE]
    split_ifs <;> first | (exfalso; omega) | ring
  have hdiag : ∀ p : Fin ρ, star (s p) * (-D.host.xi0) ^ (p.1 + 1) = 1 := by
    intro p
    have h1 := d.e'e
    rw [heP, heQ, Matrix.conjTranspose_mul] at h1
    have h2 : Pᴴ * a.aᴴ * B.gram * (a.a * Q) = Pᴴ * N * Q := by
      rw [← hgram]; simp only [Matrix.mul_assoc]
    rw [h2] at h1
    have h3 := congrFun (congrFun h1 p) p
    rw [Matrix.mul_apply] at h3
    simp only [hPN, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Q, Matrix.one_apply_eq] at h3
    simpa using h3
  have hqX : d.qX = Pᴴ * a.aᴴ * B.gram := by
    rw [HypDec.qX, heP, Matrix.conjTranspose_mul]
  have ht : d.qX *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) = (Pᴴ * N) *ᵥ u := by
    have h1 : Pᴴ * a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
      calc _ = Pᴴ * (a.aᴴ * B.gram * frameMat B A a.ι) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hK, Matrix.mul_zero]
    have h2 : Pᴴ * a.aᴴ * B.gram * a.a = Pᴴ * N := by
      rw [← hgram]; simp only [Matrix.mul_assoc]
    rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hqX, h1, h2, zero_mulVec, zero_add]
  have hu' : ∀ q : Fin c, (Q *ᵥ ((Pᴴ * N) *ᵥ u)) q = if q.1 < ρ then u q else 0 := by
    intro q
    simp only [mulVec, dotProduct, hPN, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Q]
    split_ifs with hq
    · rw [Finset.sum_eq_single ⟨q.1, hq⟩]
      · have e1 : q = Fin.castLE hρc ⟨q.1, hq⟩ := Fin.ext rfl
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [← mul_assoc, mul_comm ((-D.host.xi0) ^ _), hdiag, one_mul, if_pos e1, ← e1]
      · intro b _ hb
        rw [if_neg]
        intro e; apply hb; ext; simp only [Fin.ext_iff, Fin.val_castLE, Fin.val_mk] at e ⊢; omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro e; apply hq; rw [e]; simp
  refine ⟨0, Λ.zero_mem, Q *ᵥ ((Pᴴ * N) *ᵥ u), fun q => ?_, ?_⟩
  · rw [hu']; split_ifs
    · exact hu q
    · exact (𝔟 q).val.zero_mem
  · rw [mulVec_zero, zero_add, ← mulVec_mulVec, ht, heQ, ← mulVec_mulVec]

end GlobalTheory
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.CoreSelfDual

variable {D : D7}

theorem form_eq (S : HSp D) (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem wittHyperbolicRankZero_proj_mul_emb (y : Fin S₀.rank → D.host.E) : d.q0 *ᵥ (d.i₀ *ᵥ y) = y := by
  have hq : d.q0 * d.i₀ = 1 := by
    calc d.q0 * d.i₀ = S₀.gram⁻¹ * (d.i₀ᴴ * S.gram * d.i₀) := by
          simp only [HypDec.q0, Matrix.mul_assoc]
      _ = 1 := by rw [d.iso]; exact Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det S₀)
  rw [Matrix.mulVec_mulVec, hq, Matrix.one_mulVec]

theorem wittCoreProjection_adjoint_coreEmbedding (x : Fin S.rank → D.host.E) (y : Fin S₀.rank → D.host.E) :
    star (d.q0 *ᵥ x) ⬝ᵥ S₀.gram *ᵥ y = star x ⬝ᵥ S.gram *ᵥ (d.i₀ *ᵥ y) := by
  have hM : d.q0ᴴ * S₀.gram = S.gram * d.i₀ := by
    simp only [HypDec.q0, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      GlobalTheory.MixModel.gram_conjTranspose, GlobalTheory.MixModel.gramInv_conjTranspose, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det S₀), Matrix.mul_one]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, hM]

theorem isSelfDualC_comap {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hΛ : IsSelfDualC S Λ)
    (hP : ∀ x ∈ Λ, d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ Λ) :
    IsSelfDualC S₀ (Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))) := by
  unfold IsSelfDualC at hΛ ⊢
  obtain ⟨hlat, hdual⟩ := hΛ
  have hq : ∀ y, d.q0 *ᵥ (d.i₀ *ᵥ y) = y := GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb d
  have hmem : ∀ y, y ∈ Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ↔ d.i₀ *ᵥ y ∈ Λ :=
    fun y => Iff.rfl
  have heq : Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) =
      Λ.map ((Matrix.mulVecLin d.q0).restrictScalars (𝓞 D.host.E)) := by
    ext y
    rw [hmem, Submodule.mem_map]
    constructor
    · intro hy
      exact ⟨_, hy, hq y⟩
    · rintro ⟨x, hx, rfl⟩
      exact hP x hx
  refine ⟨?_, fun y => ?_⟩
  · rw [heq]
    exact Submodule.IsLattice.of_fg _ (hlat.fg.map _)
  · rw [hmem]
    constructor
    · intro hy x hx
      rw [hmem] at hx
      obtain ⟨b, hb⟩ := (hdual (d.i₀ *ᵥ y)).1 hy (d.i₀ *ᵥ x) hx
      refine ⟨b, ?_⟩
      rw [hb, GlobalTheory.AscFin.CoreSelfDual.form_eq, GlobalTheory.AscFin.CoreSelfDual.form_eq, ← d.iso,
        Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · intro hy
      refine (hdual (d.i₀ *ᵥ y)).2 fun w hw => ?_
      obtain ⟨b, hb⟩ := hy (d.q0 *ᵥ w) (hP w hw)
      refine ⟨b, ?_⟩
      rw [hb, GlobalTheory.AscFin.CoreSelfDual.form_eq, GlobalTheory.AscFin.CoreSelfDual.form_eq,
        GlobalTheory.AscFin.CoreSelfDual.wittCoreProjection_adjoint_coreEmbedding]

theorem mulVec_col_eq_zero {n k c r : ℕ} {q : Matrix (Fin k) (Fin n) D.host.E} {a : Matrix (Fin n) (Fin c) D.host.E}
    {f : Fin r → Fin c} {s : Fin r → D.host.E} (h : q * colsOf a f s = 0) {p : Fin r} (hs : s p ≠ 0) :
    q *ᵥ (fun i => a i (f p)) = 0 := by
  funext i
  have h1 := congrFun (congrFun h i) p
  simp only [Matrix.mul_apply, colsOf, Matrix.zero_apply] at h1
  have h2 : s p * (q *ᵥ (fun i => a i (f p))) i = 0 := by
    rw [← h1]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  exact (mul_eq_zero.mp h2).resolve_left hs

theorem wittCoreProjection_kills_offMiddle_auxiliaryVectors {A : HSp D} {c : ℕ} (a : HermitianOrthogonalExtensionData A S c (-1)) (h : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ + 1) (p : Fin c) (hp : p.1 ≠ ρ) :
    d.q0 *ᵥ (fun i => a.a i p) = 0 := by
  subst hc
  obtain ⟨h2, he, s, he'⟩ := h
  have hqe : d.q0 * d.e = 0 := by
    simp only [HypDec.q0, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc d.i₀ᴴ, d.i₀e, Matrix.mul_zero]
  have hqe' : d.q0 * d.e' = 0 := by
    simp only [HypDec.q0, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc d.i₀ᴴ, d.i₀e', Matrix.mul_zero]
  rw [he] at hqe
  rw [he'] at hqe'
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · have := GlobalTheory.AscFin.CoreSelfDual.mulVec_col_eq_zero hqe (p := ⟨p.1, hlt⟩) (pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero))
    rw [show p = Fin.castLE (by omega) (⟨p.1, hlt⟩ : Fin ρ) from Fin.ext rfl]
    exact this
  · have hk : 2 * ρ - p.1 < ρ := by omega
    have hsk : s ⟨2 * ρ - p.1, hk⟩ ≠ 0 := by
      intro h0
      have h1 := congrFun (congrFun d.e'e ⟨2 * ρ - p.1, hk⟩) ⟨2 * ρ - p.1, hk⟩
      rw [he'] at h1
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, colsOf, h0] at h1
    have := GlobalTheory.AscFin.CoreSelfDual.mulVec_col_eq_zero hqe' hsk
    rw [show p = (Fin.castLE (by omega) (⟨2 * ρ - p.1, hk⟩ : Fin ρ) : Fin (2 * ρ + 1)).rev from
      Fin.ext (by simp only [Fin.val_rev, Fin.coe_castLE]; omega)]
    exact this

private theorem mulVec_eq_sum_smul_col {R : Type} [CommRing R] {n c : ℕ} (M : Matrix (Fin n) (Fin c) R) (u : Fin c → R) :
    M *ᵥ u = ∑ p, u p • (fun i => M i p) := by
  funext i
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem proj_mem {A : HSp D} {c : ℕ} (a : HermitianOrthogonalExtensionData A S c (-1)) (h : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ + 1)
    {N : Matrix (Fin S₀.rank) (Fin A.rank) D.host.E} (hN : d.i₀ * N = frameMat S A a.ι) {z : Fin S₀.rank → D.host.E}
    (hz : d.i₀ *ᵥ z = fun i => a.a i ⟨ρ, by omega⟩) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : Fin S.rank → D.host.E} (hx : x ∈ a.lat Λ 𝔟) :
    d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ a.lat Λ 𝔟 := by
  obtain ⟨y, hy, u, hu, rfl⟩ := hx
  have hcol : ∀ p : Fin c, d.q0 *ᵥ (fun i => a.a i p) =
      if p = (⟨ρ, by omega⟩ : Fin c) then z else 0 := by
    intro p
    split_ifs with hp
    · have hpz : (fun i => a.a i p) = d.i₀ *ᵥ z := by rw [hz, hp]
      rw [hpz, GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb]
    · exact GlobalTheory.AscFin.CoreSelfDual.wittCoreProjection_kills_offMiddle_auxiliaryVectors d a h hc p (fun e => hp (Fin.ext e))
  have h1 : d.i₀ *ᵥ (d.q0 *ᵥ (frameMat S A a.ι *ᵥ y)) = frameMat S A a.ι *ᵥ y := by
    rw [← hN, ← Matrix.mulVec_mulVec, GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb]
  have h2 : d.q0 *ᵥ (a.a *ᵥ u) = u ⟨ρ, by omega⟩ • z := by
    rw [mulVec_eq_sum_smul_col a.a u, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hcol, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  show ∃ y' ∈ Λ, ∃ u' : Fin c → D.host.E, (∀ p, u' p ∈ 𝔟 p) ∧
    d.i₀ *ᵥ (d.q0 *ᵥ (frameMat S A a.ι *ᵥ y + a.a *ᵥ u)) = frameMat S A a.ι *ᵥ y' + a.a *ᵥ u'
  refine ⟨y, hy, fun p => if p = (⟨ρ, by omega⟩ : Fin c) then u p else 0, fun p => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hu p
    · exact (𝔟 p).zero_mem
  · rw [Matrix.mulVec_add, Matrix.mulVec_add, h1, h2, Matrix.mulVec_smul, hz, mulVec_eq_sum_smul_col a.a]
    congr 1
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.AscFin.CoreSelfDual

namespace GlobalTheory.AscFin

theorem isSelfDualC_lat0 {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : GlobalTheory.Asc.Frames G) (hF : Std F)
    (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := by
  have h1 : 1 ≤ 2 * ρ + 2 := by omega
  have e : G.Λ (.grid (2 * ρ + 2) 0) =
      (G.colDec (2 * ρ + 2) h1 h).lat (G.Λ (.core (2 * ρ + 2))) (stairId _ _ _) :=
    G.sp.colLat (2 * ρ + 2) h1 h
  have hc : 2 * ρ + 2 - 1 = 2 * ρ + 1 := by omega
  show IsSelfDualC (F.V₀ ρ) ((G.Λ (.grid (2 * ρ + 2) 0)).comap
    ((Matrix.mulVecLin (F.dB ρ h).i₀).restrictScalars (𝓞 D.host.E)))
  refine CoreSelfDual.isSelfDualC_comap (F.dB ρ h) (G.sp.V_is (2 * ρ + 2) 0 h1 h (Nat.zero_le _)).sd ?_
  intro x hx
  rw [e] at hx ⊢
  refine CoreSelfDual.proj_mem (F.dB ρ h) _ (hF.hB ρ h) hc (N := (F.oB ρ h).iA) (hF.aB ρ h)
    (z := (F.oB ρ h).iB *ᵥ F.ζ 0) ?_ hx
  rw [Matrix.mulVec_mulVec]
  exact hF.zB' ρ h

end GlobalTheory.AscFin

end
end
