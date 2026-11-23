module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle008
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle020

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isSplitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

theorem psi_neg_one (ψ : AddChar (AF D.host.F) ℂ) {a : AF D.host.F} (h : ψ a = 1) : ψ (-a) = 1 := by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

variable (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem heisO_zero (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO_zero_right]

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Topology Filter
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tate

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

end Tate

section Matrix

variable {D : D7} (S T : HSp D)

theorem embedding_xi_zero_ne_zero : D.host.xi0 ≠ 0 := by
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hdpos : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hd
    have : (Real.sqrt D.host.d : ℂ) = 0 := by
      rcases mul_eq_zero.1 hd.symm with h | h
      · exact absurd h Complex.I_ne_zero
      · exact h
    exact (Real.sqrt_pos.2 hdpos).ne' (by exact_mod_cast this)
  have hN : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  unfold Host.xi0
  exact div_ne_zero (neg_ne_zero.2 one_ne_zero) (mul_ne_zero hN hs)

def hE (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  ∑ a, ∑ b, ∑ c, ∑ d, S.gram⁻¹ a b * star (γ c b) * T.gram c d * e d a

def betaO (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.F :=
  Algebra.trace D.host.F D.host.E (D.host.xi0 * hE S T e γ)

theorem symplO_ratW_ratW (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplO S T (ratW T S e) (ratW T S γ) = algebraMap D.host.F (AF D.host.F) (betaO S T e γ) := by
  have h : hO S T (ratW T S e) (ratW T S γ) = incA D (hE S T e γ) := by
    unfold hO hE

    simp only [map_sum, map_mul, ratW, Matrix.map_apply, Brg.cA_inc]
  unfold symplO betaO
  rw [h, ← map_mul, trace_incA]

theorem symplO_smul_left (c : AF D.host.F) (x y : WO S T) : symplO S T (c • x) y = c * symplO S T x y := by
  have h : hO S T (c • x) y = algebraMap (AF D.host.F) (AE D) c * hO S T x y := by
    unfold hO
    simp only [Matrix.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring
  unfold symplO
  rw [h, mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

end Matrix

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7}

def jF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem jF_tmul (β : Af D.host.F) (y : D.host.E) : jF D (β ⊗ₜ[D.host.F] y) = pairA D.host.F 0 β ⊗ₜ[D.host.F] y := rfl

theorem mul_pairA (x : AF D.host.F) (α : Af D.host.F) :
    x * pairA D.host.F 0 α = pairA D.host.F 0 (sndA D.host.F x * α) :=
  Prod.ext (by show x.1 * 0 = 0; rw [mul_zero]) rfl

theorem finPart_tmul (x : AF D.host.F) (z : D.host.E) : finPart D (x ⊗ₜ[D.host.F] z) = sndA D.host.F x ⊗ₜ[D.host.F] z :=
  rfl



theorem mul_gen (a : AE D) (α : Af D.host.F) (m : D.host.E) :
    a * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      jF D (finPart D a * (α ⊗ₜ[D.host.F] (1 : D.host.E))) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] m) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul, map_zero, zero_mul]
  | tmul x z =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_pairA, finPart_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      jF_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | add x y hx hy => rw [add_mul, hx, hy, map_add (f := _), add_mul, map_add (f := _), add_mul]

theorem gen_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    {c : D.host.E} (hc : c ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ ΛS) {t : Fin T.rank → D.host.E}
    (ht : t ∈ ΛT) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j) : WO S T) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
  AddSubgroup.subset_closure ⟨α, hα, fun _ h => absurd trivial h, c, hc, s, hs, t, ht, rfl⟩


theorem jF_gen_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D)
    {c : D.host.E} (hc : c ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ ΛS) {t : Fin T.rank → D.host.E}
    (ht : t ∈ ΛT) :
    (Matrix.of fun i j => jF D z * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, y, rfl⟩ := hx
    have hyc : (y : D.host.E) * c ∈ D.host.AA := by
      have := Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) y hc
      rwa [Algebra.smul_def] at this
    have hm : (Matrix.of fun i j => jF D (β ⊗ₜ[D.host.F] (y : D.host.E)) *
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) =
        Matrix.of fun i j => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((y : D.host.E) * c * t i * ∑ k, star (s k) * S.gram k j) := by
      ext i j
      rw [Matrix.of_apply, Matrix.of_apply, jF_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc, mul_assoc,
        mul_assoc]
    rw [hm]
    exact gen_mem S T ΛS ΛT hβ hyc hs ht
  | zero =>
    have hm : (Matrix.of fun i j => jF D 0 *
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) = 0 := by
      ext i j; rw [Matrix.of_apply, map_zero, zero_mul]; rfl
    rw [hm]; exact zero_mem _
  | add x y _ _ hx hy =>
    have hm : (Matrix.of fun i j => jF D (x + y) *
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) =
        (Matrix.of fun i j => jF D x * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))) +
        (Matrix.of fun i j => jF D y * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))) := by
      ext i j; rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, map_add (f := _), add_mul]
    rw [hm]; exact add_mem hx hy
  | neg x _ hx =>
    have hm : (Matrix.of fun i j => jF D (-x) *
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) =
        -(Matrix.of fun i j => jF D x * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))) := by
      ext i j; rw [Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply, map_neg, neg_mul]
    rw [hm]; exact neg_mem hx



theorem latO_smul_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {a : AE D} (ha : finPart D a ∈ intAE D) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    a • u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩ := hx
    have hz : finPart D a * (α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
      intAE_mul ha (AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩)
    have hm : a • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j) :
        WO S T) = Matrix.of fun i j => jF D (finPart D a * (α ⊗ₜ[D.host.F] (1 : D.host.E))) *
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) := by
      ext i j
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, smul_eq_mul, mul_gen]
    rw [hm]
    exact jF_gen_mem S T ΛS ΛT hz hc hs ht
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end Formalism.IndefR.Fin

end
end
