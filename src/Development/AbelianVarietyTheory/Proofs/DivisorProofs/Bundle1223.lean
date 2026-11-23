module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.NuMul

theorem loc_mul {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b a' b' : ℤ) (f g : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (a + a') (b + b') (f * g) i j = P.loc a b f i j * P.loc a' b' g i j := by
  have h1 : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have h2 : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  simp only [Pair.loc, zpow_add₀ h1, zpow_add₀ h2]
  ring

theorem mul_mem_H_and_nu_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b a' b' : ℤ) (f g : X.functionField), f ∈ P.H a b → g ∈ P.H a' b' → f * g ∈ P.H (a + a') (b + b') ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (a + a') (b + b') σ y (f * g) = P.nu a b σ y f * P.nu a' b' σ y g := by
  intro k _ X _ p P a b a' b' f g hf hg
  refine ⟨fun x i j hi hj => ?_, fun σ y => ?_⟩
  · rw [loc_mul]
    exact (hf x i j hi hj).mul (hg x i j hi hj)
  · have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
    have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
    simp only [Pair.nu]
    rw [loc_mul, ratVal_mul (hf _ _ _ hi hj) (hg _ _ _ hi hj), norm_mul]
    have e : -(((a + a' : ℤ) : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + ((b + b' : ℤ) : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2
      = -((a : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + (b : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2
        + -((a' : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + (b' : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2 := by
      push_cast; ring
    rw [e, Real.exp_add]
    ring

end GlobalTheory.VolBr.NuMul
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.VolBr.Pair

theorem isRatSec_dual_of_inv {X : Scheme.{0}} [IsIntegral X] {L : LB X} {r : L.ι → X.functionFieldˣ}
    (hr : IsRatSec L r) : IsRatSec (CechPic.dual L) fun i => (r i)⁻¹ := fun i j hij => by
  have e : fnOf _ hij ((CechPic.dual L).g i j : Γ(X, L.U i ⊓ L.U j)ˣ).val =
      (fnOf _ hij (L.g i j : Γ(X, L.U i ⊓ L.U j)))⁻¹ := map_units_inv _ _
  rw [e, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hr i j hij, mul_inv]
  rfl

theorem dual_quot_eq {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b : ℤ) (u : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    u⁻¹ / P.loc (-a) (-b) 1 i j = (u / P.loc a b 1 i j)⁻¹ := by
  simp only [loc, one_mul, zpow_neg, div_eq_mul_inv, mul_inv, inv_inv]

theorem ratVal_inv_unit {k : Type} [CommRing k] {σ : k →+* ℂ} {Z : Scheme.{0}} [IsIntegral Z]
    {q : Z ⟶ Sp k} {y : CxPts q σ} {f : Z.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have e := ratVal_mul (y := y) hf.regAt hf.inv.regAt
  have e1 := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
  rw [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e1
  rw [mul_inv_cancel₀ hf.ne_zero, e1] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem rep_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → P.Rep (-a) (-b) M.dual := by
  intro k _ X _ p P a b M ⟨ρ, hρ, hu, hn⟩
  refine ⟨fun c => (ρ c)⁻¹, isRatSec_dual_of_inv hρ, ?_, ?_⟩
  · intro x c i j hc hi hj
    rw [Units.val_inv_eq_inv_val, dual_quot_eq]
    exact (hu x c i j hc hi hj).inv
  · intro σ y c i j hc hi hj
    have hU := hu _ c i j (mem_ptsIn.1 hc) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have e := hn σ y c i j hc hi hj
    rw [Units.val_inv_eq_inv_val, dual_quot_eq, ratVal_inv_unit hU, norm_inv, Real.log_inv]
    change _ - (-(M.φ σ).φ c y) / 2 = _
    push_cast
    linarith

end GlobalTheory.VolBr.Pair
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.FdDom

open ReciprocityTheory.ChartRestriction.G.FD

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [IsCMField E] in
theorem gram_neg_transpose (τ : E →+* ℂ) (H : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ (-Hᵀ) x = (-(xᴴ * H.map τ * x))ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem lminor_transpose (A : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)) : lminor Aᵀ i = lminor A i := by
  unfold lminor
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]

theorem map_mem_UH (τ : E →+* ℂ) (H g : Matrix (Fin r) (Fin r) E)
    (hg : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm (-Hᵀ) (g.mulVec x) (g.mulVec y) = ReciprocityTheory.ChartRestriction.G.FD.herm (-Hᵀ) x y) :
    g.map τ ∈ Formalism.QuantumDeterminants.UH (H.map τ) := by
  change (g.map τ)ᴴ * H.map τ * g.map τ = H.map τ
  ext b a
  have h := congrArg τ (hg (Pi.single a 1) (Pi.single b 1))
  have hc : ∀ z : E, τ (ReciprocityTheory.ChartRestriction.G.FD.cc z) = starRingEnd ℂ (τ z) := fun z =>
    IsCMField.complexEmbedding_complexConj E τ z

  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.mulVec_single_one, Matrix.col_apply, map_sum, map_mul, hc, Matrix.neg_apply,
  Matrix.transpose_apply, map_neg, Pi.single_apply, apply_ite τ, apply_ite (starRingEnd ℂ), map_one, map_zero,
  ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, RCLike.star_def]
  have h2 : (∑ x, ∑ y, if x = a then if y = b then -τ (H y x) else 0 else 0) = -τ (H b a) := by
    rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp)]
    simp
  rw [← neg_inj, ← h2, ← h]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := by
  intro s t h
  apply D.eTau.injective
  apply Subtype.ext
  apply (D.host.gal).symm.injective
  exact AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)

theorem dom_iff_frDoms : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ k, ∃ e : D.what₂.Tau ≃ (X k).Ψ, (∀ ρ, (e ρ).1 = tauE D ρ) ∧ (∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r, x ∈ (X k).dom ↔ (fun ρ a b => x (e ρ) (Fin.cast hr a) (Fin.cast hr b)) ∈ frDoms (gramAt D V) (fun ρ => nNeg (M.ε ρ))) ∧ ∀ γ ∈ (X k).Γ, ∀ ρ, Matrix.reindex (finCongr hr.symm) (finCongr hr.symm) ((γ : Matrix (Fin r) (Fin r) D.host.E).map (tauE D ρ)) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  intro D θ V S M w r hr Comp X la dict mu c Kf _ hG k
  subst hr
  have hΨ := hG.base.1 k
  have hp := hG.base.2.1 k
  have hGm : (X k).Gm = -V.gramᵀ := (hG.model k).1
  let f : D.what₂.Tau → (X k).Ψ := fun ρ => ⟨tauE D ρ, (hΨ _).2 ⟨ρ, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun s t h => tauE_injective D (congrArg Subtype.val h), fun τ => ?_⟩
    obtain ⟨ρ, hρ⟩ := (hΨ τ.1).1 τ.2
    exact ⟨ρ, Subtype.ext hρ.symm⟩
  refine ⟨Equiv.ofBijective f hf, fun _ => rfl, fun x => ?_, fun γ hγ ρ => ?_⟩
  · change (∀ τ : (X k).Ψ, _) ↔ ∀ ρ, _
    rw [← (Equiv.ofBijective f hf).forall_congr_right]
    refine forall_congr' fun ρ => ?_
    simp only [dmin, hGm, gram_neg_transpose, lminor_transpose, hp ρ]
    rfl
  · have h := ((X k).Γ_stab γ hγ).1
    rw [hGm] at h
    exact map_mem_UH (tauE D ρ) V.gram _ h

end GlobalTheory.HolDict.FdDom
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

private theorem eq_diagonal_of_lower_upper_zero {n : ℕ} (b : Mt n) (hlow : ∀ a c : Fin n, c < a → b a c = 0)
    (hup : ∀ a c : Fin n, a < c → b a c = 0) : b = diagonal fun a => b a a := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hup i j hij, diagonal_apply_ne _ (ne_of_lt hij)]
  · rw [diagonal_apply_eq]
  · rw [hlow i j hij, diagonal_apply_ne _ (ne_of_gt hij)]

private theorem eq_exp_arg_mul_I_of_star_mul_self_eq_one (z : ℂ) (hz : star z * z = 1) :
    z = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
  have hn : Complex.normSq z = 1 := by
    have h1 : (Complex.normSq z : ℂ) = 1 := (Complex.normSq_eq_conj_mul_self).trans hz
    exact_mod_cast h1
  have habs : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hn
    have h3 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have key := Complex.norm_mul_exp_arg_mul_I z
  rw [habs, Complex.ofReal_one, one_mul] at key
  exact key.symm

theorem diag_of_upT_of_preserves {n : ℕ} (d : Fin n → ℂ) (hd : ∀ a, d a * d a = 1) (b : Mt n) (hb : UpT b)
    (h : bᴴ * diagonal d * b = diagonal d) :
    ∃ s : Fin n → ℝ, b = diagonal fun a => Complex.exp ((s a : ℂ) * Complex.I) := by
  classical
  have hDD : diagonal d * diagonal d = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact hd a
  have hdne : ∀ a, d a ≠ 0 := by
    intro a h0
    have h1 := hd a
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1

  have hleft : diagonal d * bᴴ * diagonal d * b = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc bᴴ, h, hDD]
  letI : Invertible b.det := (Ne.isUnit hb.1).invertible
  letI : Invertible b := Matrix.invertibleOfDetInvertible b
  have hinv : b⁻¹ = diagonal d * bᴴ * diagonal d := Matrix.inv_eq_left_inv hleft

  have hbt : Matrix.BlockTriangular b id := fun i j hij => hb.2 i j hij
  have hbit := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have hup : ∀ a c : Fin n, a < c → b a c = 0 := by
    intro a c hac
    have h0 : b⁻¹ c a = 0 := hbit hac
    rw [hinv, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 (hdne c)
      · exact star_eq_zero.1 h2
    · exact absurd h1 (hdne a)
  have hdiag := eq_diagonal_of_lower_upper_zero b hb.2 hup

  have hh := h
  rw [hdiag, Matrix.diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal] at hh
  have hu : ∀ a, star (b a a) * b a a = 1 := by
    intro a
    have h1 := congrFun (Matrix.diagonal_injective hh) a
    simp only [Pi.star_apply] at h1
    have h2 : d a * (star (b a a) * b a a) = d a * 1 := by linear_combination h1
    exact mul_left_cancel₀ (hdne a) h2
  refine ⟨fun a => Complex.arg (b a a), ?_⟩
  calc b = diagonal fun a => b a a := hdiag
    _ = _ := by
      congr 1
      funext a
      exact eq_exp_arg_mul_I_of_star_mul_self_eq_one _ (hu a)

theorem diag_of_upT_unitary : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ → ∀ b : Mt n, UpT b → x₀ * b * x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm → ∃ s : Fin n → ℝ, b = diagonal fun a => Complex.exp ((s a : ℂ) * Complex.I) := by
  intro n Hm q x₀ hx b hb hu
  obtain ⟨-, hx⟩ := hx
  set d : Fin n → ℂ := fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) with hd_def
  have hd : ∀ a, d a * d a = 1 := by
    intro a
    simp only [hd_def, ReciprocityTheory.ChartRestriction.G.FD.sgn]
    split_ifs <;> norm_num
  have hdet : x₀.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hx
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at h1
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
    intro h2
    have h3 := hd a
    rw [h2, zero_mul] at h3
    exact zero_ne_one h3
  have hu' : (x₀ * b * x₀⁻¹)ᴴ * Hm * (x₀ * b * x₀⁻¹) = Hm := hu
  have hcx : x₀ * b * x₀⁻¹ * x₀ = x₀ * b := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hdet), Matrix.mul_one]

  have key : bᴴ * diagonal d * b = diagonal d := by
    calc bᴴ * diagonal d * b = bᴴ * (x₀ᴴ * Hm * x₀) * b := by rw [hx]
      _ = (x₀ * b)ᴴ * Hm * (x₀ * b) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (x₀ * b * x₀⁻¹ * x₀)ᴴ * Hm * (x₀ * b * x₀⁻¹ * x₀) := by rw [hcx]
      _ = x₀ᴴ * ((x₀ * b * x₀⁻¹)ᴴ * Hm * (x₀ * b * x₀⁻¹)) * x₀ := by
        rw [conjTranspose_mul (x₀ * b * x₀⁻¹) x₀]; simp only [Matrix.mul_assoc]
      _ = diagonal d := by rw [hu', hx]
  exact diag_of_upT_of_preserves d hd b hb key

end GlobalTheory.HolDict
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.ModelRep

section Conj

variable {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_mem (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : P * g * P⁻¹ ∈ UJset ε := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have hg' : gᴴ * G * g = G := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [hG, hg', ← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem conj_mem_inv (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH G := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  show (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G
  calc (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * ((P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)) * g) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by
        rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hg', hG]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isURepOn_conj (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ) :
    IsURepOn (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hσ
  refine ⟨⟨?_, ?_⟩, fun g hg v => hc _ (conj_mem hP hG hg) v, fun v => ?_⟩
  · simpa only [Matrix.mul_one, h1] using ha
  · intro a ha' b hb'
    have e : P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹) := by
      calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = _ := by simp only [Matrix.mul_assoc]
    show σ (P * (a * b) * P⁻¹) = _
    rw [e]
    exact hb _ (conj_mem hP hG ha') _ (conj_mem hP hG hb')
  · have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (hd v).comp hc.continuousOn fun g hg => conj_mem hP hG hg

theorem isIrredOn_conj (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsIrredOn (UJset ε) σ) :
    IsIrredOn (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  intro S hS h
  refine hσ S hS fun g hg v hv => ?_
  have := h _ (conj_mem_inv hP hG hg) v hv
  have e : P * (P⁻¹ * g * P) * P⁻¹ = g := by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h1]; simp
  simpa only [e] using this

theorem arr_injective {q : ℕ} (hq : q ≤ n) : Function.Injective (arr q : Fin n → Fin n) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := a.2
  have := b.2
  apply Fin.ext
  unfold arr at h'
  split_ifs at h' <;> simp only at h' <;> omega

def arrEquiv {q : ℕ} (hq : q ≤ n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (arr q) (Finite.injective_iff_bijective.1 (arr_injective hq))

theorem orth_sub (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (f : Fin n → Fin n) :
    ((P⁻¹).submatrix id f)ᴴ * G * (P⁻¹).submatrix id f = (Formalism.REAL.Jm ε).submatrix f f := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h3 : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  rw [← h3]
  rfl

theorem conj_single (hP : IsUnit P) (e : Fin n ≃ Fin n) (a c : Fin n) :
    (P⁻¹).submatrix id e * Matrix.single a c 1 * ((P⁻¹).submatrix id e)⁻¹ =
      P⁻¹ * Matrix.single (e a) (e c) 1 * P := by
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h3 : ((P⁻¹).submatrix id e)⁻¹ = P.submatrix e id := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.submatrix_mul_equiv, h2]
    rfl
  have h4 : (Matrix.single a c 1 : Matrix (Fin n) (Fin n) ℂ) = (Matrix.single (e a) (e c) 1).submatrix e e := by
    ext i j
    simp [Matrix.single_apply]
  rw [h3, h4, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

end Conj

theorem model_rep : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), CompleteSpace (M.H τ) ∧ IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ (HolShape M → OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) ∧ ∀ a c, x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹ = (M.fr τ)⁻¹ * Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1 * M.fr τ) := by
  intro D V S M τ
  obtain ⟨h1, -, h3, h4, -⟩ := M.ds τ
  refine ⟨h1, isURepOn_conj (M.fr_unit τ) (M.fr_gram τ) h3, isIrredOn_conj (M.fr_unit τ) (M.fr_gram τ) h4, fun hs => ⟨⟨nNeg_le _, ?_⟩, fun a c => ?_⟩⟩
  · obtain ⟨-, p, hp, h⟩ := hs τ
    have := orth_sub (M.fr_unit τ) (M.fr_gram τ) (arr (nNeg (M.ε τ)))
    refine this.trans ?_
    have hinj := arr_injective (nNeg_le (M.ε τ))
    unfold Formalism.REAL.Jm
    rw [Matrix.submatrix_diagonal _ _ hinj]
    congr 1
    funext a
    have := a.2
    simp only [Function.comp, h, nNeg_shape hp h, ReciprocityTheory.ChartRestriction.G.FD.sgn, arr, decide_eq_true_eq]
    split_ifs <;> first | (simp; done) | (exfalso; simp only at *; omega)
  · exact conj_single (M.fr_unit τ) (arrEquiv (nNeg_le (M.ε τ))) a c

end GlobalTheory.HolDict.ModelRep
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
    ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D)
    (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E),
    (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (D := E) (spOver ψ ≫ y) →
      τ E' (θ.comp ψ) = θ (τ E ψ)) →
    ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      Sm W (D := E) (spOver ψ ≫ y) → τ E ψ = ψ d := by
  first | exact @GlobalTheory.PtExt.NatGlue.existsUnique_of_natural | exact GlobalTheory.PtExt.NatGlue.existsUnique_of_natural | (intros; apply GlobalTheory.PtExt.NatGlue.existsUnique_of_natural <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.exists_unique_section_of_natural_pointwise_function
    (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y)
    (ht : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z)) :
    ∃! a : Γ(Y.left, U), ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E),
      ⊤ ≤ z.left ⁻¹ᵁ U → evU (D := E) z.left U a = t E z :=
  GlobalTheory.PtExt.NatSec.exists_unique_section R Y U t ht
end
