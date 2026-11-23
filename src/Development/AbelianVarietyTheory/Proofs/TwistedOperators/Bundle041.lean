module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle033
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Formalism.RealPlaceAnalysis.Bundle002
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx.RowSupport
open GlobalTheory.RootEx.ExchangeSupport

theorem exists_box {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (W : Set (n → k)) (hW : W ∈ 𝓝 (0 : n → k)) :
    ∃ B : Set (n → k), IsCompact B ∧ ∀ u, u ∉ B → ∃ β ∈ W, ψ (u ⬝ᵥ β) ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (AddChar.map_zero_eq_one ψ)
  have hU : ∀ s : n, {x : k | (Pi.single s x : n → k) ∈ W} ∈ 𝓝 (0 : k) := by
    intro s
    have hcont : Continuous fun x : k => (Pi.single s x : n → k) := by
      refine continuous_pi fun j => ?_
      simp only [Pi.single_apply]
      split_ifs
      · exact continuous_id
      · exact continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp (Filter.iInter_mem.mpr hU)
  refine ⟨Set.univ.pi fun _ => {x : k | valuation k x ≤ valuation k a / (γ : ValueGroupWithZero k)},
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _, ?_⟩
  intro u hu
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, not_forall, not_le] at hu
  obtain ⟨s, hs⟩ := hu
  have hus : u s ≠ 0 := by
    intro h
    rw [h, map_zero] at hs
    exact not_lt.mpr zero_le hs
  have hv : 0 < valuation k (u s) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hus
  refine ⟨Pi.single s (a / u s), ?_, ?_⟩
  · have hsmall : valuation k (a / u s) < γ := by
      rw [map_div₀, div_lt_iff₀ hv]
      have hg : (0 : ValueGroupWithZero k) < γ := by
        rw [zero_lt_iff]
        exact γ.ne_zero
      rw [div_lt_iff₀ hg] at hs
      simpa [mul_comm] using hs
    exact Set.mem_iInter.mp (hγ hsmall) s
  · rw [dotProduct_single, mul_div_cancel₀ _ hus]
    exact ha

theorem row_support_uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : ψ ≠ 1) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (F : A) (Ω : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact Ω), ∃ B : Set (n → k), IsCompact B ∧ ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ p σ l → ∀ w ∈ Ω, ∀ u, u ∉ B → l (σ (rowE c p u) (σ w F)) = 0 := by
  intro k _ _ _ _ n _ _ c p hp hc ψ hψ A _ _ σ hσ F Ω hΩ
  set S : Set (GL (n ⊕ Fin c) k) := {g | σ g F = F} with hSdef
  have hS : IsOpen S := hσ F
  have hcol : Continuous fun β : n → k => colE (k := k) c (p + 1) β :=
    ExchangeSupport.continuous_colE
  have hfix : ∀ᶠ β in 𝓝 (0 : n → k), ∀ w ∈ Ω, σ (colE c (p + 1) β) (σ w F) = σ w F := by
    refine hΩ.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc2 : Continuous fun z : (n → k) × GL (n ⊕ Fin c) k => z.2⁻¹ * colE c (p + 1) z.1 * z.2 :=
      ((continuous_snd.inv).mul (hcol.comp continuous_fst)).mul continuous_snd
    have hmem : ((0 : n → k), w).2⁻¹ * colE c (p + 1) ((0 : n → k), w).1 * ((0 : n → k), w).2 ∈ S := by
      simp [hSdef, ExchangeSupport.colE_zero]
    filter_upwards [hc2.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with z hz
    have hz' : σ (z.2⁻¹ * colE c (p + 1) z.1 * z.2) F = F := hz
    calc σ (colE c (p + 1) z.1) (σ z.2 F)
        = σ (z.2 * (z.2⁻¹ * colE c (p + 1) z.1 * z.2)) F := by
          rw [map_mul σ z.2, Module.End.mul_apply, map_mul, map_mul, Module.End.mul_apply,
            Module.End.mul_apply]
          rw [← Module.End.mul_apply (σ z.2), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = σ z.2 F := by rw [map_mul, Module.End.mul_apply, hz']
  obtain ⟨B, hB, hBout⟩ := exists_box hψ {β | ∀ w ∈ Ω, σ (colE c (p + 1) β) (σ w F) = σ w F} hfix
  refine ⟨B, hB, fun l hl w hw u hu => ?_⟩
  obtain ⟨β, hβ, hne⟩ := hBout u hu
  obtain ⟨hN, hsum⟩ := ExchangeSupport.conj_col (k := k) (n := n) hp hc u β
  have key := hl _ hN (σ (rowE c p u) (σ w F))
  rw [hsum] at key
  have lhs : σ (rowE c p u * colE c (p + 1) β * (rowE c p u)⁻¹) (σ (rowE c p u) (σ w F)) =
      σ (rowE c p u) (σ w F) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hβ w hw]
  rw [lhs] at key
  have hne' : (ψ (u ⬝ᵥ β) : ℂ) ≠ 1 := by
    intro h
    exact hne (Subtype.ext (by simpa using h))
  have : (1 - (ψ (u ⬝ᵥ β) : ℂ)) * l (σ (rowE c p u) (σ w F)) = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne'
  · exact h

end GlobalTheory.RootEx.RowSupport
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.ColumnSupport

theorem colE_inv_mul_affPt {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n]
    {c p : ℕ} (hp : p < c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (p + 1) rs} → k) (r : n) :
    (((colE c (p + 1) β)⁻¹).val * affPt (p + 1) x₀ e) (Sum.inl r) (Sum.inr ⟨p, by omega⟩) = -β r := by
  have hv : ((colE c (p + 1) β)⁻¹).val =
      fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p + 1 then β r else 0)) 0 1 := rfl
  have h1 : ∀ s : n, affPt (p + 1) x₀ e (Sum.inl s) (Sum.inr ⟨p, by omega⟩) = 0 := by
    intro s
    simp [affPt, basePt, Free]
  have h2 : affPt (p + 1) x₀ e (Sum.inr ⟨p, hp⟩) (Sum.inr ⟨p, by omega⟩) = 1 := by
    simp [affPt, basePt, Free]
  rw [hv, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [h1, mul_zero, Finset.sum_const_zero, zero_add, fromBlocks_apply₁₂]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : Fin c)]
  · simp [h2]
  · intro j _ hj
    have : j.val ≠ p := fun e => hj (Fin.ext e)
    simp [this]
  · simp


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.RootEx.ColumnSupport.opE_colE_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : p < c) (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ), ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∃ K : Set (n → k), IsCompact K ∧ ∀ β, β ∉ K → ∀ χ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => χ y * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.colE c (p + 1) β) Φ y) = 0 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp ψ ν μ Φ hΦ
  have hcs : HasCompactSupport Φ := (show IsLocallyConstant Φ ∧ HasCompactSupport Φ from hΦ).2
  let q : Fin (c + 1) := ⟨p, by omega⟩
  refine ⟨(fun z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => fun r => -z (Sum.inl r) (Sum.inr q)) '' tsupport Φ,
    hcs.isCompact.image (continuous_pi fun r => (continuous_apply_apply _ _).neg), ?_⟩
  intro β hβ χ
  funext x
  unfold _root_.GlobalTheory.RootEx.opE
  refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
  have hentry : ∀ r, ((((_root_.GlobalTheory.RootEx.colE c (p + 1) β)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x e) (Sum.inl r) (Sum.inr q) = -β r := by
    intro r
    rw [_root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp [q, Matrix.mul_apply, Fintype.sum_sum_type, _root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, _root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.RootEx.ExchangeSupport.colM, Matrix.one_apply]
    rw [Finset.sum_eq_single ⟨p, hp⟩ (fun b _ hb => if_neg (fun h => hb (Fin.ext h))) (by simp)]
    simp
  have hzero : Φ ((((_root_.GlobalTheory.RootEx.colE c (p + 1) β)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x e * ((1 : GL (n' ⊕ Fin (c + 1)) k) : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) = 0 := by
    by_contra h
    apply hβ
    refine ⟨_, subset_tsupport _ h, ?_⟩
    funext r
    simp only [Units.val_one, Matrix.mul_one]
    rw [hentry r, neg_neg]
  unfold _root_.GlobalTheory.SplitWeil.om
  simp only [Pi.zero_apply]
  rw [hzero]
  simp

end GlobalTheory.RootEx.ColumnSupport
end
end

section

open MeasureTheory

namespace GlobalTheory.FockFamily

theorem fock_vacua_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  intro V _ _ _ β hβ J hJ _ hex
  choose g0 hg0ne hg0 using hex
  have hunit : ∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t)) := fun t =>
    GlobalTheory.T.isUnit_upperRightBlock_of_heisenbergDerivative_solution β hβ (J t) (g0 t) (g0 t).continuous (fun h => hg0ne t (SchwartzMap.ext (fun x => congrFun h x))) (hg0 t)
  obtain ⟨hB, hD⟩ := GlobalTheory.T.contDiff_prodLinearMap_upperRight_lowerRight_blocks J hJ
  obtain ⟨hsm, hjoint⟩ := GlobalTheory.T.contDiff_fockGaussianFormOfLinearMap_family β J hB hD hunit
  have hray : ∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x =
      Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) → ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β (J t) x x) :=
    fun t g hg => GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq β (J t) (hunit t) g g.differentiable hg
  refine ⟨fun t => GlobalTheory.FockFamily.fockForm β (J t), hsm, hjoint, ?_, hray, ?_⟩
  · exact GlobalTheory.T.uniformly_negDefinite_near_of_continuous_quadForm_family (fun t => GlobalTheory.FockFamily.fockForm β (J t)) hjoint.continuous
      (fun t v hv => GlobalTheory.T.gaussian_form_re_neg_of_ne_zero _ (g0 t) (hg0ne t) (hray t (g0 t) (hg0 t)) v hv)
  · exact GlobalTheory.T.exists_hasDerivAt_diag_eq_sum_mul_pairings β hβ _ (fun x y => ((hsm x y).differentiable (by simp)).differentiableAt)

end GlobalTheory.FockFamily
end

section

open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem tens_maxStab_contains_left_ker : ∀ {M₀ V : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup V] [Module ℂ V]
    (Op₀ : Set (Module.End ℂ M₀)) (B : Set (Module.End ℂ V)) (Rel₀ K₀ : Submodule ℂ M₀),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → GlobalTheory.TensHead.Stab Op₀ N → N ≠ ⊤ → N ≤ K₀) →
    K₀ ≠ ⊤ → GlobalTheory.TensHead.Stab Op₀ K₀ →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] V),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N') → GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) U → N' ≤ U → U = N' ∨ U = ⊤) →
      ∀ x ∈ K₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N' := by
  classical
  intro M₀ V _ _ _ _ Op₀ B Rel₀ K₀ hlen hmax hK hKs N' hrel hN'st hN'max x hx y

  let act : Module.End ℂ M₀ → Module.End ℂ ((M₀ ⊗[ℂ] V) ⧸ N') := fun g =>
    if hs : N' ≤ N'.comap (TensorProduct.map g LinearMap.id) then
      N'.mapQ N' (TensorProduct.map g LinearMap.id) hs else 0
  let bAct : Module.End ℂ V → Module.End ℂ ((M₀ ⊗[ℂ] V) ⧸ N') := fun h =>
    if hs : N' ≤ N'.comap (TensorProduct.map LinearMap.id h) then
      N'.mapQ N' (TensorProduct.map LinearMap.id h) hs else 0
  have hsg : ∀ g ∈ Op₀, N' ≤ N'.comap (TensorProduct.map g LinearMap.id) := by
    intro g hg z hz
    exact hN'st _ (Or.inl ⟨g, hg, rfl⟩) z hz
  have hsh : ∀ h ∈ B, N' ≤ N'.comap (TensorProduct.map LinearMap.id h) := by
    intro h hh z hz
    exact hN'st _ (Or.inr ⟨h, hh, rfl⟩) z hz
  have hactg : ∀ g ∈ Op₀, ∀ z, act g (N'.mkQ z) = N'.mkQ (TensorProduct.map g LinearMap.id z) := by
    intro g hg z
    simp only [act, dif_pos (hsg g hg), Submodule.mapQ_apply, Submodule.mkQ_apply]
  have hbacth : ∀ h ∈ B, ∀ z, bAct h (N'.mkQ z) = N'.mkQ (TensorProduct.map LinearMap.id h z) := by
    intro h hh z
    simp only [bAct, dif_pos (hsh h hh), Submodule.mapQ_apply, Submodule.mkQ_apply]
  let φ : M₀ →ₗ[ℂ] (M₀ ⊗[ℂ] V) ⧸ N' := N'.mkQ ∘ₗ (TensorProduct.mk ℂ M₀ V).flip y
  have hφ : ∀ x, φ x = N'.mkQ (x ⊗ₜ[ℂ] y) := fun x => rfl
  have key := GlobalTheory.T.le_ker_of_local_finite_length_to_simple Op₀ Rel₀ K₀ φ act (bAct '' B) hlen hmax hK hKs
    (by
      intro z hz
      rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hrel z hz y)
    (by
      intro g hg
      ext z
      simp only [LinearMap.comp_apply, hφ, hactg g hg, TensorProduct.map_tmul, LinearMap.id_apply])
    (by
      rintro g hg b ⟨h, hh, rfl⟩
      apply Submodule.linearMap_qext
      apply TensorProduct.ext'
      intro u v
      simp only [LinearMap.comp_apply, Module.End.mul_apply, hactg g hg, hbacth h hh,
        TensorProduct.map_tmul, LinearMap.id_apply])
    (by
      intro U hU
      have hP : Stab (tensOps Op₀ B) (U.comap N'.mkQ) := by
        rintro f (⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩) z hz
        · rw [Submodule.mem_comap] at hz ⊢
          rw [← hactg g hg]
          exact hU _ (Or.inl ⟨g, hg, rfl⟩) _ hz
        · rw [Submodule.mem_comap] at hz ⊢
          rw [← hbacth h hh]
          exact hU _ (Or.inr ⟨h, hh, rfl⟩) _ hz
      have hle : N' ≤ U.comap N'.mkQ := by
        intro z hz
        rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N').2 hz]
        exact U.zero_mem
      have hsurj : Function.Surjective N'.mkQ := Submodule.mkQ_surjective N'
      rcases hN'max _ hP hle with h1 | h1
      · left
        rw [← Submodule.map_comap_eq_of_surjective hsurj U, h1, Submodule.mkQ_map_self]
      · right
        rw [← Submodule.map_comap_eq_of_surjective hsurj U, h1, Submodule.map_top,
          LinearMap.range_eq_top.2 hsurj])
  have := key hx
  rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  exact this

end GlobalTheory.TensHead
end

section

open scoped TensorProduct

namespace GlobalTheory.TensHead

def quotOps {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) : Set (Module.End ℂ (V ⧸ K)) :=
  {f | ∃ g ∈ G, f ∘ₗ K.mkQ = K.mkQ ∘ₗ g}

theorem quot_simple {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) (hs : Stab G K) (hK : SimpleOver G K) :
    ∀ U : Submodule ℂ (V ⧸ K), Stab (quotOps G K) U → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  have hst : Stab G (U.comap K.mkQ) := by
    intro g hg x hx
    have hf : (K.mapQ K g (fun y hy => hs g hg y hy)) ∘ₗ K.mkQ = K.mkQ ∘ₗ g := by
      ext y; simp
    have := hU _ ⟨g, hg, hf⟩ _ hx
    simpa using this
  have hle : K ≤ U.comap K.mkQ := by
    intro x hx; simp [(Submodule.Quotient.mk_eq_zero K).2 hx]
  rcases hK _ hst hle with h | h
  · left
    rw [← Submodule.map_comap_eq_of_surjective K.mkQ_surjective U, h, Submodule.mkQ_map_self]
  · right
    rw [← Submodule.map_comap_eq_of_surjective K.mkQ_surjective U, h, Submodule.map_top,
      LinearMap.range_eq_top.2 K.mkQ_surjective]

theorem ker_map_mkQ_le {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁]
    [Module ℂ V₁] (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁) :
    LinearMap.ker (TensorProduct.map K₀.mkQ K₁.mkQ) ≤ tensKer K₀ K₁ := by
  rw [TensorProduct.map_ker (LinearMap.exact_subtype_mkQ K₀) K₀.mkQ_surjective
    (LinearMap.exact_subtype_mkQ K₁) K₁.mkQ_surjective]
  refine sup_le ?_ ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul x k => exact Submodule.subset_span ⟨x, k, Or.inr k.2, by simp⟩
    | add a b ha hb => simpa only [map_add] using add_mem ha hb
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul k y => exact Submodule.subset_span ⟨k, y, Or.inl k.2, by simp⟩
    | add a b ha hb => simpa only [map_add] using add_mem ha hb

theorem simpleOver_tensKer : ∀ {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁),
    Module.rank ℂ V₀ ≤ Cardinal.aleph0 → GlobalTheory.TensHead.Stab A K₀ → GlobalTheory.TensHead.Stab B K₁ →
    GlobalTheory.TensHead.SimpleOver A K₀ → GlobalTheory.TensHead.SimpleOver B K₁ →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.tensOps A B) (GlobalTheory.TensHead.tensKer K₀ K₁) := by
  intro V₀ V₁ _ _ _ _ A B K₀ K₁ hr hA hB hsA hsB N hN hKN
  set φ := TensorProduct.map K₀.mkQ K₁.mkQ with hφ
  have hker : LinearMap.ker φ ≤ N := (ker_map_mkQ_le K₀ K₁).trans hKN
  have hstU : Stab (tensOps (quotOps A K₀) (quotOps B K₁)) (N.map φ) := by
    rintro f hf _ ⟨x, hx, rfl⟩
    rcases hf with ⟨f', ⟨g, hg, hfg⟩, rfl⟩ | ⟨f', ⟨g, hg, hfg⟩, rfl⟩
    · have hc : TensorProduct.map f' LinearMap.id ∘ₗ φ = φ ∘ₗ TensorProduct.map g LinearMap.id := by
        rw [hφ, ← TensorProduct.map_comp, ← TensorProduct.map_comp, hfg]; rfl
      refine ⟨TensorProduct.map g LinearMap.id x, hN _ (Or.inl ⟨g, hg, rfl⟩) x hx, ?_⟩
      exact (LinearMap.congr_fun hc x).symm
    · have hc : TensorProduct.map LinearMap.id f' ∘ₗ φ = φ ∘ₗ TensorProduct.map LinearMap.id g := by
        rw [hφ, ← TensorProduct.map_comp, ← TensorProduct.map_comp, hfg]; rfl
      refine ⟨TensorProduct.map LinearMap.id g x, hN _ (Or.inr ⟨g, hg, rfl⟩) x hx, ?_⟩
      exact (LinearMap.congr_fun hc x).symm
  rcases GlobalTheory.T.simple_tensor_product_operatorStable_countable (quotOps A K₀) (quotOps B K₁) ((rank_quotient_le K₀).trans hr)
    (quot_simple A K₀ hA hsA) (quot_simple B K₁ hB hsB) _ hstU with h | h
  · left
    refine le_antisymm ?_ hKN
    intro x hx
    apply ker_map_mkQ_le K₀ K₁
    rw [LinearMap.mem_ker, ← Submodule.mem_bot ℂ, ← h]
    exact Submodule.mem_map_of_mem hx
  · right
    rw [eq_top_iff]
    intro x _
    have : φ x ∈ N.map φ := h ▸ Submodule.mem_top
    obtain ⟨y, hy, hxy⟩ := this
    have : x - y ∈ LinearMap.ker φ := by simp [hxy]
    simpa using add_mem (hker this) hy

end GlobalTheory.TensHead
end

section

noncomputable section

open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

theorem phase_eq_eChar (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) :
    phase w x = GlobalTheory.Published.Metaplectic.eChar (⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2) := by
  rw [GlobalTheory.Published.Metaplectic.eChar_apply, phase]
  congr 1
  push_cast
  ring

theorem hasTemperateGrowth_phase' (w : l ⊕ l → ℝ) : Function.HasTemperateGrowth (phase w) := by
  have h1 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ :=
    (innerSL ℝ (qPart w)).hasTemperateGrowth
  have h := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (h1.add (Function.HasTemperateGrowth.const
    (⟪pPart w, qPart w⟫ / 2)))
  have e : phase w = (GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘
      ((fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫) + fun _ => ⟪pPart w, qPart w⟫ / 2) := by
    funext x
    simp [phase_eq_eChar]
  rw [e]
  exact h

def rhoSch (w : l ⊕ l → ℝ) : Sch l →L[ℂ] Sch l :=
  SchwartzMap.smulLeftCLM ℂ (phase w) ∘L SchwartzMap.compSubConstCLM ℂ (-pPart w)

theorem coe_rhoSch (w : l ⊕ l → ℝ) (f : Sch l) : ⇑(rhoSch w f) = rhoFun w ⇑f := by
  funext x
  rw [rhoSch, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase' w),
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul, rhoFun]

theorem exists_schwartz_rhoFun : ∀ (l : Type) [Fintype l] (w : l ⊕ l → ℝ) (f : Sch l), ∃ f₁ : Sch l, ⇑f₁ = rhoFun w ⇑f :=
  fun _ _ w f => ⟨rhoSch w f, coe_rhoSch w f⟩

end GlobalTheory.RealWeil
end
end

section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix : ∀ {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → ∀ k : ℕ, Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  first | exact @GlobalTheory.etr_conj_scalar_matrix | exact GlobalTheory.etr_conj_scalar_matrix | (intros; apply GlobalTheory.etr_conj_scalar_matrix <;> assumption)
end

section


theorem _root_.GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq : ∀ {ι κ : Type} [Fintype ι] {X : ι → Type} (V : ∀ l, Submodule ℂ (X l → ℂ))
    (Φ : (∀ l, V l) →ₘₗ[ℂ] ℂ) (a : κ →₀ ℂ) (f g : κ → ∀ l, V l),
    (∀ z : ∀ l, X l, (a.sum fun c b => b * ∏ l, (f c l : X l → ℂ) (z l)) = a.sum fun c b => b * ∏ l, (g c l : X l → ℂ) (z l)) →
    (a.sum fun c b => b * Φ (f c)) = a.sum fun c b => b * Φ (g c) := by
  exact @GlobalTheory.multilinear_sum_eq_of_prod_fun_eq
end
