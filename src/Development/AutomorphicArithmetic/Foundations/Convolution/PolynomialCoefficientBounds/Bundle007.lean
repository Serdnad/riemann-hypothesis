module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.CoeffL1NormNonneg
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

namespace UpperTheory.ConvolutionTheory.FX

private theorem kill_lift_single {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A)
    (τ : Multiplicative (ι → ℝ) →* A) (v : ι → ℝ) (p : MvPolynomial ι ℂ) :
    PositivityTheory.Rg.Fx.lift x τ (AddMonoidAlgebra.single v p) = aeval x p * τ (Multiplicative.ofAdd v) := by
  simp [PositivityTheory.Rg.Fx.lift]

private theorem kill_ev_X {ι : Type} [Fintype ι] (Λ : ι → ℂ) (i : ι) :
    ev Λ (AddMonoidAlgebra.single 0 (X i)) = Λ i := by
  rw [ev, kill_lift_single]
  simp

private theorem kill_aff_id {ι : Type} [Fintype ι] [DecidableEq ι] (f : EP ι) :
    aff (0 : ι → ℂ) (1 : Matrix ι ι ℝ) f = f := by
  have hx : ∀ p : MvPolynomial ι ℂ,
      aeval (fun i : ι => (AddMonoidAlgebra.single 0
        (C ((0 : ι → ℂ) i) + lin ((1 : Matrix ι ι ℝ) i)) : EP ι)) p = AddMonoidAlgebra.single 0 p := by
    intro p
    have h1 : ∀ i : ι, C ((0 : ι → ℂ) i) + lin ((1 : Matrix ι ι ℝ) i) = (X i : MvPolynomial ι ℂ) := by
      intro i
      simp [lin, Matrix.one_apply, apply_ite]
    simp only [h1]
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add (f := _), hp, hq, AddMonoidAlgebra.single_add]
    | mul_X p i hp => rw [map_mul, hp, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add (f := _), hf, hg]
  | single v p =>
    rw [aff, kill_lift_single, hx]
    simp [affChar, expChar, AddMonoidAlgebra.single_mul_single]

private theorem kill_ren_id {ι : Type} [Fintype ι] [DecidableEq ι] (f : EP ι) :
    ren (id : ι → ι) f = f := by
  have : (Matrix.of fun i j : ι => if id i = j then (1 : ℝ) else 0) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  rw [ren, this, kill_aff_id]

private theorem kill_ren_ren {ι : Type} [Fintype ι] [DecidableEq ι] (δ δ' : ι → ι) (f : EP ι) :
    ren δ' (ren δ f) = ren (δ' ∘ δ) f := by
  rw [ren, ren, ren, (subst ι ι _ _ f).2]
  congr 2
  · funext i
    simp
  · ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (δ i)]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp

private theorem kill_ev_ren {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → ι) (Λ : ι → ℂ) (f : EP ι) :
    ev Λ (ren δ f) = ev (Λ ∘ δ) f := by
  rw [ren, (subst ι ι _ _ f).1]
  congr 2
  funext i
  simp [apply_ite]

private theorem kill_evK_ren {ι κ : Type} [Fintype ι] [DecidableEq ι] (δ : ι → ι) (Λ : ι → ℂ) (h : κ → ℂ)
    (G : KF ι κ) : evK Λ h (map (ren δ) G) = evK (Λ ∘ δ) h G := by
  have : (ev Λ).comp (ren δ) = ev (Λ ∘ δ) := RingHom.ext (kill_ev_ren δ Λ)
  rw [evK, evK, coe_eval₂Hom, coe_eval₂Hom, eval₂_map, this]

private theorem kill_mem_of_ker {ι κ : Type} [Fintype ι] (b : Fam ι κ) (Λ : ι → ℂ) (h : κ → ℂ)
    (H : RingHom.ker b.sub ≤ RingHom.ker (evK Λ h)) : b.Mem Λ h := by
  classical
  let Λ₁ : Fin b.r → ℂ := fun j => - ∑ i, (b.pr j i : ℂ) * b.Λ i
  let lam : Fin b.r → ℂ := fun j => Λ₁ j + ∑ i, (b.pr j i : ℂ) * Λ i
  have hret : ∀ y : EP (Fin b.r), aff b.Λ b.emb (aff Λ₁ b.pr y) = y := by
    intro y
    rw [(subst _ _ _ _ y).2, b.pr_emb]
    have : (fun j => Λ₁ j + ∑ i, (b.pr j i : ℂ) * b.Λ i) = 0 := by
      funext j
      simp [Λ₁]
    rw [this, kill_aff_id]
  have key : ∀ F : KF ι κ, evK Λ h F = ev lam (b.sub F) := by
    intro F
    have h1 : F - C (aff Λ₁ b.pr (b.sub F)) ∈ RingHom.ker b.sub := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      generalize b.sub F = y
      rw [Fam.sub, eval₂Hom_C, hret]
    have h2 := H h1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    rw [h2, evK, eval₂Hom_C, (subst _ _ _ _ _).1]
  refine ⟨lam, fun i => ?_, fun k => ?_⟩
  · have := key (C (AddMonoidAlgebra.single 0 (X i)))
    rw [evK, Fam.sub, eval₂Hom_C, eval₂Hom_C, (subst _ _ _ _ _).1, kill_ev_X, kill_ev_X] at this
    exact this
  · have := key (X k)
    rw [evK, Fam.sub, eval₂Hom_X', eval₂Hom_X'] at this
    exact this

end UpperTheory.ConvolutionTheory.FX

open UpperTheory.ConvolutionTheory.FX in
theorem UpperTheory.ConvolutionTheory.FX.killing0 :
    ∀ (ι κ B : Type) [Fintype ι] [DecidableEq ι] [Fintype B] (W : Subgroup (Equiv.Perm ι)) (b : B → Fam ι κ) (Λ₀ : ι → ℂ) (h₀ : κ → ℂ), (∀ w ∈ W, ∀ i, ¬ (b i).Mem (Λ₀ ∘ w) h₀) → ∃ F : KF ι κ, (∀ w ∈ W, map (ren (w : ι → ι)) F = F) ∧ (∀ i, (b i).sub F = 0) ∧ evK Λ₀ h₀ F ≠ 0 := by
  intro ι κ B _ _ _ W b Λ₀ h₀ hW
  classical
  haveI : Fintype W := Fintype.ofFinite W
  have hG : ∀ i, ∃ G : KF ι κ, (b i).sub G = 0 ∧ ∀ w : W, evK (Λ₀ ∘ (w : Equiv.Perm ι)) h₀ G ≠ 0 := by
    intro i
    by_contra hc
    push Not at hc
    have hsub : ((RingHom.ker (b i).sub : Ideal (KF ι κ)) : Set (KF ι κ)) ⊆
        ⋃ w ∈ (↑(Finset.univ : Finset W) : Set W),
          ((RingHom.ker (evK (Λ₀ ∘ (w : Equiv.Perm ι)) h₀) : Ideal (KF ι κ)) : Set (KF ι κ)) := by
      intro G hG
      obtain ⟨w, hw⟩ := hc G hG
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ w)) hw
    obtain ⟨w, -, hw⟩ := (Ideal.subset_union_prime (1 : W) 1
      (fun w _ _ _ => RingHom.ker_isPrime _)).1 hsub
    exact hW w w.2 i (kill_mem_of_ker _ _ _ hw)
  choose G hG0 hG1 using hG
  refine ⟨∏ i, ∏ w : W, map (ren ((w : Equiv.Perm ι) : ι → ι)) (G i), ?_, ?_, ?_⟩
  · intro w' hw'
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨w', hw'⟩ : W)) _ _ fun w => ?_
    have hc : (ren (w' : ι → ι)).comp (ren ((w : Equiv.Perm ι) : ι → ι)) =
        ren (((w' * (w : Equiv.Perm ι) : Equiv.Perm ι)) : ι → ι) := by
      rw [Equiv.Perm.coe_mul]
      exact RingHom.ext fun f => by rw [RingHom.comp_apply, kill_ren_ren]
    rw [MvPolynomial.map_map, hc, Equiv.coe_mulLeft, Subgroup.coe_mul]
  · intro i
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ (1 : W)) ?_
    have : ren (((1 : W) : Equiv.Perm ι) : ι → ι) = RingHom.id _ := by
      rw [Subgroup.coe_one, Equiv.Perm.coe_one]
      exact RingHom.ext fun f => by rw [kill_ren_id, RingHom.id_apply]
    rw [this, MvPolynomial.map_id, hG0]
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    rw [kill_evK_ren]
    exact hG1 i w
end

section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.sub_eq_zero_iff :
    ∀ (ι κ : Type) [Fintype ι] (b : Fam ι κ) (F : KF ι κ), b.sub F = 0 ↔ ∀ Λ h, b.Mem Λ h → evK Λ h F = 0 := by
  intro ι κ _ b F
  have key : ∀ lam : Fin b.r → ℂ, ev lam (b.sub F) =
      evK (fun i => b.Λ i + ∑ j, (b.emb i j : ℂ) * lam j) (fun k => ev lam (b.h k)) F := fun lam => by
    have : (ev lam).comp b.sub = evK (fun i => b.Λ i + ∑ j, (b.emb i j : ℂ) * lam j) (fun k => ev lam (b.h k)) :=
      MvPolynomial.ringHom_ext (fun f => by
        simpa [Fam.sub, evK] using (UpperTheory.ConvolutionTheory.FX.subst ι _ b.Λ b.emb f).1 lam) (fun k => by simp [Fam.sub, evK])
    exact RingHom.congr_fun this F
  refine ⟨fun h0 Λ h ⟨lam, h1, h2⟩ => ?_, fun h => UpperTheory.ConvolutionTheory.FX.ev_inj _ _ fun lam => ?_⟩
  · rw [funext h1, funext h2, ← key, h0, map_zero]
  · rw [key]
    exact h _ _ ⟨lam, fun _ => rfl, fun _ => rfl⟩
end

section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.gen_pieces :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ) (f : EP (τ × Fin n)), (∀ w : τ → Equiv.Perm (Fin n), ren (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) f = f) → ∃ (K : ℝ) (G : ℕ → MvPolynomial (τ × Fin n) ℂ), ∀ k, aeval blockE (G k) = piece k f ∧ (G k).totalDegree ≤ k ∧ l1 (G k) ≤ K ^ (k + 1) / k.factorial := by
  intro τ _ _ n f hf
  have hgen : Generators := UpperTheory.ConvolutionTheory.FX.generators0
  obtain ⟨K₁, hK₁⟩ := hgen τ n
  obtain ⟨K₂, hK₂⟩ := UpperTheory.ConvolutionTheory.FX.piece_size (τ × Fin n) f
  have h : ∀ k, ∃ G : MvPolynomial (τ × Fin n) ℂ, aeval blockE G = piece k f ∧ G.totalDegree ≤ k ∧
      l1 G ≤ K₁ ^ (k + 1) * l1 (piece k f) := fun k =>
    hK₁ k (piece k f) (UpperTheory.ConvolutionTheory.FX.piece_hom _ f k).totalDegree_le
      (fun w => by rw [← UpperTheory.ConvolutionTheory.FX.piece_ren, hf w])
  choose G hG using h
  refine ⟨|K₁| * K₂, G, fun k => ⟨(hG k).1, (hG k).2.1, ?_⟩⟩
  have h0 : 0 ≤ l1 (piece k f) := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc l1 (G k) ≤ K₁ ^ (k + 1) * l1 (piece k f) := (hG k).2.2
    _ ≤ |K₁| ^ (k + 1) * l1 (piece k f) := by
        refine mul_le_mul_of_nonneg_right ?_ h0
        rw [← abs_pow]; exact le_abs_self _
    _ ≤ |K₁| ^ (k + 1) * (K₂ ^ (k + 1) / k.factorial) :=
        mul_le_mul_of_nonneg_left (hK₂ k) (by positivity)
    _ = (|K₁| * K₂) ^ (k + 1) / k.factorial := by rw [mul_pow]; ring
end
