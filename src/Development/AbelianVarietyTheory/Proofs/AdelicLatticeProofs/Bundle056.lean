module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle040
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle055
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsPrimeDegree
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
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.FibreDescent

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def rtr (g : Matrix ι ι ℂ) : MvPolynomial (ι × ι) ℂ →ₐ[ℂ] MvPolynomial (ι × ι) ℂ :=
  MvPolynomial.aeval fun ij : ι × ι => ∑ k, g k ij.2 • MvPolynomial.X (ij.1, k)

omit [Fintype ι] [DecidableEq ι] in
lemma evC_add (p q : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (p + q) y = evC p y + evC q y := by
  simp [evC]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_mul (p q : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (p * q) y = evC p y * evC q y := by
  simp [evC]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_smul (c : ℂ) (p : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (c • p) y = c * evC p y := by
  simp [evC, MvPolynomial.smul_eval]

omit [DecidableEq ι] in
lemma evC_rtr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (rtr g f) y = evC f (y * g) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, rtr]
  | add p q hp hq => rw [map_add (f := _), evC_add, evC_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, evC_mul, evC_mul, hp]
    congr 1
    simp [evC, rtr, Matrix.mul_apply, MvPolynomial.smul_eval, mul_comm]

omit [DecidableEq ι] in
lemma evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq => rw [map_add (f := _), evC_add, evC_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, evC_mul, evC_mul, hp]
    congr 1
    simp [evC, ltr, Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_map (p : MvPolynomial (ι × ι) ℚ) (y : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) p) y = ev p y := by
  rw [evC, ev, MvPolynomial.eval_map, MvPolynomial.aeval_def]


omit [DecidableEq ι] in
lemma exists_fg_rtr (f : MvPolynomial (ι × ι) ℂ) :
    ∃ V : Submodule ℂ (MvPolynomial (ι × ι) ℂ), V.FG ∧ ∀ g, rtr g f ∈ V := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Submodule.span ℂ {MvPolynomial.C a}, Submodule.fg_span (Set.finite_singleton _), fun g => ?_⟩
    apply Submodule.subset_span
    simp [rtr]
  | add p q hp hq =>
    obtain ⟨V, hV, h⟩ := hp
    obtain ⟨V', hV', h'⟩ := hq
    refine ⟨V ⊔ V', hV.sup hV', fun g => ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h g) (h' g)
  | mul_X p ij hp =>
    obtain ⟨V, hV, h⟩ := hp
    refine ⟨V * Submodule.span ℂ (Set.range MvPolynomial.X),
      hV.mul (Submodule.fg_span (Set.finite_range _)), fun g => ?_⟩
    rw [map_mul]
    refine Submodule.mul_mem_mul (h g) ?_
    rw [rtr, MvPolynomial.aeval_X]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)


omit [DecidableEq ι] in
lemma exists_finset_rtr (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    ∃ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ p ∈ s, ∃ g ∈ Γ, p = rtr g f) ∧
      ∀ g ∈ Γ, rtr g f ∈ Submodule.span ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
  obtain ⟨V, hV, h⟩ := exists_fg_rtr f
  have hle : Submodule.span ℂ ((fun g => rtr g f) '' Γ) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨g, -, rfl⟩
    exact h g
  have hfg : (Submodule.span ℂ ((fun g => rtr g f) '' Γ)).FG := by
    have : Module.Finite ℂ V := Module.Finite.iff_fg.2 hV
    exact Module.Finite.iff_fg.1 (Submodule.finiteDimensional_of_le hle)
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  refine ⟨s, fun p hp => ?_, fun g hg => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := hs hp
    exact ⟨g, hg, rfl⟩
  · rw [← hspan]
    exact Submodule.subset_span ⟨g, hg, rfl⟩

def multIdeal (Γ : Set (Matrix ι ι ℂ)) (π : Matrix ι ι ℂ → Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    Ideal (MvPolynomial (ι × ι) ℂ) where
  carrier := {b | ∀ g ∈ Γ, ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ,
    evC b (π x) * evC f (x * g) = evC b' (π x)}
  zero_mem' := fun g _ => ⟨0, fun x _ => by simp [evC]⟩
  add_mem' := by
    intro a b ha hb g hg
    obtain ⟨a', ha'⟩ := ha g hg
    obtain ⟨b', hb'⟩ := hb g hg
    exact ⟨a' + b', fun x hx => by rw [evC_add, evC_add, add_mul, ha' x hx, hb' x hx]⟩
  smul_mem' := by
    intro c b hb g hg
    obtain ⟨b', hb'⟩ := hb g hg
    exact ⟨c * b', fun x hx => by rw [smul_eq_mul, evC_mul, evC_mul, mul_assoc, hb' x hx]⟩

omit [DecidableEq ι] in
lemma exists_common_zero (D : Ideal (MvPolynomial (ι × ι) ℂ)) (hD : D ≠ ⊤) :
    ∃ z : Matrix ι ι ℂ, ∀ b ∈ D, evC b z = 0 := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal D hD
  obtain ⟨x, rfl⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  refine ⟨Matrix.of fun i j => x (i, j), fun b hb => ?_⟩
  have := (MvPolynomial.mem_vanishingIdeal_singleton_iff _ _).1 (hle hb)
  simpa [evC, MvPolynomial.aeval_eq_eval] using this

end GlobalTheory.ClassFin.FibreDescent


open GlobalTheory.ClassFin.FibreDescent in
theorem GlobalTheory.ClassFin.exists_evC_blk_of_fibre_const : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC f x = evC b (blk e x) := by
  intro ι _ _ Γ e hΓ he htri f hf
  have hmul : ∀ x ∈ Γ, ∀ y ∈ Γ, blk e (x * y) = blk e x * blk e y := fun x hx y hy =>
    ((GlobalTheory.ClassFin.blk_mul_of_triangular ι e ℂ he).2.1 x y (htri x hx) (htri y hy)).1
  have hpre : IsPre (blk e '' Γ) := GlobalTheory.ClassFin.isPre_blk_image ι Γ e hΓ.toIsPre he htri
  obtain ⟨-, hm, hadj, hdet⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι _ hpre ℂ
  obtain ⟨s, hs, hspan⟩ := exists_finset_rtr Γ f
  obtain ⟨b₀, ⟨x₀, hx₀, hb₀⟩, hb⟩ := GlobalTheory.T.exists_multiplier_descend_blockDiagPartOfRatIdempotent ι Γ e hΓ.closed ⟨1, hΓ.one_mem⟩ s (by
    intro p hp x hx x' hx' hxx
    obtain ⟨g, hg, rfl⟩ := hs p hp
    rw [evC_rtr, evC_rtr]
    exact hf _ (hΓ.mul_mem _ hx _ hg) _ (hΓ.mul_mem _ hx' _ hg)
      (by rw [hmul _ hx _ hg, hmul _ hx' _ hg, hxx]))
  have hb₀D : b₀ ∈ multIdeal Γ (blk e) f := by
    intro g hg
    have key : ∀ p ∈ Submodule.span ℂ (s : Set (MvPolynomial (ι × ι) ℂ)),
        ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC b₀ (blk e x) * evC p x = evC b' (blk e x) := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem p hp => exact hb p hp
      | zero => exact ⟨0, fun x _ => by simp [evC]⟩
      | add p q _ _ hp hq =>
        obtain ⟨a', ha'⟩ := hp
        obtain ⟨b', hb'⟩ := hq
        exact ⟨a' + b', fun x hx => by rw [evC_add, evC_add, mul_add, ha' x hx, hb' x hx]⟩
      | smul c p _ hp =>
        obtain ⟨a', ha'⟩ := hp
        exact ⟨c • a', fun x hx => by rw [evC_smul, evC_smul, ← ha' x hx]; ring⟩
    obtain ⟨b', hb'⟩ := key _ (hspan g hg)
    exact ⟨b', fun x hx => by rw [← hb' x hx, evC_rtr]⟩
  have hstab : ∀ h ∈ Γ, rtr (blk e h) b₀ ∈ multIdeal Γ (blk e) f := by
    intro h hh g hg
    obtain ⟨b', hb'⟩ := hb₀D (h.adjugate * g) (hΓ.mul_mem _ (hΓ.adj_mem _ hh) _ hg)
    refine ⟨rtr (blk e h) b', fun x hx => ?_⟩
    rw [evC_rtr, evC_rtr, ← hmul _ hx _ hh, ← hb' _ (hΓ.mul_mem _ hx _ hh), Matrix.mul_assoc,
      ← Matrix.mul_assoc h, Matrix.mul_adjugate, hΓ.det_eq _ hh, one_smul, Matrix.one_mul]
  have htop : multIdeal Γ (blk e) f = ⊤ := by
    by_contra hD
    obtain ⟨z, hz⟩ := exists_common_zero _ hD
    have hzp : z ∈ pts (blk e '' Γ) ℂ := by
      intro p hp
      rw [← evC_map]
      refine hz _ fun g _ => ⟨0, fun x hx => ?_⟩
      rw [evC_map, hp _ ⟨x, hx, rfl⟩]
      simp [evC]
    have hx₀p : blk e x₀ ∈ pts (blk e '' Γ) ℂ := fun p hp => hp _ ⟨x₀, hx₀, rfl⟩
    have := GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure ι _ hpre.aut_mem (ltr z b₀) (by
      rintro _ ⟨h, hh, rfl⟩
      rw [evC_ltr, ← evC_rtr]
      exact hz _ (hstab h hh)) _ (hm _ (hadj z hzp) _ hx₀p)
    rw [evC_ltr, ← Matrix.mul_assoc, Matrix.mul_adjugate, hdet z hzp, one_smul, Matrix.one_mul] at this
    exact hb₀ this
  have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ multIdeal Γ (blk e) f := htop ▸ Submodule.mem_top
  obtain ⟨b, hb⟩ := h1 1 hΓ.one_mem
  refine ⟨b, fun x hx => ?_⟩
  rw [← hb x hx, Matrix.mul_one]
  simp [evC]
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatClosure

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem subset_pts (Γ : Set (Matrix ι ι ℂ)) : Γ ⊆ pts Γ ℂ := fun g hg _ hf => hf g hg

omit [Fintype ι] [DecidableEq ι] in
theorem vanI_pts (Γ : Set (Matrix ι ι ℂ)) : vanI (pts Γ ℂ) = vanI Γ := by
  ext f
  exact ⟨fun h g hg => h g (subset_pts Γ hg), fun h g hg => hg f h⟩

omit [Fintype ι] [DecidableEq ι] in
theorem ev_map_aut (σ : ℂ ≃+* ℂ) (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    ev f (g.map σ) = σ (ev f g) := by
  unfold ev
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Matrix.map_apply]

theorem exists_poly_of_dual (φ : Module.Dual ℂ (Matrix ι ι ℂ)) :
    ∃ f : MvPolynomial (ι × ι) ℂ, ∀ g, evC f g = φ g := by
  refine ⟨∑ ij : ι × ι, MvPolynomial.C (φ (Matrix.single ij.1 ij.2 1)) * MvPolynomial.X ij, fun g => ?_⟩
  conv_rhs => rw [Matrix.matrix_eq_sum_single g]

  simp only [evC, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : Matrix.single i j (g i j) = g i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

theorem ratClosure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → IsQGroup (pts Γ ℂ) ∧ vanI (pts Γ ℂ) = vanI Γ ∧ Submodule.span ℂ (pts Γ ℂ) = Submodule.span ℂ Γ := by
  intro ι _ _ Γ h
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι Γ h ℂ
  refine ⟨⟨⟨h1, h2, h3, h4, ?_⟩, ?_⟩, vanI_pts Γ, ?_⟩
  · intro σ g hg f hf
    rw [ev_map_aut, hg f hf, map_zero]
  · intro g hg f hf
    exact hg f (by rw [vanI_pts]; exact hf)
  · refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) (Submodule.span_mono (subset_pts Γ))
    refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (Submodule.span ℂ Γ) y).1 fun φ hφ => ?_
    obtain ⟨f, hf⟩ := exists_poly_of_dual φ
    rw [← hf]
    refine GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure ι Γ h.aut_mem f (fun g hg => ?_) y hy
    rw [hf]
    exact (Submodule.mem_dualAnnihilator φ).1 hφ g (Submodule.subset_span hg)

end GlobalTheory.ClassFin.RatClosure
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.leftTranslateMatrixPoly_completelyReducible : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ U : Submodule ℂ (MvPolynomial (ι × ι) ℂ), (∀ g ∈ Γ, ∀ f ∈ U, ltr g f ∈ U) → ∃ U' : Submodule ℂ (MvPolynomial (ι × ι) ℂ), (∀ g ∈ Γ, ∀ f ∈ U', ltr g f ∈ U') ∧ IsCompl U U' := by
  first | exact @GlobalTheory.ClassFin.ltr_completely_reducible | exact GlobalTheory.ClassFin.ltr_completely_reducible | (intros; apply GlobalTheory.ClassFin.ltr_completely_reducible <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.relIndex_squares_sUnitsNumberField : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  first | exact @GlobalTheory.QNorm.relIndex_sqs_sUnits | exact GlobalTheory.QNorm.relIndex_sqs_sUnits | (intros; apply GlobalTheory.QNorm.relIndex_sqs_sUnits <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.first_inequality_sUnits_prime_degree : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧ p * (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ p ^ tNon p F δ S := by
  first | exact @GlobalTheory.CNorm.first_inequality_sUnits_prime | exact GlobalTheory.CNorm.first_inequality_sUnits_prime | (intros; apply GlobalTheory.CNorm.first_inequality_sUnits_prime <;> assumption)
end
