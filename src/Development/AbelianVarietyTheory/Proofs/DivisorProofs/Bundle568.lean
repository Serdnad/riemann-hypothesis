module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOfQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle517
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeShift

theorem hmon_mul_unit {ζ : ℂ} (hζ : ‖ζ‖ = 1) (n : ℤ) (v : ℂ) :
    GlobalTheory.HeckeTheta.hmon n (ζ * v) = ζ ^ (-n) * GlobalTheory.HeckeTheta.hmon n v := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · have hc : starRingEnd ℂ ζ = ζ⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hζ]; simp
    rw [map_mul, mul_pow, hc, inv_pow, ← zpow_natCast, ← zpow_neg, Int.toNat_of_nonneg h]
  · rw [mul_pow, ← zpow_natCast ζ, Int.toNat_of_nonneg (by omega)]

theorem factor_shift (n : ℤ) (y : ℝ) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * (z * w)) *
                 Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * (z * w)‖ ^ 2 : ℝ) : ℂ) =
      (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) *
        (GlobalTheory.HeckeTheta.hmon n ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) *
          Complex.exp ((-2 * Real.pi * ‖(Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w‖ ^ 2 : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hE : Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) = Real.exp (y / 2) * ‖z‖ := by
    rw [Real.log_pow, add_div, Real.exp_add]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * Real.log ‖z‖ / 2 = Real.log ‖z‖ by push_cast; ring, Real.exp_log hn0]
  have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hζ : ‖z / ((‖z‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn0.ne']
  have hv : (Real.exp (y / 2) : ℂ) * (z * w) =
      (z / ((‖z‖ : ℝ) : ℂ)) * ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) := by
    rw [hE]; push_cast; field_simp
  rw [hv, hmon_mul_unit hζ, norm_mul, hζ, one_mul, mul_assoc]

theorem sum_ulog {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {I : Type} [Fintype I]
    (φ : I → K →+* ℂ) (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) : ∑ i, GlobalTheory.HeckeTheta.ulog φ u i = 0 := by
  have hbij : Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
    constructor
    · intro i j hij
      obtain ⟨k, _, hk⟩ := hφ (φ i)
      have hi := hk i (Or.inl rfl)
      rcases InfinitePlace.mk_eq_iff.1 hij with h | h
      · rw [hi, hk j (Or.inl h)]
      · rw [hi, hk j (Or.inr (by rw [← h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]))]
    · intro w
      obtain ⟨k, hk, _⟩ := hφ w.embedding
      refine ⟨k, ?_⟩
      rcases hk with h | h
      · simp only; rw [← h, InfinitePlace.mk_embedding]
      · simp only; rw [← InfinitePlace.mk_conjugate_eq (φ k), ← h, InfinitePlace.mk_embedding]
  have h0 := NumberField.Units.sum_mult_mul_log u
  rw [← (Equiv.ofBijective _ hbij).sum_comp] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : (InfinitePlace.mk (φ i)).mult = 2 :=
    InfinitePlace.mult_isComplex ⟨_, IsTotallyComplex.isComplex _⟩
  simp only [Equiv.ofBijective_apply, InfinitePlace.apply, hm, GlobalTheory.HeckeTheta.ulog, Real.log_pow]

end GlobalTheory.HeckeShift

theorem GlobalTheory.HeckeShift.term_unit_mul : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ),
    GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) *
        GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  intro K _ _ _ I _ φ hφ n s u α y
  have hsum : (∑ i, (y + GlobalTheory.HeckeTheta.ulog φ u) i) = ∑ i, y i := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, GlobalTheory.HeckeShift.sum_ulog φ hφ u, add_zero]
  have hu0 : ((u : 𝓞 K) : K) ≠ 0 := by
    intro h
    exact (Units.ne_zero u) (by exact_mod_cast h)
  unfold GlobalTheory.HeckeMellin.term
  rw [hsum, ← mul_assoc]
  congr 1
  unfold GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeStrip.wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [GlobalTheory.HeckeTheta.dil, GlobalTheory.HeckeTheta.emb, GlobalTheory.HeckeTheta.ulog, Pi.add_apply, map_mul]
  exact GlobalTheory.HeckeShift.factor_shift (n i) (y i) ((map_ne_zero _).2 hu0) (φ i α)
end
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwoEq

theorem ofReal_prod_cpow {ι : Type} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (c : ℂ) :
    (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ c = ∏ i ∈ s, ((r i : ℂ) ^ c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, ofReal_mul,
      mul_cpow_ofReal_nonneg (hr j (Finset.mem_insert_self _ _)) (Finset.prod_nonneg fun i hi => hr i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hr i (Finset.mem_insert_of_mem hi)]

variable {F : Type} [Field F] [NumberField F]

theorem eisTerm_eq_kFac (σ : ℂ) (z : Emb F → ℂ) (a b : F) :
    eisTerm 2 σ z (a, b) = kFac F σ * ∏ τ : Emb F, phi σ ((τ a : ℂ) + (τ b : ℂ) * z τ) := by
  unfold eisTerm kFac phi
  rw [← Finset.prod_mul_distrib, norm_prod, ofReal_prod_cpow _ _ (fun _ _ => norm_nonneg _), ← Finset.prod_inv_distrib,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hn : ‖latPt z (a, b) τ‖ = (2 * Real.pi) * ‖(τ a : ℂ) + (τ b : ℂ) * z τ‖ := by
    simp only [latPt, norm_mul, norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hn, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
  simp only [latPt, mul_inv, mul_pow]
  ring

theorem split_zero (I : FractionalIdeal (𝓞 F)⁰ F) (g : F → ℂ) (h : Summable (fun ν : {ν : F // ν ∈ I} => g ν.1)) :
    ∑' ν : {ν : F // ν ∈ I}, g ν.1 = g 0 + ∑' ν : NZ I, g ν.1 := by
  classical
  have h0 : (0 : F) ∈ I := (I : Submodule (𝓞 F) F).zero_mem
  rw [h.tsum_eq_add_tsum_ite ⟨0, h0⟩]
  congr 1
  let e : NZ I → {ν : F // ν ∈ I} := fun ν => ⟨ν.1, ν.2.1⟩
  have he : Function.Injective e := fun x y hxy => Subtype.ext (congrArg Subtype.val hxy : _)
  rw [← he.tsum_eq]
  · refine tsum_congr fun ν => ?_
    have : e ν ≠ ⟨0, h0⟩ := fun h' => ν.2.2 (congrArg Subtype.val h' : _)
    simp only [this, if_false, e]
  · intro x hx
    have hx0 : x ≠ ⟨0, h0⟩ := by
      intro h'; apply hx; simp [h']
    exact ⟨⟨x.1, x.2, fun h' => hx0 (Subtype.ext h')⟩, rfl⟩

theorem prod_abs_emb [IsTotallyReal F] (b : F) : ∏ τ : Emb F, |τ b| = |((Algebra.norm ℚ b : ℚ) : ℝ)| := by
  rw [← Finset.abs_prod]
  congr 1
  apply Complex.ofReal_injective
  push_cast
  exact prod_emb b

theorem fTerm_zero [IsTotallyReal F] (hzero : ∀ (σ : ℂ) (y : ℝ), y ≠ 0 → GlobalTheory.HeckeTwo.hTrans σ 0 y = GlobalTheory.HeckeTwo.cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ)) (σ : ℂ) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b : F} (hb : b ≠ 0) :
    fTerm σ z b 0 = (∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))) *
      ((|((Algebra.norm ℚ b : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  unfold fTerm
  rw [← prod_abs_emb, ofReal_prod_cpow _ _ (fun _ _ => abs_nonneg _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hy : 0 < (z τ).im := hz τ
  have hτb : τ b ≠ 0 := (map_ne_zero τ).2 hb
  rw [map_zero, zero_mul, zero_mul, ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    hzero σ _ (mul_ne_zero hτb hy.ne'), abs_mul, abs_of_pos hy, ofReal_mul,
    mul_cpow_ofReal_nonneg (abs_nonneg _) hy.le]
  ring

theorem gFun_eq_eisSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ σ : ℂ, 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) ∧ GlobalTheory.HeckeTwo.gFun Zb 𝔞 𝔟 σ z = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 2 σ z := by
  intro F _ _ _ 𝔞 𝔟 Zb hZ σ hσ z hz
  have hS := GlobalTheory.T.summable_hilbertEisensteinLatticeClass_weight_two F 𝔞 𝔟 σ hσ z hz
  refine ⟨hS, ?_⟩
  have hinv : ∀ (ε : (𝓞 F)ˣ) (a b : F),
      eisTerm 2 σ z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = eisTerm 2 σ z (a, b) :=
    fun ε a b => eisTerm_unit even_two σ z ε a b
  obtain ⟨-, -, hBs, hsum⟩ := GlobalTheory.T.tsum_latticePair_unitQuotient_regroup F 𝔞 𝔟 (eisTerm 2 σ z) hinv hS
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  set P : ℂ := ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) with hPdef
  set K : ℂ := kFac F σ * (omegaFactor 𝔞 : ℂ) with hKdef
  have hper : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' a : {a : F // a ∈ latM 𝔞}, eisTerm 2 σ z (a.1, c.out.1) =
        K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) +
          K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1 := by
    intro c
    have hb : c.out.1 ≠ 0 := c.out.2.2
    obtain ⟨hfs, hP⟩ := GlobalTheory.T.heckeWeightTwo_poisson_summation_fractionalIdeal F 𝔞 σ hσ z hz c.out.1 hb
    simp_rw [eisTerm_eq_kFac]
    rw [tsum_mul_left, hP.tsum_eq, split_zero _ _ hfs, fTerm_zero GlobalTheory.T.heckePhiFourierTransform_zero_eq σ hz hb]
    ring
  have hz2 := GlobalTheory.T.hasSum_abs_norm_cpow_unitClasses_partialZeta F 𝔟 Zb hZ (1 + 2 * σ) (by simp; linarith)
  rw [show -(1 + 2 * σ) = -1 - 2 * σ by ring] at hz2
  have hX := hz2.mul_left (K * P)
  have hT : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =>
      K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) +
          K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1) := by
    simpa only [hper] using hBs
  have hY : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =>
      K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1) :=
    (hT.sub hX.summable).congr fun c => by ring
  unfold eisSum eisClass
  rw [hsum, tsum_congr hper, hX.summable.tsum_add hY, hX.tsum_eq, tsum_mul_left]
  have hA : ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ z (c.out.1, 0) = aPart 𝔞 σ :=
    tsum_congr fun c => by simp [eisTerm, latPt]
  rw [hA]
  unfold gFun bZero bOne
  rw [if_neg hσ0]
  ring

end GlobalTheory.HeckeTwoEq
end
end

section

namespace GlobalTheory.HilbAff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem exists_unique_lift (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {N r : ℕ}
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (C : Type) [CommRing C] [Algebra A C]
    (J : Ideal (C ⊗[A] B))
    (hli : LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k))))
    (hsp : Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k)))) = ⊤)
    (huniv : ∀ (A' : Type) [CommRing A'] [Algebra A A'] (J' : Ideal (A' ⊗[A] B)),
      LinearIndependent A' (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k))) →
      Submodule.span A' (Set.range (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k)))) = ⊤ →
      ∃! φ : C →ₐ[A] A', J' = J.map (Algebra.TensorProduct.map φ (AlgHom.id A B)))
    (hgood : Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (xI A B C J))
    (Z : Scheme.{0}) (g : Z ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    (hI : Good A B r g I)
    (hy : ∀ U : Z.affineOpens, letI := (secAlg A g U).toAlgebra
      Function.Bijective fun c : Fin r → Γ(Z, U) => kappa A B g I U (∑ k, c k ⊗ₜ[A] e (σ k))) :
    ∃! h : Z ⟶ Spec (CommRingCat.of C), (functor A B r).map h.op
      (⟨Spec.map (CommRingCat.ofHom (algebraMap A C)), ⟨xI A B C J, hgood⟩⟩ :
        (functor A B r).obj (op (Spec (CommRingCat.of C)))) = ⟨g, ⟨I, hI⟩⟩ := by
  have hch : ∀ U : Z.affineOpens, ∃ φ : C →+* Γ(Z, U), ∃ hφ : ∀ a : A,
      φ (algebraMap A C a) = secAlg A g U a,
      letI := (secAlg A g U).toAlgebra
      RingHom.ker (kappa A B g I U) = J.map (Algebra.TensorProduct.map
        ({ toRingHom := φ, commutes' := hφ } : C →ₐ[A] Γ(Z, U)) (AlgHom.id A B)) ∧
      ∀ ψ : C →ₐ[A] Γ(Z, U), RingHom.ker (kappa A B g I U) =
        J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B)) → ψ.toRingHom = φ := by
    intro U
    letI := (secAlg A g U).toAlgebra
    obtain ⟨-, hli', hsp'⟩ := (GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mp (hy U)
    obtain ⟨φ, hφ, hφu⟩ := huniv Γ(Z, U) _ hli' hsp'
    exact ⟨φ.toRingHom, φ.commutes, hφ, fun ψ hψ => congrArg AlgHom.toRingHom (hφu ψ hψ)⟩
  choose φ hφA hφ hφu using hch
  have compat : ∀ (U V : Z.affineOpens) (hUV : (U : Z.Opens) ≤ V),
      (Z.presheaf.map (homOfLE hUV).op).hom.comp (φ V) = φ U := by
    intro U V hUV
    letI iU := (secAlg A g U).toAlgebra
    letI iV := (secAlg A g V).toAlgebra
    obtain ⟨ρ, hρ, hle⟩ := GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict A B g I U V hUV
    let φV : C →ₐ[A] Γ(Z, V) := { toRingHom := φ V, commutes' := hφA V }
    have hmap : J.map (Algebra.TensorProduct.map (ρ.comp φV) (AlgHom.id A B)) =
        (RingHom.ker (kappa A B g I V)).map (Algebra.TensorProduct.map ρ (AlgHom.id A B)) := by
      rw [hφ V, show Algebra.TensorProduct.map (ρ.comp φV) (AlgHom.id A B) =
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)).comp
          (Algebra.TensorProduct.map φV (AlgHom.id A B)) by
        rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id]]
      exact (Ideal.map_map (Algebra.TensorProduct.map φV (AlgHom.id A B)).toRingHom
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)).toRingHom).symm
    have hsp2 := (GlobalTheory.T.basis_quotient_tensor_base_change A B C Γ(Z, U) (fun k => e (σ k)) J (ρ.comp φV) hli hsp).2
    have hliU := ((GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mp (hy U)).2.1
    have heq := GlobalTheory.T.ideals_eq_of_span_independent A B Γ(Z, U) (fun k => e (σ k)) _ _ (hmap ▸ hle) hsp2 hliU
    rw [← hφu U (ρ.comp φV) heq.symm, ← hρ]
    rfl
  obtain ⟨Φ, hΦ, hΦu⟩ := GlobalTheory.T.ring_map_from_affine_opens Z C φ compat
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_hom_affineHilbertBaseSectionRingHom Z C Φ
  have hhU : ∀ U : Z.affineOpens, secAlg C h U = φ U := fun U => by
    rw [← secAlg_res C h (le_top : (U : Z.Opens) ≤ ⊤), hh, hΦ U]
  have hgA : h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = g := by
    apply eq_of_secAlg_top
    rw [secAlg_comp, hh]
    obtain ⟨Ψ, -, hΨu⟩ := GlobalTheory.T.ring_map_from_affine_opens Z A (fun U => secAlg A g U) (fun U V hUV => secAlg_res A g hUV)
    have h1 := hΨu (Φ.comp (algebraMap A C)) (fun U => by
      rw [← RingHom.comp_assoc, hΦ U]; ext a; exact hφA U a)
    have h2 := hΨu (secAlg A g ⊤) (fun U => secAlg_res A g le_top)
    rw [h1, h2]
  refine ⟨h, ?_, ?_⟩
  · subst hgA
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
    apply GlobalTheory.T.idealSheaf_eq_of_ker_tensorToSubschemeSections
    intro U
    obtain ⟨φ', hφ', hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h U
    letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
    refine (hker.trans ?_).trans (hφ U).symm
    congr 2
    exact AlgHom.ext fun c => congrArg (fun F => F c) (hφ'.trans (hhU U))
  · intro h' hh'
    have hU : ∀ U : Z.affineOpens, secAlg C h' U = φ U := by
      intro U
      obtain ⟨φ', hφ', hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h' U
      cases hh'
      rw [← hφ']
      exact hφu U φ' hker
    have hΦ' : secAlg C h' ⊤ = Φ := hΦu _ (fun U => by rw [secAlg_res, hU U])
    exact eq_of_secAlg_top C (hΦ'.trans hh.symm)

theorem chart_represents (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) :
    ∃ (X : Scheme.{0}) (x : (functor A B r).obj (op X)), IsAffine X ∧ LocallyOfFiniteType x.1 ∧
      Basic A B e σ x ∧ ∀ (Z : Scheme.{0}) (y : (functor A B r).obj (op Z)), Basic A B e σ y →
        ∃! g : Z ⟶ X, (functor A B r).map g.op x = y := by
  obtain ⟨C, _, _, J, hfp, hli, hsp, huniv⟩ := GlobalTheory.hilbChart_representable A B N r e σ
  have hgood : Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (xI A B C J) :=
    GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_quotient_basis A B C J (fun k => e (σ k)) hli hsp
  let x : (functor A B r).obj (op (Spec (CommRingCat.of C))) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap A C)), ⟨xI A B C J, hgood⟩⟩
  have hBx : ∀ (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)),
      Basic A B e σ ((functor A B r).map h.op x) := by
    intro Z h
    rw [functor_map, basic_iff_kappa]
    intro U
    obtain ⟨φ, -, hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h U
    letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
    obtain ⟨hli', hsp'⟩ := GlobalTheory.T.basis_quotient_tensor_base_change A B C Γ(Z, U) (fun k => e (σ k)) J φ hli hsp
    refine (GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mpr ⟨GlobalTheory.T.affineHilbertTensorToSubschemeSections_surjective A B _ _ U, ?_, ?_⟩
    · rw [hker]; exact hli'
    · rw [hker]; exact hsp'
  have hBasic : Basic A B e σ x := by
    simpa using hBx _ (𝟙 _)
  refine ⟨Spec (CommRingCat.of C), x, inferInstance, ?_, hBasic, ?_⟩
  · show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A C)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    haveI := hfp
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  intro Z y hy
  obtain ⟨g, I, hI⟩ := y
  rw [basic_iff_kappa] at hy
  exact exists_unique_lift A B e σ C J hli hsp huniv hgood Z g I hI hy
end GlobalTheory.HilbAff
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_pow_cocycle_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    (∀ k j, GlobalTheory.SecGlue.IsCombIn (V j) (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j) (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ t k j)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k] ![algebraMap R (Localization.Away (f j * f k)) (f k) ^ N]) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    ∃ (M : ℕ) (t' : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
      (∀ k j, t' k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) ∧
      (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t' k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) ∧
      (∀ k j, t' k j ⁻¹ᵁ V j = ⊤) ∧
      ∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t' k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t' k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N + M)] := by
  first | exact @GlobalTheory.SecGlue.exists_pow_cocycle | exact GlobalTheory.SecGlue.exists_pow_cocycle | (intros; apply GlobalTheory.SecGlue.exists_pow_cocycle <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  first | exact @GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion | exact GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion | (intros; apply GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule : ∀ (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M], Injective ((homSh J).obj (op M)) := by
  first | (exact @GlobalTheory.EtC.homSh_injective) | (exact GlobalTheory.EtC.homSh_injective) | (intros; apply GlobalTheory.EtC.homSh_injective  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact : ∀ (R : Type) [CommRing R] (J X : Shv R), Module.Injective (ULift.{1} R) (X ⟶ J) → ∀ (A B C : ModuleCat.{1} (ULift.{1} R)) (u : A ⟶ B) (v : B ⟶ C), (∀ b, v.hom b = 0 → ∃ a, u.hom a = b) → ∀ f : X ⟶ (homSh J).obj (op B), f ≫ (homSh J).map u.op = 0 → ∃ g : X ⟶ (homSh J).obj (op C), g ≫ (homSh J).map v.op = f := by
  first | (exact @GlobalTheory.EtC.lift_homSh) | (exact GlobalTheory.EtC.lift_homSh) | (intros; apply GlobalTheory.EtC.lift_homSh  <;> assumption)
end

section

open IsDedekindDomain NumberField
open scoped Classical


theorem _root_.GlobalTheory.T.slice_multiplicationDerivativeWord_iteratedFDeriv : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (u : κ → mixedEmbedding.mixedSpace F) (i : ℕ) (vs : List (κ → mixedEmbedding.mixedSpace F))
        (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
            vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x := by
  first | exact @GlobalTheory.WeilL2Words.slice_word_mul_fderivs | exact GlobalTheory.WeilL2Words.slice_word_mul_fderivs | (intros; apply GlobalTheory.WeilL2Words.slice_word_mul_fderivs <;> assumption)
end

section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

theorem _root_.GlobalTheory.T.mem_end_lattice_of_trace_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → (∀ Z ∈ endLat Λ, IsIntegral ℤ (Y * Z).trace) → Y ∈ endLat Λ := by
  first | exact @GlobalTheory.LieDisc.mem_endLat_of_trace_integral | exact GlobalTheory.LieDisc.mem_endLat_of_trace_integral | (intros; apply GlobalTheory.LieDisc.mem_endLat_of_trace_integral <;> assumption)
end

section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

theorem _root_.GlobalTheory.T.end_lattice_trace_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → IsIntegral ℤ Y.trace := by
  first | exact @GlobalTheory.LieDisc.trace_integral_main | exact GlobalTheory.LieDisc.trace_integral_main | (intros; apply GlobalTheory.LieDisc.trace_integral_main <;> assumption)
end
