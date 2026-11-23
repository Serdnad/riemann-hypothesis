module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle006
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle007
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.Chebotarev.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Matrix

namespace Ht

variable {p q : Type} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

theorem htOf_le {R : Type} [CommRing R] {N₁ : Matrix p p R → ℝ≥0} {N₂ : Matrix q q R → ℝ≥0}
    {N : Matrix (p ⊕ q) (p ⊕ q) R → ℝ≥0} (hN : ∀ a b, N (fromBlocks a 0 0 b) ≤ max (N₁ a) (N₂ b))
    {X : GL (p ⊕ q) R} {x : GL p R} {y : GL q R} (h1 : X.1 = fromBlocks x.1 0 0 y.1) :
    htOf N X ≤ htOf N₁ x * htOf N₂ y := by
  have h2 : (X⁻¹).1 = fromBlocks (x⁻¹).1 0 0 (y⁻¹).1 :=
    Units.inv_eq_of_mul_eq_one_right (by rw [h1, fromBlocks_multiply]; simp)
  have hx := one_le_htOf N₁ x
  have hy := one_le_htOf N₂ y
  refine max_le (one_le_mul_of_one_le_of_one_le hx hy) (max_le ?_ ?_)
  · rw [h1]
    exact (hN _ _).trans (max_le ((le_htOf N₁ x).trans (le_mul_of_one_le_right' hy))
      ((le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)))
  · rw [h2]
    exact (hN _ _).trans (max_le ((inv_le_htOf N₁ x).trans (le_mul_of_one_le_right' hy))
      ((inv_le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)))

theorem opNorm_le (a : Matrix p p ℂ) (b : Matrix q q ℂ) : opNorm (fromBlocks a 0 0 b) ≤ max (opNorm a) (opNorm b) := by
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  obtain ⟨v, rfl⟩ : ∃ v : p ⊕ q → ℂ, x = WithLp.toLp 2 v := ⟨x.ofLp, rfl⟩
  set c : ℝ := ((max (opNorm a) (opNorm b) : ℝ≥0) : ℝ) with hc
  have h0 : 0 ≤ c := NNReal.coe_nonneg _
  have ha : ‖(WithLp.toLp 2 (a *ᵥ v ∘ .inl) : EuclideanSpace ℂ p)‖ ≤ c * ‖(WithLp.toLp 2 (v ∘ .inl) : EuclideanSpace ℂ p)‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.2 (le_max_left (opNorm a) (opNorm b))) (norm_nonneg _))
  have hb : ‖(WithLp.toLp 2 (b *ᵥ v ∘ .inr) : EuclideanSpace ℂ q)‖ ≤ c * ‖(WithLp.toLp 2 (v ∘ .inr) : EuclideanSpace ℂ q)‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.2 (le_max_right (opNorm a) (opNorm b))) (norm_nonneg _))
  have kn : ∀ w : p ⊕ q → ℂ, ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (p ⊕ q))‖ ^ 2 =
      ‖(WithLp.toLp 2 (w ∘ .inl) : EuclideanSpace ℂ p)‖ ^ 2 + ‖(WithLp.toLp 2 (w ∘ .inr) : EuclideanSpace ℂ q)‖ ^ 2 := fun w => by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]; rfl
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _)) two_ne_zero).1 ?_
  rw [Matrix.toEuclideanCLM_toLp, fromBlocks_mulVec, kn, mul_pow, kn, mul_add, ← mul_pow, ← mul_pow]
  simp only [zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl, Sum.elim_comp_inr]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) ha 2) (pow_le_pow_left₀ (norm_nonneg _) hb 2)

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

omit [DecidableEq p] [DecidableEq q] in
theorem normFin_le (v : Pl F) (a : Matrix p p (Fv F v ⊗[F] E)) (b : Matrix q q (Fv F v ⊗[F] E)) :
    normFin F v (fromBlocks a 0 0 b) ≤ max (normFin F v a) (normFin F v b) := by
  refine (normFin_le_iff F v).2 ?_
  rintro (i | i) (j | j)
  · exact (absFin_le_normFin F v a i j).trans (le_max_left _ _)
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, absFin_zero]; exact zero_le
  · exact (absFin_le_normFin F v b i j).trans (le_max_right _ _)

theorem normInf_le (w : InfinitePlace F) (a : Matrix p p (w.Completion ⊗[F] E)) (b : Matrix q q (w.Completion ⊗[F] E)) :
    normInf F w (fromBlocks a 0 0 b) ≤ max (normInf F w a) (normInf F w b) :=
  (normInf_le_iff F w).2 fun τ => by
    rw [fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    exact (opNorm_le _ _).trans (max_le_max ((normInf_le_iff F w).1 le_rfl τ) ((normInf_le_iff F w).1 le_rfl τ))

theorem heightGL_le {X : GL (p ⊕ q) (AE F E)} {x : GL p (AE F E)} {y : GL q (AE F E)} (h : X.1 = fromBlocks x.1 0 0 y.1) :
    heightGL F X ≤ heightGL F x * heightGL F y := by
  have b : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R), (Formalism.UG.bc φ X).1 = fromBlocks (Formalism.UG.bc φ x).1 0 0 (Formalism.UG.bc φ y).1 := fun φ => by
    show X.1.map φ = _
    rw [h, fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]; rfl
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib (finite_mulSupport_htFin F x) (finite_mulSupport_htFin F y)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => htOf_le (normInf_le F w) (b _))
    (finprod_le_finprod' (finite_mulSupport_htFin F _) ?_ fun v => htOf_le (normFin_le F v) (b _))
  exact ((finite_mulSupport_htFin F x).union (finite_mulSupport_htFin F y)).subset (Function.mulSupport_mul _ _)

end Ht

theorem htEmb : HtEmb := fun F _ _ _ _ _ _ _ _ _ =>
  ⟨1, fun _ _ _ h => (Ht.heightGL_le F h).trans_eq (one_mul _).symm,
    fun h h' => (heightGL_mul_le F h.1 h'.1).trans_eq (one_mul _).symm, fun h => one_le_heightGL F h.1⟩

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem euler_half {ι : Type} (q : ι → ℕ) (hq : ∀ v, 2 ≤ q v) (hs : ∀ s : ℝ, 1 < s → Summable fun v => (q v : ℝ) ^ (-s))
    (c : ι → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (k : ℕ) : ∃ d : ℂ → ℂ, DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re →
      d z ≠ 0 ∧ HasProd (fun v => (1 - c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ))))⁻¹) (d z) := by
  let x : ι → ℂ → ℂ := fun v z => -(c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ))))
  have h1 : ∀ v, (1 : ℝ) ≤ q v := fun v => by exact_mod_cast one_le_two.trans (hq v)
  have hx : ∀ v z (t : ℝ), t ≤ 2 * z.re + 1 → ‖x v z‖ ≤ (q v : ℝ) ^ (-t) := fun v z t ht => by
    rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos (two_pos.trans_le (hq v))]
    refine (mul_le_of_le_one_left (by positivity) (hc v)).trans (Real.rpow_le_rpow_of_exponent_le (h1 v) ?_)
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    linarith
  have hh : ∀ v z, 0 < z.re → ‖x v z‖ ≤ 1 / 2 := fun v z hz => by
    refine (hx v z 1 (by linarith)).trans ?_
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ two_pos (by exact_mod_cast hq v)
  have hb : ∀ v z (t : ℝ), 0 < z.re → t ≤ 2 * z.re + 1 → ‖Complex.log (1 + x v z)‖ ≤ 3 / 2 * (q v : ℝ) ^ (-t) :=
    fun v z t hz ht => (Complex.norm_log_one_add_half_le_self (hh v z hz)).trans (by gcongr; exact hx v z t ht)
  have hsl : ∀ v z, 0 < z.re → 1 + x v z ∈ Complex.slitPlane := fun v z hz =>
    Complex.mem_slitPlane_of_norm_lt_one ((hh v z hz).trans_lt (by norm_num))
  refine ⟨fun z => Complex.exp (-∑' v, Complex.log (1 + x v z)), fun z hz => ?_, fun z hz => ⟨Complex.exp_ne_zero _, ?_⟩⟩
  · have hz' : 0 < z.re := hz
    have ho : IsOpen {w : ℂ | z.re / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have := Complex.differentiableOn_tsum_of_summable_norm (F := fun v w => Complex.log (1 + x v w))
      ((hs (z.re + 1) (by linarith)).mul_left (3 / 2)) (fun v w hw => ?_) ho
      fun v w (hw : z.re / 2 < w.re) => hb v w _ (by linarith) (by linarith)
    · exact (this.differentiableAt (ho.mem_nhds (show z.re / 2 < z.re by linarith))).neg.cexp.differentiableWithinAt
    · have hw' : z.re / 2 < w.re := hw
      have hw0 : 0 < w.re := by linarith
      refine (DifferentiableAt.clog (f := fun w => 1 + x v w) ?_ (hsl v w hw0)).differentiableWithinAt
      have : (q v : ℂ) ≠ 0 := by exact_mod_cast (two_pos.trans_le (hq v)).ne'
      exact (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -(2 * z + (k + 1 : ℕ))) w).const_cpow
        (Or.inl this)).const_mul _).neg.const_add _
  · have := (Summable.of_norm_bounded ((hs (2 * z.re + 1) (by linarith)).mul_left (3 / 2))
      fun v => hb v z _ hz le_rfl).hasSum.neg.cexp
    convert this using 2 with v
    rw [Function.comp, Complex.exp_neg, Complex.exp_log (Complex.slitPlane_ne_zero (hsl v z hz)), sub_eq_add_neg]

open Classical in
theorem dProd : DProd := by
  intro F E _ _ _ _ _ n T
  choose d h1 h2 using fun i => euler_half (ι := {v : Pl F // v ∉ T}) (fun v => Ideal.absNorm v.1.asIdeal)
    (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
    (fun s hs => (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective
      (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective))
    (fun v => (if Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1) then 1 else -1) ^ (n - (i + 1)))
    (fun v => by split_ifs <;> simp) i
  exact ⟨fun z => ∏ i ∈ Finset.range n, d i z, DifferentiableOn.fun_finsetProd fun i _ => h1 i, fun z hz =>
    ⟨Finset.prod_ne_zero_iff.2 fun i _ => (h2 i z hz).1, hasProd_prod fun i _ => (h2 i z hz).2⟩⟩

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n' d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

local instance borelU {J : Matrix (Fin n) (Fin n) E} : BorelSpace (UA σ J) := ⟨rfl⟩

local instance topU {J : Matrix (Fin n) (Fin n) E} : IsTopologicalGroup (UA σ J) :=
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  Subgroup.instIsTopologicalGroupSubtypeMem _

def Ker (θ : UA σ X.J → UA σ W.J → ℂ) : Prop :=
  Continuous (fun x : UA σ X.J × UA σ W.J => θ x.1 x.2) ∧
    (∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, θ (γ * g) (γ' * h) = θ g h) ∧
    ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖θ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k

variable {θ : UA σ X.J → UA σ W.J → ℂ} {φ : UA σ W.J → ℂ} {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)}

theorem Ker.bd (hθ : Ker θ) (hφ : IsRapid φ) : ∃ (K : ℝ) (k : ℕ), 0 ≤ K ∧ ∀ g h, ‖φ h * star (θ g h)‖ ≤ K * (ht g : ℝ) ^ k := by
  obtain ⟨-, hi, C, k, hC⟩ := hθ
  obtain ⟨C', hC'⟩ := hφ.2.2 k
  have h0 : 0 ≤ C' := le_trans (by positivity) (hC' 1)
  refine ⟨|C| * C', k, by positivity, fun g h => ?_⟩
  have h1 : ‖θ g h‖ ≤ |C| * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k := by
    have := Monotone.map_ciInf_of_continuousAt (f := fun x : ℝ≥0 => |C| * (ht g : ℝ) ^ k * (x : ℝ) ^ k)
      (g := fun γ : ratU σ W.J => ht (γ.1 * h)) (by fun_prop) (fun x y hxy => by
        have : (x : ℝ) ≤ y := hxy
        dsimp only; gcongr) (OrderBot.bddBelow _)
    refine le_of_le_of_eq (le_ciInf fun γ => ?_) this.symm
    rw [← hi 1 (one_mem _) γ.1 γ.2, one_mul, mul_assoc, ← mul_pow]
    exact (hC _ _).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  rw [norm_mul, norm_star]
  calc _ ≤ ‖φ h‖ * (|C| * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = |C| * (ht g : ℝ) ^ k * (‖φ h‖ * (qht h : ℝ) ^ k) := by ring
    _ ≤ |C| * (ht g : ℝ) ^ k * C' := mul_le_mul_of_nonneg_left (hC' h) (by positivity)
    _ = _ := by ring

theorem Ker.meas (hθ : Ker θ) (hφ : IsRapid φ) (g) : AEStronglyMeasurable (fun h => φ h * star (θ g h)) (μ.restrict D) :=
  (hφ.1.mul (hθ.1.comp (Continuous.prodMk_right g)).star).aestronglyMeasurable

theorem Ker.int (hθ : Ker θ) (hφ : IsRapid φ) (hD : μ D < ⊤) (g) : IntegrableOn (fun h => φ h * star (θ g h)) D μ := by
  obtain ⟨K, k, -, hK⟩ := hθ.bd hφ
  exact Measure.integrableOn_of_bounded hD.ne (hφ.1.mul (hθ.1.comp (Continuous.prodMk_right g)).star).aestronglyMeasurable
    (Eventually.of_forall (hK g))

theorem Ker.cont [LocallyCompactSpace (UA σ X.J)] [FirstCountableTopology (UA σ X.J)]
    (hb : ∀ Ω : Set (UA σ X.J), IsCompact Ω → ∃ C : ℝ≥0, ∀ g ∈ Ω, ht g ≤ C) (hθ : Ker θ) (hφ : IsRapid φ) (hD : μ D < ⊤) :
    Continuous fun g => pet μ D φ (θ g) := by
  obtain ⟨K, k, h0, hK⟩ := hθ.bd hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  obtain ⟨Ω, hΩ, hg⟩ := exists_compact_mem_nhds g
  obtain ⟨C, hC⟩ := hb Ω hΩ
  refine continuousAt_of_dominated (bound := fun _ => K * (C : ℝ) ^ k) (Eventually.of_forall (hθ.meas hφ)) ?_
    (integrableOn_const hD.ne) (Eventually.of_forall fun h => ?_)
  · filter_upwards [hg] with x hx
    refine Eventually.of_forall fun h => (hK x h).trans ?_
    have : (ht x : ℝ) ≤ C := hC x hx
    gcongr
  · exact (continuous_const.mul (hθ.1.comp (Continuous.prodMk_left h)).star).continuousAt

theorem theta_act (om : Rep σ X W) (Ψ : Fn F n d) (u g : UA σ X.J) (h x : UA σ W.J) :
    theta om (om (u, h) Ψ) g x = theta om Ψ (g * u) (x * h) := by
  rw [theta, theta, ← Module.End.mul_apply, ← map_mul]; rfl

theorem theta_add {om : Rep σ X W} (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F _) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (hΨ : Ψ ∈ schA F _) (g h) : theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  simp only [theta, map_add (f := _)]
  exact thetaSum_add F (hp _ _ hΦ) (hp _ _ hΨ)

theorem theta_smul (om : Rep σ X W) (c : ℂ) (Φ : Fn F n d) (g h) : theta om (c • Φ) g h = c * theta om Φ g h := by
  simp only [theta, map_smul, thetaSum_smul]

theorem exists_form {om : Rep σ X W} (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F _)
    (hk : ∀ Ψ ∈ schA F (Fin n × Fin d), Ker (theta om Ψ)) (hD : μ D < ⊤) {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (P : Submodule ℂ Q) (C : Q →ₗ[ℂ] (UA σ W.J → ℂ)) (hr : ∀ Φ ∈ P, IsRapid (C Φ)) (g : UA σ X.J) :
    ∃ L : Q →ₗ[ℂ] Fn F n d →ₛₗ[starRingEnd ℂ] ℂ, ∀ Φ ∈ P, ∀ Ψ ∈ schA F _, L Φ Ψ = th om μ D (C Φ) Ψ g := by
  obtain ⟨q, hq⟩ := P.subtype.exists_leftInverse_of_injective P.ker_subtype
  obtain ⟨q', hq'⟩ := (schA F (Fin n × Fin d)).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have i := fun (a : Q) (b : Fn F n d) => (hk _ (q' b).2).int (hr _ (q a).2) hD g
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a b => th om μ D (C (q a)) (q' b) g) (fun a a' b => ?_)
    (fun c a b => ?_) (fun a b b' => ?_) fun c a b => ?_, fun Φ hΦ Ψ hΨ => ?_⟩
  · simp only [th, pet, map_add (f := _), Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (i a b) (i a' b)
  · simp only [th, pet, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, RingHom.id_apply]
  · simp only [th, pet, map_add (f := _), Submodule.coe_add, theta_add hp (q' b).2 (q' b').2, star_add, mul_add]
    exact integral_add (i a b) (i a b')
  · simp only [th, pet, map_smul, Submodule.coe_smul, theta_smul, star_mul', smul_eq_mul, mul_left_comm _ (star c),
      integral_const_mul]
    rfl
  · have e : q Φ = ⟨Φ, hΦ⟩ := LinearMap.congr_fun hq ⟨Φ, hΦ⟩
    have e' : q' Ψ = ⟨Ψ, hΨ⟩ := LinearMap.congr_fun hq' ⟨Ψ, hΨ⟩
    change th om μ D (C (q Φ)) (q' Ψ) g = _
    rw [e, e']

theorem th_right [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [Countable (ratU σ W.J)] (hD : IsFundamentalDomain (ratU σ W.J) D μ)
    {om : Rep σ X W} {Ψ : Fn F n d} (hθ : Ker (theta om Ψ)) (hφ : IsRapid φ) (g h) :
    th om μ D (fun x => φ (x * h)) (om (1, h) Ψ) g = th om μ D φ Ψ g := by
  simp only [th, pet, theta_act, mul_one]
  exact PositivityTheory.ThKF.L2.integral_right hD (fun x => φ x * star (theta om Ψ g x)) (fun γ hγ x => by
    rw [hφ.2.1 γ hγ, ← hθ.2.1 1 (one_mem _) γ hγ g x, one_mul]) h

theorem exists_fac {P A Z : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (f : P →ₗ[ℂ] A) (g : P →ₗ[ℂ] Z) (h : ∀ x, f x = 0 → g x = 0) : ∃ C : A →ₗ[ℂ] Z, ∀ x, C (f x) = g x := by
  obtain ⟨C, hC⟩ := ((LinearMap.ker f).liftQ g h ∘ₗ f.quotKerEquivRange.symm.toLinearMap).exists_extend
  refine ⟨C, fun x => (LinearMap.congr_fun hC ⟨f x, x, rfl⟩).trans ?_⟩
  exact congrArg ((LinearMap.ker f).liftQ g h) (f.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩)

end GlobalTheory.ThK.Dbl.TC

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DeterminantProjection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem det_ne_zero_of_sig {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := fun z => by
  obtain ⟨e, A, hA⟩ := h
  let q : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr e)
  have := congrArg Matrix.det (show (Aᵀ.submatrix id q * M.submatrix q q) * (A.map star).submatrix q id = Matrix.fromBlocks 1 0 0 (-1) by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]; exact hA)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, z, mul_zero, zero_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) this.symm

omit [NumberField E] in
theorem hermND_transpose {B : Base F E} {X : Spc F E n} {r s : ℕ} (h : X.IsHerm σ B r s) : IsHermND σ X.Jᵀ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨fun i j => h.herm j i, fun z => det_ne_zero_of_sig (h.sig w) ?_⟩
  rw [Matrix.det_transpose] at z
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, z, map_zero]

omit [NumberField E] in
theorem mem_UG_of {J : Matrix (Fin n) (Fin n) E} {g : GL (Fin n) (AE F E)} :
    g ∈ UG (cA σ) (incM F J) ↔ g ∈ HR (AF F) σ Jᵀ := by
  change (g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J) ↔ (g.1.map (sigR (AF F) σ))ᵀ * (incM F J)ᵀ * g.1 = (incM F J)ᵀ
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    show (cA σ : AE F E → AE F E) = sigR (AF F) σ from funext cA_eq]

def sec {A : Type} [CommRing A] (R : Matrix (Fin n) (Fin n) A) (h : R * R = R) : A →* Matrix (Fin n) (Fin n) A where
  toFun z := 1 + (z - 1) • R
  map_one' := by simp
  map_mul' a b := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul, add_assoc, ← add_smul]
    congr 2
    ring

theorem su_mem (hS : GlobalTheory.Published.StrongApproxSU) (hc : IsCMExt F E σ) {X : Spc F E n} (hJ : IsHermND σ X.Jᵀ) (hn : 2 ≤ n)
    (L : Subgroup (UA σ X.J)) (hL : IsClosed (L : Set (UA σ X.J))) (hr : ratU σ X.J ≤ L) {v : Pl F}
    (hv : ∀ u ∈ UAt σ X (evFin F v), u ∈ L) {ε : AF F} {e : AE F E} (hε : GlobalTheory.Published.IsPlacesIdem ∅ {v} ε) (e1 : e * e = e)
    (e2 : e * sigR (AF F) σ e = 0) (e3 : e + sigR (AF F) σ e = algebraMap (AF F) (AE F E) ε) (g : UA σ X.J)
    (hg : (mat g).det = 1) : g ∈ L := by
  let ι : HA (AF F) σ X.Jᵀ → UA σ X.J := fun x => ⟨HA.mat _ _ _ x, mem_UG_of.2 (show HR (AF F) σ X.Jᵀ from x).2⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have z : ∀ t, evFin F v t = 0 → t * ε = 0 := fun t ht => by
    refine Prod.ext (funext fun w => (congrArg (t.1 w * ·) (hε.2.1 w (Finset.notMem_empty w))).trans (mul_zero _))
      (FiniteAdeleRing.ext _ fun u => ?_)
    by_cases hu : u = v
    · subst hu
      exact (congrArg (· * ε.2 u) ht).trans (zero_mul _)
    · exact (congrArg (t.2 u * ·) (hε.2.2.2 u fun x => hu (Finset.mem_singleton.1 x))).trans (mul_zero _)
  refine closure_minimal (t := ι ⁻¹' L) ?_ (hL.preimage hι) (hS F E σ hc n _ hn hJ ∅ {v} ε hε
    (GlobalTheory.Published.StrongApprox.not_isCompact_split σ hn hJ v ε (hε.2.2.1 v (Finset.mem_singleton_self v)) e e1 e2 e3)
    (⟨g.1, mem_UG_of.1 g.2⟩ : HR (AF F) σ X.Jᵀ) (GlobalTheory.Published.StrongApprox.mem_SUAdelic.2 hg))
  rintro _ ⟨γ, ⟨-, y, -, hy⟩, h, ⟨-, hh⟩, rfl⟩
  have h1 : ι γ ∈ L := hr ⟨y, hy⟩
  have h2 : ι h ∈ L := hv _ fun t ht => Matrix.ext fun i j => by
    refine (congrArg (t • ·) (hh i j).symm).trans ?_
    rw [← Algebra.smul_def, smul_smul, z t ht, zero_smul, Matrix.zero_apply]
  exact mul_mem h1 h2

theorem exists_sec (hc : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ Jᵀ) (hn : 1 ≤ n) :
    ∃ S : normOne (cA σ) →* UA σ J, Continuous S ∧ (∀ z, (mat (S z)).det = (z.1 : (AE F E)ˣ)) ∧
      (∀ z : normOne (cA σ), (∃ k : E, k ≠ 0 ∧ ((z.1 : (AE F E)ˣ) : AE F E) = inclR (F := F) (AF F) k) → S z ∈ ratU σ J) ∧
      ∀ (z : normOne (cA σ)) (t : AF F), t • (((z.1 : (AE F E)ˣ) : AE F E) - 1) = 0 → t • (mat (S z) - 1) = 0 := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hσ := GlobalTheory.UnitaryHeckeBaseChange.sig_sig hc
  obtain ⟨u, hu⟩ := exists_aniso (σ : E →+* E) hσ Jᵀ (fun i j => hJ.1 j i) hJ.2
  have ha := inv_mul_cancel₀ hu
  have hb : (σ : E →+* E) (hsq (σ : E →+* E) Jᵀ u)⁻¹ = (hsq (σ : E →+* E) Jᵀ u)⁻¹ := by
    rw [map_inv₀, sigma_hsq (σ : E →+* E) hσ _ fun i j => hJ.1 j i]
  generalize (hsq (σ : E →+* E) Jᵀ u)⁻¹ = b at ha hb
  let i : E →+* AE F E := inclR (F := F) (AF F)
  have hR := proj_idem' _ _ _ _ ha
  have hi : ∀ a, i ((σ : E →+* E) a) = sigR (AF F) σ (i a) := fun _ => rfl
  have hA : i b * hsq (sigR (AF F) σ) (Jᵀ.map i) (fun k => i (u k)) = 1 := by
    rw [← hsq_map i (σ : E →+* E) _ hi, ← map_mul, ha, map_one]
  have h1 := proj_unitary (sigR (AF F) σ) (GlobalTheory.UnitaryHeckeBaseChange.cA_cA hc) (Jᵀ.map i)
    (fun a b => (hi _).symm.trans (congrArg i (hJ.1 b a))) _ _ hA (by rw [← hi, hb])
  have h2 := det_proj' _ _ _ _ hA
  rw [← proj_map i (σ : E →+* E) (sigR (AF F) σ) hi] at h1 h2
  generalize proj (σ : E →+* E) Jᵀ u b = R at hR h1 h2
  have hR' : R.map i * R.map i = R.map i := by rw [← Matrix.map_mul, hR]
  have cS : Continuous (sec _ hR') := continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)
  refine ⟨((Units.map (sec _ hR')).comp (normOne (cA σ)).subtype).codRestrict _ fun z =>
    mem_UG_of.2 (h1 z.1 (by rw [← cA_eq, mul_comm]; exact mem_normOne.1 z.2)),
    ((Continuous.units_map _ cS).comp continuous_subtype_val).subtype_mk _, fun z => h2 _,
    fun z ⟨k, k0, hk⟩ => ⟨Units.map (sec _ hR) (Units.mk0 k k0), Units.ext (Matrix.ext fun a b => ?_)⟩, fun z t ht => ?_⟩
  · change i ((1 : Matrix _ _ E) a b + (k - 1) * R a b) =
      (1 : Matrix _ _ (AE F E)) a b + (((z.1 : (AE F E)ˣ) : AE F E) - 1) * i (R a b)
    rw [hk, map_add (f := _), map_mul, map_sub, map_one, Matrix.one_apply, Matrix.one_apply, apply_ite i, map_one, map_zero]
  · change t • (1 + (((z.1 : (AE F E)ˣ) : AE F E) - 1) • R.map i - 1) = 0
    rw [add_sub_cancel_left, ← smul_assoc, ht, zero_smul]

omit [NumberField E] in
theorem conj_mem_UAt {X : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {u : UA σ X.J} (hu : u ∈ UAt σ X ev) (g : UA σ X.J) :
    g⁻¹ * u * g ∈ UAt σ X ev := fun t ht => by
  have : mat (g⁻¹ * u * g) - 1 = mat g⁻¹ * (mat u - 1) * mat g := by
    rw [mul_sub, sub_mul, mul_one]
    exact congrArg₂ (· - ·) rfl (Units.inv_mul g.1).symm
  rw [this, ← smul_mul_assoc, ← mul_smul_comm, hu t ht, mul_zero, zero_mul]

theorem mem_of_good (hS : GlobalTheory.Published.StrongApproxSU) (hH : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (hc : IsCMExt F E σ)
    [IsGalois ℚ E] {X : Spc F E n} (hJ : IsHermND σ X.Jᵀ) (hn : 2 ≤ n) (T : Finset (Pl F)) (L : Subgroup (UA σ X.J))
    (hL : IsClosed (L : Set (UA σ X.J))) (hr : ratU σ X.J ≤ L)
    (hv : ∀ v ∉ T, SplitsFully E v → ∀ u ∈ UAt σ X (evFin F v), u ∈ L) (g : UA σ X.J) : g ∈ L := by
  obtain ⟨v, a, b, ε, e, hε, e1, e2, e3⟩ := exists_split hH hc T
  obtain ⟨S, cS, s1, s2, s3⟩ := exists_sec hc hJ (by omega)
  have hg : IsUnit (incM F X.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ (Matrix.det_transpose X.J ▸ hJ.2)).map _
  let z : normOne (cA σ) := ⟨_, det_mem_normOne ⟨fun a b => congrArg (inclR (F := F) (AF F)) (hJ.1 b a), hg⟩ g⟩
  have h1 : S z ∈ L := normOne_mem hH hc T (L.comap S) (hL.preimage cS) (fun z h => hr (s2 z h))
    (fun v a b z hz => hv v a b _ fun t ht => s3 z t (hz t ht)) z
  have h2 : g * S z⁻¹ ∈ L := su_mem hS hc hJ hn L hL hr (hv v a b) hε e1 e2 e3 _ (by
    rw [show mat (g * S z⁻¹) = mat g * mat (S z⁻¹) from rfl, Matrix.det_mul, s1]
    exact z.1.mul_inv)
  simpa using mul_mem h2 h1

theorem constOfGood_of (hS : GlobalTheory.Published.StrongApproxSU) (hH : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) : ConstOfGood := by
  intro F E _ _ _ _ _ σ B n X r s hB hX hn T f hf hr hv g
  have := hB.galois
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let L : Subgroup (UA σ X.J) :=
    { carrier := ⋂ g, {x | f (x * g) = f g}
      one_mem' := Set.mem_iInter.2 fun g => congrArg f (one_mul g)
      mul_mem' := fun {a b} ha hb => Set.mem_iInter.2 fun g =>
        (congrArg f (mul_assoc a b g)).trans ((Set.mem_iInter.1 ha _).trans (Set.mem_iInter.1 hb _))
      inv_mem' := fun {a} ha => Set.mem_iInter.2 fun g =>
        (Set.mem_iInter.1 ha _).symm.trans (congrArg f (mul_inv_cancel_left a g)) }
  have := mem_of_good hS hH hB.cm (hermND_transpose hX) hn T L
    (isClosed_iInter fun g => isClosed_eq (hf.comp (continuous_mul_const g)) continuous_const)
    (fun γ h => Set.mem_iInter.2 (hr γ h)) (fun v a b u hu => Set.mem_iInter.2 fun g =>
      (congrArg f (by group)).trans (hv v a b _ (conj_mem_UAt hu g) g)) g
  exact (congrArg f (mul_one g)).symm.trans (Set.mem_iInter.1 this 1)

end GlobalTheory.ThK.Dbl

end
end
